{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines the visual scene types, which act as the view model interface for the UI, and to implement
-- -- the forward and backward mappings between scenes and curve states.
module Scene
  ( -- * Visual scene types
    VisualEpicycle (..),
    VisualScene (..),

    -- * Forward mapping
    evalScene,

    -- * Scene edits
    SceneEdit (..),
    applySceneEdit,

    -- * Backward mapping
    UpdateStrategy (..),
    Strategy (..),
    heuristicStrategy,
    naiveStrategy,
    applyEdit,
    applyEditWithInfo,
    fuseDMStrategy,
    EditInfo (..),
    tracePoints,
    StrategyMetrics (..),
  )
where

import AST (AST (..), ASTSort (SCurve), CurveState (..), EpicycleId, IEnv, SortVal (VNum), Stage (Numbered), evalEpiParams, evalExpr)
import Data.Complex (cis)
import Data.Map qualified as Map
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Delta
import Unembedding.Env qualified as Ue
import Update.Delta (Conflict, fuseDMBackward)
import Update.SnS.Common
import Update.SnS.Heuristic (curveUpdateWithInfo)
import Update.SnS.Naive (curveUpdateNaive)
import Update.Types qualified as Update (EpicycleParam (..))
import Vec (Vec (..), fromComplex, scale)

-- | The visual representation of a single epicycle at a specific point in time.
data VisualEpicycle = VisualEpicycle
  { -- | Which epicycle this represents
    veId :: EpicycleId,
    -- | Centre of the circle
    veCentre :: Vec,
    -- | Endpoint of the arm
    veEndpoint :: Vec,
    -- | Radius of the circle
    veRadius :: Double,
    -- | Frequency of rotation
    veFreq :: Int,
    -- | Phase
    vePhase :: Double,
    -- | Current arm angle = freq * t + phase
    veArmAngle :: Double,
    -- | Whether construction should be shown for this epicycle
    veVisible :: Bool
  }
  deriving (Show, Eq)

-- | geometric snapshot of an epicycle curve at a time @t@
data VisualScene = VisualScene
  { -- | The time at which this snapshot was taken
    vsTime :: Double,
    -- | All epicycles in the curve keyed by their ID
    vsEpicycles :: Map EpicycleId VisualEpicycle,
    -- | Epicycles in evaluation order (for rendering arms in sequence)
    vsEpicycleOrder :: NonEmpty EpicycleId,
    -- | The final pen-tip position (sum of all contributions), in curve-local space
    vsPenTip :: Vec
  }
  deriving (Show)

epicycleContrib :: Double -> Int -> Double -> Double -> Vec
epicycleContrib radius freq phase t =
  let angle = realToFrac freq * t + phase
   in scale radius (fromComplex (cis angle))

evalScene :: (DiffEnv env) => CurveState env -> Double -> VisualScene
evalScene cs t =
  let (tip, ves) = walk cs.envParams cs.curveAST (Vec 0 0)
   in VisualScene
        { vsTime = t,
          vsEpicycles = Map.fromList [(veId v, v) | v <- toList ves],
          vsEpicycleOrder = fmap veId ves,
          vsPenTip = tip
        }
  where
    walk :: IEnv env -> AST Numbered env SCurve -> Vec -> (Vec, NonEmpty VisualEpicycle)
    walk env (Epicycle eid r f p) centre =
      let radius = fromRational (evalExpr env r)
          freq = evalExpr env f
          phase = fromRational (evalExpr env p)
          endpoint = centre + epicycleContrib radius freq phase t
          ve =
            VisualEpicycle
              { veId = eid,
                veCentre = centre,
                veEndpoint = endpoint,
                veRadius = radius,
                veFreq = freq,
                vePhase = phase,
                veArmAngle = realToFrac freq * t + phase,
                veVisible = True
              }
       in (endpoint, ve :| [])
    walk env (Append a b) centre =
      let (centre', ves1) = walk env a centre
          (centre'', ves2) = walk env b centre'
       in (centre'', ves1 <> ves2)
    walk env (Let val body) centre =
      walk (Ue.ECons (VNum (evalExpr env val)) env) body centre

-- | A  description of an edit to the visual scene.
data SceneEdit
  = -- | Set the radius of an epicycle to a new value
    SetRadius EpicycleId Double
  | -- | Set the frequency of an epicycle to a new value
    SetFrequency EpicycleId Int
  | -- | Set the phase of an epicycle to a new value
    SetPhase EpicycleId Double
  deriving (Show, Eq)

-- | Apply a 'SceneEdit' to a 'VisualScene', producing an updated scene.
applySceneEdit :: SceneEdit -> VisualScene -> VisualScene
applySceneEdit edit scene = case edit of
  SetRadius eid newR ->
    scene {vsEpicycles = Map.adjust (\ve -> ve {veRadius = newR}) eid scene.vsEpicycles}
  SetFrequency eid newF ->
    let newAngle ve = fromIntegral Double newF * scene.vsTime + ve.vePhase
     in scene
          { vsEpicycles =
              Map.adjust
                (\ve -> ve {veFreq = newF, veArmAngle = newAngle ve})
                eid
                scene.vsEpicycles
          }
  SetPhase eid newP ->
    let newAngle ve = fromIntegral Double ve.veFreq * scene.vsTime + newP
     in scene
          { vsEpicycles =
              Map.adjust
                (\ve -> ve {vePhase = newP, veArmAngle = newAngle ve})
                eid
                scene.vsEpicycles
          }

-- | An update strategy maps a 'SceneEdit' backward through the AST.
-- This abstraction allows swapping in different backward implementations
-- (heuristic cost model, lenses, etc) while keeping the same forward mapping and edit representation.
data UpdateStrategy strategy = UpdateStrategy
  { -- | Name for display purposes
    usName :: Text,
    -- | how to update the curve satate given an edit
    usRun ::
      forall env.
      (DiffEnv env) =>
      SceneEdit ->
      CurveState env ->
      Maybe (CurveState env, EditInfo strategy)
  }

-- | Information about a backward edit
data EditInfo strategy = EditInfo
  { eiStrategy :: Text,
    eiMetrics :: StrategyMetrics strategy
  }

deriving instance (Show (StrategyMetrics strategy)) => Show (EditInfo strategy)

type data Strategy = SnS | FuseDM

data StrategyMetrics (strat :: Strategy) where
  SearchMetrics ::
    -- | how deep the chosen update was in the search tree
    EditDepth ->
    -- | alternatives considered
    [(Text, EditDepth)] ->
    StrategyMetrics SnS
  FuseDMMetrics :: [Conflict] -> StrategyMetrics FuseDM

deriving instance Show (StrategyMetrics strat)

-- | The heuristic backward strategy
heuristicStrategy :: UpdateStrategy SnS
heuristicStrategy = UpdateStrategy "Heuristic" $ \edit cs ->
  case edit of
    SetRadius eid newR -> wrapInfo "Heuristic" <$> curveUpdateWithInfo @Update.Radius eid (toRational newR) cs
    SetFrequency eid newF -> wrapInfo "Heuristic" <$> curveUpdateWithInfo @Update.Frequency eid newF cs
    SetPhase eid newP -> wrapInfo "Heuristic" <$> curveUpdateWithInfo @Update.Phase eid (toRational newP) cs

naiveStrategy :: UpdateStrategy SnS
naiveStrategy = UpdateStrategy "Naive (first match)" $ \edit cs ->
  case edit of
    SetRadius eid newR -> wrapInfo "Naive" <$> curveUpdateNaive @Update.Radius eid (toRational newR) cs
    SetFrequency eid newF -> wrapInfo "Naive" <$> curveUpdateNaive @Update.Frequency eid newF cs
    SetPhase eid newP -> wrapInfo "Naive" <$> curveUpdateNaive @Update.Phase eid (toRational newP) cs

fuseDMStrategy :: UpdateStrategy FuseDM
fuseDMStrategy = UpdateStrategy "FuseDM" $ \edit (CurveState ast env) ->
  let findEpiParams eid = case evalEpiParams env ast eid of
        Just params -> params
        Nothing -> error "Epicycle ID not found during edit" -- this should be impossible
      curveDelta = case edit of
        SetRadius eid newR ->
          let (curR, _, _) = findEpiParams eid
              diff = toRational newR - curR
           in CurveDeltaEpi eid (AtomicNumDelta (ANumDeltaAdd diff)) NumDeltaId NumDeltaId
        SetFrequency eid newF ->
          let (_, curF, _) = findEpiParams eid
              diff = newF - curF
           in CurveDeltaEpi eid NumDeltaId (AtomicNumDelta (ANumDeltaAdd diff)) NumDeltaId
        SetPhase eid newP ->
          let (_, _, curP) = findEpiParams eid
              diff = toRational newP - curP
           in CurveDeltaEpi eid NumDeltaId NumDeltaId (AtomicNumDelta (ANumDeltaAdd diff))

      (newCS, conflicts) = fuseDMBackward curveDelta (CurveState ast env)
      info = EditInfo "FuseDM" (FuseDMMetrics conflicts)
   in Just (newCS, info)

-- | wrap the result of a SnS update with edit info
wrapInfo ::
  Text ->
  UpdateInfo env ->
  (CurveState env, EditInfo SnS)
wrapInfo name (UpdateInfo cs depth alts) =
  (cs, EditInfo name (SearchMetrics depth alts))

-- | Apply a scene edit backward using the given strategy.
applyEdit :: (DiffEnv env) => UpdateStrategy strategy -> SceneEdit -> CurveState env -> Maybe (CurveState env)
applyEdit strategy edit cs = fmap fst (usRun strategy edit cs)

-- | Apply a scene edit backward using the given strategy, returning edit info.
applyEditWithInfo :: UpdateStrategy strategy -> forall env. (DiffEnv env) => SceneEdit -> CurveState env -> Maybe (CurveState env, EditInfo strategy)
applyEditWithInfo = usRun

-- | Compute a trace of a scene's point  by evaluating the scene's epicycle chain at
-- evenly spaced time values from 0 to the given limit.
tracePoints :: VisualScene -> Double -> Double -> VU.Vector Vec
tracePoints scene step tMax =
  let ordered = V.fromList [scene.vsEpicycles Map.! eid | eid <- toList scene.vsEpicycleOrder]
      evalAt t = V.foldl' (\acc ve -> acc + epiContrib ve t) (Vec 0 0) ordered
      numSteps = floor (tMax / step) + 1
   in VU.generate numSteps (\i -> evalAt (fromIntegral _ i * step))
  where
    epiContrib :: VisualEpicycle -> Double -> Vec
    epiContrib ve = epicycleContrib ve.veRadius ve.veFreq ve.vePhase
