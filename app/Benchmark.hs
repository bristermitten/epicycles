{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TupleSections #-}

-- | Benchmark to compare the backwards semantics on a number of different scenarios.
module Main (main) where

import AST (CurveState (..), EpicycleId (..), approxEq)
import BenchMetrics (BenchScene (..), astNodeCount, benchScenes)
import Colonnade
import Data.Foldable (maximum, minimum)
import Data.List ((!!))
import Data.List.NonEmpty qualified as NE (filter, reverse)
import Data.Map qualified as Map
import PrettyAST ()
import Scene
import System.Random (RandomGen, mkStdGen, randomR)
import Text.Printf
import Update.SnS
import Update.Types

toDouble :: (Integral a) => a -> Double
toDouble = fromIntegral Double

data BenchStrategy env strategy = BenchStrategy
    { bsLabel :: BenchStrategyId
    , bsApply :: (DiffEnv env) => SceneEdit -> CurveState env -> Maybe (CurveState env, EditInfo strategy)
    }

data AnyBenchStrategy env where
    AnyBenchStrategy :: BenchStrategy env strat -> AnyBenchStrategy env

data BenchStrategyId = Heuristic | Naive | FuseDM
    deriving (Eq, Show, Ord)

heuristicBench :: BenchStrategy env SnS
heuristicBench = BenchStrategy Heuristic $ \edit cs -> usRun heuristicStrategy edit cs

naiveBench :: BenchStrategy env SnS
naiveBench = BenchStrategy Naive $ \edit cs -> usRun naiveStrategy edit cs

fuseDMBench :: BenchStrategy env FuseDM
fuseDMBench = BenchStrategy FuseDM $ \edit cs -> usRun fuseDMStrategy edit cs

allStrategies :: [AnyBenchStrategy env]
allStrategies =
    [ AnyBenchStrategy heuristicBench
    , AnyBenchStrategy naiveBench
    , AnyBenchStrategy fuseDMBench
    ]

-- | results about a single edit being applied to a scene
data BenchRow = BenchRow
    { brScene :: Text
    -- ^ the scene name
    , scenario :: ScenarioId
    -- ^ the scenario name
    , brSeed :: Int
    -- ^ the random seed for this run
    , brEditIndex :: Int
    -- ^ the index of the edit in the scenario
    , strategy :: BenchStrategyId
    -- ^ the strategy used for this edit
    , brTargetEpi :: EpicycleId
    -- ^ the epicycle being edited
    , brParam :: EpicycleParam
    -- ^ the parameter being edited (radius, frequency, or phase)
    , brAstNodesBefore :: Int
    -- ^ the number of AST nodes in the curve before the edit
    , brAstNodesAfter :: Int
    -- ^ the number of AST nodes in the curve after the edit
    , brSolverSuccess :: Bool
    -- ^ whether the strategy successfully produced a new curve state
    , brLocalPutGetHolds :: Bool
    -- ^ whether the putget law held for this edit
    , brUnintendedEpiChanges :: Int
    -- ^ the number of unintended epicycle changes
    , brScenePutGetHolds :: Bool
    }
    deriving (Show)

data EditSpec = EditSpec
    { esEpiIndex :: Int
    , esParam :: EpicycleParam
    , esDelta :: Double
    }

data ScenarioId = Random | Drag | SiblingChain | Oscillate | BigJump
    deriving (Eq, Show, Ord)

data Scenario = Scenario
    { scName :: ScenarioId
    , scGenerate :: NonEmpty EpicycleId -> Int -> [EditSpec]
    }

paramDelta :: EpicycleParam -> Double
paramDelta Radius = 1.0
paramDelta Phase = 0.5
paramDelta Frequency = 1.0

focusBursts :: Int -> Int -> [(Int, EpicycleParam)]
focusBursts seed n =
    let allPairs = [(i, p) | i <- [0 .. n - 1], p <- [Radius, Frequency, Phase]]
     in shuffleSeeded (mkStdGen seed) allPairs

shuffleSeeded :: (RandomGen g) => g -> [a] -> [a]
shuffleSeeded _ [] = []
shuffleSeeded g xs =
    let (i, g') = randomR (0, length xs - 1) g
     in case splitAt i xs of
            (h, picked : t) -> picked : shuffleSeeded g' (h <> t)
            _ -> xs

randomScenario :: Int -> Scenario
randomScenario n = Scenario Random randomF
  where
    randomF eids seed =
        take n . unfoldr step $ mkStdGen seed
      where
        nEpi = length eids
        step g0 =
            let (i, g1) = randomR (0, nEpi - 1) g0
                (p, g2) = randomR (0, 2) g1
                (d, g3) = randomR (-20.0, 20.0) g2
             in Just (EditSpec i (toEnum p) d, g3)

dragScenario :: Int -> Scenario
dragScenario k = Scenario Drag $ \eids seed ->
    let mkBurst (i, p) = replicate k (EditSpec i p (paramDelta p))
     in concatMap mkBurst (focusBursts seed (length eids))

siblingChainScenario :: Int -> Scenario
siblingChainScenario k = Scenario SiblingChain $ \eids seed ->
    let n = length eids
        pairs = shuffleSeeded (mkStdGen seed) [(i, i + 1) | i <- [0 .. n - 2]]
        mkChain (a, b) =
            take k . cycle $
                [ EditSpec a Radius (paramDelta Radius)
                , EditSpec b Radius (paramDelta Radius)
                , EditSpec a Frequency (paramDelta Frequency)
                , EditSpec b Frequency (paramDelta Frequency)
                , EditSpec a Phase (paramDelta Phase)
                , EditSpec b Phase (paramDelta Phase)
                ]
     in pairs >>= mkChain

oscillateScenario :: Int -> Scenario
oscillateScenario k = Scenario Oscillate $ \eids seed ->
    let mkBurst (i, p) =
            take k . cycle $
                [ EditSpec i p (paramDelta p)
                , EditSpec i p (-(paramDelta p))
                ]
     in concatMap mkBurst (focusBursts seed (length eids))

bigJumpScenario :: Scenario
bigJumpScenario = Scenario BigJump $ \eids seed ->
    let magnitude = \case Radius -> 100.0; Frequency -> 5.0; Phase -> 180.0
     in [EditSpec i p (magnitude p) | (i, p) <- focusBursts seed (length eids)]

allScenarios :: [Scenario]
allScenarios =
    let runs = 300
     in [ randomScenario runs
        , dragScenario runs
        , siblingChainScenario runs
        , oscillateScenario runs
        , bigJumpScenario
        ]

runLockstep :: ScenarioId -> Int -> BenchScene -> [EditSpec] -> [BenchRow]
runLockstep scenarioName seed scene specs =
    let initialStates = map (,bsState scene) allStrategies
     in go 0 initialStates specs
  where
    go _ _ [] = []
    go i states (spec : rest) =
        let stepped = map (advance scenarioName scene seed i spec) states
         in map snd stepped <> go (i + 1) (map fst stepped) rest

advance :: ScenarioId -> BenchScene -> Int -> Int -> EditSpec -> (AnyBenchStrategy '[], CurveState '[]) -> ((AnyBenchStrategy '[], CurveState '[]), BenchRow)
advance scenarioName scene seed i spec (AnyBenchStrategy strat, cs) =
    case bsApply strat edit cs of
        Nothing ->
            -- the edit failed
            let row = baseBenchRow{brSolverSuccess = False}
             in ((AnyBenchStrategy strat, cs), row)
        Just (cs', _) ->
            let sceneAfter = evalScene cs' 0
                (unintended, _, hit) = intentMetrics edit eid sceneBefore sceneAfter
                row =
                    baseBenchRow
                        { brAstNodesAfter = astNodeCount cs'.curveAST
                        , brSolverSuccess = True
                        , brLocalPutGetHolds = hit
                        , brUnintendedEpiChanges = unintended
                        , brScenePutGetHolds = hit && unintended == 0
                        }
             in ((AnyBenchStrategy strat, cs'), row)
  where
    eid = toList scene.bsEpicycleIds !! esEpiIndex spec
    sceneBefore = evalScene cs 0
    (edit, paramName, _) = makeEditFromScene sceneBefore eid spec
    nodesBefore = astNodeCount cs.curveAST
    baseBenchRow =
        BenchRow
            (bsName scene)
            scenarioName
            seed
            i
            strat.bsLabel
            eid
            paramName
            nodesBefore
            0
            False
            False
            0
            False

-- | measure if any "intent" escaped (i.e. if any unintended epicycles were changed, and if so, how many)
intentMetrics :: SceneEdit -> EpicycleId -> VisualScene -> VisualScene -> (Int, Bool, Bool)
intentMetrics edit targetEid before after =
    let changed eid = case (Map.lookup eid (vsEpicycles before), Map.lookup eid (vsEpicycles after)) of
            (Just b, Just a) -> not (epiApproxEq b a)
            _ -> True
        unintended = length $ filter changed (filter (/= targetEid) (Map.keys (vsEpicycles before)))
        hit = case Map.lookup targetEid (vsEpicycles after) of
            Nothing -> False
            Just ve -> case edit of
                SetRadius _ v -> approxEq v (veRadius ve)
                SetFrequency _ v -> v == veFreq ve
                SetPhase _ v -> approxEq v (vePhase ve)
     in (unintended, unintended > 0, hit)

epiApproxEq :: VisualEpicycle -> VisualEpicycle -> Bool
epiApproxEq a b = approxEq (veRadius a) (veRadius b) && veFreq a == veFreq b && approxEq (vePhase a) (vePhase b)

makeEditFromScene :: VisualScene -> EpicycleId -> EditSpec -> (SceneEdit, EpicycleParam, Double)
makeEditFromScene sc eid spec =
    case Map.lookup eid (vsEpicycles sc) of
        Nothing -> (SetRadius eid 0, Radius, 0)
        Just ve -> case esParam spec of
            Radius -> (SetRadius eid (max 1 (veRadius ve + esDelta spec)), Radius, veRadius ve)
            Frequency -> (SetFrequency eid (max 1 (veFreq ve + round (esDelta spec))), Frequency, toDouble (veFreq ve))
            Phase -> (SetPhase eid (vePhase ve + esDelta spec * 0.1), Phase, vePhase ve)

-- | information about a putput test
data PPRow = PPRow
    { ppScene :: Text
    , ppStrategy :: BenchStrategyId
    , ppEpi :: EpicycleId
    , ppParam :: EpicycleParam
    , ppV1 :: Double
    -- ^ the value of the parameter in the first edit
    , ppV2 :: Double
    -- ^ the value of the parameter in the second edit
    , ppIntermediateOk :: Bool
    -- ^ did the intermediate edit sequence succeed
    , ppDirectOk :: Bool
    -- ^ did the direct edit succeed
    , ppHolds :: Bool
    }

ppTestCases :: EpicycleParam -> [(Double, Double)]
ppTestCases Radius = [(v1, v2) | v1 <- [10, 20, 30, 60, 90], v2 <- [10, 15, 20, 40, 70, 100], v1 /= v2]
ppTestCases Frequency = [(v1, v2) | v1 <- [2, 4, 6], v2 <- [3, 5, 7], v1 /= v2]
ppTestCases Phase = [(v1, v2) | v1 <- [0.5, 1.5], v2 <- [1.0, 2.0], v1 /= v2]

ppMakeEdit :: EpicycleId -> EpicycleParam -> Double -> SceneEdit
ppMakeEdit eid Radius v = SetRadius eid v
ppMakeEdit eid Frequency v = SetFrequency eid (round v)
ppMakeEdit eid Phase v = SetPhase eid v

{- | measure the putput "disagreement" between two edits
i.e. numer of epicycles that changed in the intermediate edit but not the direct edit, and vice versa
-}
putPutDisagreement :: EpicycleId -> VisualScene -> VisualScene -> (Int, Int)
putPutDisagreement targetEid s1 s2 =
    let diffs =
            [ ( eid
              , case (Map.lookup eid (vsEpicycles s1), Map.lookup eid (vsEpicycles s2)) of
                    (Just a, Just b) -> epiApproxEq a b
                    _ -> False
              )
            | eid <- Map.keys (vsEpicycles s1)
            ]
        tgtDiff = length [() | (eid, eq) <- diffs, eid == targetEid, not eq]
        otherDiff = length [() | (eid, eq) <- diffs, eid /= targetEid, not eq]
     in (tgtDiff, otherDiff)

ppRunOne :: BenchScene -> AnyBenchStrategy '[] -> Int -> EpicycleParam -> (Double, Double) -> PPRow
ppRunOne scene (AnyBenchStrategy strat) epiIdx param (v1, v2) =
    let eid = toList scene.bsEpicycleIds !! epiIdx
        s0 = bsState scene
        apply edit cs = fst <$> bsApply strat edit cs
        intermediateState = apply (ppMakeEdit eid param v1) s0 >>= apply (ppMakeEdit eid param v2)
        directState = apply (ppMakeEdit eid param v2) s0
        holds = case (intermediateState, directState) of
            (Just ss, Just ds) -> let (t, o) = putPutDisagreement eid (evalScene ss 0) (evalScene ds 0) in (t == 0 && o == 0)
            _ -> False
     in PPRow (bsName scene) strat.bsLabel eid param v1 v2 (isJust intermediateState) (isJust directState) holds

main :: IO ()
main = runBenchmarks

runBenchmarks :: IO ()
runBenchmarks = do
    putStrLn "Running Benchmarks...\n"
    benchRows <-
        concat
            <$> sequence
                [ pure (runLockstep scenario.scName seed scene (scenario.scGenerate scene.bsEpicycleIds seed))
                | scene <- benchScenes
                , scenario <- allScenarios
                , seed <- [100, 200, 300, 400, 500 :: Int]
                ]

    let ppRows =
            [ ppRunOne scene strat epiIdx param pair
            | scene <- benchScenes
            , strat <- allStrategies
            , epiIdx <- [0 .. length scene.bsEpicycleIds - 1]
            , param <- [Radius, Frequency, Phase]
            , pair <- ppTestCases param
            ]

    printAstSizeStats benchRows
    printLeakageStats benchRows
    printReversibilityStats benchRows
    printPutPutStats ppRows

groupByKey :: (Ord k) => (a -> k) -> [a] -> [(k, NonEmpty a)]
groupByKey f = Map.toList . fmap NE.reverse . Map.fromListWith (<>) . map (\x -> (f x, x :| []))

mean :: NonEmpty Double -> Double
mean xs = sum xs / toDouble (length xs)

stddev :: NonEmpty Double -> Double
stddev xs =
    let m = mean xs
     in sqrt (sum (fmap (\x -> (x - m) ^ (2 :: Int)) xs) / toDouble (length xs))

median :: NonEmpty Double -> Double
median xs =
    let sorted = sort (toList xs)
        n = length sorted
        m = n `div` 2
     in case (sorted !!? m, sorted !!? (m - 1)) of
            (Just mid, Just midPrev) ->
                if odd n then mid else (midPrev + mid) / 2
            (Just mid, Nothing) -> mid -- length = 1
            _ -> 0 -- length = 0, shouldn't happen due to NonEmpty

-- | measure the ast growth with a bunch of FuseDM edits
printAstSizeStats :: [BenchRow] -> IO ()
printAstSizeStats rows = do
    putStrLn "AST Size Growth"

    let fmRows = filter (\r -> strategy r == FuseDM && r.brSolverSuccess) rows
        runs = groupByKey (\r -> (r.brScene, r.scenario, r.brSeed)) fmRows
        sceneStats = groupByKey (\((sc, _, _), _) -> sc) runs

        tableData =
            mapMaybe
                ( \(scene, groupRuns) -> do
                    let finalsList = fmap (\(_, rs) -> toDouble $ brAstNodesAfter (last rs)) (toList groupRuns)
                    finals <- nonEmpty finalsList
                    let initial = toDouble $ brAstNodesBefore (head (snd (head groupRuns)))
                        minF = minimum finals
                        maxF = maximum finals
                        stdF = stddev finals
                        growth = minF / initial
                    pure (scene, round initial, round minF, round maxF, stdF, growth, length groupRuns)
                )
                sceneStats

        spec :: Colonnade Headed (Text, Int, Int, Int, Double, Double, Int) String
        spec =
            mconcat
                [ headed "Scene" (\(s, _, _, _, _, _, _) -> toString s)
                , headed "Initial" (\(_, i, _, _, _, _, _) -> show i)
                , headed "Final Min" (\(_, _, m, _, _, _, _) -> show m)
                , headed "Final Max" (\(_, _, _, m, _, _, _) -> show m)
                , headed "Final Std" (\(_, _, _, _, s, _, _) -> printf "%.3f" s)
                , headed "Growth x" (\(_, _, _, _, _, g, _) -> printf "%.3fx" g)
                , headed "Runs" (\(_, _, _, _, _, _, r) -> show r)
                ]

    putStrLn $ ascii spec tableData
    putStrLn ""

printLeakageStats :: [BenchRow] -> IO ()
printLeakageStats rows = do
    putStrLn "total intent leakage when oscillating on shared scenes"

    let oscRows = filter (\r -> scenario r == Oscillate && brSolverSuccess r) rows
        runs = groupByKey (\r -> (strategy r, brScene r, brSeed r)) oscRows
        runTotals = fmap (\((strat, _, _), rs) -> (strat, sum (fmap brUnintendedEpiChanges rs))) runs
        stratStats = groupByKey fst runTotals

        tableData =
            mapMaybe
                ( \(strat, vals) -> do
                    leakages <- nonEmpty (fmap (toDouble . snd) (toList vals))
                    pure (strat, mean leakages, median leakages, round (minimum leakages) :: Int, round (maximum leakages) :: Int, length vals)
                )
                stratStats

        spec :: Colonnade Headed (BenchStrategyId, Double, Double, Int, Int, Int) String
        spec =
            mconcat
                [ headed "Strategy" (\(s, _, _, _, _, _) -> show s)
                , headed "Mean" (\(_, m, _, _, _, _) -> printf "%.1f" m)
                , headed "Median" (\(_, _, m, _, _, _) -> printf "%.1f" m)
                , headed "Min" (\(_, _, _, m, _, _) -> show m)
                , headed "Max" (\(_, _, _, _, m, _) -> show m)
                , headed "Runs" (\(_, _, _, _, _, r) -> show r)
                ]

    putStrLn $ ascii spec tableData
    putStrLn ""

printReversibilityStats :: [BenchRow] -> IO ()
printReversibilityStats rows = do
    putStrLn "AST shape reversibility (i.e. whether the same curve was returned to after a round trip) when oscillating on shared scenes"

    let oscRows = filter (\r -> r.scenario == Oscillate && brSolverSuccess r) rows
        runs = groupByKey (\r -> (strategy r, brScene r, brSeed r)) oscRows
        runMetrics =
            map
                ( \((strat, _, _), rs) ->
                    let returned = brAstNodesAfter (last rs) == brAstNodesBefore (head rs)
                        leakage = sum (fmap brUnintendedEpiChanges (toList rs))
                     in (strat, (returned, leakage))
                )
                runs
        stratStats = groupByKey fst runMetrics

        tableData =
            mapMaybe
                ( \(strat, vals) -> do
                    let metrics = fmap snd (toList vals)
                        pctReturned = 100 * (toDouble (length (filter fst metrics)) / toDouble (length metrics))
                    leakages <- nonEmpty (fmap (toDouble . snd) metrics)
                    pure (strat, pctReturned, mean leakages)
                )
                stratStats

        spec :: Colonnade Headed (BenchStrategyId, Double, Double) String
        spec =
            mconcat
                [ headed "Strategy" (\(s, _, _) -> show s)
                , headed "Returned %" (\(_, p, _) -> printf "%.1f" p)
                , headed "Mean Leakage" (\(_, _, m) -> printf "%.1f" m)
                ]

    putStrLn $ ascii spec tableData
    putStrLn ""

printPutPutStats :: [PPRow] -> IO ()
printPutPutStats rows = do
    putStrLn "PutPut violations"

    let stratStats = groupByKey ppStrategy rows

        tableData =
            map
                ( \(strat, rs) ->
                    let n = toDouble (length rs)
                        intermediateOk = 100 * (toDouble (length (NE.filter ppIntermediateOk rs)) / n)
                        dirOk = 100 * (toDouble (length (NE.filter ppDirectOk rs)) / n)
                        asymm = 100 * (toDouble (length (NE.filter (\r -> ppIntermediateOk r /= ppDirectOk r) rs)) / n)
                        endDis = 100 * (toDouble (length (NE.filter (not . ppHolds) rs)) / n)
                        combined = 100 * (toDouble (length (NE.filter (\r -> not (ppHolds r) || (ppIntermediateOk r /= ppDirectOk r)) rs)) / n)
                     in (strat, intermediateOk, dirOk, asymm, endDis, combined, length rs)
                )
                stratStats

        spec :: Colonnade Headed (BenchStrategyId, Double, Double, Double, Double, Double, Int) String
        spec =
            mconcat
                [ headed "Strategy" (\(s, _, _, _, _, _, _) -> show s)
                , headed "Intermediate OK %" (\(_, v, _, _, _, _, _) -> printf "%.2f" v)
                , headed "Direct OK %" (\(_, _, v, _, _, _, _) -> printf "%.2f" v)
                , headed "Asymm %" (\(_, _, _, v, _, _, _) -> printf "%.2f" v)
                , headed "End Dis %" (\(_, _, _, _, v, _, _) -> printf "%.2f" v)
                , headed "Combined %" (\(_, _, _, _, _, v, _) -> printf "%.2f" v)
                , headed "Tests" (\(_, _, _, _, _, _, r) -> show r)
                ]

    putStrLn $ ascii spec tableData
    putStrLn ""
