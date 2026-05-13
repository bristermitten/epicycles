-- | a set of benchmark scenes and metrics for evaluating the updates quantitavely.
module BenchMetrics (
    astNodeCount,
    astLetCount,
    BenchScene (..),
    benchScenes,
)
where

import AST (AST (..), CurveExpr (epicycle), CurveState (..), EpicycleId, Expr (let_), SCurve, Stage (..), numberCurve)
import AST.Instances ()
import Scene (VisualScene (..), evalScene, vsEpicycleOrder)
import Text.Show (show)
import Unembedding (runClose)
import Unembedding.Env qualified as Ue

-- | count the total number of AST nodes in a curve expression
astNodeCount :: AST x env s -> Int
astNodeCount (Lit _) = 1
astNodeCount (Param_ _ _) = 1
astNodeCount (Add a b) = 1 + astNodeCount a + astNodeCount b
astNodeCount (Mul a b) = 1 + astNodeCount a + astNodeCount b
astNodeCount (Recip a) = 1 + astNodeCount a
astNodeCount (Epicycle _ r f p) = 1 + astNodeCount r + astNodeCount f + astNodeCount p
astNodeCount (Append a b) = 1 + astNodeCount a + astNodeCount b
astNodeCount (Let val body) = 1 + astNodeCount val + astNodeCount body

-- | count the total number of let bindings in a curve expression
astLetCount :: AST x env s -> Int
astLetCount Lit{} = 0
astLetCount Param_{} = 0
astLetCount (Add a b) = astLetCount a + astLetCount b
astLetCount (Mul a b) = astLetCount a + astLetCount b
astLetCount (Recip a) = astLetCount a
astLetCount (Epicycle _ r f p) = astLetCount r + astLetCount f + astLetCount p
astLetCount (Append a b) = astLetCount a + astLetCount b
astLetCount (Let val body) = 1 + astLetCount val + astLetCount body

data BenchScene = BenchScene
    { bsName :: Text
    , bsTerm :: forall e. (CurveExpr e) => e SCurve
    , bsState :: CurveState '[]
    , bsEpicycleIds :: NonEmpty EpicycleId
    }

instance Show BenchScene where
    show (BenchScene name e state ids) =
        let ast :: AST Parsed '[] SCurve = runClose e
         in "BenchScene "
                <> Text.Show.show name
                <> "\n"
                <> "AST: "
                <> Text.Show.show ast
                <> "\n"
                <> "State: "
                <> Text.Show.show state
                <> "\n"
                <> "EpicycleIds: "
                <> Text.Show.show ids

mkBenchScene :: Text -> (forall e. (CurveExpr e) => e SCurve) -> BenchScene
mkBenchScene name term =
    let cs = CurveState (numberCurve term) Ue.ENil
        scene = evalScene cs 0
     in BenchScene
            { bsName = name
            , bsTerm = term
            , bsState = cs
            , bsEpicycleIds = vsEpicycleOrder scene
            }

-- | baseline curve with nothing unusual
curveSimple :: (CurveExpr e) => e SCurve
curveSimple =
    epicycle 120 1 0
        <> epicycle 60 3 0
        <> epicycle 30 5 0

-- | curve with a shared variable
curveNested :: (CurveExpr e, Expr e) => e SCurve
curveNested = let_ 40 $ \r ->
    epicycle r 1 0
        <> epicycle (r * 0.5) (-2) 0
        <> epicycle r 5 0

-- | curve with a shared variable that appears in multiple types of parameter
curveShared :: (CurveExpr e, Expr e) => e SCurve
curveShared = let_ 80 $ \rBase ->
    epicycle rBase 1 0
        <> epicycle (rBase * 0.45) (-5) (rBase * 0.02)
        <> epicycle (rBase * 0.15) 13 0

-- | curve with parameters split into multiple literal sub-expressions, which creates multiple valid branches for the sns semantics
curveAmbiguous :: (CurveExpr e) => e SCurve
curveAmbiguous =
    epicycle (60 + 60) 1 0
        <> epicycle (20 * 3) 3 0
        <> epicycle (10 + 10 + 10) 5 0
        <> epicycle (5 + 5 + 5 + 5) 7 0

{- | to examine how the semantics differ - sns is nondet, fusedm is left biased. so they should pick different updates for this one.
both epicycles use both bindings, so updating either parameter creates an aliasing problem.
-}
curveLeftBias :: (CurveExpr e, Expr e) => e SCurve
curveLeftBias =
    let_ 40 $ \x ->
        let_ 20 $ \y ->
            epicycle (x + y) 1 0
                <> epicycle (x * y * 0.05) 3 0

-- | deep sharing - 1 parameter shared across 5 epicycles
curveDeepShared :: (CurveExpr e, Expr e) => e SCurve
curveDeepShared = let_ 50 $ \r ->
    epicycle r 1 0
        <> epicycle (r * 0.5) 3 0
        <> epicycle (r * 0.25) 5 0
        <> epicycle (r * 2) 7 0
        <> epicycle (r * 0.1) 11 0

-- | The deterministic stability counterexample from the dissertations section `PutPut (Composability)'
curveDualRecip :: (CurveExpr e, Expr e) => e SCurve
curveDualRecip = let_ 0.1 $ \x ->
    let_ 0.05 $ \y ->
        epicycle (recip x + recip y) 1 0

-- | additive aliasing - sns will often fail here because it tries to update both leaves individually
curveAddAlias :: (CurveExpr e, Expr e) => e SCurve
curveAddAlias = let_ 10 $ \r ->
    epicycle (r + r) 1 0

-- | if we replace the r with a literal, the problem should resolve itself
curveMulAlias :: (CurveExpr e, Expr e) => e SCurve
curveMulAlias = let_ 10 $ \r ->
    epicycle (r * 2) 1 0

-- | same as the additive alias, but worse
curveSquareAlias :: (CurveExpr e, Expr e) => e SCurve
curveSquareAlias = let_ 10 $ \r ->
    epicycle (r * r) 1 0

benchScenes :: [BenchScene]
benchScenes =
    [ mkBenchScene "Simple" curveSimple
    , mkBenchScene "NestedLet" curveNested
    , mkBenchScene "Shared" curveShared
    , mkBenchScene "Ambiguous" curveAmbiguous
    , mkBenchScene "LeftBias" curveLeftBias
    , mkBenchScene "DeepShared" curveDeepShared
    , mkBenchScene "DualRecip" curveDualRecip
    , mkBenchScene "AddAlias" curveAddAlias
    , mkBenchScene "MulAlias" curveMulAlias
    , mkBenchScene "SquareAlias" curveSquareAlias
    ]
