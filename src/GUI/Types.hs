module GUI.Types where

import Curve
import Scene

-- | a single curve with some extra information for the gui
data CurveEntry = CurveEntry
    { cePlaced :: CurveDisplay
    -- ^ the actual curve to render
    , ceScene :: VisualScene
    -- ^ cached 'evalScene' of @cePlaced.cdState@ at the current time
    , ceSourcePoints :: Maybe [(Double, Double)]
    , ceNumTerms :: Int
    }

-- | a unique identifier for a curve (i.e. a chain of epicycles), to distinguish between different curves in the same scene
newtype CurveId = CurveId Int
    deriving (Show, Eq, Ord, Num, Enum)
