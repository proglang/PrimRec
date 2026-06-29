{-# OPTIONS --safe #-}

module Core.Translations where

-- Translations between the point-free calculi and the contextual
-- presentation, together with preservation proofs.

import Core.Types
import Core.Equations.PRFO
import Core.Equations.PRFOFold
import Core.Equations.PRHO
import Core.Equations.PRHOFold
import Core.Translations.PRFOParamorphismFold
import Core.Translations.PRFOToPRHO
import Core.Translations.PRHOParamorphismFold
import Core.Translations.ContextualPRFO
import Core.Translations.ContextualPRHO
