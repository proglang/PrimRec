{-# OPTIONS --safe #-}

module Core.Translations where

-- Translations between the point-free calculi and the contextual
-- presentation, together with preservation proofs.

import Core.Types
import Core.Equations.PRFO
import Core.Equations.PRFOCatamorphism
import Core.Equations.PRHO
import Core.Equations.PRHOCatamorphism
import Core.Translations.PRFOParamorphismCatamorphism
import Core.Translations.PRFOToPRHO
import Core.Translations.PRHOParamorphismCatamorphism
import Core.Translations.ContextualPRFO
import Core.Translations.ContextualPRHO
