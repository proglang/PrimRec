{-# OPTIONS --safe #-}

module Core.Equations where

-- Aggregates the syntax-specific equational theories. Shared setoid
-- infrastructure can be factored into this module when models are added.

import Core.Equations.PRFO as PRFO
import Core.Equations.PRHO as PRHO
