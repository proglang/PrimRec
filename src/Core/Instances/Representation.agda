{-# OPTIONS --safe #-}

module Core.Instances.Representation where

-- Canonical encodings of source values, proofs that the encodings inhabit
-- the logical relations, and compiler-correctness corollaries specialized to
-- represented inputs.  The many-sorted result is intentionally not a
-- surjectivity theorem: erasing sort indices admits ill-sorted target trees.

import Core.Instances.Representation.Nat
import Core.Instances.Representation.Words
import Core.Instances.Representation.Trees
import Core.Instances.Representation.ManySorted
