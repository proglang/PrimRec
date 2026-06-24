{-# OPTIONS --safe #-}

module Core.Instances.Equations where

-- Independent, inductively generated source equalities, including the
-- constructor-specific recursion beta schemes.  Target extends the generic
-- Core equations by the corresponding finite-signature and Nat beta schemes.
-- Words use a subordinate finite-alphabet target relation with structurally
-- generated empty/letter beta schemes.
-- this is necessary because the abstract Core theory intentionally leaves the
-- action of primitive fmap/strength on sums and products unspecified.

import Core.Instances.Equations.Target
import Core.Instances.Equations.Common
import Core.Instances.Equations.Nat
import Core.Instances.Equations.Words
import Core.Instances.Equations.Trees
import Core.Instances.Equations.ManySorted
