{-# OPTIONS --safe #-}

module Core.Instances.Equations where

-- Independent, inductively generated source equalities, including the
-- constructor-specific recursion beta schemes.  Target extends the generic
-- Core equations by the corresponding finite-signature and Nat beta schemes.
-- Words use a subordinate finite-alphabet target relation with structurally
-- generated empty/letter beta schemes.
-- this is necessary because the abstract Core theory intentionally leaves the
-- action of primitive fmap/strength on sums and products unspecified.
-- System T uses the legacy intrinsic syntax and adds the corresponding
-- beta/eta, substitution, and natural-number recursor source equations.
-- Its preservation theorem targets Core.Equations.PRHO directly, using the
-- structural fmap/strength computation laws for the Nat functor.

import Core.Instances.Equations.Target
import Core.Instances.Equations.Common
import Core.Instances.Equations.PREC
import Core.Instances.Equations.Nat
import Core.Instances.Equations.Words
import Core.Instances.Equations.Trees
import Core.Instances.Equations.ManySorted
import Core.Instances.Equations.SystemT
