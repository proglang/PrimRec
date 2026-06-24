module Core.Instances.Legacy where

-- This compatibility layer is kept separate from Core.Instances because the
-- original modules use TERMINATING and therefore cannot be imported by a
-- --safe module.

import Core.Instances.Legacy.Finite
import Core.Instances.Legacy.PRTrees
import Core.Instances.Legacy.PRHTrees
