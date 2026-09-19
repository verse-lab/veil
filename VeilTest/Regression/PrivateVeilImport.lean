module

-- `veil module` elaborates its generated declarations into the public scope, so Veil has
-- to be publicly imported. A private import used to surface only as a wall of
-- unknown-identifier errors from `#gen_state`, naming Veil internals rather than the fix.
import Veil

/--
error: Veil is only imported into this module's private scope, but `veil module` elaborates its generated declarations into the public scope. Write `public import Veil` instead of `import Veil` at the top of this file.
-/
#guard_msgs in
veil module PrivatelyImportedVeil

end PrivatelyImportedVeil
