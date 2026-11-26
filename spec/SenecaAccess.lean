import SenecaAccess.Message
import SenecaAccess.Pattern
import SenecaAccess.Permission
import SenecaAccess.Policy
import SenecaAccess.Examples

/-!
# SenecaAccess specification

Layer one: whether an actor may call a message.

An actor may call a message only with permission, and the answer is always
yes or no. A permission is a set of patterns. The actor may call the
message when it matches at least one pattern in the permission they hold.

The modules, in reading order:

* `SenecaAccess.Message`: a message, as the rule sees it.
* `SenecaAccess.Pattern`: a pattern, and what it is for a message to match one.
* `SenecaAccess.Permission`: a set of patterns, and what it permits.
* `SenecaAccess.Policy`: the permission each actor holds, and the access rule.
* `SenecaAccess.Examples`: the rule applied to concrete messages.
-/
