import SenecaAccess.Message
import SenecaAccess.Pattern
import SenecaAccess.Permission
import SenecaAccess.Policy
import SenecaAccess.Examples
import SenecaAccess.Allowance
import SenecaAccess.Entity
import SenecaAccess.Expressiveness
import SenecaAccess.EntityExamples

/-!
# SenecaAccess specification

The core engine: a set of key and value facts is checked against a set of
patterns.

An actor may call a message only with permission, and the answer is always
yes or no. A permission is a set of patterns. The actor may call the
message when it matches at least one pattern in the permission they hold.

Entities extend this. The facts for an entity are gathered from the context
of the operation, the actor, and the entity as loaded from the store, and
are checked in the same way.

The modules, in reading order:

* `SenecaAccess.Message`: a message, as a map from string keys to values.
* `SenecaAccess.Pattern`: a pattern, and what it is for a message to match one.
* `SenecaAccess.Permission`: a set of patterns, and what it permits.
* `SenecaAccess.Policy`: the permission each actor holds, and the access rule.
* `SenecaAccess.Examples`: the rule applied to concrete messages.
* `SenecaAccess.Allowance`: patterns that carry data, and which one is found.
* `SenecaAccess.Entity`: facts, entities, and what each entity operation checks.
* `SenecaAccess.Expressiveness`: what the core can express, and where it stops.
* `SenecaAccess.EntityExamples`: the engine applied to concrete entities.
-/
