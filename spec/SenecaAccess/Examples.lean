import SenecaAccess.Policy

/-!
# Worked examples

The rule applied to concrete messages, with keys, values and actor names
all strings.

Each `#guard` line is evaluated when the spec is built, and the build
fails if any of them is false.
-/

namespace SenecaAccess.Examples

/-- A message, written as its properties. -/
def msg (properties : List (String × String)) : Message String String :=
  Message.ofList properties

/--
A small policy.

* `alice` may load any entity, and may save notes.
* `root` holds the empty pattern, and so may call anything.
* Nobody else holds any pattern.
-/
def policy : Policy String String String where
  permission
    | "alice" =>
      [ [("sys", "entity"), ("cmd", "load")],
        [("sys", "entity"), ("cmd", "save"), ("name", "note")] ]
    | "root" => [ [] ]
    | _ => []

-- A message with exactly the properties of a pattern alice holds is allowed.
#guard policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "load")])

-- Properties beyond those the pattern names are ignored.
#guard policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "load"), ("name", "order")])

-- The order in which a message lists its properties makes no difference.
#guard policy.Allows "alice" (msg [("name", "order"), ("cmd", "load"), ("sys", "entity")])

-- Alice's second pattern asks for `name` to be `note`, and nothing else will do.
#guard policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "save"), ("name", "note")])
#guard ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "save"), ("name", "order")])
#guard ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "save")])

-- No pattern alice holds is met by a `remove`.
#guard ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "remove"), ("name", "note")])

-- Values are compared exactly.
#guard ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "LOAD")])

-- A message that lacks a property every pattern asks for is denied.
#guard ¬ policy.Allows "alice" (msg [("sys", "entity")])
#guard ¬ policy.Allows "alice" (msg [])

-- The empty pattern matches every message, the empty message included.
#guard policy.Allows "root" (msg [("sys", "entity"), ("cmd", "remove"), ("name", "note")])
#guard policy.Allows "root" (msg [])

-- Default deny: the policy gives mallory no patterns.
#guard ¬ policy.Allows "mallory" (msg [("sys", "entity"), ("cmd", "load")])
#guard ¬ policy.Allows "mallory" (msg [])

end SenecaAccess.Examples
