import SenecaAccess.Policy

/-!
# Worked examples

The rule applied to concrete messages, with keys, values and actor names
all strings.

Each example is a proof by `decide`. Lean runs the rule's decision
procedure in its kernel and accepts the example only if the answer comes
out as stated, so the build fails if any example is false.
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
example : policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "load")]) := by decide

-- Properties beyond those the pattern names are ignored.
example : policy.Allows "alice"
    (msg [("sys", "entity"), ("cmd", "load"), ("name", "order")]) := by decide

-- The order in which a message lists its properties makes no difference.
example : policy.Allows "alice"
    (msg [("name", "order"), ("cmd", "load"), ("sys", "entity")]) := by decide

-- Alice's second pattern asks for `name` to be `note`, and nothing else will do.
example : policy.Allows "alice"
    (msg [("sys", "entity"), ("cmd", "save"), ("name", "note")]) := by decide
example : ¬ policy.Allows "alice"
    (msg [("sys", "entity"), ("cmd", "save"), ("name", "order")]) := by decide
example : ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "save")]) := by decide

-- No pattern alice holds is met by a `remove`.
example : ¬ policy.Allows "alice"
    (msg [("sys", "entity"), ("cmd", "remove"), ("name", "note")]) := by decide

-- Values are compared exactly.
example : ¬ policy.Allows "alice" (msg [("sys", "entity"), ("cmd", "LOAD")]) := by decide

-- A message that lacks a property every pattern asks for is denied.
example : ¬ policy.Allows "alice" (msg [("sys", "entity")]) := by decide
example : ¬ policy.Allows "alice" (msg []) := by decide

-- The empty pattern matches every message, the empty message included.
example : policy.Allows "root"
    (msg [("sys", "entity"), ("cmd", "remove"), ("name", "note")]) := by decide
example : policy.Allows "root" (msg []) := by decide

-- Default deny: the policy gives mallory no patterns.
example : ¬ policy.Allows "mallory" (msg [("sys", "entity"), ("cmd", "load")]) := by decide
example : ¬ policy.Allows "mallory" (msg []) := by decide

end SenecaAccess.Examples
