import SenecaAccess.Permission

/-!
# The access rule

An actor wishes to call a message, and may do so only with permission.
This file states that rule, which is the whole of layer one.
-/

namespace SenecaAccess

/--
A policy records the permission held by each actor.

`Actor` is left open. The rule never looks inside an actor; it only looks
up the permission the policy gives it.
-/
structure Policy (Actor Key Value : Type) where
  /-- The permission held by `actor`. -/
  permission : Actor → Permission Key Value

namespace Policy

variable {Actor Key Value : Type}

/--
**The access rule.** An actor may call a message exactly when the
permission that actor holds permits the message.
-/
def Allows (policy : Policy Actor Key Value) (actor : Actor) (message : Message Key Value) :
    Prop :=
  (policy.permission actor).Permits message

/--
**Binary.** For every policy, actor and message, whether the call is
allowed can be computed. The answer is yes or no, and there is no third
outcome.
-/
instance [DecidableEq Value] (policy : Policy Actor Key Value) (actor : Actor)
    (message : Message Key Value) : Decidable (policy.Allows actor message) :=
  inferInstanceAs (Decidable ((policy.permission actor).Permits message))

variable {policy other : Policy Actor Key Value} {actor : Actor}
variable {message wider : Message Key Value}

/--
The access rule in full, with every definition unfolded: the call is
allowed exactly when some pattern held by the actor has all of its
key/value pairs present in the message.
-/
theorem allows_iff :
    policy.Allows actor message ↔
      ∃ pattern ∈ policy.permission actor,
        ∀ key value, (key, value) ∈ pattern → message.get key = some value :=
  Iff.rfl

/-- **Default deny.** An actor who holds no patterns may call nothing. -/
theorem not_allows_of_permission_eq_nil (hnone : policy.permission actor = []) :
    ¬ policy.Allows actor message :=
  fun (h : (policy.permission actor).Permits message) =>
    Permission.not_permits_nil (hnone ▸ h)

/--
**Grants only add.** If a second policy gives an actor every pattern the
first one does, every call the first allows that actor is also allowed by
the second.
-/
theorem Allows.mono (h : policy.Allows actor message)
    (hsub : policy.permission actor ⊆ other.permission actor) :
    other.Allows actor message :=
  Permission.Permits.mono h hsub

/--
**Each actor stands alone.** Whether an actor may call a message depends
only on the patterns that actor holds, not on what any other actor holds.
-/
theorem allows_congr
    (hsame : ∀ pattern,
      pattern ∈ policy.permission actor ↔ pattern ∈ other.permission actor) :
    policy.Allows actor message ↔ other.Allows actor message :=
  Permission.permits_congr hsame

/--
Extra properties are ignored. An allowed call stays allowed when
properties are added to the message.
-/
theorem Allows.of_extends (h : policy.Allows actor message) (hext : wider.Extends message) :
    policy.Allows actor wider :=
  Permission.Permits.of_extends h hext

end Policy

end SenecaAccess
