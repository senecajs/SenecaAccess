import SenecaAccess.Allowance

/-!
# Entities

An entity is a record of named fields. Entities are reached through
messages, so permission on entities is the message rule again, applied to
more facts.

The fields of an entity are not in the message that asks for it. They are
known only once the entity has been loaded from the store, so the check
happens after loading: the facts about the context, the actor and the
loaded entity are gathered into one set and matched against the permission.

What a caller writes in a message is never taken as a fact about a stored
entity.
-/

namespace SenecaAccess

/-- An entity: a record holding fields with values. -/
abbrev Entity (Value : Type) := Message Value

/--
Facts: the key and value pairs known when a decision is made. They have the
shape of a message, and a permission is matched against them in the same
way.
-/
abbrev Facts (Value : Type) := Message Value

namespace Facts

variable {Value : Type}
variable {context actor : Message Value} {entity : Entity Value}

/--
The facts for one decision, gathered from three sources: the context of the
operation, the actor, and the entity.

Key clashes between the sources are not addressed in this layer. So that
the definition is complete, a key found in more than one source takes its
value from the context first, then from the actor, then from the entity.
-/
def collect (context actor : Message Value) (entity : Entity Value) : Facts Value :=
  entity ∪ actor ∪ context

/-- Where each collected fact comes from. -/
theorem getElem?_collect (key : String) :
    (collect context actor entity)[key]? =
      (context[key]?).or ((actor[key]?).or (entity[key]?)) := by
  simp only [collect, Std.ExtTreeMap.getElem?_union]

/-- Every fact of the context is among the collected facts. -/
theorem context_within_collect : context.Within (collect context actor entity) := by
  intro key value hget
  rw [getElem?_collect, hget]
  rfl

end Facts

namespace Permission

variable {Value : Type}

/--
**The entity check.** A permission permits an entity, for a given context
and actor, when it permits the facts gathered from all three.
-/
def PermitsEntity (permission : Permission Value) (context actor : Message Value)
    (entity : Entity Value) : Prop :=
  permission.Permits (Facts.collect context actor entity)

instance [DecidableEq Value] (permission : Permission Value) (context actor : Message Value)
    (entity : Entity Value) : Decidable (permission.PermitsEntity context actor entity) :=
  inferInstanceAs (Decidable (permission.Permits (Facts.collect context actor entity)))

end Permission

/--
An operation on one entity, with the entities it involves.

A save is a `create` when the entity is not yet in the store and an
`update` when it is.
-/
inductive EntityOperation (Value : Type) where
  /-- Read an entity. `stored` is the entity as loaded from the store. -/
  | load (stored : Entity Value)
  /-- Delete an entity. `stored` is the entity as loaded from the store. -/
  | remove (stored : Entity Value)
  /-- Save an entity that is not yet stored. `created` is the entity to be written. -/
  | create (created : Entity Value)
  /-- Save an entity that is already stored. `stored` is the entity as loaded from the
  store, and `updated` is the entity as it would be written. -/
  | update (stored updated : Entity Value)

namespace Permission

variable {Value : Type}

/--
**What each operation checks.**

* `load` and `remove` check the stored entity.
* `create` checks the entity to be written.
* `update` checks both the stored entity and the entity to be written. The
  actor must be allowed to touch what is there, and allowed to leave behind
  what they write.
-/
def PermitsOperation (permission : Permission Value) (context actor : Message Value) :
    EntityOperation Value → Prop
  | .load stored => permission.PermitsEntity context actor stored
  | .remove stored => permission.PermitsEntity context actor stored
  | .create created => permission.PermitsEntity context actor created
  | .update stored updated =>
    permission.PermitsEntity context actor stored ∧
      permission.PermitsEntity context actor updated

instance [DecidableEq Value] (permission : Permission Value) (context actor : Message Value)
    (operation : EntityOperation Value) :
    Decidable (permission.PermitsOperation context actor operation) := by
  cases operation <;> unfold PermitsOperation <;> infer_instance

/--
**List.** Listing comes down to the read check on each entity. Of the
entities the store returns, the actor is shown those the permission permits
them to read. `context` is the context of that read.
-/
def visible [DecidableEq Value] (permission : Permission Value) (context actor : Message Value)
    (entities : List (Entity Value)) : List (Entity Value) :=
  entities.filter fun entity => decide (permission.PermitsEntity context actor entity)

variable {permission larger : Permission Value} {context actor : Message Value}
variable {entity stored updated : Entity Value} {entities : List (Entity Value)}
variable {operation : EntityOperation Value}

/-- **Default deny.** The empty permission permits no entity. -/
theorem not_permitsEntity_nil :
    ¬ PermitsEntity ([] : Permission Value) context actor entity :=
  not_permits_nil

/-- **Grants only add.** A permission with more patterns permits at least the same entities. -/
theorem PermitsEntity.mono (h : permission.PermitsEntity context actor entity)
    (hsub : permission ⊆ larger) : larger.PermitsEntity context actor entity :=
  Permits.mono h hsub

/-- **Grants only add**, for operations. -/
theorem PermitsOperation.mono (h : permission.PermitsOperation context actor operation)
    (hsub : permission ⊆ larger) : larger.PermitsOperation context actor operation := by
  cases operation with
  | load stored => exact PermitsEntity.mono h hsub
  | remove stored => exact PermitsEntity.mono h hsub
  | create created => exact PermitsEntity.mono h hsub
  | update stored updated => exact ⟨PermitsEntity.mono h.1 hsub, PermitsEntity.mono h.2 hsub⟩

/--
An update cannot touch an entity the actor is not permitted. Writing
permitted values over someone else's entity is refused.
-/
theorem permitsEntity_stored_of_update
    (h : permission.PermitsOperation context actor (.update stored updated)) :
    permission.PermitsEntity context actor stored :=
  h.1

/--
An update cannot leave behind an entity the actor is not permitted. Moving
an entity out of the actor's own reach is refused.
-/
theorem permitsEntity_updated_of_update
    (h : permission.PermitsOperation context actor (.update stored updated)) :
    permission.PermitsEntity context actor updated :=
  h.2

variable [DecidableEq Value]

/--
**A list shows exactly the readable entities.** An entity is shown when the
store returned it and the actor is permitted to read it, and never
otherwise.
-/
theorem mem_visible_iff :
    entity ∈ permission.visible context actor entities ↔
      entity ∈ entities ∧ permission.PermitsEntity context actor entity := by
  simp only [visible, List.mem_filter, decide_eq_true_eq]

/-- **Default deny.** With the empty permission a list shows nothing. -/
theorem visible_nil : visible ([] : Permission Value) context actor entities = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entity hmem
  exact not_permitsEntity_nil (mem_visible_iff.mp hmem).2

/-- **Grants only add.** With more patterns a list shows at least the same entities. -/
theorem mem_visible_mono (hmem : entity ∈ permission.visible context actor entities)
    (hsub : permission ⊆ larger) : entity ∈ larger.visible context actor entities :=
  let ⟨hin, hpermits⟩ := mem_visible_iff.mp hmem
  mem_visible_iff.mpr ⟨hin, hpermits.mono hsub⟩

end Permission

namespace Allowances

variable {Value Data : Type} [DecidableEq Value]

/-- The allowance found for an entity, in a given context and for a given actor. -/
def findEntity? (allowances : Allowances Value Data) (context actor : Message Value)
    (entity : Entity Value) : Option (Allowance Value Data) :=
  allowances.find? (Facts.collect context actor entity)

/-- Something is found for an entity exactly when the entity is permitted. -/
theorem findEntity?_isSome_iff {allowances : Allowances Value Data}
    {context actor : Message Value} {entity : Entity Value} :
    (allowances.findEntity? context actor entity).isSome ↔
      allowances.permission.PermitsEntity context actor entity :=
  find?_isSome_iff

end Allowances

end SenecaAccess
