# The core engine and other permission models

What the pattern-set core can express, where it stops, and how it compares
with the usual families of permission system. Names in `code` are
definitions and theorems in the Lean spec.

## The core in one paragraph

A decision starts from a set of facts: key and value pairs gathered from
the context of the operation, the actor, and (for entities) the entity as
loaded from the store. A permission is a list of patterns, and each pattern
asks for some keys to have exact values. The facts are permitted when at
least one pattern is within them. Nothing else is consulted.

In logical terms a permission is a positive formula in disjunctive normal
form over tests of the shape `key = value`. Three properties follow, and
they explain everything below.

- **Allow only.** There is no way to refuse. Adding a pattern can only
  permit more (`Permission.Permits.mono`).
- **Monotone in the facts.** What is permitted stays permitted when facts
  are added (`Permission.Permits.extend`).
- **Equality with a written value.** A test compares one fact with a value
  written in the pattern. It never compares two facts with each other.

## Comparison

| Model | It decides from | In the core | What is missing |
| --- | --- | --- | --- |
| Access list, access matrix | (actor, record, right) entries | Direct. One pattern per record: `Permission.ofValues`, `Permission.permits_ofValues_iff` | Size grows with records times actors. "Who can reach this record?" means scanning every actor. |
| Capabilities | Tokens the actor holds | An actor's permission is a list of capabilities, each a pattern | Rules for handing a capability on or narrowing it. Administration is out of scope. |
| Role-based (flat) | Actor to roles, role to permissions | Direct. The union of the roles' permissions: `Policy.ofRoles`, `Policy.ofRoles_allows_iff` | Nothing, for the decision itself. |
| Role-based with a hierarchy | Roles inherit from roles | Outside the core. Work out the full list of roles first, then take the union | The inheritance rule lives in whatever assembles the permission. |
| Role constraints (separation of duty) | Roles that must not be held or used together | Not expressible | It is a refusal that depends on something else being present. See "No exceptions". |
| Attribute-based | Conditions on attributes of actor, resource, action and environment | The same idea, restricted. Facts are the attributes, and the only condition is `key = value` | Comparisons and ranges, "list contains", comparing two attributes, refusals. |
| Relationship-based (Zanzibar) | A graph of relationships, with rules that follow it recursively | One step only, when the relationship is a field on the entity (`folder: a`) | Following a chain of relationships. A change in a relationship does not reach the permission unless something rewrites it. |
| Levels (no read up) | An order on clearance and classification | By listing: one pattern for each allowed pair of levels | No test for "at least". The listing grows with the square of the number of levels. |
| Allow and deny rules | Both kinds of rule, with a precedence | Not expressible | Exclusions. A second pattern set is the planned way to add them. |

## The limits, stated as theorems

- **No exceptions** (`Permission.no_exception`). If some facts are
  permitted, no added fact can make them refused. "Every note in the
  folder except this one" cannot be said.
- **Absence cannot be required** (`Permission.no_permission_requires_absence`).
  No permission permits exactly the facts that lack a given key.
- **Two facts cannot be related** (`Permission.no_permission_relates_two_keys`).
  No permission says "`owner` equals `actor`" for every value. It takes one
  pattern per value.

Two consequences for design:

- **"The entity is the actor's own"** needs either a pattern written for
  each actor with their own value in it (`owner: alice` in alice's
  permission), or a fact worked out when the facts are gathered
  (`owner_is_actor: yes`).
- **A key has one value.** Facts are a map. An actor with several roles, or
  an entity field holding a list, cannot be a single fact. Roles are
  handled by the union of permissions and not by a `role` fact.

## Zanzibar in particular

Neither system contains the other.

- Changing who belongs to a group changes Zanzibar's answers. It cannot
  change an answer here unless something rewrites the actor's permission.
- Changing a field of an entity changes answers here. It cannot change
  Zanzibar's, which never looks at the content of an object.

Each can imitate the other only by working answers out in advance. Any
snapshot of Zanzibar can be flattened into one `id` pattern per actor and
record, but one change of membership may then touch many permissions. The
other way round, field values have to be mirrored as relationships.

What the core has that Zanzibar finds hard: a permission is already a
filter, so listing what an actor may read needs nothing extra
(`Permission.mem_visible_iff`).

## Entities

Entity fields are known only after loading, so the check comes after the
load. Values a caller writes in a message are never taken as facts about a
stored entity.

| Operation | What is checked (`Permission.PermitsOperation`) |
| --- | --- |
| load | the stored entity |
| remove | the stored entity |
| create | the entity to be written |
| update | the stored entity and the entity to be written, both |
| list | the read check on each entity returned (`Permission.visible`) |

Checking both sides of an update refuses two things: writing permitted
values over someone else's entity, and moving an entity out of the actor's
own reach.

Not covered: permissions on individual fields, and what happens when the
context, the actor and the entity use the same key. For the second,
`Facts.collect` takes the context's value first, then the actor's.

## The found value

A pattern can carry data, as in patrun, and one of the matching patterns is
the one found (`Allowances.find?`). The rule is patrun's intended rule.

- The pattern with the most keys wins (`Allowances.size_le_of_find?`).
- Alphabetical order of the keys only breaks ties
  (`Allowances.not_keys_lt_of_find?`).
- Two different matching patterns are never level
  (`Pattern.eq_of_not_outranks`), so the result does not depend on the
  order patterns were added in (`Allowances.find?_pattern_eq`).
- The found value never changes the yes or no answer
  (`Allowances.find?_isSome_iff`).

One thing the found value cannot do: a patrun holds one value per pattern.
If two sources grant the same pattern, only the value added last is kept.

### patrun 7.3.0 does not follow this rule yet

Checked against patrun 7.3.0 with literal values. It walks keys in
alphabetical order, takes the first key that matches, and goes back to try
another key only if it has found no value at all.

| Stored patterns | Facts | Rule | patrun 7.3.0 |
| --- | --- | --- | --- |
| `{a:1}`=A, `{b:1,c:1}`=BC | `{a:1,b:1,c:1}` | BC | A |
| `{}`=ROOT, `{c:1}`=C, `{a:1,b:1}`=AB | `{a:1,c:1}` | C | ROOT |

In the second row a pattern that does not match changes which matching
pattern is returned.

What is safe to rely on in 7.3.0:

- **The yes or no answer.** `find` returned a value whenever some pattern
  matched, and never otherwise.
- **All matches.** `find(facts, false, true)` returned the value of every
  matching pattern.

So an implementation on patrun 7.3.0 should decide with either of those,
and should not use the single value from `find` where its meaning matters.
The same cases are proved with the intended answers in
`SenecaAccess/EntityExamples.lean`.
