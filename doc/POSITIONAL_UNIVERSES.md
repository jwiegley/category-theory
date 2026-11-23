# Positional universe instances: #1412 inventory and reviewed batches

These are partial #1412 batches, not issue closure or core-signature redesign.
The first-batch baseline is `438d83b2b706d33f1deaad60672c3ed5ed2a6554`
(including PR #1407); its measurements and per-file table below are historical.
The later batches have separate source baselines and release-only evidence.
Counts concern **live non-probe reference syntax**, not redundant instances or
public universe-slot savings. Outside this batch, retain every unassessed site.

## Inclusion and measurement

Use `scripts/probe_arity.py`'s lexer, command splitter and instance extractor.
Nested comments and string contents do not count; declaration universe binders
(including mutual heads) and sort expressions do not count. Exclude every `Fail`
command and every file under `Test/` or a `probes/` directory. Notation bodies DO
count as reference syntax; local/notation/global identity needs compiler evidence.
The baseline scan also covered the four tracked unregistered `.v` files; none
contributed a live non-probe instance.

Baseline: 1181 tracked `.v` files, 1177 duplicate-free build registrations;
15648 live non-probe reference-syntax sites (15602 outside notation commands and
46 in notation commands). Excluded live sites: 5602 declaration binders, 1087
sort expressions, 1669 instances inside `Fail`, and 4986 other test/probe
instances. This batch removes 293 references, leaving 15355 under the same rule.

Reproduce current per-file counts from the repository root:

```python
from collections import Counter
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
import probe_arity as p
counts = Counter()
for file in Path("_CoqProject").read_text().splitlines():
    if not file.endswith(".v") or file.startswith("Test/") or "/probes/" in file:
        continue
    for command in p.commands(Path(file).read_text()):
        words = [token.text for token in command]
        if "Fail" not in words[:p.head(words)]:
            counts[file] += len(p.instances(command))
for file, count in sorted(counts.items()):
    if count:
        print(file, count, sep="\t")
print("TOTAL", sum(counts.values()), sep="\t")
```

## First joint batch and retained pins

`Instance/SupLat/Free/Morphism.v` loses 144 of 146 reference annotations;
`Instance/SupLat/Examples.v` loses 149 of 177. Declaration binders, terms apart
from these annotations, and all probe commands/eager twins remain intact.
Both files were tested **together**, not inferred removable from independent
single-site compilations.

The generated dependency graph over all build registrations gives exactly two
external callers: `Test/ProbeSupLat466.v` and `Test/ProbeMonadMorphism468.v`,
with no further reverse dependants. Complete qualified `About`, `Print` and
`Print Assumptions` requests cover all 43 exported library declarations and all
129 caller declarations, including the helper record constructor. `Print Module`
cross-checks this inventory. On Rocq 9.1.1, all 520 framed responses (including
four complete module readbacks) are byte-identical before and after joint removal:
full bodies, constraints, Arguments and opacity, not merely public types.
All 172 assumption results are closed. Every one of the callers' 51 `Fail`
commands was individually stripped in a whole-file copy; complete error payloads
are byte-identical, without whitespace or universe-name normalization. Existing
positive computation controls, including #1347's restored setoid-morphism
`eq_refl` laws, remain positive. This measurement does not replace fresh
final-source compiler-matrix, assumptions and semantic-arity gates.

The 30 remaining annotations in these two files are deliberate:

- `SL_theta_iso` keeps `Monads@{so o m1 m2}`. Removing it still compiles, but
  specializes both category levels to `so` in the full type and body rather than
  preserving `m1` and `m2`. Compilation alone would falsely certify this removal.
- `SL_factor` keeps `Cat@{c so so so o}`. Removing it after the joint batch leaves
  a generated universe unbound in the explicit declaration context.
- Each of Examples.v's 28 remaining annotations anchors a declaration's named
  levels. Removing any one after the joint batch also produces an unbound
  generated universe. These are preservation diagnostics, not mathematical
  impossibility claims or new shipped refusal probes.

All five historical candidate files were refreshed by complete ordered name/level
sequence identity, then every current reference in those files was checked against
fresh direct compiler metadata and same-file, same-command `About` resolution.
`Theory/OGraph.v` (245 references) and `Adjunction/GAFT.v` (22) remain outside this
batch. `Instance/CMon.v` (7) also remains unchanged: removing its
`cmon_hom_compose@{u p}` application alone compiles and preserves the complete
`CMon` readback apart from source-origin metadata, but this is not a joint audit
of its obligations and broad caller closure. Its explanatory pin paragraph stays
true. Neither `cmon_hom_compose` itself nor any core signature is changed.

## Second joint batch: GAFT on Rocq 9.2.0

The source intervention in `a18ab43efd02ef12892cfd5d5565042e4244b7ad`
removes eight annotations together from `Adjunction/GAFT.v`: two `Category`
instances in `sols_of_wif`, and two `Category` instances and one `Complete`
instance in each of `comma_initial_of_sols` and `GAFT_via_comma_initial`.
Declaration binders, solution-set indices, terms apart from those instances,
opacity and probe sources are unchanged. This establishes joint removability,
not separate removability of each occurrence or a reduction in public slots.

The paired source baseline is `b9e74514ec47221aaca2096865c9a176b0f56235`.
The candidate differs in this `.v` file alone. Its SHA-256 is
`1d5be723f1aca323b90aab75e445138a8b3e35ea4bb8985034986df06b5c2188`,
against baseline `4128f870aaebbf0af6cb23dc61d9203c26a97c7823ab4945ea8c7923df07197d`.
Both sides freshly built all 1177 registered files with released Rocq 9.2.0,
Stdlib 9.1.0 and Equations 1.3.2+9.2. The release-toolchain commit
`4c3a4dc08c49dabd6c79df1d4513148a9223d443` changes build and CI selection,
not those paired `.v` sources. Earlier compiler results are historical;
no earlier-version compatibility is asserted by this batch.

Measurements on those paired builds:

- Complete qualified `About`, `Print` and `Print Assumptions` responses for
  13 selected constants are byte-identical: 39 responses, with no normalization.
  With `Set Printing All`, `Set Printing Universes` and printing depth 1000000,
  the targets are the three edited definitions; `SolutionSet`, `sol_index`,
  `sol_obj`, `sol_arr`, `sol_covers`, `sols_of_wif_index`, `GAFT` and
  `sols_of_comma_initial` in `Category.Adjunction.GAFT`;
  `Category.Adjunction.Representability.Sets.representability_theorem`; and
  `Category.Adjunction.SAFT.Characterization.Corollaries.continuous_Set_functor_representable_at`.
- The registered-project `coqdep` graph has 44 direct dependent modules and a
  73-module reverse closure including GAFT. `Print Module` listings match;
  `About`, `Print` and `Print Assumptions` for the 353 `Definition`/`Parameter`
  names ending in `_obligation_` followed by digits in those listings give
  1059 matching responses. This is not every generated declaration. The lexer
  enumerates 347 `Fail` commands in the closure; their captured refusal
  diagnostics match without normalization. Equality of diagnostics does not
  make name or typing failures universe proofs.
- Projection readbacks use `eq_refl` for the family index, member object and
  arrow, including transport along an arbitrary equality of indices. They do
  not identify entire solution-set records. Five positive/negative universe
  pairs at `h = Set` retain the tested strict upper bounds: slot 8 of
  `sols_of_wif`, slots 9 and 10 of `comma_initial_of_sols`, and slots 4 and 11
  of `GAFT_via_comma_initial`, counting their displayed instances from 1.
  Each pair uses the same constant and full arity, with one strict upper slot
  lowered to `Set`. These tests do not isolate an exclusive constraint donor.
- All 14506 configured assumption requests give identical raw responses. Only
  `ZX_Cat` lists the three Phase parameters. This is the configured audit, not
  certification of every declaration. Semantic arity and its compiler-backed
  positive/negative controls pass. The source commit's normal hooks also pass;
  its semantic check reports 1177 freshly built files and zero violations.

A fresh syntax scan using the inclusion rule above counts 15363 references at
this baseline and 15355 after the batch, over 1181 tracked `.v` files and 1177
build registrations. GAFT changes from 22 to 14; OGraph remains 245, CMon 7,
SupLat/Free/Morphism 2 and SupLat/Examples 28. The earlier table remains the
first-batch measurement, not a current necessity census. Re-run the displayed
scanner recipe at each source revision to obtain its registered-file counts.

## Third joint batch: OGraph on Rocq 9.2.0

This batch removes 106 reference annotations together from `Theory/OGraph.v`.
Its declaration binders, terms apart from those annotations, proof endings,
instance registrations and probe sources are unchanged. The retained annotations
still anchor graph, category and proof levels; this batch does not establish that
every retained annotation is necessary. Nor does it establish individual
removability, fewer public universe slots or an exclusive constraint donor.

The paired source baseline is merge commit
`4b19b78129c25cf70044d839490ba5dee75425b3`. Only `Theory/OGraph.v` differs
between the formal-source snapshots. Its SHA-256 changes from
`4a6b0e8bf9c01cea74e19e408fc435fec6c6c9046d045a536f9bb4126175b367` to
`c21eac187f8c82945aa8b2b5058dd51f8bd30986fa38eaf9f98c390e0dbb8eb0`.
Both sides freshly built all 1177 registered files on released Rocq 9.2.0,
Stdlib 9.1.0 and Equations 1.3.2+9.2, with executable and library identities
matched. An earlier seeded unit experiment is not the full-build evidence.

Measurements on the fresh paired builds:

- Complete `Print Module Category.Theory.OGraph` output is byte-identical.
  With all printing enabled, universes shown and printing depth 1000000, it
  enumerates 108 `Definition`/`Parameter` headings, three records and their
  three constructors. Qualified `About`, `Print` and `Print Assumptions`
  requests cover all 114 items, including `coarse_unit_obligation_1`.
  The inventory agrees with source declarations and fresh `.glob` metadata.
  The older `109/109` figure is a historical report, not this inventory.
  The index's claim of no `Program` is corrected: `coarse_unit` generates the
  discharged, opaque and closed `coarse_unit_obligation_1`. The header's matching
  no-`Program`/no-obligations claim is stale; its source-comment correction is
  deferred to #1416 to preserve this batch's annotation-only source binding.
- Of those 342 responses, 340 are byte-identical. The two remaining complete
  `Print` responses differ only by a checked bijection of compiler-declared
  private universe IDs: `ograph_compose_respects` changes
  `Category.Theory.OGraph.227` to `.265`; `coarse_respectfulness_entails_UIP`
  changes `.21528` to `.21872` and `.21529` to `.21873`, with the same module
  prefix. The substitution preserves every other byte of the bodies and
  constraint blocks, including the first proof's strict `p <` private-level
  bound. No whitespace, ordering, public-slot or constraint normalization is
  used. All 114 assumption responses are closed.
- The fresh registered-project dependency graph and `.glob` references find
  no external caller. OGraph contains no existing `Fail` command. The four
  tracked unregistered files have no lexical reference to the enumerated
  OGraph names; they were inspected, not compiled as part of the build set.
- Seven additional positive/refusal pairs preserve the tested bounds on
  `OGraphHom`, `OGraphHomEquiv`, `OGrph`, `OGrph_Monoidal`, `MonoidOfCat` and
  `CategoryOfOMonoid`. Every refusal has an adjacent eager check of the same
  constant and arity. Complete diagnostic streams match byte-for-byte.
  Eleven `eq_refl` checks cover the five category data projections,
  composable-pair eta, graph and multiplication round trips, the unit at
  `eq_refl`, and the natural-number composition and identity computations.
  These are not whole-category-record equality or functional unit eta.
- The existing arity checker accepts those controls using fresh direct
  references and canonical whole-file `About` evidence. It rejects a
  deliberately shortened negative instance even though its enclosing `Fail`
  makes the file compile; that arity failure is not universe evidence.
  The configured semantic gate independently rebuilds 1177 files and reports
  zero violations and zero exceptions. New comparison and inventory logic
  has positive and negative tests.
- All 14506 configured assumption requests, run on verified copies of the
  paired build products, have identical raw responses. Only `ZX_Cat` lists
  the three documented Phase parameters. This remains an enumerated audit.

The live non-probe syntax scan above now measures 15355 references before and
15249 after, across 1181 tracked `.v` files and 1177 registrations. OGraph
changes from 245 to 139; every other file's count is unchanged. The remaining
139 are retained, not certified necessary. The monoidal construction, no-UIP
boundary and existing packaged-universe collapse are not redesigned here.
Earlier compiler results remain historical, and #1412 remains open.

## Fourth batch: composition in CMon on Rocq 9.2.0

In `Instance/CMon.v`, the `compose` field now uses `@cmon_hom_compose`
without `@{u p}`. `Print CMon` still shows `@cmon_hom_compose@{u p}` in the
constructed record. Neither the two public slots of `cmon_hom_compose` nor
the constraint `p < u` has gone away. The `compose_respects` field retains
`@cmon_hom_compose_respects@{u p}`. In trials against verified copies of
compiled dependencies, deleting either annotation alone compiled; deleting
both left an unbound universe in the `compose` field. The latter is an
elaboration failure, not a mathematical refusal. In particular, the original
pin paragraph describes a sufficient construction with every field explicit,
not a proof that each annotation is necessary.

The baseline is merge `d8d0c748d47838518c4cc99b7197975ec5b1aad4`.
PR #1419's explicit bindings on `CanonicalMap` and the terminal/initial
point functors are already in this baseline and are unchanged here. The
release toolchain was Rocq and Corelib 9.2.0, Stdlib 9.1.0 and Equations
1.3.2+9.2, with matching executable and library identities in the pair.
Fresh source-only builds compiled all 1177 registered files on each side.
The sole source difference in the build inputs was the `compose` annotation:
`Instance/CMon.v` SHA-256 `3fcd7df5095e8ed88a123ee61a1d1b03d37179b74b02ffaed38cf5257a600f28`
before, `03125daf25678f6ad1adedd5aefaf8c40bc949c1ded83e8dfc48804573f79e5a` after.
The live non-probe inventory over 1181 tracked `.v` files fell from 15249 to
15248, with only `Instance/CMon.v` changing (7 to 6).

For all 36 items enumerated from `Print Module` for `Category.Instance.CMon`
(including generated obligations, records and constructors), the complete
qualified `About`, `Print` and `Print Assumptions` responses match byte for
byte; all 36 are closed. The registered build dependencies give 132 direct
importers and 173 downstream files in total. Across those 173 modules plus
`Theory/Metacategory/ArrowsOnly.v`, module displays and all three responses
for each of 10300 enumerated items match without normalization, including
52 unchanged nonclosed assumption responses. Names come from printed
`Definition`, `Parameter`, `Record` and `Inductive` headings plus constructors
from fresh `.glob` files. Qualified `Locate` found no object on either side
for the 449 additional source names from declaration entries. `ArrowsOnly`
is included separately because its `.vo` differed outside the import closure:
its 85 items match by the same criterion; the byte difference is unexplained.
This comparison is not a claim of identical object-file serialization.

All 588 outer `Fail` commands in the closure (64 files) were replayed in
source order on verified copies of each build. Complete stdout and stderr
matched, including refusal payloads; a nested `Fail Fail` is an instrument,
not a mathematical counterexample. Separate paired controls checked all six
record projections through `compose_respects` by `eq_refl` and three strict
universe refusals with adjacent same-constant, same-arity eager controls at
`Set < cmonCarrier < cmonUpper`. A shortened arity-one instance compiled
under `Fail` but was rejected by the semantic guard; it is not evidence of a
universe bound. The configured assumption gate yielded identical output for
14506 requests. The candidate semantic arity gate freshly built 1177 files,
with eight protected extractions, zero violations and zero exceptions.

## Fifth batch: inferred CMon fields on Rocq 9.2.0

Starting at merge `5a8549ce2aa2e0c5a3302cf60409945fa60c34ae`, remove the
reference instances on `obj`, `hom`, `homset` and `id` together. The explicit
category type and the `compose_respects` instance remain. In separate trials
against verified copies of compiled dependencies, removing either remaining
instance from that four-field candidate left an unbound universe. This is a
limit of deletion in this record expression, not a theorem about alternative
ascriptions. `CMon@{u p} : Category@{u p p}` and `p < u` are unchanged.

Fresh source-only builds on the fourth batch's release toolchain compiled
all 1177 registered files on each side. Only `Instance/CMon.v` differed in
the build inputs. The live non-probe inventory over 1181 tracked `.v` files
falls from 15248 to 15244, entirely in `Instance/CMon.v` (6 to 2).

The full CMon module display and qualified `About`, `Print` and `Print
Assumptions` responses for the same 36 items as in the fourth batch match
byte-for-byte; all 36 are closed. The registered reverse dependency closure
contains CMon and 173 downstream modules. This time no `.vo` outside that
closure differed. Module displays and all three responses for 10215 items
in those downstream modules match by the fourth batch's enumeration and
comparison criteria. This includes 52 unchanged nonclosed assumption results;
qualified `Locate` found no object for 447 additional source names on either
side. No global axiom-freedom or serialization guarantee follows.

On verified build copies, all 588 outer `Fail` commands in 64 affected files
had identical paired diagnostic streams. Six `eq_refl` projection checks
and the three strict-bound refusals with same-arity eager twins passed; the
semantic guard rejected the deliberately shortened instance. Configured
assumption output for 14506 requests matched. The candidate semantic arity
gate freshly built 1177 products, with eight protected extractions, zero
violations and zero exceptions.

## Remaining #1412 scope

Continue in reviewable jointly verified batches: resolve full constant identities,
distinguish genuine identifications from redundant annotations, compare all
affected declarations/bodies/constraints and actual callers, preserve full refusal
payloads and eager controls, and run exact Rocq 9.2.0 and the configured gates.
The retained OGraph references, the remaining GAFT
references and every other unassessed site remain #1412 work. Hub/signature
redesign belongs to later issues.

## Core proof obligations (#1413, Rocq 9.2.0)

Unlike the #1412 reference-syntax changes, these edits change the declarations
being referenced. The table compares qualified `About` outputs against
`38d70c67` using released Rocq/Corelib 9.2.0, Stdlib 9.1.0 and Equations
1.3.2+9.2. Positions are one-based: delete the indicated slot and keep the
order of the others. This rule applies to the named declarations, not to every
constant that mentions one of them.

| Declaration | Public slots before → after | Delete |
|---|---:|---:|
| `Functor_Setoid` | 6 → 5 | 4 |
| `iso_id` | 4 → 3 | 4 |
| `nat_id` | 4 → 3 | 3 |
| `nat_compose` | 4 → 3 | 2 |
| `Fun` | 7 → 6 | 7 |
| `EilenbergMoore` | 4 → 3 | 3 |
| `cmon_hom_compose` | 2 → 1 | 1 |

`Functor_Setoid` still compares functors by a family of isomorphisms with
its naturality equation. Its opaque lemma fixes the common hom level of the
two categories. The other six changes use category laws or respectfulness
directly in opaque obligations instead of going through generalized rewriting.
In each of the seven public contexts the removed level was an upper endpoint
of a strict inequality; projecting it away leaves the constraints among the
surviving levels unchanged. `CMon` remains `Category@{u p p}`; its explicit
`compose_respects` field now takes `@cmon_hom_compose_respects@{p}`.

Absence from the printed type did not suffice elsewhere. An isolated
four-slot `Compose` made `p453_n18_lift_at_pc` typecheck: its opaque law no
longer distinguished `pc` from `pa` by conversion. A four-slot `RMod` made
`p454_n7_wp_up_fifth_slot` typecheck despite `x < w`. Keep the five slots of
both constants, the five of `Cat` and the seven of `rmod_hom_compose`. The
separate #1419 larger-universe bindings remain in place.

Callers may reorder without changing arity: `Compose_Monoidal` exchanges
its first two slots; `EM_Free` exchanges its last two. A comparison of
parsed reference instances in the baseline and candidate `.v` sources,
with compiled reference identities and the arity gate's protected extractions,
accounts for 349 changed existing reference instances and 13 additional
pins. It does not count declaration binders as migrated references. Earlier
index entries for #464, #468 and #469 describe their original measurements:
the six-slot `Fun` and three-slot `EilenbergMoore` above supersede their
printed instances, not their mathematical results.

## Adjunction binders (#1414, Rocq 9.2.0)

Against `c1dd3027`, the qualified `About` contexts for the three records
identify the hom and proof levels of both categories. Keep the two object
levels independent. The common hom level `h` satisfies `h < so`; existing
upper bounds from `Basics.compose` and `ID` remain (correction, 2026-11-23:
they went when `Sets` took `fun` terms for its identity and composite; by
`About` on Rocq 9.3.0 `Adjunction` has `h < so` alone). For positional clients,
select these positions from the old instance, in this order (one-based):

| Declaration | Old → new slots | Select |
|---|---:|---|
| `Adjunction`, `Build_Adjunction`, `adj` | 11 → 5 | 1, 4, 2, 9, 11 |
| `Build_Adjunction'`, `unit`, `counit` | 8 → 5 | 1, 4, 2, 7, 8 |
| `AdjointOnTheRight`, `AdjointOnTheLeft` | 10 → 4 | 1, 4, 2, 8 |

The ordinary record's last level `sp` occurs in no constraint. Dropping
it nevertheless makes two record instances convertible that were not
convertible before (`adj_distinct_sp`). The contravariant records had no
such free level. In `Ex3a_left_literal` no position disappears: its fifth
and sixth positions exchange roles. `p458_ex3a_literal_above_set` keeps both strict inequalities
and exchanges the two arguments to that constant, not its own binders.

## Per-file inventory

`Before` is the first-batch baseline `438d83b2`; `After` includes only that batch. Unlisted files have
zero non-probe reference-syntax sites under the criterion above. Unchanged rows
mean retained/unassessed, not proven necessary. Changed rows retain the pins above.

| File | Before | After |
| --- | ---: | ---: |
| `Adjunction/CokernelPair.v` | 1 | 1 |
| `Adjunction/Continuity/Equalizer.v` | 4 | 4 |
| `Adjunction/Diagonal/Connected.v` | 6 | 6 |
| `Adjunction/Diagonal/Limit.v` | 4 | 4 |
| `Adjunction/Fullness.v` | 1 | 1 |
| `Adjunction/GAFT.v` | 22 | 22 |
| `Adjunction/GAFT/Necessity.v` | 3 | 3 |
| `Adjunction/GAFT/Resize.v` | 23 | 23 |
| `Adjunction/LeftInverse.v` | 5 | 5 |
| `Adjunction/Representability/Sets.v` | 6 | 6 |
| `Adjunction/Right.v` | 60 | 60 |
| `Adjunction/SAFT.v` | 6 | 6 |
| `Adjunction/SAFT/Characterization.v` | 162 | 162 |
| `Adjunction/SAFT/Characterization/Corollaries.v` | 59 | 59 |
| `Adjunction/SAFT/Characterization/Cover.v` | 163 | 163 |
| `Adjunction/SAFT/Characterization/Examples.v` | 65 | 65 |
| `Adjunction/SAFT/InitialObject.v` | 105 | 105 |
| `Adjunction/SAFT/InitialObject/Examples.v` | 44 | 44 |
| `Adjunction/SAFT/Sets.v` | 16 | 16 |
| `Adjunction/SAFT/WellPowered.v` | 8 | 8 |
| `Adjunction/Unitalization.v` | 6 | 6 |
| `Construction/Comma/Functorial.v` | 1 | 1 |
| `Construction/Coproduct/Indexed.v` | 86 | 86 |
| `Construction/Free.v` | 2 | 2 |
| `Construction/Free/Groupoid.v` | 4 | 4 |
| `Construction/Free/Quiver.v` | 14 | 14 |
| `Construction/Free/Quiver/Constructions.v` | 38 | 38 |
| `Construction/Free/Quiver/Coproduct.v` | 17 | 17 |
| `Construction/Free/Quiver/Examples.v` | 5 | 5 |
| `Construction/Free/Quiver/Presented.v` | 1 | 1 |
| `Construction/Lift.v` | 17 | 17 |
| `Construction/Reflective/Coreflective.v` | 15 | 15 |
| `Construction/Reflective/Idempotent/Induced.v` | 19 | 19 |
| `Construction/Reflective/Monadic.v` | 14 | 14 |
| `Construction/Reflective/Universal.v` | 6 | 6 |
| `Functor/Construction/Postcompose.v` | 6 | 6 |
| `Functor/Hom/Continuous.v` | 4 | 4 |
| `Functor/Hom/Yoneda/Natural.v` | 10 | 10 |
| `Functor/Representable.v` | 5 | 5 |
| `Functor/Representable/Additive.v` | 28 | 28 |
| `Functor/Representable/Functorial.v` | 3 | 3 |
| `Instance/Ab.v` | 8 | 8 |
| `Instance/Ab/Character/Finite.v` | 1 | 1 |
| `Instance/Ab/Free.v` | 13 | 13 |
| `Instance/Ab/FreeMonad.v` | 49 | 49 |
| `Instance/Ab/Generator.v` | 10 | 10 |
| `Instance/Ab/Monoidal.v` | 23 | 23 |
| `Instance/Ab/Torsion.v` | 52 | 52 |
| `Instance/CMon.v` | 7 | 7 |
| `Instance/CMon/Biproduct.v` | 16 | 16 |
| `Instance/CMon/Free.v` | 100 | 100 |
| `Instance/Cat/Components.v` | 11 | 11 |
| `Instance/Cat/Coproduct.v` | 3 | 3 |
| `Instance/Cat/Limit.v` | 16 | 16 |
| `Instance/Cat/Objects.v` | 15 | 15 |
| `Instance/Cat/SplitFork.v` | 50 | 50 |
| `Instance/Concrete.v` | 6 | 6 |
| `Instance/Discrete.v` | 5 | 5 |
| `Instance/Discrete/Reconstruct.v` | 6 | 6 |
| `Instance/FinSet/Subsets.v` | 29 | 29 |
| `Instance/FinSet/WellPowered.v` | 3 | 3 |
| `Instance/Fun/Action/Monad.v` | 411 | 411 |
| `Instance/Fun/Action/Monad/BG.v` | 387 | 387 |
| `Instance/Fun/Action/Monad/BG/Morphism.v` | 123 | 123 |
| `Instance/Fun/Action/Monad/Comparison.v` | 232 | 232 |
| `Instance/Fun/Classifier.v` | 5 | 5 |
| `Instance/Fun/Closed.v` | 5 | 5 |
| `Instance/Fun/Creation.v` | 7 | 7 |
| `Instance/Fun/Eval.v` | 2 | 2 |
| `Instance/Fun/Exponential.v` | 6 | 6 |
| `Instance/Fun/Group.v` | 11 | 11 |
| `Instance/Fun/Limit.v` | 15 | 15 |
| `Instance/Fun/Morphisms.v` | 2 | 2 |
| `Instance/Fun/Terminal.v` | 5 | 5 |
| `Instance/Fun/Topos.v` | 17 | 17 |
| `Instance/Grp.v` | 42 | 42 |
| `Instance/Grp/Abelianize/Reflective.v` | 71 | 71 |
| `Instance/Grp/Coequalizer.v` | 36 | 36 |
| `Instance/Grp/Colimit.v` | 5 | 5 |
| `Instance/Grp/Colimit/Presentation.v` | 104 | 104 |
| `Instance/Grp/Completion.v` | 7 | 7 |
| `Instance/Grp/EckmannHilton.v` | 6 | 6 |
| `Instance/Grp/Galois.v` | 108 | 108 |
| `Instance/Grp/Generator.v` | 12 | 12 |
| `Instance/Grp/TwoFunctors.v` | 1 | 1 |
| `Instance/Indiscrete.v` | 10 | 10 |
| `Instance/InnerProduct/Galois.v` | 70 | 70 |
| `Instance/Matr/FunExercises.v` | 7 | 7 |
| `Instance/Met.v` | 1 | 1 |
| `Instance/Met/Uniform.v` | 45 | 45 |
| `Instance/Mod/BaseChange.v` | 1 | 1 |
| `Instance/Mod/Closed.v` | 2 | 2 |
| `Instance/Mod/Coextension.v` | 1 | 1 |
| `Instance/Mod/Cogenerator.v` | 104 | 104 |
| `Instance/Mod/Colimit.v` | 27 | 27 |
| `Instance/Mod/Colimit/Creation.v` | 183 | 183 |
| `Instance/Mod/Free.v` | 19 | 19 |
| `Instance/Mod/FreeMonad.v` | 118 | 118 |
| `Instance/Mod/FreeMonad/FinSupp.v` | 10 | 10 |
| `Instance/Mod/HomTensor.v` | 10 | 10 |
| `Instance/Mod/Monoidal.v` | 1 | 1 |
| `Instance/Mod/RingEpi.v` | 29 | 29 |
| `Instance/Mod/TensorMonad.v` | 305 | 305 |
| `Instance/Mod/TensorMonad/Cocontinuous.v` | 86 | 86 |
| `Instance/Mod/Watts.v` | 208 | 208 |
| `Instance/Mod/Watts/Unconditional.v` | 91 | 91 |
| `Instance/Mod/WellPowered.v` | 59 | 59 |
| `Instance/Mon/Free.v` | 10 | 10 |
| `Instance/Mon/Presentation.v` | 9 | 9 |
| `Instance/Mon/Word.v` | 131 | 131 |
| `Instance/Mon/Word/System.v` | 97 | 97 |
| `Instance/Monoid/Translation.v` | 4 | 4 |
| `Instance/Omega.v` | 9 | 9 |
| `Instance/One.v` | 4 | 4 |
| `Instance/Ordinal.v` | 11 | 11 |
| `Instance/Ordinal/Large.v` | 44 | 44 |
| `Instance/Parallel/Wide.v` | 56 | 56 |
| `Instance/Pos/Monadicity.v` | 387 | 387 |
| `Instance/Powerset.v` | 219 | 219 |
| `Instance/Powerset/Quantifier.v` | 400 | 400 |
| `Instance/Powerset/Subobject.v` | 42 | 42 |
| `Instance/Powerset/WellPowered.v` | 18 | 18 |
| `Instance/Props/Modal.v` | 87 | 87 |
| `Instance/Proset/Monad.v` | 107 | 107 |
| `Instance/Proset/Monad/Awodey.v` | 26 | 26 |
| `Instance/Proset/Monad/Interior.v` | 179 | 179 |
| `Instance/Rg.v` | 23 | 23 |
| `Instance/Rng/Coequalizer.v` | 27 | 27 |
| `Instance/Rng/Commutativize.v` | 37 | 37 |
| `Instance/Rng/Commutativize/UT2.v` | 12 | 12 |
| `Instance/Rng/Free.v` | 23 | 23 |
| `Instance/Rng/FreeMonad.v` | 77 | 77 |
| `Instance/Rng/FreeMonad/System.v` | 65 | 65 |
| `Instance/Rng/FreeMonad/Words.v` | 80 | 80 |
| `Instance/Sets.v` | 60 | 60 |
| `Instance/Sets/Classifier.v` | 142 | 142 |
| `Instance/Sets/Classifier/OneLevel.v` | 686 | 686 |
| `Instance/Sets/Cocomplete.v` | 2 | 2 |
| `Instance/Sets/Cogenerator.v` | 37 | 37 |
| `Instance/Sets/CokernelPair.v` | 42 | 42 |
| `Instance/Sets/Generator.v` | 36 | 36 |
| `Instance/Sets/InverseLimit.v` | 12 | 12 |
| `Instance/Sets/Powerset.v` | 343 | 343 |
| `Instance/Sets/Powerset/Monad.v` | 103 | 103 |
| `Instance/Sets/Powerset/Monad/Riehl.v` | 55 | 55 |
| `Instance/Sets/Powerset/Universal.v` | 283 | 283 |
| `Instance/Sets/Propositional/Full.v` | 110 | 110 |
| `Instance/Sets/QuotObj.v` | 77 | 77 |
| `Instance/Sets/SpecialInitial.v` | 49 | 49 |
| `Instance/Sets/Split.v` | 2 | 2 |
| `Instance/Sets/SubobjectLattice.v` | 25 | 25 |
| `Instance/Sets/Topos.v` | 111 | 111 |
| `Instance/Sets/WellPowered.v` | 73 | 73 |
| `Instance/Smgrp.v` | 277 | 277 |
| `Instance/Smgrp/Word.v` | 463 | 463 |
| `Instance/Square/Rectangle.v` | 9 | 9 |
| `Instance/SupLat.v` | 432 | 432 |
| `Instance/SupLat/Examples.v` | 177 | 28 |
| `Instance/SupLat/Free.v` | 283 | 283 |
| `Instance/SupLat/Free/Morphism.v` | 146 | 2 |
| `Instance/Top.v` | 16 | 16 |
| `Instance/Top/Circle.v` | 157 | 157 |
| `Instance/Top/Cocomplete.v` | 126 | 126 |
| `Instance/Top/Cocomplete/Refutations.v` | 73 | 73 |
| `Instance/Top/Cocomplete/TypeValued.v` | 31 | 31 |
| `Instance/Top/CompHaus.v` | 10 | 10 |
| `Instance/Top/Complete.v` | 150 | 150 |
| `Instance/Top/Complete/ConeComma.v` | 36 | 36 |
| `Instance/Top/Complete/Refutations.v` | 89 | 89 |
| `Instance/Top/Components.v` | 400 | 400 |
| `Instance/Top/Components/Paths.v` | 447 | 447 |
| `Instance/Top/Forgetful.v` | 17 | 17 |
| `Instance/Top/Hausdorff.v` | 183 | 183 |
| `Instance/Top/Hausdorff/TypeValued.v` | 96 | 96 |
| `Instance/Top/Image.v` | 21 | 21 |
| `Instance/Top/Interior.v` | 90 | 90 |
| `Instance/Top/Interval.v` | 1 | 1 |
| `Instance/Top/Kolmogorov.v` | 1 | 1 |
| `Instance/Top/Monadicity.v` | 232 | 232 |
| `Instance/Top/Monadicity/TypeValued.v` | 20 | 20 |
| `Instance/Top/Prop.v` | 70 | 70 |
| `Instance/Top/Quotient.v` | 129 | 129 |
| `Instance/Top/Quotient/Pairs.v` | 298 | 298 |
| `Instance/Top/Separation.v` | 136 | 136 |
| `Instance/Top/Solenoid.v` | 194 | 194 |
| `Instance/Top/Solenoid/Presentations.v` | 360 | 360 |
| `Instance/Top/StoneCech.v` | 66 | 66 |
| `Instance/Top/StoneCech/Refutations.v` | 70 | 70 |
| `Instance/Top/Subspace.v` | 98 | 98 |
| `Instance/Top/Subspace/TypeValued.v` | 88 | 88 |
| `Lib/Setoid.v` | 10 | 10 |
| `Lib/Setoid/Propositional.v` | 8 | 8 |
| `Monad/Comparison/Resolution.v` | 6 | 6 |
| `Monad/Eilenberg/Moore/Limit.v` | 5 | 5 |
| `Monad/Eilenberg/Moore/Limit/Examples.v` | 61 | 61 |
| `Monad/Identity.v` | 43 | 43 |
| `Monad/Kleisli/Comparison/Examples.v` | 1 | 1 |
| `Monad/Monoid.v` | 14 | 14 |
| `Monad/Morphism.v` | 49 | 49 |
| `Monad/Morphism/Algebra.v` | 119 | 119 |
| `Monad/Morphism/Monoid.v` | 102 | 102 |
| `Monad/Morphism/Transformer.v` | 18 | 18 |
| `Structure/Bicartesian/Matrix.v` | 1 | 1 |
| `Structure/Coequalizer.v` | 2 | 2 |
| `Structure/Coequalizer/Absolute.v` | 27 | 27 |
| `Structure/Coequalizer/Contractible.v` | 4 | 4 |
| `Structure/Coequalizer/Split.v` | 4 | 4 |
| `Structure/Complete.v` | 6 | 6 |
| `Structure/Complete/Freyd.v` | 5 | 5 |
| `Structure/Cone.v` | 8 | 8 |
| `Structure/Lattice.v` | 8 | 8 |
| `Structure/Limit/Absolute.v` | 62 | 62 |
| `Structure/Limit/Comparison.v` | 7 | 7 |
| `Structure/Limit/Components.v` | 2 | 2 |
| `Structure/Limit/Constant.v` | 6 | 6 |
| `Structure/Limit/Finite.v` | 15 | 15 |
| `Structure/Limit/Preservation.v` | 9 | 9 |
| `Structure/Limit/Reflection.v` | 4 | 4 |
| `Structure/Monoidal/Dual.v` | 2 | 2 |
| `Structure/Projective.v` | 5 | 5 |
| `Structure/Ring.v` | 15 | 15 |
| `Structure/SlicedInverse.v` | 47 | 47 |
| `Structure/SlicedInverse/Strict.v` | 27 | 27 |
| `Structure/Thin/Monad.v` | 29 | 29 |
| `Structure/WellPowered.v` | 77 | 77 |
| `Structure/WellPowered/Counterexample.v` | 23 | 23 |
| `Theory/Adamek.v` | 4 | 4 |
| `Theory/Adjunction.v` | 4 | 4 |
| `Theory/Algebra/Group/Hom.v` | 3 | 3 |
| `Theory/Algebra/Monoid/Product.v` | 3 | 3 |
| `Theory/Algebra/Rig.v` | 19 | 19 |
| `Theory/Category.v` | 5 | 5 |
| `Theory/Centre.v` | 18 | 18 |
| `Theory/Concrete.v` | 22 | 22 |
| `Theory/Connected/Components.v` | 34 | 34 |
| `Theory/Coq/Traversable.v` | 1 | 1 |
| `Theory/Density.v` | 6 | 6 |
| `Theory/Equivalence/Adjoint/Compose.v` | 3 | 3 |
| `Theory/Equivalence/Strict.v` | 3 | 3 |
| `Theory/Functor.v` | 6 | 6 |
| `Theory/Isomorphism.v` | 1 | 1 |
| `Theory/Natural/Transformation.v` | 2 | 2 |
| `Theory/OGraph.v` | 245 | 245 |
| `Theory/Sheaf.v` | 2 | 2 |
| `Theory/Size.v` | 13 | 13 |
| `Theory/Subobject.v` | 1 | 1 |
| `Theory/WeaklyInitial.v` | 4 | 4 |
| **Total** | **15648** | **15355** |
