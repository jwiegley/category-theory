# Positional universe instances: #1412 inventory and first batch

This is a partial #1412 batch, not issue closure or core-signature redesign.
Baseline: `438d83b2b706d33f1deaad60672c3ed5ed2a6554` (including PR #1407).
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

## Remaining #1412 scope

Continue in reviewable jointly verified batches: resolve full constant identities,
distinguish genuine identifications from redundant annotations, compare all
affected declarations/bodies/constraints and actual callers, preserve full refusal
payloads and eager controls, and run the supported matrix and gates. The other
historical candidates, CMon application and every other unassessed site remain
#1412 work. Hub/signature redesign belongs to later issues.

## Per-file inventory

`Before` is the bound baseline; `After` includes this batch. Unlisted files have
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
