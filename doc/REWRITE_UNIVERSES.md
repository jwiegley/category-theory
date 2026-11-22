# Universe cost of rewriting both sides of `≈` (#1371)

At `bc67f5844fc8305509fe220f6c425f85dd5b66b4`, on released Rocq 9.2.0, `rewrite H` in `f ∘ g ≈ f ∘ k` uses `CMorphisms.PER_type_morphism` when `H` rewrites `f`. Its result relation is `iffT`, a product of two functions. Transport out of that product leaves upper bounds from the equivalence level to `prod_rect.u0`, `.u1` and `.u2`, even when the proof ends in `Qed`. Rewriting only the left side of `f ∘ g ≈ t` uses `trans_co_eq_inv_arrow_morphism` instead; that proof has none of those bounds. Splitting the two changes with transitivity and `compose_respects` also avoids them.

## Intervention

`Lib/Setoid.v` exports two `Proper` instances for `equiv`. A conclusion needs transport from the new goal back to the old one (`flip arrow`); a hypothesis needs the forward function (`arrow`). Supplying only the former cures the goal but not the hypothesis. Both use transitivity and symmetry directly. In the proof-term controls at priorities 1 and 2 the new backward instance also displaces the old one-sided instance. At 3, 4 and 5 the two-sided goals and hypotheses select their respective new instances while the one-sided goal keeps its original proof. At 6, 10 and 100 the two-sided controls again select `PER_type_morphism`. We use 5. `Test/Issue1371.v` checks both directions above all three product eliminator levels, as well as the one-sided control and an opaque lemma. On the unmodified library the one-sided proof succeeds; the first two-sided `rewrite` fails to resolve the required `Proper` instance.

## Which files lose caps?

`git grep -l prod_rect -- '*.v'` at the baseline returns 49 paths (47 in the original report). This is a list of mentions, not a count of affected modules. For each path we queried the qualified `.glob` heads of kind `ind`, `constr`, `def`, `class`, `inst`, `prf`, `proj`, `meth`, `rec` or `ax`, plus top-level `Parameter` and `Definition` heads in `Print Module` not already selected, including generated obligations. Of 2,102 `.glob` names, 16 were not defined objects on either side; the module queries added 337 names. This selection is not a traversal of every submodule or private proof.

Each count below is a **declaration**, not a proof step or a constraint edge. Of 967 surveyed declarations whose baseline `About` printed a constraint with `prod_rect.uN` on the right, 619 lose every such edge after recompilation with the two instances. These are intervention results: a declaration can lose a cap inherited from another proof. For example, the baseline printed bodies of `wide_pullback_proj_monic`, `hom_test_iso`, `cmp_e_cofork`, `image_of_rel` and `RMod_ring_separates` themselves name `PER_type_morphism`; the treated versions no longer need the cap. In contrast, the 348 declarations in the second column retain at least one printed edge. This does **not** establish that every retained edge has an unrelated cause. A zero in both columns means no selected declaration had a printed cap, not that the file never discusses one.

| File | Lose all | Retain any |
|---|---:|---:|
| `Adjunction/FunctorCategory.v` | 19 | 0 |
| `Construction/Slice/Adjunction.v` | 19 | 3 |
| `Functor/Hom/Continuous.v` | 0 | 15 |
| `Instance/FdVect/NoRightAdjoint.v` | 34 | 11 |
| `Instance/FinSet/Limit.v` | 3 | 0 |
| `Instance/Fun/Action/Monad.v` | 0 | 44 |
| `Instance/Fun/Action/Monad/BG.v` | 7 | 33 |
| `Instance/Fun/Action/Monad/BG/Morphism.v` | 0 | 12 |
| `Instance/Fun/Action/Monad/Comparison.v` | 0 | 32 |
| `Instance/Fun/Eval.v` | 13 | 0 |
| `Instance/Fun/Eval/Cat.v` | 0 | 6 |
| `Instance/Mod/Coextension.v` | 63 | 0 |
| `Instance/Mod/Colimit/Creation.v` | 29 | 0 |
| `Instance/Mod/TensorMonad.v` | 36 | 0 |
| `Instance/Mod/TensorMonad/Cocontinuous.v` | 14 | 0 |
| `Instance/Mod/Watts.v` | 7 | 18 |
| `Instance/Mod/WellPowered.v` | 25 | 0 |
| `Instance/Pos/Monadicity.v` | 25 | 0 |
| `Instance/Props/Modal.v` | 10 | 0 |
| `Instance/Sets/NoAdjoint.v` | 3 | 1 |
| `Instance/Sets/Propositional.v` | 0 | 2 |
| `Instance/Sets/Propositional/Full.v` | 4 | 0 |
| `Instance/Smgrp.v` | 8 | 0 |
| `Instance/Smgrp/Word.v` | 66 | 0 |
| `Instance/SupLat/Free.v` | 16 | 0 |
| `Instance/Top/Monadicity.v` | 34 | 0 |
| `Instance/Top/Monadicity/TypeValued.v` | 1 | 0 |
| `Instance/Top/Solenoid.v` | 1 | 0 |
| `Instance/Top/Solenoid/Presentations.v` | 7 | 35 |
| `Instance/Top/Subspace.v` | 24 | 0 |
| `Instance/Variety/Colimit.v` | 6 | 4 |
| `Lib/Setoid/Propositional.v` | 0 | 1 |
| `Lib/Tactics.v` | 0 | 0 |
| `Monad/Comparison/Resolution.v` | 43 | 0 |
| `Monad/Eilenberg/Moore/Limit.v` | 0 | 0 |
| `Monad/Eilenberg/Moore/Limit/Examples.v` | 1 | 0 |
| `Monad/Morphism/Monoid.v` | 21 | 0 |
| `Monad/Morphism/Transformer.v` | 0 | 0 |
| `Structure/Coequalizer/Contractible.v` | 0 | 0 |
| `Structure/Equalizer/Coreflexive.v` | 2 | 4 |
| `Structure/Generator.v` | 5 | 0 |
| `Structure/Lattice.v` | 0 | 29 |
| `Structure/Limit/Diagrams.v` | 15 | 0 |
| `Structure/Monoidal/Dual.v` | 0 | 37 |
| `Structure/Projective.v` | 7 | 0 |
| `Structure/Ring.v` | 0 | 44 |
| `Theory/Algebra/Monoid/Product.v` | 1 | 17 |
| `Theory/Subobject/Lattice.v` | 28 | 0 |
| `Theory/Subobject/Quotient.v` | 22 | 0 |

## Whole configured gate

Before and after `About` queries in the import context of the assumptions gate give 14,506 paired blocks. At priority 5, 11,097 are byte-identical. Of the other 3,409, 3,274 lose every printed `prod_rect` upper bound, 129 retain at least one, and six had none on either side. None gains a first bound. For comparison, at priority 1 the backward instance alone eliminates all printed caps for 2,002 gated names; supplying both directions at 1 eliminates them for 3,274 but changes 3,560 blocks. These figures do not assert that every difference is a removed edge.

In particular the printed universe instance **changes length** for `fixed` in `Instance/Grp/Galois.v` (5→4), `Two_Fun_Arrow` (96→88), `graph_limitcone` (9→8), `two_IsALimit` (8→7), `two_IsAColimit` (17→16), `two_transport_moves_inj` (31→29), `two_shift_induced_computes` and `two_shift_induced_not_iso` (both 11→9), `SemidirectRing` (10→9), `rsdp_mul_fst` and `rsdp_mul_snd` (both 9→8). External positional callers must recheck their instances.

### Reproduce every changed block

Build separate trees for the baseline named above and this change, in the locked release shell. Save the actual `pa.v` generated by the baseline `make print-assumptions` before its recipe removes `.pa-tmp`. For example, in that shell use the following forwarding wrapper during the baseline audit only (`base` and `after` are absolute paths to the built trees):

```sh
tmp=$(mktemp -d)
export AUDIT_QUERY="$tmp/pa.v" REAL_COQC="$(command -v coqc)"
cat > "$tmp/coqc" <<'SH'
#!/bin/sh
for arg do
  case "$arg" in .pa-tmp/pa.v) cp "$arg" "$AUDIT_QUERY" || exit 1;; esac
done
exec "$REAL_COQC" "$@"
SH
chmod +x "$tmp/coqc"
(cd "$base" && PATH="$tmp:$PATH" make print-assumptions) &&
python3 "$after/scripts/compare_rewrite_gate.py" "$AUDIT_QUERY" "$base" "$after" "$tmp/comparison"
```

`comparison/gate.diff` records each changed block under its configured name, without normalizing locations or private universes. Both full streams, query sources and diagnostics remain beside it. The original priority-5 treatment's unified diff has SHA-256 `2681ef3e4c23c0393b6c9dfb8deffd31e3d6150b4c2993446794b269cfa84a95`; locations can change with source layout.
