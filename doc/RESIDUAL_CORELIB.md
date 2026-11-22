# Equality as the domain relation of a chain map (#1399)

On released Rocq/Corelib 9.2.0, `Corelib.Classes.CMorphisms.reflexive_eq_dom_reflexive` proves reflexivity of `respectful eq R` on functions `A -> B` provided `R` is reflexive on `B`. Its expanded type has `respectful@{a Set b rb f rf}`: **the relation on `A` is read at `Set`, not the carrier of `B`**. The remaining constraints are `Set <= rf`, `b <= f`, `a <= f`, `a <= rf`, `rb <= rf`, `a <= eq_rect_r.u0` and `rb <= eq_rect_r.u1`. All five bound levels occur in the type. The constant is closed and opaque. This reading requires only `From Corelib Require Import Classes.CMorphisms.` followed by `Set Printing All. Set Printing Universes. About reflexive_eq_dom_reflexive.`

## Which part matters to an actual caller?

Baseline: `ff7443058c53575660a10aab172cdb9b3f9c119c`, Stdlib 9.1.0, Equations 1.3.2+9.2. Compile three separate copies of baseline `Construction/Chain.v` with its normal imports. Leave the original alone. For the treatment insert the following before `Section Chain.`; for the sham insert the identical text, substituting `Set` for **only the second argument** `ra` of `respectful`. Retain `ra` in the binder: dropping it would change another variable. These hints are experimental and file-local.

```coq
From Stdlib Require CRelationClasses CMorphisms.
#[local] Instance reflexive_eq_dom_local@{a ra +} {B : Type}
  (R' : Corelib.Classes.CRelationClasses.crelation B)
  `{H : @Corelib.Classes.CRelationClasses.Reflexive B R'} {A : Type@{a}} :
  @Corelib.Classes.CRelationClasses.Reflexive (A -> B)
    (@Corelib.Classes.CMorphisms.respectful@{a ra _ _ _ _} A B (@eq A) R').
Proof. intros f x y e. destruct e. apply H. Qed.
#[local] Remove Hints Corelib.Classes.CMorphisms.reflexive_eq_dom_reflexive
  : typeclass_instances.
```

Append `Set Printing All. Set Printing Universes. About Chain. Print Chain. About Cochain. Print Assumptions Chain. Print Assumptions Cochain.` in each copy. `Print Chain` identifies the selected proof: the stock head in the original; the local head in **both** modified copies. Use `o,h` for the target's object and shared hom/proof levels, `i` for the index object level and `j` for its shared hom/proof level:

| `Chain` | Index | Target | Other printed constraints |
|---|---|---|---|
| Original | `Omega@{i Set Set}` | `Category@{o h h}` | `h <= eq_rect_r.u1` |
| `ra` | `Omega@{i j j}` | `Category@{o h h}` | `j <= h, eq.u0, Logic_lemmas.equality.u0, eq_ind_r.u0` |
| `Set` sham | `Omega@{i Set Set}` | `Category@{o h h}` | none; fourth bound level absent from applied type |
| Direct substitution in `fmap_respects` | as `ra` | as `ra` | as `ra` |

A proof-only level in the sham is not a new index level. Changing the proof body from Corelib's proof suffices to lose the old `eq_rect_r` bound even in the sham; **only the treatment lifts the literal pin** in this controlled pair. In `Cochain` the original takes `C : Category@{o Set Set}`; with direct substitution both the index and the target use the same `h` for hom and proof, with `h <= eq.u0, Logic_lemmas.equality.u0, eq_ind_r.u0`. This is not unrestricted polymorphism. `Test/ProbeInverseLimit408.v` applies the actual cochain functor at `Set < ch`, not merely to an anonymous universe that could minimize to `Set`.

The library route changes **one field**, the `fmap_respects` proof of `Chain`: substitute the equality between the two `le_t` paths, then use reflexivity of the target hom-setoid. No hint is registered or removed. `chain_hom`, the functor's object and arrow functions, its identity/composition proofs, and the definition of `Cochain` by duality are unchanged. Both functors remain transparent and closed. Already specialized consumers are a separate matter: `cochain_inverse_limit`, `cochain_tower_limit`, the stage examples and `StreamTower` in `Instance/Sets/InverseLimit.v` explicitly select small carriers. To generalize those statements requires restating and checking them, not a claim about the donor alone.

The historical walking-arrow experiment is **not** reproduced at `_2` on this release. In fresh whole-file copies of `Instance/Two.v` all three variants give `Category@{o Set Set}`. The two bound levels in the original are not two independent visible levels of the category. Explicit annotations on the category and `Morphism_equality` lift the pin in **all three** variants, hence do not isolate the hint as its present cause. `_2` and its existing refusal probes stay untouched. This separates the `Chain` finding from #1180's broader minimization question. Neither `rig_mult_monoid` nor its already restricted forgetful functors (#1160) are migrated by this proof; #1367's consolidation of constant functors is also separate, and #1383's Point repair is pre-existing.

## Inventory and upstream scope

In the installed `Classes/CRelationClasses.glob` and `Classes/CMorphisms.glob`, collect distinct qualified names from declaration rows of kind `def`, `prf`, `inst`, `proj`, `ind`, `rec` or `constr`. Include module qualifiers and coalesce duplicate class/projection rows. Query each with `About` and both printing flags, counting a name once if a printed `head@{...}` in its type (after the outer binder, before constraints) contains the token `Set`. This gives 28 of 142 names, not an enumeration of all Corelib declarations or a count of bugs. The affected readings break down as follows:

* `complement`, `complement_inverse`, `irreflexivity`, `complement_Irreflexive`, `complement_Symmetric` and `PartialOrder_StrictOrder` read the complement relation at the small sort; negation has a proposition-valued result. This is not an upper bound on the original relation.
* `impl_Reflexive`, `impl_Transitive`, `iff_Reflexive`, `iff_Symmetric`, `iff_Transitive`, `iff_equivalence`, `iff_impl_subrelation`, `iff_flip_impl_subrelation`, `proper_sym_impl_iff` and `proper_sym_impl_iff_2` have slots for implication or logical equivalence on propositions. Those relations are intentionally small; their use does not in itself require forcing every ambient relation universe to `Set`.
* `eq_Reflexive`, `eq_Symmetric`, `eq_Transitive`, `eq_equivalence`, `eq_proper_proxy`, `pointwise_pointwise`, `proper_subrelation_proper_arrow`, `trans_co_eq_inv_arrow_morphism`, `reflexive_eq_dom_reflexive`, `eq_subrelation`, `proper_eq` and `proper_proper` have slots for Leibniz equality. Equality is proposition-valued, but its use at a larger relation universe is legitimate. The controlled intervention above establishes the effect for **one** of these heads. It does not attribute every specialized caller to this mechanism or authorize rewriting the other instances.

Upstream [rocq-prover/rocq#22575](https://github.com/rocq-prover/rocq/pull/22575) merged at `4975c9d338952e0f38146518c56a4ad05d128e02`. This is distinct from what the released 9.2.0 binaries print. No upstream build, replacement Corelib, global hint shim or claim of backward compatibility forms part of this library repair.
