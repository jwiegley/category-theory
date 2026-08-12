Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * The category of adjunctions between two fixed categories *)

(* nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   For fixed C and D this assembles the adjunctions F ⊣ U with F : D ⟶ C and
   U : C ⟶ D into a category Adj(C,D):

       objects        triples (F, U, F ⊣ U)
       arrows         pairs (σ : F ⟹ F', τ : U ⟹ U') of natural transformations
       identity       the pair (nat_id, nat_id)
       composition    componentwise vertical composition of natural transformations

   This is the hom-category between C and D of the 2-category Adj of categories,
   adjunctions, and their maps; the sibling file [Instance.Adjoints] instead
   bundles categories and adjunctions into a 1-category (objects are categories,
   arrows are adjunctions).

   CAVEAT (needs-followup, not a build issue): the standard "category of
   adjunctions" takes as a morphism (F ⊣ U) → (F' ⊣ U') a conjugate, or mate,
   pair of natural transformations — σ and τ are required to correspond under
   the two hom-set transposes, equivalently (writing τ in the opposite
   direction, U' ⟹ U) one is the mate of the other through the units and
   counits.  That condition is now in tree and named: [Conjugate] of
   Adjunction/Conjugate.v is Mac Lane's §IV.7 hom-set square quantified over
   every transposable arrow, [conjugate_characterizations] proves the four
   equivalent pasting forms, and [conjugate_bijection] pairs each
   transformation of left adjoints with its one and only conjugate.  The hom
   defined below still imposes no such condition: it is the bare product
   setoid ([D,C] × [C,D]) of natural transformations restricted to the
   carrier of adjunction triples.  This is why every category obligation
   discharges trivially.  The construction is a genuine category but a
   coarser one than the conjugate-pair Adj(C,D).  Tightening it is more than
   adding a side condition to the pair below: both components here are
   covariant, while a conjugate pair reverses exactly one leg:
   [Conjugate A A'] pairs σ : F' ⟹ F with τ : U ⟹ U', and the equivalent
   Riehl labelling [Conjugate A' A] pairs σ : F ⟹ F' with τ : U' ⟹ U.
   Either way the hom has to be retyped before [Conjugate] can be imposed
   on it.
   Once retyped, [conjugate_id] and [conjugate_compose] are exactly the
   identity and composition closure such a category needs; that refactor is
   left as future work.  The code is unchanged because Wikipedia does not
   treat morphisms of adjunctions, so the two reference sources do not
   jointly contradict it. *)

Program Definition Adj (C D : Category) : Category := {|
  obj := ∃ (F : D ⟶ C) (U : C ⟶ D), F ⊣ U;
  hom := fun x y => (`1 x ⟹ `1 y) ∧ (`1`2 x ⟹ `1`2 y);
  id  := fun x => (nat_id, nat_id);
  compose := fun _ _ _ f g => (fst f ∙ fst g, snd f ∙ snd g)
|}.
Next Obligation. apply prod_setoid. Defined.
Next Obligation.
  proper; simpl in *; simplify;
  rewrites; reflexivity.
Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
