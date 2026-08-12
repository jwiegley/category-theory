Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Conjugate natural transformations *)

(* nLab: https://ncatlab.org/nlab/show/mate
   nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
     pp. 99-100: Definition 2 (conjugate transformations) and Theorem 2 (the
     four characterizations and the bijection).
   Riehl, "Category Theory in Context", 2nd ed., §4.3, p. 148: the same
     bijection, and exercise (iv).

   Fix two adjunctions between the same pair of categories, A : F ⊣ U and
   A' : F' ⊣ U' with F, F' : D ⟶ C and U, U' : C ⟶ D.  Mac Lane calls
   σ : F' ⟹ F and τ : U ⟹ U' CONJUGATE when the two hom-set transposes carry
   one into the other:

       ⌊ k ∘ σ x ⌋²  ≈  τ a ∘ ⌊ k ⌋        for every k : F x ~> a,

   which is [Conjugate] below, quantified over every transposable arrow
   rather than evaluated at one distinguished argument.  Reading the same
   square through the inverse transposes gives [ConjugateFrom], and
   [conjugate_iff_from] shows the two readings agree.

   Mac Lane's Theorem 2 is that four further equations are each equivalent to
   that square, and [conjugate_characterizations] proves all four:

       (mate)        τ  =  U'ε ∘ U'σU ∘ η'U
       (mate_inv)    σ  =  ε'F ∘ F'τF ∘ F'η
       (unit)        τF ∘ η  =  U'σ ∘ η'
       (counit)      ε ∘ σU  =  ε' ∘ F'τ

   The first two are the pasting composites that Theory/Bicategory/Mates.v's
   [mate] and [mate_inv] compute — [ConjugateMate_pasting] and
   [ConjugateMateInv_pasting] give them in that three-fold spelling — while
   the counit equation had no statement in tree before this file, and the
   unit equation only in the degenerate case F = F', as the hypothesis of
   Theory/Bicategory/Adjunction.v:347 [mate_charac] and the conclusion of
   :636 [mate_unit_compat].
   Each σ has one and only one conjugate, and each τ one and only one
   ([conjugate_unique_right], [conjugate_unique_left]), both obtained by
   evaluating the square at a universal arrow: at k := ε for τ, at k := id
   for σ.  The two operators [conj_mate] and [conj_mate_inv] package that as
   [conjugate_bijection], an isomorphism in Sets of the two transformation
   setoids, shaped after Mates.v:515 [mate_iso].

   WHY THIS LIVES HERE, IN ORDINARY VOCABULARY.  Mates.v already delivers the
   bijection over an arbitrary bicategory with arbitrary bounding 1-cells,
   and Mac Lane's setting is the case where both bounding cells are
   identities.  That route is not the
   source's DEFINITION, which is a hom-set square, and it is expensive:
   making C and D objects of Cat pulls Instance/Cat, Instance/Fun and the
   whole bicategory chain into a development that otherwise needs the seven
   modules above.  It is not a typability barrier — Cat is universe-
   polymorphic, so Instance/Cat/Bicategory/Conjugate.v takes arbitrary C and
   D (and Cat itself) through the bicategory — the cost is the dependency
   cone, which is also why the print-assumptions audit lists this file and
   not the satellite.  The two are reconciled in
   Instance/Cat/Bicategory/Conjugate.v, where padding transformations mediate
   between F' ⟹ F and the bicategorical F' ◯ Id ⟹ Id ◯ F — not the same
   type, since the two functor records carry different [fmap_respects],
   [fmap_id] and [fmap_comp] fields, which are data here and which record
   eta cannot identify — and
   [Cat_conj_mate_agrees] identifies [conj_mate] with [mate].

   ORIENTATION.  Riehl states the same bijection with the primes exchanged,
   pairing F ⟹ F' with U' ⟹ U.  That is this relation with its two
   adjunction arguments swapped, [Conjugate A' A], not a second theorem.

   SCOPE, three disclosures.

   (1) [conj_unit_nat] and [conj_counit_nat] are the naturality squares of
   the unit and counit at an ARBITRARY morphism.  Theory/Adjunction.v:228
   [counit_comp] and :238 [unit_comp] look like these but pin one endpoint to
   an F- or U-image, and are not usable for the two [Transform] obligations
   here.  The general unit form already exists at
   Theory/Equivalence/Adjoint.v:85 and the general counit form twice, at :95
   and at Construction/Reflective.v:46;
   importing either pulls the equivalence-of-categories or the reflective
   subcategory development into a file that otherwise needs the seven modules
   above, so this file re-derives them in two lines each.  Consolidating those three
   with the two below into Theory/Adjunction.v is a separate hygiene change.

   (2) [conjugate_id] and [conjugate_compose] are the identity-bounding-cell
   shadow of the pasting functoriality that Mates.v deliberately leaves out
   of scope (its descope ledger entry 10, the double category of
   adjunctions).  They do not discharge that entry; the general bicategorical
   statement remains out of scope there.

   (3) [conjugate_invertible_iff] is pointwise: it converts a componentwise
   two-sided inverse for σ into one for τ and back, using only the square and
   neither transformation's naturality.  It does not state invertibility in
   the functor categories [D,C] and [C,D]. *)

Section Conjugate.

Context {C D : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A  : F  ⊣ U).
Context (A' : F' ⊣ U').

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).

Notation "'η'"  := (@unit   _ _ _ _ A).
Notation "'ε'"  := (@counit _ _ _ _ A).
Notation "'η²'" := (@unit   _ _ _ _ A') (at level 0).
Notation "'ε²'" := (@counit _ _ _ _ A') (at level 0).

(* ---- the definition: Mac Lane IV.7 Definition 2, the hom-set square ---- *)

Definition Conjugate (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a), ⌊ k ∘ σ x ⌋² ≈ τ a ∘ ⌊ k ⌋.

Definition ConjugateFrom (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ (x : D) (a : C) (g : x ~> U a), ⌈ τ a ∘ g ⌉² ≈ ⌈ g ⌉ ∘ σ x.

Lemma Conjugate_respects_left (σ σ' : F' ⟹ F) (τ : U ⟹ U') :
  σ ≈ σ' → Conjugate σ τ → Conjugate σ' τ.
Proof.
  intros Hs H x a k.
  rewrite <- (Hs x).
  now apply H.
Qed.

Lemma Conjugate_respects_right (σ : F' ⟹ F) (τ τ' : U ⟹ U') :
  τ ≈ τ' → Conjugate σ τ → Conjugate σ τ'.
Proof.
  intros Ht H x a k.
  rewrite <- (Ht a).
  now apply H.
Qed.

Theorem conjugate_iff_from (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ ↔ ConjugateFrom σ τ.
Proof.
  split.
  - intros H x a g.
    rewrite <- (from_adj_comp_law (H:=A) g) at 1.
    rewrite <- (H x a ⌈ g ⌉).
    now rewrite (to_adj_comp_law (H:=A')).
  - intros H x a k.
    rewrite <- (to_adj_comp_law (H:=A) k) at 1.
    rewrite <- (H x a ⌊ k ⌋).
    now rewrite (from_adj_comp_law (H:=A')).
Qed.

(* ---- general naturality of unit and counit ---- *)

Lemma conj_unit_nat {x y : D} (g : x ~> y) :
  fmap[U] (fmap[F] g) ∘ η ≈ η ∘ g.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_r, <- to_adj_nat_l; cat.
Qed.

Lemma conj_counit_nat {a b : C} (f : a ~> b) :
  f ∘ ε ≈ ε ∘ fmap[F] (fmap[U] f).
Proof.
  unfold counit.
  rewrite <- from_adj_nat_r, <- from_adj_nat_l; cat.
Qed.

(* ---- the four characterizations ---- *)

Definition ConjugateMate (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ a : C, τ a ≈ fmap[U'] ε ∘ ⌊ σ (U a) ⌋².

Definition ConjugateMateInv (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ x : D, σ x ≈ ε² ∘ fmap[F'] (τ (F x) ∘ η).

Definition ConjugateUnit (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ x : D, τ (F x) ∘ η ≈ fmap[U'] (σ x) ∘ η².

Definition ConjugateCounit (σ : F' ⟹ F) (τ : U ⟹ U') : Type :=
  ∀ a : C, ε ∘ σ (U a) ≈ ε² ∘ fmap[F'] (τ a).

(* the pasting spellings, for statement fidelity *)

Lemma ConjugateMate_pasting (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateMate σ τ ↔
    ∀ a : C, τ a ≈ fmap[U'] ε ∘ (fmap[U'] (σ (U a)) ∘ η²).
Proof.
  split; intros H a; rewrite (H a);
  now rewrite (to_adj_unit (H:=A')).
Qed.

Lemma ConjugateMateInv_pasting (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateMateInv σ τ ↔
    ∀ x : D, σ x ≈ ε² ∘ (fmap[F'] (τ (F x)) ∘ fmap[F'] η).
Proof.
  split; intros H x; rewrite (H x);
  now rewrite fmap_comp.
Qed.

(* ---- the eight directed legs ---- *)

Lemma conjugate_to_mate (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → ConjugateMate σ τ.
Proof.
  intros H a.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (H (U a) a ε).
  rewrite (to_adj_counit (H:=A)).
  now rewrite id_right.
Qed.

Lemma mate_to_conjugate (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateMate σ τ → Conjugate σ τ.
Proof.
  intros H x a k.
  rewrite (H a).
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  apply (to_adj_respects (H:=A')).
  rewrite <- comp_assoc.
  rewrite (naturality_sym σ _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Lemma conjugate_to_counit (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → ConjugateCounit σ τ.
Proof.
  intros H a.
  rewrite <- (from_adj_counit (H:=A')).
  rewrite (conjugate_to_mate σ τ H a).
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Lemma counit_to_conjugate (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateCounit σ τ → Conjugate σ τ.
Proof.
  intros H.
  apply mate_to_conjugate.
  intros a.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (H a).
  rewrite <- (from_adj_counit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Lemma conjugate_to_unit (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → ConjugateUnit σ τ.
Proof.
  intros H x.
  transitivity (⌊ id[F x] ∘ σ x ⌋²).
  - symmetry; exact (H x (F x) id).
  - rewrite id_left.
    now rewrite (to_adj_unit (H:=A')).
Qed.

Lemma unit_to_conjugate (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateUnit σ τ → Conjugate σ τ.
Proof.
  intros H.
  apply mate_to_conjugate.
  intros a.
  rewrite (to_adj_unit (H:=A')).
  rewrite <- (H (U a)).
  rewrite comp_assoc.
  rewrite (naturality τ _ _ ε).
  rewrite <- comp_assoc.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite id_right.
Qed.

Lemma unit_to_mate_inv (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateUnit σ τ → ConjugateMateInv σ τ.
Proof.
  intros H x.
  rewrite <- (from_adj_counit (H:=A')).
  rewrite (H x).
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Lemma mate_inv_to_unit (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateMateInv σ τ → ConjugateUnit σ τ.
Proof.
  intros H x.
  rewrite <- (to_adj_unit (H:=A')).
  rewrite (H x).
  rewrite <- (from_adj_counit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Lemma conjugate_to_mate_inv (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → ConjugateMateInv σ τ.
Proof. intro H; exact (unit_to_mate_inv σ τ (conjugate_to_unit σ τ H)). Qed.

Lemma mate_inv_to_conjugate (σ : F' ⟹ F) (τ : U ⟹ U') :
  ConjugateMateInv σ τ → Conjugate σ τ.
Proof. intro H; exact (unit_to_conjugate σ τ (mate_inv_to_unit σ τ H)). Qed.

Theorem conjugate_characterizations (σ : F' ⟹ F) (τ : U ⟹ U') :
  (Conjugate σ τ ↔ ConjugateMate σ τ)
  ∧ (Conjugate σ τ ↔ ConjugateMateInv σ τ)
  ∧ (Conjugate σ τ ↔ ConjugateUnit σ τ)
  ∧ (Conjugate σ τ ↔ ConjugateCounit σ τ).
Proof.
  repeat split.
  - exact (conjugate_to_mate σ τ).
  - exact (mate_to_conjugate σ τ).
  - exact (conjugate_to_mate_inv σ τ).
  - exact (mate_inv_to_conjugate σ τ).
  - exact (conjugate_to_unit σ τ).
  - exact (unit_to_conjugate σ τ).
  - exact (conjugate_to_counit σ τ).
  - exact (counit_to_conjugate σ τ).
Qed.

(* ---- the two operators ---- *)

Program Definition conj_mate (σ : F' ⟹ F) : U ⟹ U' := {|
  transform := λ a, ⌊ ε ∘ σ (U a) ⌋²
|}.
Next Obligation.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  apply (to_adj_respects (H:=A')).
  rewrite <- !comp_assoc.
  rewrite (naturality_sym σ _ _ (fmap[U] f)).
  rewrite !comp_assoc.
  now rewrite <- (conj_counit_nat f).
Qed.
Next Obligation.
  symmetry.
  now apply conj_mate_obligation_1.
Qed.

Program Definition conj_mate_inv (τ : U ⟹ U') : F' ⟹ F := {|
  transform := λ x, ⌈ τ (F x) ∘ η ⌉²
|}.
Next Obligation.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite <- (from_adj_nat_l (Adjunction:=A')).
  apply (from_adj_respects (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality τ _ _ (fmap[F] f)).
  rewrite <- comp_assoc.
  rewrite (conj_unit_nat f).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  symmetry.
  now apply conj_mate_inv_obligation_1.
Qed.

Lemma conj_mate_respects (σ σ' : F' ⟹ F) :
  σ ≈ σ' → conj_mate σ ≈ conj_mate σ'.
Proof. intros Hs a; simpl; now rewrite (Hs (U a)). Qed.

Lemma conj_mate_inv_respects (τ τ' : U ⟹ U') :
  τ ≈ τ' → conj_mate_inv τ ≈ conj_mate_inv τ'.
Proof. intros Ht x; simpl; now rewrite (Ht (F x)). Qed.

Lemma conj_mate_pasting (σ : F' ⟹ F) (a : C) :
  conj_mate σ a ≈ fmap[U'] ε ∘ (fmap[U'] (σ (U a)) ∘ η²).
Proof.
  simpl.
  rewrite (to_adj_nat_r (Adjunction:=A')).
  now rewrite (to_adj_unit (H:=A')).
Qed.

Lemma conj_mate_inv_pasting (τ : U ⟹ U') (x : D) :
  conj_mate_inv τ x ≈ ε² ∘ (fmap[F'] (τ (F x)) ∘ fmap[F'] η).
Proof.
  simpl.
  rewrite (from_adj_counit (H:=A')).
  now rewrite fmap_comp.
Qed.

(* ---- existence, uniqueness, the bijection ---- *)

Theorem conjugate_conj_mate (σ : F' ⟹ F) : Conjugate σ (conj_mate σ).
Proof.
  apply mate_to_conjugate.
  intros a; simpl.
  now rewrite <- (to_adj_nat_r (Adjunction:=A')).
Qed.

Theorem conjugate_conj_mate_inv (τ : U ⟹ U') : Conjugate (conj_mate_inv τ) τ.
Proof.
  apply unit_to_conjugate.
  intros x; simpl.
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Theorem conj_mate_uniq (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → τ ≈ conj_mate σ.
Proof.
  intros H a; simpl.
  rewrite (to_adj_nat_r (Adjunction:=A')).
  now apply conjugate_to_mate.
Qed.

Theorem conj_mate_inv_uniq (σ : F' ⟹ F) (τ : U ⟹ U') :
  Conjugate σ τ → σ ≈ conj_mate_inv τ.
Proof.
  intros H x; simpl.
  rewrite (from_adj_counit (H:=A')).
  now apply (unit_to_mate_inv σ τ), (conjugate_to_unit σ τ).
Qed.

Theorem conjugate_unique_right (σ : F' ⟹ F) : ∃! τ : U ⟹ U', Conjugate σ τ.
Proof.
  unshelve refine {| unique_obj := conj_mate σ |}.
  - apply conjugate_conj_mate.
  - intros τ H; symmetry; now apply conj_mate_uniq.
Qed.

Theorem conjugate_unique_left (τ : U ⟹ U') : ∃! σ : F' ⟹ F, Conjugate σ τ.
Proof.
  unshelve refine {| unique_obj := conj_mate_inv τ |}.
  - apply conjugate_conj_mate_inv.
  - intros σ H; symmetry; now apply (conj_mate_inv_uniq σ τ).
Qed.

Corollary conj_mate_inv_mate (σ : F' ⟹ F) : conj_mate_inv (conj_mate σ) ≈ σ.
Proof. symmetry; apply conj_mate_inv_uniq, conjugate_conj_mate. Qed.

Corollary conj_mate_mate_inv (τ : U ⟹ U') : conj_mate (conj_mate_inv τ) ≈ τ.
Proof. symmetry; apply conj_mate_uniq, conjugate_conj_mate_inv. Qed.

Definition conj_dom : SetoidObject := {| carrier := F' ⟹ F |}.
Definition conj_cod : SetoidObject := {| carrier := U  ⟹ U' |}.

#[local] Obligation Tactic := idtac.

Program Definition conjugate_bijection : @Isomorphism Sets conj_dom conj_cod := {|
  to   := {| morphism := conj_mate |};
  from := {| morphism := conj_mate_inv |}
|}.
Next Obligation. exact conj_mate_respects. Qed.
Next Obligation. exact conj_mate_inv_respects. Qed.
Next Obligation. exact conj_mate_mate_inv. Qed.
Next Obligation. exact conj_mate_inv_mate. Qed.

End Conjugate.

(* ---- identity and vertical composition ---- *)

Section ConjugateCompose.

Context {C D : Category}.
Context {F1 : D ⟶ C} {U1 : C ⟶ D}.
Context {F2 : D ⟶ C} {U2 : C ⟶ D}.
Context {F3 : D ⟶ C} {U3 : C ⟶ D}.
Context (A1 : F1 ⊣ U1) (A2 : F2 ⊣ U2) (A3 : F3 ⊣ U3).

Theorem conjugate_id : Conjugate A1 A1 nat_id nat_id.
Proof.
  intros x a k; simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Theorem conjugate_compose (σ : F2 ⟹ F1) (τ : U1 ⟹ U2)
        (σ' : F3 ⟹ F2) (τ' : U2 ⟹ U3) :
  Conjugate A1 A2 σ τ → Conjugate A2 A3 σ' τ' →
  Conjugate A1 A3 (σ ∙ σ') (τ' ∙ τ).
Proof.
  intros H1 H2 x a k; simpl.
  rewrite comp_assoc.
  rewrite (H2 x a (k ∘ σ x)).
  rewrite (H1 x a k).
  now rewrite comp_assoc.
Qed.

Corollary conj_mate_id : conj_mate A1 A1 nat_id ≈ nat_id.
Proof. symmetry; apply conj_mate_uniq, conjugate_id. Qed.

Corollary conj_mate_compose (σ : F2 ⟹ F1) (σ' : F3 ⟹ F2) :
  conj_mate A1 A3 (σ ∙ σ')
    ≈ conj_mate A2 A3 σ' ∙ conj_mate A1 A2 σ.
Proof.
  symmetry.
  apply conj_mate_uniq.
  apply (conjugate_compose σ (conj_mate A1 A2 σ) σ' (conj_mate A2 A3 σ')).
  - apply conjugate_conj_mate.
  - apply conjugate_conj_mate.
Qed.

End ConjugateCompose.

(* ---- Riehl 4.3(iv): invertibility transfers, both directions ---- *)

Section ConjugateIso.

Context {C D : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A  : F  ⊣ U).
Context (A' : F' ⊣ U').

Lemma conjugate_tau_monic (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hσ : ∀ x, IsIsomorphism (σ x))
      (x : D) (a : C) (g1 g2 : x ~> U a) :
  τ a ∘ g1 ≈ τ a ∘ g2 → g1 ≈ g2.
Proof.
  intro Heq.
  assert (Hs : from adj[A] g1 ∘ σ x ≈ from adj[A] g2 ∘ σ x).
  { rewrite <- (fst (conjugate_iff_from A A' σ τ) Hc x a g1).
    rewrite <- (fst (conjugate_iff_from A A' σ τ) Hc x a g2).
    apply proper_morphism.
    exact Heq. }
  assert (Hf : from adj[A] g1 ≈ from adj[A] g2).
  { rewrite <- (id_right (from adj[A] g1)).
    rewrite <- (is_right_inverse (IsIsomorphism := Hσ x)).
    rewrite comp_assoc.
    rewrite Hs.
    rewrite <- comp_assoc.
    rewrite is_right_inverse.
    now rewrite id_right. }
  transitivity (to adj[A] (from adj[A] g1)).
  - symmetry; apply from_adj_comp_law.
  - apply (fst (adj_univ (H:=A) (from adj[A] g1) g2)).
    exact Hf.
Qed.

Definition conj_tau_inv (σ : F' ⟹ F)
    (Hσ : ∀ x, IsIsomorphism (σ x)) (a : C) : U' a ~> U a :=
  to adj[A] (from adj[A'] (id[U' a])
               ∘ two_sided_inverse (IsIsomorphism := Hσ (U' a))).

Lemma conj_tau_inv_right (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hσ : ∀ x, IsIsomorphism (σ x)) (a : C) :
  τ a ∘ conj_tau_inv σ Hσ a ≈ id[U' a].
Proof.
  unfold conj_tau_inv.
  transitivity (to adj[A'] (from adj[A'] (id[U' a]))).
  - rewrite <- Hc.
    apply proper_morphism.
    rewrite <- comp_assoc.
    rewrite is_left_inverse.
    now rewrite id_right.
  - apply from_adj_comp_law.
Qed.

Lemma conj_tau_inv_left (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hσ : ∀ x, IsIsomorphism (σ x)) (a : C) :
  conj_tau_inv σ Hσ a ∘ τ a ≈ id[U a].
Proof.
  apply (conjugate_tau_monic σ τ Hc Hσ (U a) a).
  rewrite comp_assoc.
  rewrite (conj_tau_inv_right σ τ Hc Hσ).
  now rewrite id_left, id_right.
Qed.

Definition conjugate_tau_iso (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
    (Hσ : ∀ x, IsIsomorphism (σ x)) (a : C) : IsIsomorphism (τ a) :=
  {| two_sided_inverse := conj_tau_inv σ Hσ a;
     is_right_inverse  := conj_tau_inv_right σ τ Hc Hσ a;
     is_left_inverse   := conj_tau_inv_left σ τ Hc Hσ a |}.

Lemma conjugate_sigma_epic (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hτ : ∀ a, IsIsomorphism (τ a))
      (x : D) (a : C) (k1 k2 : F x ~> a) :
  k1 ∘ σ x ≈ k2 ∘ σ x → k1 ≈ k2.
Proof.
  intro Heq.
  assert (Hq : τ a ∘ to adj[A] k1 ≈ τ a ∘ to adj[A] k2).
  { rewrite <- (Hc x a k1).
    rewrite <- (Hc x a k2).
    apply proper_morphism.
    exact Heq. }
  assert (Ht : to adj[A] k1 ≈ to adj[A] k2).
  { rewrite <- (id_left (to adj[A] k1)).
    rewrite <- (is_left_inverse (IsIsomorphism := Hτ a)).
    rewrite <- comp_assoc.
    rewrite Hq.
    rewrite comp_assoc.
    rewrite is_left_inverse.
    now rewrite id_left. }
  transitivity (from adj[A] (to adj[A] k2)).
  - apply (snd (adj_univ (H:=A) k1 (to adj[A] k2))).
    exact Ht.
  - apply to_adj_comp_law.
Qed.

Definition conj_sigma_inv (τ : U ⟹ U')
    (Hτ : ∀ a, IsIsomorphism (τ a)) (x : D) : F x ~> F' x :=
  from adj[A] (two_sided_inverse (IsIsomorphism := Hτ (F' x))
                 ∘ to adj[A'] (id[F' x])).

Lemma conj_sigma_inv_left (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hτ : ∀ a, IsIsomorphism (τ a)) (x : D) :
  conj_sigma_inv τ Hτ x ∘ σ x ≈ id[F' x].
Proof.
  unfold conj_sigma_inv.
  transitivity (from adj[A'] (to adj[A'] (id[F' x]))).
  - rewrite <- (fst (conjugate_iff_from A A' σ τ) Hc).
    apply proper_morphism.
    rewrite comp_assoc.
    rewrite is_right_inverse.
    now rewrite id_left.
  - apply to_adj_comp_law.
Qed.

Lemma conj_sigma_inv_right (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
      (Hτ : ∀ a, IsIsomorphism (τ a)) (x : D) :
  σ x ∘ conj_sigma_inv τ Hτ x ≈ id[F x].
Proof.
  apply (conjugate_sigma_epic σ τ Hc Hτ x (F x)).
  rewrite <- comp_assoc.
  rewrite (conj_sigma_inv_left σ τ Hc Hτ).
  now rewrite id_left, id_right.
Qed.

Definition conjugate_sigma_iso (σ : F' ⟹ F) (τ : U ⟹ U') (Hc : Conjugate A A' σ τ)
    (Hτ : ∀ a, IsIsomorphism (τ a)) (x : D) : IsIsomorphism (σ x) :=
  {| two_sided_inverse := conj_sigma_inv τ Hτ x;
     is_right_inverse  := conj_sigma_inv_right σ τ Hc Hτ x;
     is_left_inverse   := conj_sigma_inv_left σ τ Hc Hτ x |}.

Theorem conjugate_invertible_iff (σ : F' ⟹ F) (τ : U ⟹ U')
        (Hc : Conjugate A A' σ τ) :
  (∀ x, IsIsomorphism (σ x)) ↔ (∀ a, IsIsomorphism (τ a)).
Proof.
  split; intro H.
  - exact (conjugate_tau_iso σ τ Hc H).
  - exact (conjugate_sigma_iso σ τ Hc H).
Qed.

End ConjugateIso.
