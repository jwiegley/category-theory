Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Theory.Adjunction.

Generalizable All Variables.

(** Adjunctions and mates in the bicategory `Cat` *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/mate

   `Instance/Cat/Bicategory.v` exhibits `Cat` as a bicategory: its 0-cells are
   categories, its hom-category `bicat C D` is *definitionally* the functor
   category `[C, D]`, horizontal composition `∘∘∘` is functor composition `◯`
   (extended to natural transformations by the Godement composite), `bi1id` is
   the identity functor, and the unitors/associator are the coherence natural
   isomorphisms `nat_ρ`/`nat_λ`/`nat_α` of `Instance/Fun.v`.

   This file is the payoff of the bicategory-mates development: it identifies the
   abstract 2-cell calculus of `Theory/Bicategory/{Adjunction,Mates}.v`,
   specialised to `Cat`, with the ordinary category-theoretic notions, so that
   the general constructions become usable by ordinary-CT files.

   1. AN INTERNAL ADJUNCTION IN `Cat` IS AN ORDINARY ADJUNCTION.  Because
      `∘∘∘ = ◯` and `bi1id = Id`, a `BicatAdjunction (B:=Cat_Bicategory) F U`
      carries a unit `adj_unit : Id ⟹ U ◯ F` and a counit
      `adj_counit : F ◯ U ⟹ Id` that are literally natural transformations, and
      its two bicategorical triangle identities — conjugated by the `Cat`
      unitors `nat_λ`/`nat_ρ` and the associator `nat_α`, whose components are
      all `fmap id` — collapse COMPONENTWISE to exactly the two zig-zag
      identities of the unit/counit presentation `F ∹ U`
      (`Adjunction/Natural/Transformation.v`).  Hence
      `Cat_BicatAdjunction_iff : BicatAdjunction F U ↔ (F ∹ U)`, and, composing
      with the `F ∹ U ↔ F ⊣ U` bridge of
      `Adjunction/Natural/Transformation/Universal.v`, internal adjunctions in
      `Cat` coincide with hom-set adjunctions `F ⊣ U`
      (`Cat_BicatAdjunction_Adjunction_iff`).

   2. MATES IN `Cat` UNFOLD TO THE TRANSPOSES.  The precomposition
      hom-adjunction `precomp_to` of `Theory/Bicategory/Mates.v`, specialised to
      `Cat`, IS the adjunction transpose `⌊−⌋`: componentwise
      `(precomp_to A σ) t ≈ fmap[U] (σ t) ∘ η (c t) = ⌊ σ t ⌋`.  The
      postcomposition hom-adjunction `postcomp_to` is the counit whiskering
      `(postcomp_to A γ) t ≈ fmap[e] (ε t) ∘ γ (U t)`.  Threading these through
      the definition `mate σ = postcomp (α⁻¹ ∘ precomp σ)` gives the classical
      mate formula componentwise (`Cat_mate_unfold`):

        (mate σ) Z ≈ fmap[U'] (fmap[b] (ε Z)) ∘ ⌊ σ (U Z) ⌋
                   = fmap[U'] (fmap[b] (ε Z))
                       ∘ fmap[U'] (σ (U Z)) ∘ η' (a (U Z)),

      where `η'` is the unit of `F' ⊣ U'` and `ε` the counit of `F ⊣ U`.

   The engine behind every proof here is the "standing trap" made harmless: in
   `Cat` the identity 2-cell `bi2id`, the unitor and associator components are
   all `fmap[_] id`, so after `simpl` a single `rewrite !fmap_id` followed by
   `id_left`/`id_right` clears every coherence factor, leaving precisely the
   ordinary-CT expression. *)

(* ------------------------------------------------------------------ *)
(* 1. Internal adjunctions in `Cat` coincide with `F ∹ U` and `F ⊣ U`. *)
(* ------------------------------------------------------------------ *)

Section CatAdjunction.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context {U : D ⟶ C}.

(* Pristine obligations: the two structural fields we supply (`unit`/`counit`
   and `adj_unit`/`adj_counit`) are complete natural transformations, so the
   only obligations are the triangle/zig-zag laws, which we discharge by hand
   through the componentwise `fmap id` collapse. *)
#[local] Obligation Tactic := idtac.

(* Forward: an internal adjunction supplies the unit/counit data directly, and
   its bicategorical triangle identities give the two zig-zag identities. *)
Program Definition Cat_BicatAdjunction_to_Transform
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ∹ U := {|
  Transformation.unit   := adj_unit   (B:=Cat_Bicategory) F U;
  Transformation.counit := adj_counit (B:=Cat_Bicategory) F U
|}.
Next Obligation.
  (* counit_fmap_unit: εF ∘ Fη = 1, read off the left bicat triangle at X. *)
  intros H X.
  pose proof (adj_triangle_left (B:=Cat_Bicategory) F U X) as TLX.
  simpl in TLX.
  rewrite !fmap_id in TLX.
  rewrite ?id_left, ?id_right in TLX.
  exact TLX.
Qed.
Next Obligation.
  (* fmap_counit_unit: Uε ∘ ηU = 1, read off the right bicat triangle at X. *)
  intros H X.
  pose proof (adj_triangle_right (B:=Cat_Bicategory) F U X) as TRX.
  simpl in TRX.
  rewrite !fmap_id in TRX.
  rewrite ?id_left, ?id_right in TRX.
  exact TRX.
Qed.

(* Backward: the unit/counit data assembles into an internal adjunction, its two
   bicategorical triangle identities holding componentwise by the same collapse,
   where each side reduces to a zig-zag identity of the transform. *)
Program Definition Cat_Transform_to_BicatAdjunction
  (A : F ∹ U) : BicatAdjunction (B:=Cat_Bicategory) F U := {|
  adj_unit   := @Category.Adjunction.Natural.Transformation.unit   _ _ _ _ A;
  adj_counit := @Category.Adjunction.Natural.Transformation.counit _ _ _ _ A
|}.
Next Obligation.
  (* adj_triangle_left, componentwise, is εF ∘ Fη = 1. *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.counit_fmap_unit _ _ _ _ A X).
Qed.
Next Obligation.
  (* adj_triangle_right, componentwise, is Uε ∘ ηU = 1. *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.fmap_counit_unit _ _ _ _ A X).
Qed.

(* Internal adjunctions in `Cat` are exactly unit/counit adjunctions `F ∹ U`.
   (Type-valued `↔`, i.e. `iffT`; `Print Assumptions` closed on both legs.)
   Both directions transport the unit/counit data verbatim — `adj_unit ↔ unit`,
   `adj_counit ↔ counit` — so this is the identity correspondence on that data
   (only the triangle-law witnesses are re-derived); record-level mutual
   inverseness is not separately asserted and is not needed downstream. *)
Theorem Cat_BicatAdjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ∹ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_to_Transform.
  - exact Cat_Transform_to_BicatAdjunction.
Qed.

(* Composing with the `F ∹ U ↔ F ⊣ U` bridge (Universal.v): an internal
   adjunction in `Cat` yields a hom-set adjunction, and conversely. *)
Definition Cat_BicatAdjunction_Adjunction
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ⊣ U :=
  Adjunction_from_Transform (Cat_BicatAdjunction_to_Transform H).

Definition Cat_Adjunction_BicatAdjunction
  (A : F ⊣ U) : BicatAdjunction (B:=Cat_Bicategory) F U :=
  Cat_Transform_to_BicatAdjunction (Adjunction_to_Transform (A:=A)).

Theorem Cat_BicatAdjunction_Adjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ⊣ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_Adjunction.
  - exact Cat_Adjunction_BicatAdjunction.
Qed.

End CatAdjunction.

(* ------------------------------------------------------------------ *)
(* 2. The two hom-adjunctions in `Cat` are the transpose and the       *)
(*    counit whiskering.                                                *)
(* ------------------------------------------------------------------ *)

Section CatHomAdjunction.

Context {vx vy : Category}.
Context {F : vx ⟶ vy} {U : vy ⟶ vx}.
Context (A : BicatAdjunction (B:=Cat_Bicategory) F U).

(* Precomposition transpose `precomp_to A : (F ◯ c ⟹ d) → (c ⟹ U ◯ d)`, read
   componentwise, is the unit-transpose `⌊−⌋` of the induced adjunction: the
   unitor/associator components of `preΘ` collapse to identities. *)
Lemma Cat_precomp_to_component {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ fmap[U] (σ t) ∘ adj_unit (B:=Cat_Bicategory) F U (fobj[c] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(* The same, phrased through the hom-set transpose `⌊−⌋ = to adj[-]` of the
   induced adjunction: `precomp_to` at `Cat` IS `⌊−⌋` componentwise.  (The two
   sides are in fact definitionally equal — `Adjunction_from_Transform` sends
   `g` to `fmap[U] g ∘ η` — so `reflexivity` closes it after rewriting.) *)
Lemma Cat_precomp_to_transpose {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ to adj[Cat_BicatAdjunction_Adjunction A] (σ t).
Proof.
  rewrite Cat_precomp_to_component.
  reflexivity.
Qed.

(* Postcomposition transpose `postcomp_to A : (c ⟹ e ◯ F) → (c ◯ U ⟹ e)`, read
   componentwise, is the counit `ε` whiskered by `e`: the unitor/associator
   components of `postΛ` collapse to identities. *)
Lemma Cat_postcomp_to_component {w0 : Category}
  {c : vx ⟶ w0} {e : vy ⟶ w0} (γ : c ⟹ e ◯ F) (t : vy) :
  transform[postcomp_to A γ] t
    ≈ fmap[e] (adj_counit (B:=Cat_Bicategory) F U t) ∘ γ (fobj[U] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

End CatHomAdjunction.

(* ------------------------------------------------------------------ *)
(* 3. Mates in `Cat` unfold to the transposes (the payoff).            *)
(* ------------------------------------------------------------------ *)

Section CatMates.

Context {x y x' y' : Category}.
Context {F  : x  ⟶ y }  {U  : y  ⟶ x }  (Af  : BicatAdjunction (B:=Cat_Bicategory) F  U ).
Context {F' : x' ⟶ y'}  {U' : y' ⟶ x'}  (Af' : BicatAdjunction (B:=Cat_Bicategory) F' U').
Context {a : x ⟶ x'} {b : y ⟶ y'}.
Context (σ : F' ◯ a ⟹ b ◯ F).

(* Raw unfolding of the mate: the classical pasting formula, in terms of the
   unit `η'` of `F' ⊣ U'`, the counit `ε` of `F ⊣ U`, `fmap`, and `σ` alone.
   Every coherence isomorphism (unitors, associators) contributes only a
   `fmap id`, cleared by the collapse; `α⁻¹ ∘ α = id` never even appears because
   the associator components are themselves identities in `Cat`. *)
Theorem Cat_mate_unfold_raw (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ (fmap[U'] (σ (fobj[U] Z))
             ∘ adj_unit (B:=Cat_Bicategory) F' U' (fobj[a] (fobj[U] Z))).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(* The headline: the mate unfolds to the hom-set transpose `⌊−⌋` of `F' ⊣ U'`
   post-whiskered by the counit `ε` of `F ⊣ U`.  This is the form that makes the
   bicategorical mate usable from ordinary-CT files: `⌊ σ (U Z) ⌋` is the
   adjunction transpose of the component of `σ`. *)
Theorem Cat_mate_unfold (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ to adj[Cat_BicatAdjunction_Adjunction Af'] (σ (fobj[U] Z)).
Proof.
  rewrite Cat_mate_unfold_raw.
  reflexivity.
Qed.

End CatMates.
