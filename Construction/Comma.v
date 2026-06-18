Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Comma.

Context {A B C : Category}.

Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

(** The comma category (S ↓ T) of two functors with common codomain. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Given functors S : A ⟶ C and T : B ⟶ C, the comma category S ↓ T has as
   objects the triples (a, b, h) of objects a : A and b : B together with a
   morphism h : S a ~> T b in C; here a triple is encoded as the dependent
   pair (∃ p : A ∏ B, S (fst p) ~> T (snd p)), so `1 x is the pair (a, b) and
   `2 x is the mediating morphism h. A morphism (a, b, h) ~> (a', b', h') is a
   pair of morphisms (f : a ~> a' in A, g : b ~> b' in B) making the square

       S a  --h-->  T b
        |            |
      S f           T g           commute, i.e.  h' ∘ S f ≈ T g ∘ h.
        v            v
       S a' --h'--> T b'

   Identity is (id, id) and composition is componentwise, (f, g) ∘ (f', g') :=
   (f ∘ f', g ∘ g'); both laws hold because they hold in A and B. Equivalence
   of morphisms is the componentwise conjunction of ≈ in A and ≈ in B (the
   commuting-square proof component is irrelevant to equality).

   The construction is due to Lawvere (1963), who used a comma punctuation mark
   for it; the name persists even though the modern notation is the arrow ↓.

   Special cases: taking S = T = Id[C] gives the arrow category C^→, whose
   objects are the morphisms of C and whose morphisms are commuting squares;
   taking S = Id[C] and T = Δ(c) the constant functor at c : C gives the slice
   C/c (see Construction/Slice.v, where C ̸ c ≅ (Id ↓ =(c)) is proven); dually
   S = Δ(c), T = Id[C] gives the coslice c/C. The projection functors below,
   comma_proj1 : S ↓ T ⟶ A and comma_proj2 : S ↓ T ⟶ B, recover a and b, and
   comma_proj_nat is the natural transformation S ◯ comma_proj1 ⟹ T ◯
   comma_proj2 whose component at (a, b, h) is h. Comma categories characterize
   adjunctions and universal arrows: a universal arrow from S to T is an
   initial object of the appropriate comma category. *)

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma : Category := {|
  (* objects: triples (a, b, h : S a ~> T b) *)
  obj     := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p);
  (* morphisms: pairs (f, g) with the commuting square h' ∘ S f ≈ T g ∘ h *)
  hom     := fun x y =>
    ∃ f : (fst (`1 x) ~{A}~> fst (`1 y)) * (snd (`1 x) ~{B}~> snd (`1 y)),
      `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x;
  (* equivalence: componentwise ≈ in A and B (square proof is irrelevant) *)
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);    (* identity (id_a, id_b) *)
  (* composition is componentwise (f ∘ f', g ∘ g') *)
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros.
  simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ?; simpl.
  intros [[]] [[]]; simpl in *.
  rewrite !fmap_comp.
  rewrite comp_assoc.
  rewrites.
  rewrite <- !comp_assoc.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation.
  intros; simpl.
  split; now rewrite id_left.
Qed.
Next Obligation.
  intros. simpl.
  split; now rewrite id_right.
Qed.
Next Obligation.
  intros.
  simpl.
  split; apply comp_assoc.
Qed.
Next Obligation.
  intros. simpl.
  split; apply comp_assoc_sym.
Qed.

Program Instance comma_proj  : Comma ⟶ A ∏ B := {|
  fobj := fun x => ``x;
  fmap := fun _ _ f => ``f
|}.
Next Obligation.
  intros ? ? ? ? [e0 e1].
  now split.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj1 : Comma ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj2 : Comma ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

#[local] Obligation Tactic := cat_simpl.

Program Instance comma_proj_nat : S ◯ comma_proj1 ⟹ T ◯ comma_proj2.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_mor_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y → `1 x ≅[A ∏ B] `1 y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Defined.

Theorem comma_proj_com_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  ∀ iso : x ≅ y,
    `2 x ≈ fmap[T] (snd `1 (from iso)) ∘ `2 y ∘ fmap[S] (fst `1 (to iso)).
Proof.
  intros.
  pose proof (iso_from_to iso); simpl in X.
  destruct (from iso), x0; simpl in *.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst X).
  cat.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(* The "cocomma" defined here is the comma category formed in the opposite
   categories, @Comma (B^op) (A^op) (C^op) (T^op) (S^op). Since the comma of
   opposite functors is the opposite of the comma, this is (S ↓ T)^op up to
   isomorphism: it dualizes S ↓ T by reversing every arrow. Note this is the
   pointwise/op dual and is NOT the cocomma *object* of nLab (the colimit-side
   dual, a.k.a. the collage), which is a genuinely different construction. *)
Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
