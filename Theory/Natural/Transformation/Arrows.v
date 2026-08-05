Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The arrows-only presentation of natural transformations *)

(* nLab: https://ncatlab.org/nlab/show/natural+transformation
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer 1998, §I.4 (printed p. 19), exercise 5

   A natural transformation τ : S ⟹ T between functors S T : C ⟶ D is
   ordinarily a family indexed by the OBJECTS of C — one component
   τ_c : S c ~> T c for each c — subject to one naturality square per arrow
   (Theory/Natural/Transformation.v).  Mac Lane's exercise gives the
   object-free reading of the same data: index instead by the ARROWS of C.
   To each f : c ~> c' assign a single morphism τ f : S c ~> T c', subject
   to the chain

       fmap[T] g ∘ τ f  ≈  τ (g ∘ f)  ≈  τ g ∘ fmap[S] f

   for every composable pair g, f.  [ArrowTransform] below is that record,
   its two equations being the fields [τ_arr_left] and [τ_arr_right].  The
   correspondence with [Transform] is [Transform_to_Arrows] and
   [Arrows_to_Transform]; they are mutually inverse up to ≈
   ([Transform_to_Arrows_to_Transform], [Arrows_to_Transform_to_Arrows]),
   each respects the relevant setoid ([Transform_to_Arrows_respects],
   [Arrows_to_Transform_respects]), and the pair is packaged as an
   isomorphism of setoids in Sets ([Transform_Arrows_iso]). *)

(* Where the naturality square went

   Given τ : S ⟹ T there are two ways to turn f : c ~> c' into a morphism
   S c ~> T c': travel by S and then transform, τ_{c'} ∘ fmap[S] f, or
   transform and then travel by T, fmap[T] f ∘ τ_c.  The naturality square
   says precisely that the two agree, so the pair collapses into one
   operation on arrows — and that operation is the arrow family.  This is
   the point of the exercise, and it is recorded here as
   [Transform_to_Arrows_alt]: the family built from τ by the first formula
   satisfies the second, the proof being [naturality] and nothing else.
   In the reverse direction the components are read off the identities,
   τ_c := τ (id[c]), and the naturality square is recovered as
   [τ_arr_diagonal_naturality].

   Object-free presentations run through the library one level further
   down.  Theory/Metacategory/ArrowsOnly.v carries Mac Lane's arrows-only
   axiomatization of a CATEGORY (CWM §I.1): there is no sort of objects at
   all, an object being recovered as an identity arrow, and
   [Category_from_Metacategory] builds a [Category] whose objects are the
   identity arrows [{i | is_identity i}] of a [Metacategory].  The move
   made here is the same move one dimension up — the components of a
   transformation are its values at the identity arrows — and the
   machinery is entirely separate: that file's partial composition on
   [N]-indexed arrows shares no constant with this one.

   A third reading of the same fusion is the interval category.  As
   Instance/Two.v records, a natural transformation between two functors
   C ⟶ D is a functor C ∏ 2 ⟶ D, a directed homotopy; the arrow family is
   what such a functor does to the arrows of C ∏ 2 that cross the
   interval, namely (f, TwoXY) ↦ τ f.  The walking arrow 2 reappears below
   as the base of the independence countermodels. *)

(* Two equations, both of which carry content

   The tree's [Transform] carries [naturality] together with
   [naturality_sym], but those are one equation in two orientations, kept
   apart so that duality holds definitionally; the comment above
   [Transform] says so, and [Build_Transform'] derives the second from the
   first by [symmetry].  The two splice laws here are not of that kind.
   Neither implies the other, and section [Independence] below proves it
   with two concrete families over the walking arrow 2 (Instance/Two.v)
   and the walking parallel pair (Instance/Parallel.v), whose two arrows
   ParX ~> ParY are non-equivalent: [dom_family], which reads only the
   domain of its argument, satisfies the left law ([dom_family_left]) and
   refutes the right one ([dom_family_not_right]); [cod_family], which
   reads only the codomain, does the reverse.  Both are respectful
   ([dom_family_respects], [cod_family_respects]), so the independence is
   not an artifact of dropping respectfulness.

   What the two laws jointly buy is respectfulness itself.  A family that
   respects ≈ in its argument is what the tree's setoid discipline
   normally has to require as a field, but here it is a consequence:
   [τ_arr_from_left] proves τ f ≈ fmap[T] f ∘ τ (id[c]) by rewriting once
   with each law — the left law supplies fmap[T] f ∘ τ (id) ≈ τ (f ∘ id),
   the right law supplies τ (f ∘ id) ≈ τ f ∘ fmap[S] (id) — and the
   right-hand side depends on f only through fmap[T] f, which respects ≈
   already.  [τ_arr_respects] is that argument, and the record therefore
   has no [Proper] field.  Each law alone reaches only one half of the
   detour: the equations constrain the family at terms literally of the
   form g ∘ f, so passing between τ f and τ (f ∘ id) is itself an appeal
   to a law, and it is the other one.

   The dual reading [τ_arr_from_right], τ f ≈ τ (id[c']) ∘ fmap[S] f, is
   available on the same footing, and the equality of the two right-hand
   sides is the naturality square of the diagonal family c ↦ τ (id[c]).
   That is the whole content of the reverse direction of the
   correspondence, and it is what [Arrows_to_Transform] is built from. *)

Section ArrowTransform.

Context {C : Category}.
Context {D : Category}.
Context {S : C ⟶ D}.
Context {T : C ⟶ D}.

(* An arrow-indexed family: one morphism S c ~> T c' for each f : c ~> c',
   with the two splice laws.  [τ_arr_left] absorbs a post-composition into
   the family through T, [τ_arr_right] absorbs a pre-composition through
   S; together they are Mac Lane's displayed chain, and [τ_arr_splice]
   below states that chain as the single equation it is usually written
   as. *)

Record ArrowTransform := {
  τ_arr {c c' : C} (f : c ~> c') : S c ~> T c';

  (* post-composition splices in through T *)
  τ_arr_left {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    fmap[T] g ∘ τ_arr f ≈ τ_arr (g ∘ f);

  (* pre-composition splices in through S *)
  τ_arr_right {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    τ_arr (g ∘ f) ≈ τ_arr g ∘ fmap[S] f
}.

(* The two fields chained, i.e. the exercise's displayed equation with its
   middle term elided. *)

Lemma τ_arr_splice (A : ArrowTransform) {c c' c'' : C}
      (g : c' ~> c'') (f : c ~> c') :
  fmap[T] g ∘ τ_arr A f ≈ τ_arr A g ∘ fmap[S] f.
Proof.
  rewrite τ_arr_left.
  apply τ_arr_right.
Qed.

(* The family is determined by its values at the identities, in two ways.
   Each derivation uses BOTH laws: the detour through the padded term
   f ∘ id[c] is legitimized by one law and removed by the other. *)

Lemma τ_arr_from_left (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ fmap[T] f ∘ τ_arr A (id[c]).
Proof.
  rewrite (τ_arr_left A f (id[c])).       (* fmap[T] f ∘ τ id ≈ τ (f ∘ id) *)
  rewrite (τ_arr_right A f (id[c])).      (* τ (f ∘ id) ≈ τ f ∘ fmap[S] id *)
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Lemma τ_arr_from_right (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- (τ_arr_right A (id[c']) f).  (* τ id ∘ fmap[S] f ≈ τ (id ∘ f) *)
  rewrite <- (τ_arr_left A (id[c']) f).   (* τ (id ∘ f) ≈ fmap[T] id ∘ τ f *)
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* Respectfulness is a consequence of the two laws, not a further field. *)

#[export]
Instance τ_arr_respects (A : ArrowTransform) {c c'} :
  Proper (equiv ==> equiv) (@τ_arr A c c').
Proof.
  intros f f' Hf.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left A f').
  now rewrite Hf.
Qed.

(* The naturality square of the diagonal family c ↦ τ (id[c]), obtained by
   reading the previous two lemmas in opposite directions. *)

Lemma τ_arr_diagonal_naturality (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  fmap[T] f ∘ τ_arr A (id[c]) ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- τ_arr_from_left.
  apply τ_arr_from_right.
Qed.

(* Arrow families form a setoid under pointwise ≈ at every arrow, exactly
   as transformations form one under pointwise ≈ at every object
   ([Transform_Setoid]).  The correspondence below is an equivalence of
   these two setoids, not merely a bijection of their carriers. *)

#[export]
Program Instance ArrowTransform_Setoid : Setoid ArrowTransform := {|
  equiv := fun A B => ∀ (c c' : C) (f : c ~> c'), τ_arr A f ≈ τ_arr B f
|}.
Next Obligation.
  constructor.
  - intros A c c' f.
    reflexivity.
  - intros A B H c c' f.
    symmetry.
    apply H.
  - intros A B E H1 H2 c c' f.
    transitivity (τ_arr B f).
    + apply H1.
    + apply H2.
Qed.

(* From a transformation to its arrow family: transport along S, then
   transform.  Both laws are then instances of naturality and
   functoriality. *)

Program Definition Transform_to_Arrows (N : S ⟹ T) : ArrowTransform := {|
  τ_arr := fun c c' f => transform[N] c' ∘ fmap[S] f
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  now rewrite <- fmap_comp.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

(* The other formula for the same family: transform, then transport along
   T.  That the two agree IS the naturality square of N — the proof is
   [naturality] alone — and it is the observation the exercise turns on. *)

Lemma Transform_to_Arrows_alt (N : S ⟹ T) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows N) f ≈ fmap[T] f ∘ transform[N] c.
Proof.
  simpl.
  symmetry.
  apply naturality.
Qed.

(* From an arrow family back to a transformation: the components are the
   values at the identities, and the naturality square is
   [τ_arr_diagonal_naturality].  [Build_Transform'] supplies the symmetric
   orientation, so nothing further is proved here. *)

Definition Arrows_to_Transform (A : ArrowTransform) : S ⟹ T :=
  Build_Transform' (fun c => τ_arr A (id[c]))
                   (fun c c' f => τ_arr_diagonal_naturality A f).

(* Both composites are the identity up to ≈. *)

Theorem Transform_to_Arrows_to_Transform (N : S ⟹ T) :
  Arrows_to_Transform (Transform_to_Arrows N) ≈ N.
Proof.
  intros c.
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Arrows_to_Transform_to_Arrows (A : ArrowTransform) :
  Transform_to_Arrows (Arrows_to_Transform A) ≈ A.
Proof.
  intros c c' f.
  simpl.
  now rewrite <- τ_arr_from_right.
Qed.

(* Both directions respect the two setoids. *)

#[export]
Instance Transform_to_Arrows_respects :
  Proper (equiv ==> equiv) Transform_to_Arrows.
Proof.
  intros N M H c c' f.
  simpl.
  now rewrite (H c').
Qed.

#[export]
Instance Arrows_to_Transform_respects :
  Proper (equiv ==> equiv) Arrows_to_Transform.
Proof.
  intros A B H c.
  simpl.
  apply H.
Qed.

(* Uniqueness, in the four forms one wants of it.

   [Transform_determined_by_arrows]: a natural transformation is determined
   by its arrow family, so the assignment is injective up to ≈.
   [Arrows_determined_by_transform]: an arrow family is determined by the
   transformation it induces, i.e. by its diagonal.
   [Arrows_unique_transform]: the transformation inducing a given family is
   unique — with [Arrows_to_Transform_to_Arrows] for existence, this is
   Mac Lane's "arises from a unique natural transformation".
   [Transform_unique_arrows]: and the family induced by a transformation is
   unique. *)

Theorem Transform_determined_by_arrows (N M : S ⟹ T) :
  Transform_to_Arrows N ≈ Transform_to_Arrows M → N ≈ M.
Proof.
  intros H c.
  pose proof (H c c (id[c])) as Hc.
  simpl in Hc.
  rewrite !fmap_id in Hc.
  now rewrite !id_right in Hc.
Qed.

Theorem Arrows_determined_by_transform (A B : ArrowTransform) :
  Arrows_to_Transform A ≈ Arrows_to_Transform B → A ≈ B.
Proof.
  intros H c c' f.
  simpl in H.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left B f).
  now rewrite (H c).
Qed.

Theorem Arrows_unique_transform (A : ArrowTransform) (N : S ⟹ T) :
  Transform_to_Arrows N ≈ A → N ≈ Arrows_to_Transform A.
Proof.
  intros H c.
  simpl.
  rewrite <- (H c c (id[c])).
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Transform_unique_arrows (N : S ⟹ T) (A : ArrowTransform) :
  Arrows_to_Transform A ≈ N → A ≈ Transform_to_Arrows N.
Proof.
  intros H c c' f.
  simpl.
  rewrite (τ_arr_from_right A f).
  now rewrite (H c').
Qed.

(* The correspondence as an isomorphism of setoids in Sets, in the manner
   of [classifier_classifies] (Structure/SubobjectClassifier.v): the
   underlying maps are the two directions above, and the two round trips
   are the two theorems above. *)

Theorem Transform_Arrows_iso :
  @Isomorphism Sets {| carrier := S ⟹ T |} {| carrier := ArrowTransform |}.
Proof.
  unshelve econstructor.
  - (* to: a transformation to its arrow family; the setoid-map obligation
       is discharged by [Transform_to_Arrows_respects] *)
    simpl.
    unshelve refine {| morphism := Transform_to_Arrows |}.
  - (* from: an arrow family to the transformation on the identities *)
    simpl.
    unshelve refine {| morphism := Arrows_to_Transform |}.
  - (* to ∘ from ≈ id, pointwise *)
    intros A.
    apply Arrows_to_Transform_to_Arrows.
  - (* from ∘ to ≈ id, pointwise *)
    intros N.
    apply Transform_to_Arrows_to_Transform.
Defined.

End ArrowTransform.

Arguments ArrowTransform {C D} S T.

(* The identity transformation's arrow family is the functorial action of
   the functor itself: a functor is its own arrow family, which is the
   arrows-only counterpart of the identity arrows standing in for the
   objects.  This also witnesses that [ArrowTransform] is inhabited for
   every endo-pair (F, F). *)

Lemma Transform_to_Arrows_nat_id `(F : C ⟶ D) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (@nat_id C D F)) f ≈ fmap[F] f.
Proof.
  simpl.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* Non-triviality in general: distinct transformations have distinct arrow
   families.  This is [Transform_determined_by_arrows] contraposed, and a
   concrete pair of witnesses appears below. *)

Corollary distinct_Transforms_distinct_Arrows {C D : Category}
      {S T : C ⟶ D} (N M : S ⟹ T) :
  ¬ (N ≈ M) → ¬ (Transform_to_Arrows N ≈ Transform_to_Arrows M).
Proof.
  intros H HA.
  apply H.
  now apply Transform_determined_by_arrows.
Qed.

(* The remaining sections need two concrete small categories and the
   constant functors between them; the requires are placed here to keep
   the development above free of them. *)

Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Parallel.

(* The functorial action of a constant functor is an identity; every
   computation in the two sections below reduces through this lemma. *)

Lemma diagonal_fmap {C J : Category} (x : C) {c c' : J} (f : c ~> c') :
  fmap[Δ[J](x)] f ≈ id[x].
Proof. reflexivity. Qed.

(* Parallel (Instance/Parallel.v) has exactly two arrows ParX ~> ParY, and
   they are not equivalent: its hom-setoid compares the boolean tags that
   index the arrows.  The two objects are named again at the type
   [Parallel] so that the ambient category is available to inference in
   every statement below. *)

Definition parX : Parallel := ParX.
Definition parY : Parallel := ParY.

Definition par_one : parX ~> parY := (true; ParOne).
Definition par_two : parX ~> parY := (false; ParTwo).

Lemma par_one_par_two_distinct : ¬ (par_one ≈ par_two).
Proof.
  intros H.
  unfold par_one, par_two in H.
  simpl in H.
  discriminate.
Qed.

(* The two constant functors 2 ⟶ Parallel that carry every example and
   every countermodel below: one sending all of 2 to parX, the other
   sending all of 2 to parY.  Their functorial actions are identities, by
   [diagonal_fmap]. *)

Local Notation ConstX := (Δ[_2](parX)).
Local Notation ConstY := (Δ[_2](parY)).

Section ConcreteArrows.

(* A concrete non-identity example: the constant arrow family at
   h : parX ~> parY, taken between ConstX and ConstY.  Both splice laws
   hold because both functorial actions are identities.  Nothing here is
   an identity transformation — the source and target functors differ —
   and the record is thereby shown non-vacuous over a pair of distinct
   functors as well as over the pairs (F, F) covered by
   [Transform_to_Arrows_nat_id]. *)

Definition const_arrows (h : parX ~> parY) : ArrowTransform ConstX ConstY.
Proof.
  unshelve refine
    (@Build_ArrowTransform _2 Parallel ConstX ConstY (fun c c' f => h) _ _).
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_left.
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_right.
Defined.

(* The correspondence computes on it: the induced transformation has h at
   every component (by conversion alone), and the family recovered from
   that transformation is again the constant family. *)

Lemma const_arrows_transform (h : parX ~> parY) (c : _2) :
  transform[Arrows_to_Transform (const_arrows h)] c ≈ h.
Proof. reflexivity. Qed.

Lemma const_arrows_roundtrip (h : parX ~> parY) {c c' : _2} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (Arrows_to_Transform (const_arrows h))) f ≈ h.
Proof.
  rewrite (Arrows_to_Transform_to_Arrows (const_arrows h) c c' f).
  reflexivity.
Qed.

(* Non-triviality, concretely: the two constant families at the two arrows
   of Parallel are distinct, hence so are the transformations they induce
   — the latter by [Arrows_determined_by_transform], i.e. through the
   round trip rather than by inspection. *)

Lemma const_arrows_distinct :
  ¬ (const_arrows par_one ≈ const_arrows par_two).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  exact (H TwoX TwoY TwoXY).
Qed.

Lemma const_transforms_distinct :
  ¬ (Arrows_to_Transform (const_arrows par_one)
       ≈ Arrows_to_Transform (const_arrows par_two)).
Proof.
  intros H.
  apply const_arrows_distinct.
  now apply Arrows_determined_by_transform.
Qed.

End ConcreteArrows.

Section Independence.

(* The two splice laws are independent: neither follows from the other,
   with or without respectfulness.  Both countermodels live over the same
   pair of constant functors ConstX, ConstY : 2 ⟶ Parallel, where both
   functorial actions are identities, so that the left law reads
   τ f ≈ τ (g ∘ f) and the right law reads τ (g ∘ f) ≈ τ g.  The first
   constrains the family only along the domain of its argument, the second
   only along the codomain, and in the walking arrow 2 the two come apart
   at the non-identity arrow TwoXY : TwoX ~> TwoY. *)

Definition dom_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c with
  | TwoX => par_one
  | TwoY => par_two
  end.

Definition cod_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c' with
  | TwoX => par_one
  | TwoY => par_two
  end.

(* Both families respect ≈, ignoring their argument outright. *)

Lemma dom_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@dom_family c c').
Proof. intros f g Hf; reflexivity. Qed.

Lemma cod_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@cod_family c c').
Proof. intros f g Hf; reflexivity. Qed.

(* Reading the domain satisfies the left law and refutes the right one. *)

Lemma dom_family_left {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  fmap[ConstY] g ∘ dom_family f ≈ dom_family (g ∘ f).
Proof. now rewrite diagonal_fmap, id_left. Qed.

Lemma dom_family_not_right :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       dom_family (g ∘ f) ≈ dom_family g ∘ fmap[ConstX] f).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_right par_two).
  exact (H TwoX TwoY TwoY (@id _2 TwoY) TwoXY).
Qed.

(* Reading the codomain satisfies the right law and refutes the left one. *)

Lemma cod_family_right {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  cod_family (g ∘ f) ≈ cod_family g ∘ fmap[ConstX] f.
Proof. now rewrite diagonal_fmap, id_right. Qed.

Lemma cod_family_not_left :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       fmap[ConstY] g ∘ cod_family f ≈ cod_family (g ∘ f)).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_left par_one).
  exact (H TwoX TwoX TwoY TwoXY (@id _2 TwoX)).
Qed.

End Independence.
