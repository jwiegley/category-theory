Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Two functors between free categories, agreeing on objects *)

(* Book: Fong, Spivak, "An Invitation to Applied Category Theory: Seven
         Sketches in Compositionality", Cambridge University Press, 2019,
         Section 3.3.2, Exercise 3.40, printed p. 92
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, Section I.3 ("Functors"), printed p. 15
   nLab: https://ncatlab.org/nlab/show/free+category

   Exercise 3.40 asks for two functors that agree on objects and differ on
   morphisms, and supplies the cheapest possible witness: from the free
   category on a single arrow to the free category on two parallel arrows,
   send the generator to one parallel arrow or to the other.  The two
   functors have the SAME object function -- here literally [fun n => n],
   the identity -- and different arrow functions.  This is Mac Lane's
   Section I.3 question with the algebra removed; the group-theoretic
   reading is in Instance/Grp/TwoFunctors.v.

   Everything rests on Construction/Free/Quiver.v.  A quiver built by
   [Build_Quiver_Standard_Eq] compares edges by propositional equality, and
   [FreeOnQuiver] makes its morphisms the type-aligned paths of Lib/TList.v
   with [tlist_quiver_equiv] as the hom-setoid; a quiver homomorphism into
   the underlying quiver of a category induces a functor out of the free
   category ([InducedFunctor], which is also the mediating functor in the
   proof of the universal property [UniversalArrowQuiverCat]).  So both
   functors here are induced from a choice of image for the single
   generator.

   WHERE THE DIFFERENCE LIVES.  [fs_singleton_distinct] is the load-bearing
   lemma: the two one-edge paths are inequivalent IN THE HOM-SETOID of the
   target free category.  Unfolding [tlist_quiver_equiv] on two singletons
   leaves an equality of intermediate nodes and an equation between the two
   edges after transport along it; uniqueness of identity proofs on the
   two-element node type (Hedberg, via the stdlib's axiom-free [UIP_dec])
   discharges the first, and the second is then an equality of distinct
   constructors.  So the separation is a statement about the setoid, not
   about the shape of the terms.

   The distinctness is stated in [Functor_StrictEq_Setoid]
   (Theory/Functor.v:508), the hom-setoid of [StrictCat]
   (Instance/StrictCat.v:59).  No claim is made here about the weak setoid
   [Functor_Setoid] (Theory/Functor.v:148) of [Cat] (Instance/Cat.v:145),
   which identifies naturally isomorphic functors; the twisted pair of
   Functor/Twist.v and Instance/Grp/TwoFunctors.v is the one that
   deliberately exhibits a pair separated strictly and identified weakly. *)

(** ** The two quivers *)

(* Two nodes, with decidable equality. *)
Inductive fs_node : Type := fs_dom | fs_cod.

Definition fs_node_eq_dec (x y : fs_node) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  - now left.
  - now right.
  - now right.
  - now left.
Defined.

(* One arrow from [fs_dom] to [fs_cod] ... *)
Inductive fs_one_edge : fs_node → fs_node → Type :=
  | fs_gen : fs_one_edge fs_dom fs_cod.

(* ... and two parallel arrows between the same nodes. *)
Inductive fs_two_edges : fs_node → fs_node → Type :=
  | fs_left  : fs_two_edges fs_dom fs_cod
  | fs_right : fs_two_edges fs_dom fs_cod.

Definition WalkingArrowQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_one_edge.

Definition ParallelPairQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_two_edges.

Definition FreeWalkingArrow : Category := FreeOnQuiver WalkingArrowQuiver.

Definition FreeParallelPair : Category := FreeOnQuiver ParallelPairQuiver.

(** ** The two functors *)

(* The generator goes to the left parallel arrow ... *)
Definition free_pick_left_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_left end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

(* ... or to the right one.  Nothing else changes. *)
Definition free_pick_right_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_right end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

Definition FreePickLeft : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_left_hom.

Definition FreePickRight : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_right_hom.

(* The object functions are equal as FUNCTIONS, not merely pointwise: both
   are the identity function on the two nodes.  (This is an equality of
   object maps, which is what the exercise is about; morphisms are still
   compared with ≈ everywhere below.) *)
Lemma free_two_functors_same_objects :
  fobj[FreePickLeft] = fobj[FreePickRight].
Proof. reflexivity. Qed.

(** ** The generator, and where the two functors send it *)

(* A functor induced from a quiver homomorphism sends a one-edge path to
   the chosen image of that edge: the induction defining [InducedFunctor]
   contributes an identity on the empty tail. *)
Lemma fmap_free_singleton {G : Quiver} {C : Category}
  (F : QuiverHomomorphism G (QuiverOfCat C)) {x y : G} (e : edges x y) :
  fmap[InducedFunctor G F] (tlist_singleton e) ≈ @fedgemap _ _ F x y e.
Proof.
  simpl.
  apply id_left.
Qed.

Example free_pick_left_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen) ≈ tlist_singleton fs_left.
Proof. apply (fmap_free_singleton free_pick_left_hom fs_gen). Qed.

Example free_pick_right_generator :
  fmap[FreePickRight] (tlist_singleton fs_gen) ≈ tlist_singleton fs_right.
Proof. apply (fmap_free_singleton free_pick_right_hom fs_gen). Qed.

(** ** The separation *)

(* The hom-setoid of the target really does separate the two generating
   paths: it is not a setoid that identifies everything. *)
Lemma fs_singleton_distinct :
  @equiv _ (@homset FreeParallelPair fs_dom fs_cod)
    (tlist_singleton fs_left) (tlist_singleton fs_right) → False.
Proof.
  simpl.
  unfold tlist_quiver_equiv, tlist_singleton.
  simpl.
  intros [q Hedge _].
  rewrite (UIP_dec fs_node_eq_dec q eq_refl) in Hedge.
  assert (Hlr : fs_left = fs_right) by exact Hedge.
  discriminate.
Qed.

(* The concrete separating datum: the two arrow maps disagree on the
   generator, in the hom-setoid of the target. *)
Theorem free_two_functors_differ_on_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen)
    ≈ fmap[FreePickRight] (tlist_singleton fs_gen) → False.
Proof.
  intro H.
  apply fs_singleton_distinct.
  rewrite <- free_pick_left_generator.
  rewrite <- free_pick_right_generator.
  exact H.
Qed.

(* Two functors, the same object function, different arrow functions:
   distinct in the strict functor setoid.  The object components of a
   strict equality are loops at the two nodes, which uniqueness of identity
   proofs collapses to [eq_refl]; the arrow condition then says the two
   images of the generator agree in the hom-setoid, and they do not. *)
Theorem free_two_functors_distinct :
  @equiv _ (@Functor_StrictEq_Setoid FreeWalkingArrow FreeParallelPair)
    FreePickLeft FreePickRight → False.
Proof.
  intros [eq_on_obj coherent].
  pose proof (coherent fs_dom fs_cod (tlist_singleton fs_gen)) as Hc.
  rewrite (UIP_dec fs_node_eq_dec (eq_on_obj fs_dom) eq_refl),
          (UIP_dec fs_node_eq_dec (eq_on_obj fs_cod) eq_refl) in Hc.
  (* both transports are along [eq_refl] and vanish *)
  apply free_two_functors_differ_on_generator.
  exact Hc.
Qed.
