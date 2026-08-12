Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Witnesses for [Commutative]: concrete diagrams, and in-tree instances *)

(* Theory/Diagram.v proves [square_commutative_iff] and its triangle
   counterpart parametrically, over an arbitrary category and arbitrary
   morphisms.  This file supplies concrete inhabitants, because a
   universally quantified predicate can be true for two uninteresting
   reasons and both must be ruled out for [Commutative] to have been tested:

   1. VACUITY OF THE SHAPE.  If a quiver has no two distinct parallel paths,
      [Commutative] holds of every diagram over it for lack of anything to
      check.  [SquareQuiver] escapes this: [sq_via_B_neq_via_C]
      (Theory/Diagram.v) proves its two routes from [SqA] to [SqD] are
      DISTINCT morphisms of [FreeOnQuiver SquareQuiver], and
      [tri_via_Y_neq_direct] does the same for [TriangleQuiver].

   2. VACUITY OF THE TARGET.  If the target category is thin (a preorder --
      at most one morphism between any two objects) then all parallel
      composites agree and [Commutative] holds of every diagram into it.  The
      target used here is [Coq] (Instance/Coq.v: objects are types, morphisms
      are functions, [f ≈ g] is [∀ x, f x = g x]), and it is NOT thin: the
      examples below exhibit parallel morphisms that are provably not [≈]
      ([coq_parallel_not_equiv], [coq_sq_legs_differ],
      [coq_sq_sides_differ]).

   So the positive witnesses below are commuting diagrams over a shape that
   has a real parallel pair, into a category that has parallel morphisms it
   distinguishes; and the negative witnesses are diagrams over the SAME
   shapes, into the SAME category, for which [Commutative] is refuted.

   The category [Coq] is used rather than a setoid model because its category
   laws hold with no axioms (Instance/Coq.v, header) and disequality of
   functions here is decided by computation on [bool].

   The final section is of a different kind: it exhibits two of the tree's own
   shape-specific commutativity statements as instances of [Commutative], so
   that the claim in Theory/Diagram.v's header that the predicate generalizes
   them is a theorem here rather than an assertion. *)

(** ** A commuting square in [Coq] *)

(*      unit --(fun _ => true)--> bool
          |                        |
    (fun _ => false)             negb
          |                        |
          v                        v
         bool --------id--------> bool

   Both routes send the unique element of [unit] to [false]. *)

Definition coq_sq_u : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_sq_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_sq_h : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.
Definition coq_sq_k : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_sq_u coq_sq_v coq_sq_h coq_sq_k.

(* The square commutes, hence so does every pair of parallel paths over it. *)
Example coq_square_commutative : Commutative CoqCommutingSquare.
Proof.
  apply square_commutes.
  now intros [].
Qed.

(* The commutation is not an artefact of the two legs coinciding: the top and
   left edges differ, and so do the right and bottom edges. *)
Example coq_sq_legs_differ : (coq_sq_u ≈[Coq] coq_sq_h) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

Example coq_sq_sides_differ : (coq_sq_v ≈[Coq] coq_sq_k) -> False.
Proof.
  intro Heq.
  specialize (Heq true); simpl in Heq.
  discriminate Heq.
Qed.

(** ** A square over the same quiver that does NOT commute *)

(*      unit ----id----> unit
          |                |
         id        (fun _ => true)
          |                |
          v                v
         unit --(fun _ => false)--> bool

   One route lands on [true], the other on [false]. *)

Definition coq_bad_u : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_v : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_bad_h : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_k : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.

Definition CoqNonCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_bad_u coq_bad_v coq_bad_h coq_bad_k.

(* [Coq] is not thin: these two parallel morphisms are not [≈]. *)
Example coq_parallel_not_equiv : (coq_bad_v ≈[Coq] coq_bad_k) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

(* The negative witness: [Commutative] is refuted for this diagram, over the
   very same quiver that carries the commuting one above.  The refutation goes
   through [square_commutes_inv], which instantiates the predicate at the two
   genuinely distinct paths of [SquareQuiver]. *)
Example coq_square_not_commutative : Commutative CoqNonCommutingSquare -> False.
Proof.
  intro Hc.
  pose proof (square_commutes_inv coq_bad_u coq_bad_v coq_bad_h coq_bad_k Hc)
    as Hbad.
  specialize (Hbad tt); simpl in Hbad.
  discriminate Hbad.
Qed.

(** ** The same, for the triangle *)

(*   bool --negb--> bool --negb--> bool   versus   bool --id--> bool  *)

Definition coq_tri_u : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_w : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_w.

Example coq_triangle_commutative : Commutative CoqCommutingTriangle.
Proof.
  apply triangle_commutes.
  now intros [].
Qed.

(* Replacing the direct edge by [negb] breaks it, over the same quiver. *)
Definition CoqNonCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_u.

Example coq_triangle_not_commutative :
  Commutative CoqNonCommutingTriangle -> False.
Proof.
  intro Hc.
  pose proof (triangle_commutes_inv coq_tri_u coq_tri_v coq_tri_u Hc) as Hbad.
  specialize (Hbad true); simpl in Hbad.
  discriminate Hbad.
Qed.

(** ** The tree's shape-specific commutativity statements are instances *)

(* Theory/Diagram.v's header claims that the reusable in-tree statements of
   commutativity each fix one figure, and that [Commutative] generalizes them.
   These four results discharge that claim for two of the three, by exhibiting
   each as a [Commutative] diagram of the corresponding walking shape.  (The
   third, Construction/Sq.v:50's [dsq], is the same square as
   [square_commutative_iff] after permuting its four arguments to [dsq]'s
   [(h, u, v, k)] AND applying [symmetry]: the permutation alone yields
   [v ∘ h ≈ k ∘ u], while [dsq] is stated as [k ∘ u ≈ v ∘ h].  It is not
   restated here, to avoid importing the double-category development.) *)

(* A cone leg triangle: [Structure/Cone.v:30]'s [cone_coherence] is exactly
   the commutativity of the walking triangle on the two legs and the image
   morphism between them.

   Division of labour between the two results below, stated precisely because
   it is easy to misread.  The [_iff] is a SHAPE match: its [ACone] instance is
   used only to name [vertex_map], and the biconditional holds for any three
   morphisms of matching type, so it carries no more content than
   [triangle_commutative_iff] with the arguments instantiated.  The cone-ness is
   used by [cone_leg_commutes], which discharges the right-hand side from
   [cone_coherence].  Together they exhibit [cone_coherence] as an instance;
   neither alone does.  The same split applies to the pullback pair below. *)
Corollary cone_leg_commutative_iff {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y))
    ↔ fmap[F] f ∘ vertex_map x ≈ vertex_map y.
Proof. apply triangle_commutative_iff. Qed.

Corollary cone_leg_commutes {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y)).
Proof. apply triangle_commutes, cone_coherence. Qed.

(* A pullback square: [Theory/Morphisms/Stability.v:55]'s
   [is_pullback_commutes] is exactly the commutativity of the walking square
   on the two projections and the two given morphisms. *)
Corollary pullback_square_commutative_iff {C : Category} {x y z : C}
          (f : x ~> z) (g : y ~> z) {P : C} (p1 : P ~> x) (p2 : P ~> y) :
  Commutative (SquareDiagram p1 f p2 g) ↔ f ∘ p1 ≈ g ∘ p2.
Proof. apply square_commutative_iff. Qed.

Corollary pullback_square_commutes {C : Category} {x y z : C}
          {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
          (Hpb : IsPullback f g P p1 p2) :
  Commutative (SquareDiagram p1 f p2 g).
Proof. apply square_commutes, (is_pullback_commutes Hpb). Qed.


(** ** The walking loop: a diagram that draws a non-identity endomorphism *)

(* Theory/Diagram.v's [loop_commutative_iff] proves that over the walking loop,
   [Commutative] is exactly "the drawn endomorphism is the identity".  That is
   the clause of the predicate driven by the EMPTY path, and it is the one no
   figure-fixing statement can express.  Here it is exercised concretely, in
   both directions, over the same category [Coq].

   [negb] is a non-identity endomorphism of [bool], so the diagram drawing it
   is not [Commutative] -- while the diagram drawing [Datatypes.id] is. *)

Definition CoqLoopNegb : Diagram LoopQuiver Coq :=
  LoopDiagram (negb : (bool : Coq) ~{Coq}~> (bool : Coq)).

Definition CoqLoopId : Diagram LoopQuiver Coq :=
  LoopDiagram (Datatypes.id : (bool : Coq) ~{Coq}~> (bool : Coq)).

(* The negative witness.  Note there is no parallel PAIR of nonempty paths at
   work: what refutes commutativity is the one-edge path against [tnil]. *)
Example coq_loop_negb_not_commutative : Commutative CoqLoopNegb -> False.
Proof.
  intro Hc.
  pose proof (loop_commutes_inv _ Hc true) as H.
  discriminate H.
Qed.

(* The positive witness over the same shape and the same category. *)
Example coq_loop_id_commutative : Commutative CoqLoopId.
Proof.
  apply loop_commutes.
  now intro b.
Qed.
