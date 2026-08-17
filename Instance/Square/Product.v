Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Square.

Require Import Coq.Lists.List.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(** * The walking commutative square as 2 × 2

    Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
          Example 1.6.6, printed p. 41
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          §II.8, Exercise 1, printed p. 52

    Riehl introduces the walking commutative square not by generators
    and relations but as a PRODUCT: the shape 2 × 2, two copies of the
    walking arrow.  That presentation makes the arrow count immediate —
    an arrow of a product of thin categories is a pair of arrows, and
    the walking arrow has three (two identities and the map between
    them), so 3 × 3 = 9 — while Mac Lane's presentation makes the
    UNIVERSAL PROPERTY immediate.  This file proves the two shapes are
    the same category, so each reading is available for the other.

    WHAT IS DELIVERED.  (1) the comparison functors both ways,
    [Square_to_22] (built through [Instance/Square.v]'s
    [SquareFunctor], so it IS the universal property applied to the
    evident commutative square in 2 × 2) and [Square_of_22] (built by
    hand, its three functor laws discharged by thinness); (2) their
    object actions, mutually inverse at LEIBNIZ equality
    ([square_22_node_round], [square_22_obj_round] — proved by case
    analysis, not by [eq_refl] uniformly: both maps are matches, and on
    the 2 × 2 side the argument must additionally be exposed as a pair,
    [prod] carrying no eta); (3) the identification
    [Square_2x2_iso : Square ≅[StrictCat] _2 ∏ _2];
    (4) the arrow count of 2 × 2, proved independently of
    [Instance/Square.v]'s count, and the cross-check that the two agree
    ([square_22_counts_agree]).

    THE STRENGTH IS [StrictCat], and that is the strong reading, not the
    weak one.  [Instance/Cat.v] gives [Cat] the hom-setoid
    [Functor_Setoid], which identifies naturally isomorphic functors, so
    an isomorphism [C ≅[Cat] D] in this library is an EQUIVALENCE of
    categories and says strictly less.  [≅[StrictCat]] is the genuine
    isomorphism of categories: the two round trips are equalities of
    functors in [Functor_StrictEq_Setoid], Leibniz on objects and a
    [hom_cast] conjugation on morphisms.  The [Cat] reading is derived
    from it ([Square_2x2_Cat_iso]) rather than stated in its place.

    An isomorphism of categories, rather than a mere equivalence, is
    available here for two reasons, both cheap: the categories are thin,
    so the morphism half of each round trip is an equation between
    parallel arrows and discharges outright; and the two object maps are
    mutually inverse by case analysis on four constructors, so no
    half-adjoint correction and no object-UIP hypothesis is needed.
    (Contrast [Theory/Skeleton.v]'s
    [skeletal_equivalence_is_isomorphism], where turning an equivalence
    into a [StrictCat] isomorphism does need the HoTT half-adjoint
    correction; nothing of the sort is used below, because the two
    functors are written down rather than extracted.)

    WHAT IS NOT DELIVERED.  No claim that the two categories are equal
    as records — their object types are [SquareNode] and
    [TwoObj * TwoObj], distinct inductive types, so no Leibniz equality
    of categories is available or attempted.  No comparison with
    [Construction/Funny.v]'s [_2 □ _2]: that is a DIFFERENT category
    (the funny tensor imposes no interchange law, so its two diagonals
    stay apart — [funny_diagonals_distinct]), and it is the free square
    rather than the commutative one; the tree carries no comparison
    functor and none is built here.  The count below is proved directly
    rather than transported along the isomorphism: the library has no
    machinery for transporting an arrow count along a comparison
    functor, and proving it twice is what makes it a CROSS-CHECK. *)

(** ** Thinness of the product shape *)

(** The walking arrow is thin.  Its hom-setoid is [Morphism_equality],
    so [≈] is Leibniz [=] and this is [ord_two_thin]
    ([Instance/Ordinal.v]) verbatim; it is cited rather than reproved. *)
Lemma Two_Thin : Thin _2.
Proof. intros x y f g; exact (ord_two_thin f g). Qed.

Lemma Two2_Thin : Thin (_2 ∏ _2).
Proof. exact (Thin_Product Two_Thin Two_Thin). Qed.

(** ** From 2 × 2 to the square

    The four corners.  The first factor is the horizontal direction of
    the square (A → B and C → D), the second the vertical (A → C and
    B → D). *)
Definition sq22_node (a b : TwoObj) : SquareNode :=
  match a, b with
  | TwoX, TwoX => Sq_A
  | TwoY, TwoX => Sq_B
  | TwoX, TwoY => Sq_C
  | TwoY, TwoY => Sq_D
  end.

Definition sq22_obj (x : TwoObj * TwoObj) : SquareNode :=
  sq22_node (fst x) (snd x).

(** The nine arrows of 2 × 2, sent to the nine arrows of the square.
    The last line is the one with content: a pair of non-identity arrows
    goes to the DIAGONAL, which is where the imposed relation is spent —
    without it there would be two candidate images and no functor. *)
Definition sq22_map {a b c d : TwoObj} (u : TwoHom a c) (v : TwoHom b d) :
  sq22_node a b ~{Square}~> sq22_node c d :=
  match u in TwoHom a0 c0, v in TwoHom b0 d0
    return sq22_node a0 b0 ~{Square}~> sq22_node c0 d0 with
  | TwoIdX, TwoIdX => id
  | TwoIdX, TwoIdY => id
  | TwoIdY, TwoIdX => id
  | TwoIdY, TwoIdY => id
  | TwoXY,  TwoIdX => square_f
  | TwoIdX, TwoXY  => square_g
  | TwoIdY, TwoXY  => square_h
  | TwoXY,  TwoIdY => square_k
  | TwoXY,  TwoXY  => square_diagonal
  end.

(** All three functor laws are equations between parallel arrows of
    [Square], hence instances of [Square_Thin]. *)
Definition Square_of_22 : (_2 ∏ _2) ⟶ Square :=
  Build_Functor (_2 ∏ _2) Square
    sq22_obj
    (fun x y f => sq22_map (fst f) (snd f))
    (fun x y f g _ => Square_Thin _ _ _ _)
    (fun x => Square_Thin _ _ _ _)
    (fun x y z f g => Square_Thin _ _ _ _).

(** ** From the square to 2 × 2

    The evident commutative square in 2 × 2, and the functor the
    universal property of [Square] makes of it. *)
Definition sq22_commuting : CommutingSquare (_2 ∏ _2) :=
  @Build_CommutingSquare (_2 ∏ _2)
    (TwoX, TwoX) (TwoY, TwoX) (TwoX, TwoY) (TwoY, TwoY)
    (TwoXY, TwoIdX) (TwoIdX, TwoXY) (TwoIdY, TwoXY) (TwoXY, TwoIdY)
    (Two2_Thin _ _ _ _).

Definition Square_to_22 : Square ⟶ (_2 ∏ _2) := SquareFunctor sq22_commuting.

(** Its object action, on the nose. *)
Example Square_to_22_A : fobj[Square_to_22] Sq_A = (TwoX, TwoX) := eq_refl.
Example Square_to_22_B : fobj[Square_to_22] Sq_B = (TwoY, TwoX) := eq_refl.
Example Square_to_22_C : fobj[Square_to_22] Sq_C = (TwoX, TwoY) := eq_refl.
Example Square_to_22_D : fobj[Square_to_22] Sq_D = (TwoY, TwoY) := eq_refl.

(** ** The two object actions are mutually inverse

    Leibniz equalities, but not [eq_refl] uniformly: both maps are
    matches, so they reduce only once their argument is a constructor,
    and on the 2 × 2 side the argument must additionally be exposed as a
    PAIR, [prod] carrying no eta. *)
Lemma square_22_node_round (n : SquareNode) :
  sq22_obj (fobj[Square_to_22] n) = n.
Proof. destruct n; reflexivity. Qed.

Lemma square_22_obj_round (x : TwoObj * TwoObj) :
  fobj[Square_to_22] (sq22_obj x) = x.
Proof. destruct x as [a b]; destruct a, b; reflexivity. Qed.

(** ** The identification

    Both round trips at [Functor_StrictEq_Setoid] strength: Leibniz on
    objects, and on morphisms a [hom_cast] conjugation which thinness
    discharges outright on either side. *)
Lemma Square_22_round : @equiv _ (@Functor_StrictEq_Setoid Square Square)
  (Square_of_22 ◯ Square_to_22) (Id[Square]).
Proof.
  apply (strict_of_hom_cast (Square_of_22 ◯ Square_to_22) (Id[Square])
           square_22_node_round).
  intros x y p; exact (Square_Thin _ _ _ _).
Qed.

Lemma Square_22_round' :
  @equiv _ (@Functor_StrictEq_Setoid (_2 ∏ _2) (_2 ∏ _2))
    (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2]).
Proof.
  apply (strict_of_hom_cast (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2])
           square_22_obj_round).
  intros x y p; exact (Two2_Thin _ _ _ _).
Qed.

(** Riehl §1.6 Example 1.6.6: the walking commutative square IS 2 × 2 —
    an isomorphism of categories, not merely an equivalence. *)
Definition Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2) :=
  @Build_Isomorphism StrictCat Square (_2 ∏ _2)
    Square_to_22 Square_of_22 Square_22_round' Square_22_round.

(** The weaker [Cat] reading, derived.  Recall that [≅[Cat]] in this
    library is an EQUIVALENCE of categories, [Cat]'s hom-setoid being
    [Functor_Setoid]; the [StrictCat] statement above is the strong
    one. *)
Definition Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2) :=
  @Build_Isomorphism Cat Square (_2 ∏ _2)
    Square_to_22 Square_of_22
    (strict_equiv_implies_fun_equiv _ _ Square_22_round')
    (strict_equiv_implies_fun_equiv _ _ Square_22_round).

(** ** The arrow count of 2 × 2, independently

    An arrow of [_2 ∏ _2] is a pair of arrows of [_2], so the count is
    the square of the walking arrow's.  Proved here from scratch — not
    transported along [Square_2x2_iso] — so that it is a genuine
    cross-check on [Instance/Square.v]'s count rather than a restatement
    of it. *)

(** The walking arrow has three arrows: [TwoHom] is inhabited except at
    (Y, X), and then by exactly one element. *)
Definition two_homcount (a b : TwoObj) : nat :=
  match a, b with
  | TwoY, TwoX => 0
  | _, _ => 1
  end.

Lemma two_hom_empty (f : TwoHom TwoY TwoX) : False.
Proof. exact (TwoHom_Y_X_absurd f). Qed.

Lemma two_hom_inhabited (a b : TwoObj) :
  two_homcount a b = 1%nat → TwoHom a b.
Proof.
  destruct a, b; simpl; intro H;
    solve [ exact TwoIdX | exact TwoIdY | exact TwoXY | discriminate ].
Qed.

Definition two_objs : list TwoObj := TwoX :: TwoY :: nil.

Definition two_pairs : list (TwoObj * TwoObj) := list_prod two_objs two_objs.

Definition two_arrow_total : nat :=
  fold_right (fun q n => two_homcount (fst q) (snd q) + n)%nat 0%nat two_pairs.

Theorem two_arrow_total_3 : two_arrow_total = 3%nat.
Proof. reflexivity. Qed.

(** In the product, the hom-set at a pair of endpoint pairs is the
    product of the two component hom-sets, so its count is the product
    of the two counts. *)
Definition prod22_homcount (x y : TwoObj * TwoObj) : nat :=
  (two_homcount (fst x) (fst y) * two_homcount (snd x) (snd y))%nat.

Definition prod22_pairs : list ((TwoObj * TwoObj) * (TwoObj * TwoObj)) :=
  list_prod two_pairs two_pairs.

Example prod22_pairs_16 : length prod22_pairs = 16%nat := eq_refl.

Definition prod22_arrow_total : nat :=
  fold_right (fun q n => prod22_homcount (fst q) (snd q) + n)%nat 0%nat
    prod22_pairs.

Theorem prod22_arrow_total_9 : prod22_arrow_total = 9%nat.
Proof. reflexivity. Qed.

Definition prod22_identity_total : nat :=
  fold_right (fun x n => prod22_homcount x x + n)%nat 0%nat two_pairs.

Theorem prod22_identity_total_4 : prod22_identity_total = 4%nat.
Proof. reflexivity. Qed.

Definition prod22_nonidentity_total : nat :=
  (prod22_arrow_total - prod22_identity_total)%nat.

Theorem prod22_nonidentity_total_5 : prod22_nonidentity_total = 5%nat.
Proof. reflexivity. Qed.

(** The counting function is correct: it is 0 exactly where the hom-set
    is empty, and where it is 1 the hom-set is inhabited and thin.
    (Thinness is [Two2_Thin] and holds everywhere, so only inhabitation
    and emptiness are per-pair.) *)
Theorem prod22_homcount_empty (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 0%nat → (x ~{_2 ∏ _2}~> y) → False.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl;
    solve [ intros H _; discriminate H
          | intros _ [u v]; solve [ exact (two_hom_empty u)
                                  | exact (two_hom_empty v) ] ].
Qed.

Theorem prod22_homcount_inhabited (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 1%nat → x ~{_2 ∏ _2}~> y.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl; intro H;
    solve [ discriminate H
          | exact (TwoIdX, TwoIdX) | exact (TwoIdX, TwoIdY)
          | exact (TwoIdX, TwoXY)  | exact (TwoIdY, TwoIdX)
          | exact (TwoIdY, TwoIdY) | exact (TwoIdY, TwoXY)
          | exact (TwoXY, TwoIdX)  | exact (TwoXY, TwoIdY)
          | exact (TwoXY, TwoXY) ].
Qed.

(** The cross-check the two presentations owe each other: Mac Lane's
    count and Riehl's agree, arrow for arrow, identity for identity. *)
Theorem square_22_counts_agree :
  ((square_arrow_total = prod22_arrow_total) *
   (square_identity_total = prod22_identity_total) *
   (square_nonidentity_total = prod22_nonidentity_total))%type.
Proof. repeat split; reflexivity. Qed.

(** ...and 9 = 3 × 3, which is the whole of Riehl's argument. *)
Example square_count_is_three_squared :
  square_arrow_total = (two_arrow_total * two_arrow_total)%nat := eq_refl.
