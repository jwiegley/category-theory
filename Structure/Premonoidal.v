Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(** * Premonoidal categories

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    Wikipedia: https://en.wikipedia.org/wiki/Premonoidal_category

    A premonoidal category (Power–Robinson, "Premonoidal categories and
    notions of computation", Math. Structures Comput. Sci. 7(5), 1997) is a
    binoidal category — Structure/Binoidal.v — together with

      - a unit object [premon_I];
      - unitor isomorphisms  lambda : I ⊗ x ≅ x   ([premon_unit_left])
                             rho    : x ⊗ I ≅ x   ([premon_unit_right]);
      - an associator alpha : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)  ([premon_assoc]);

    such that the forward components of lambda, rho and alpha are CENTRAL
    (Structure/Binoidal.v, [central]), each family is natural in every
    variable SEPARATELY, and the triangle and pentagon coherence laws hold.
    The iso orientations and the naturality-square orientations mirror
    Structure/Monoidal.v exactly, so that a monoidal category yields a
    premonoidal one field-for-field (Structure/Premonoidal/Monoidal.v).

    Design of the field set:

      - Naturality is one variable at a time.  In a binoidal category the
        tensor is only separately functorial, so a jointly-natural square in
        the style of Monoidal.v's [to_tensor_assoc_natural] is not the
        primitive notion; the three one-variable associator squares
        ([premon_assoc_natural_left]/[_middle]/[_right]) are.  Remarkably,
        the JOINT square for the interleaved composite [composite_ff'] is
        still derivable from them with no centrality hypothesis at all
        ([premon_joint_assoc_natural] below).

      - Only the forward (to) directions are data.  The from-direction
        centralities follow by [central_iso_from], and the from-direction
        naturality squares follow by conjugating the to-squares with the
        isomorphisms ([premon_square_from]).  Keeping the class minimal
        means fewer obligations for instance builders; the derived lemmas
        below restore the full Monoidal.v-style surface.

      - Centrality of the structural isomorphisms is what separates a
        premonoidal category from a mere "binoidal category with coherent
        isos": it makes the unitors and associator morphisms of the centre
        Z(C), so that Z(C) becomes a genuine monoidal category
        (Structure/Premonoidal/Centre.v), and it is exactly what the
        one-sided interchange lemmas [composite_ff'_comp_l]/[_r] of
        Structure/Binoidal/Central.v consume.

    The [composite_ff']-phrased translation lemmas at the end of this file
    ([premon_unit_left_natural_ff'], [premon_unit_right_natural_ff'],
    [premon_triangle_ff'], [premon_pentagon_ff'], and the unitor from-forms)
    restate the class fields with identity padding, which is the exact shape
    [Build_Monoidal] needs when every morphism is central
    (Structure/Premonoidal/Monoidal.v) and when the tensor is restricted to
    the centre (Structure/Premonoidal/Centre.v). *)

Section Premonoidal.

Context {C : Category}.
Context `{@Binoidal C}.

(* Section-local object-level tensor, mirroring the section notation of
   Structure/Binoidal.v.  The global ⊗ lives in two scopes (objects and,
   via [composite_ff'], morphisms); since morphism_scope is opened on top
   of object_scope, an unscoped section notation is needed for ⊗ to mean
   the OBJECT tensor inside the field types below.  Morphism-level
   interleaved tensoring is always written [composite_ff'] in this file. *)
Local Notation "x ⊗ y" := (tensor x y)
  (at level 30, right associativity).

(* Conjugating a commuting square by isomorphisms on both vertical edges:
   from   g ∘ to i ≈ to j ∘ f   we get   f ∘ from i ≈ from j ∘ g.
   Instantiated below with the unitors and the associator, this converts
   every to-direction naturality field into its from-direction form, so the
   inverse squares need not be part of the class data. *)
Lemma premon_square_from {a b c d : C} (i : a ≅ b) (j : c ≅ d)
      (f : a ~> c) (g : b ~> d) :
  g ∘ to i ≈ to j ∘ f →
  f ∘ from i ≈ from j ∘ g.
Proof.
  intros sq.
  symmetry.
  rewrite <- (id_right g).
  rewrite <- (iso_to_from i).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from j) g (to i)).
  rewrite sq.
  rewrite (comp_assoc (from j) (to j) f).
  rewrite (iso_from_to j).
  now rewrite id_left.
Qed.

(* The premonoidal structure proper.  Field orientations follow
   Structure/Monoidal.v L48-94: the isos point I ⊗ x → x, x ⊗ I → x and
   (x ⊗ y) ⊗ z → x ⊗ (y ⊗ z); the naturality squares put the tensored
   morphism after the structural map on the right-hand side; triangle and
   pentagon are verbatim transcriptions with the joint bimap replaced by
   the separate tensorings ⋉ / ⋊ of Structure/Binoidal.v. *)
Class Premonoidal := {
  premon_I : C;

  premon_unit_left  {x} : premon_I ⊗ x ≅ x;                 (* lambda *)
  premon_unit_right {x} : x ⊗ premon_I ≅ x;                 (* rho *)
  premon_assoc {x y z} : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z);         (* alpha *)

  (* The forward structural maps are central; the from-directions are
     derived below via [central_iso_from]. *)
  premon_unit_left_central  {x} : central (to (@premon_unit_left x));
  premon_unit_right_central {x} : central (to (@premon_unit_right x));
  premon_assoc_central {x y z} : central (to (@premon_assoc x y z));

  (* Naturality, one variable at a time.  For the unitors there is a single
     variable; for the associator there are three squares, one for each
     tensor position. *)
  premon_unit_left_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_left
      << premon_I ⊗ x ~~> y >>
    to premon_unit_left ∘ (premon_I ⋊ g);

  premon_unit_right_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_right
      << x ⊗ premon_I ~~> y >>
    to premon_unit_right ∘ (g ⋉ premon_I);

  premon_assoc_natural_left {x y z w} (g : x ~> y) :
    (g ⋉ (z ⊗ w)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ w ~~> y ⊗ (z ⊗ w) >>
    to premon_assoc ∘ ((g ⋉ z) ⋉ w);

  premon_assoc_natural_middle {x z w y} (h : z ~> w) :
    (x ⋊ (h ⋉ y)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ y ~~> x ⊗ (w ⊗ y) >>
    to premon_assoc ∘ ((x ⋊ h) ⋉ y);

  premon_assoc_natural_right {x y z w} (i : z ~> w) :
    (x ⋊ (y ⋊ i)) ∘ to premon_assoc
      << (x ⊗ y) ⊗ z ~~> x ⊗ (y ⊗ w) >>
    to premon_assoc ∘ ((x ⊗ y) ⋊ i);

  (* Coherence: triangle (unitors against the associator, across the unit)
     and pentagon (the two reassociations of a fourfold tensor agree). *)
  premon_triangle {x y} :
    to premon_unit_right ⋉ y
      << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
    (x ⋊ to premon_unit_left) ∘ to premon_assoc;

  premon_pentagon {x y z w} :
    (x ⋊ to premon_assoc) ∘ to premon_assoc ∘ (to premon_assoc ⋉ w)
      << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
    to premon_assoc ∘ to premon_assoc
}.

Context `{Premonoidal}.

(** ** From-direction centrality

    The inverse of a central isomorphism is central
    (Structure/Binoidal/Central.v, [central_iso_from]), so the inverse
    structural maps are central as well. *)

Lemma premon_unit_left_central_from {x} :
  central (from (@premon_unit_left _ x)).
Proof. apply central_iso_from, premon_unit_left_central. Qed.

Lemma premon_unit_right_central_from {x} :
  central (from (@premon_unit_right _ x)).
Proof. apply central_iso_from, premon_unit_right_central. Qed.

Lemma premon_assoc_central_from {x y z} :
  central (from (@premon_assoc _ x y z)).
Proof. apply central_iso_from, premon_assoc_central. Qed.

(** ** From-direction naturality

    Each to-square conjugates to the corresponding from-square via
    [premon_square_from]; the orientations mirror Monoidal.v's
    [from_unit_left_natural] etc. *)

Lemma premon_unit_left_natural_from {x y} (g : x ~> y) :
  (premon_I ⋊ g) ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof. apply premon_square_from, premon_unit_left_natural. Qed.

Lemma premon_unit_right_natural_from {x y} (g : x ~> y) :
  (g ⋉ premon_I) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof. apply premon_square_from, premon_unit_right_natural. Qed.

Lemma premon_assoc_natural_left_from {x y z w} (g : x ~> y) :
  ((g ⋉ z) ⋉ w) ∘ from premon_assoc
    << x ⊗ (z ⊗ w) ~~> (y ⊗ z) ⊗ w >>
  from premon_assoc ∘ (g ⋉ (z ⊗ w)).
Proof. apply premon_square_from, premon_assoc_natural_left. Qed.

Lemma premon_assoc_natural_middle_from {x z w y} (h : z ~> w) :
  ((x ⋊ h) ⋉ y) ∘ from premon_assoc
    << x ⊗ (z ⊗ y) ~~> (x ⊗ w) ⊗ y >>
  from premon_assoc ∘ (x ⋊ (h ⋉ y)).
Proof. apply premon_square_from, premon_assoc_natural_middle. Qed.

Lemma premon_assoc_natural_right_from {x y z w} (i : z ~> w) :
  ((x ⊗ y) ⋊ i) ∘ from premon_assoc
    << x ⊗ (y ⊗ z) ~~> (x ⊗ y) ⊗ w >>
  from premon_assoc ∘ (x ⋊ (y ⋊ i)).
Proof. apply premon_square_from, premon_assoc_natural_right. Qed.

(** ** Joint naturality of the associator, without centrality

    In a binoidal category the interleaved tensor [composite_ff' f f']
    (written f ⊗ g in the global morphism scope) is in general functorial
    only up to a centrality hypothesis, and the two interleavings of a
    pair of morphisms in general disagree.  Nevertheless, the associator
    is natural against [composite_ff'] JOINTLY in all three variables,
    with NO centrality hypothesis: decompose each [composite_ff'] into
    its ⋊-then-⋉ factors, expand the outer tensorings of composites by
    functoriality, and push alpha through the three one-variable squares;
    both sides land on the same fully right-associated word

        alpha ∘ ((y ⊗ w) ⋊ i) ∘ ((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u).

    The reason no interchange is needed: in [composite_ff' g (composite_ff'
    h i) ∘ alpha] the three factors are already stacked in the order
    right-position, middle-position, left-position, which is exactly the
    order in which the three one-variable squares consume them, and each
    square permutes a factor past alpha without ever swapping two
    non-structural factors.

    This lemma is the engine behind Structure/Premonoidal/Monoidal.v's
    [Premonoidal_Monoidal] (where it discharges [to_tensor_assoc_natural]
    once every morphism is central) and, at `1-projections, behind the
    monoidal structure of the centre in Structure/Premonoidal/Centre.v. *)

Lemma premon_joint_assoc_natural {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' g (composite_ff' h i) ∘ to premon_assoc
    << (x ⊗ z) ⊗ u ~~> y ⊗ (w ⊗ v) >>
  to premon_assoc ∘ composite_ff' (composite_ff' g h) i.
Proof.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  (* left-position square: (g ⋉ (z ⊗ u)) ∘ alpha ≈ alpha ∘ ((g ⋉ z) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ ((y ⋊ (h ⋉ u)) ∘ (to premon_assoc ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    apply compose_respects; [reflexivity|].
    apply premon_assoc_natural_left. }
  (* middle-position square: (y ⋊ (h ⋉ u)) ∘ alpha ≈ alpha ∘ ((y ⋊ h) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ (to premon_assoc ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_middle. }
  (* right-position square: (y ⋊ (w ⋊ i)) ∘ alpha ≈ alpha ∘ ((y ⊗ w) ⋊ i) *)
  rewrite comp_assoc.
  transitivity
    ((to premon_assoc ∘ ((y ⊗ w) ⋊ i))
       ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u))).
  { apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_right. }
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma premon_joint_assoc_natural_from {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' (composite_ff' g h) i ∘ from premon_assoc
    << x ⊗ (z ⊗ u) ~~> (y ⊗ w) ⊗ v >>
  from premon_assoc ∘ composite_ff' g (composite_ff' h i).
Proof. apply premon_square_from, premon_joint_assoc_natural. Qed.

(** ** Translation to [composite_ff'] form

    The unitor naturality squares and the coherence laws, restated with
    identity padding through [composite_ff'] (via [composite_id_left] /
    [composite_id_right] of Structure/Binoidal/Central.v).  With the
    tensor bifunctor of an all-central or centre-restricted premonoidal
    category defined by [fmap := composite_ff'], these are literally the
    [Build_Monoidal] fields of Structure/Monoidal.v. *)

Lemma premon_unit_left_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_left
    << premon_I ⊗ x ~~> y >>
  to premon_unit_left ∘ composite_ff' (id[premon_I]) g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural.
Qed.

Lemma premon_unit_right_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_right
    << x ⊗ premon_I ~~> y >>
  to premon_unit_right ∘ composite_ff' g (id[premon_I]).
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural.
Qed.

Lemma premon_unit_left_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' (id[premon_I]) g ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural_from.
Qed.

Lemma premon_unit_right_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' g (id[premon_I]) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural_from.
Qed.

Lemma premon_triangle_ff' {x y} :
  composite_ff' (to premon_unit_right) (id[y])
    << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
  composite_ff' (id[x]) (to premon_unit_left) ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_triangle.
Qed.

Lemma premon_pentagon_ff' {x y z w} :
  composite_ff' (id[x]) (to premon_assoc)
      ∘ to premon_assoc
      ∘ composite_ff' (to premon_assoc) (id[w])
    << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
  to premon_assoc ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_pentagon.
Qed.

End Premonoidal.
