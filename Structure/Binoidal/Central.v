Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(** * The centrality closure kit for binoidal categories

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    (centrality and the centre are discussed there; bare binoidal
    categories have no dedicated nLab page and are covered under
    premonoidal categories)

    Structure/Binoidal.v defines when a morphism [f : x ~> y] of a
    binoidal category is [central]: tensoring [f] with any morphism [f']
    in either order gives the same composite, on both the [x ⊗ x'] and
    the [x' ⊗ x] side.  This file develops the closure properties of that
    predicate that are available in a BARE binoidal category — no unit,
    no associator:

      - [central_id]        : identities are central;
      - [central_respects]  : centrality respects ≈;
      - [central_comp]      : central morphisms compose;
      - [central_iso_from]  : the inverse of a central isomorphism is
                              central;

    together with the interaction of [composite_ff'] with identities
    ([composite_id_left] / [composite_id_right]) and with composition
    under a single centrality hypothesis ([composite_ff'_comp_l] /
    [composite_ff'_comp_r]).  The last two isolate the exact "middle
    interchange" that one-sided functoriality of the tensor needs; both
    reduce to the same square, read off one conjunct of the centrality of
    [f] or of [g'].

    The closure properties package the central morphisms as the centre
    Z(C) — here [Centre] — a wide subcategory of [C] built through
    Construction/Subcategory.v, mirroring the deterministic subcategory
    [Det] of Structure/Monoidal/CopyDiscard/Deterministic.v.

    What is deliberately NOT here: closure of centrality under the tensor
    [composite_ff'] itself.  For central [f] and [f'], commuting
    [composite_ff' f f'] past a right-tensored morphism is a square at
    the nested tensor [(x ⊗ x') ⊗ a], and a bare binoidal category
    carries no morphism relating the two nesting levels, so that square
    is unreachable from the single-level centrality data.  Once an
    associator is present the chase goes through; the closure lemma
    [composite_ff'_central] therefore lives in
    Structure/Premonoidal/Centre.v, where Z(C) is also shown to be
    monoidal ([Centre_Monoidal]), discharging the promise recorded in the
    comment above [central] in Structure/Binoidal.v. *)

Section CentralKit.

Context {C : Category}.
Context `{@Binoidal C}.

(** ** Closure properties of centrality *)

(* Identities are central: both defining squares reduce by [fmap_id] and
   the unit laws to a triviality. *)
Lemma central_id {x : C} : central (@id C x).
Proof.
  intros x' y' f'; split.
  - rewrite !fmap_id; cat.
  - rewrite !fmap_id; cat.
Qed.

(* Centrality is a property of the ≈-class of a morphism: both defining
   squares mention [f] only through [fmap], which respects ≈. *)
Lemma central_respects {x y : C} {f g : x ~> y} :
  f ≈ g → central f → central g.
Proof.
  intros E cf x' y' f'.
  destruct (cf x' y' f') as [sq1 sq2].
  split.
  - rewrite <- E; exact sq1.
  - rewrite <- E; exact sq2.
Qed.

(* Central morphisms compose: expand [fmap] over the composite with
   [fmap_comp], then paste [g]'s square followed by [f]'s square.  Each
   conjunct is a single-level pasting of two commuting squares. *)
Lemma central_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  central f → central g → central (f ∘ g).
Proof.
  intros cf cg x' y' f'.
  destruct (cf x' y' f') as [f1 f2].
  destruct (cg x' y' f') as [g1 g2].
  split.
  - rewrite !fmap_comp.
    rewrite !comp_assoc_sym.
    rewrite g1.
    rewrite !comp_assoc.
    now rewrite f1.
  - rewrite !fmap_comp.
    rewrite !comp_assoc.
    rewrite f2.
    rewrite !comp_assoc_sym.
    now rewrite g2.
Qed.

(* The inverse of a central isomorphism is central: conjugate each
   to-square by the tensored inverse on both sides and cancel via
   [fmap_comp], the isomorphism laws, and [fmap_id].  The auxiliary
   equation [E] expresses the tensored [f'] as the to-square composite
   flanked by one inverse; substituting it into the goal leaves only the
   other cancellation. *)
Lemma central_iso_from {x y : C} (i : x ≅ y) :
  central (to i) → central (from i).
Proof.
  intros ci x' y' f'.
  destruct (ci x' y' f') as [sq1 sq2].
  split.
  - assert (E : fmap[inj_right y] f'
                  ≈ fmap[inj_left y'] (to i)
                      ∘ (fmap[inj_right x] f' ∘ fmap[inj_left x'] (from i))).
    { rewrite !comp_assoc.
      rewrite sq1.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
  - assert (E : fmap[inj_left y] f'
                  ≈ fmap[inj_right y'] (to i)
                      ∘ (fmap[inj_left x] f' ∘ fmap[inj_right x'] (from i))).
    { rewrite !comp_assoc.
      rewrite <- sq2.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
Qed.

(** ** [composite_ff'] against identities *)

(* Tensoring the identity on the left leaves the right tensoring of [g]. *)
Lemma composite_id_left {x y : C} (w : C) (g : x ~> y) :
  composite_ff' (id[w]) g ≈ fmap[inj_right w] g.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

(* Tensoring the identity on the right leaves the left tensoring of [f]. *)
Lemma composite_id_right {x y : C} (w : C) (f : x ~> y) :
  composite_ff' f (id[w]) ≈ fmap[inj_left w] f.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(** ** One-sided bifunctoriality

    In a monoidal category [bimap] is functorial in both variables
    jointly.  For the binoidal [composite_ff'] the analogous interchange

      composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'

    needs exactly one middle swap,

      fmap[inj_right z] g' ∘ fmap[inj_left x'] f
        ≈ fmap[inj_left y'] f ∘ fmap[inj_right y] g',

    and a SINGLE centrality hypothesis supplies it: this square is
    conjunct 1 of [central f] instantiated at [g'], and equally conjunct 2
    of [central g'] instantiated at [f].  [composite_ff'_comp_swap] is
    keyed on the bare square and pastes the swap between the [fmap_comp]
    expansions once; the two variants below each read the square off one
    conjunct. *)

Lemma composite_ff'_comp_swap {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  fmap[inj_left y'] f ∘ fmap[inj_right y] g'
    ≈ fmap[inj_right z] g' ∘ fmap[inj_left x'] f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof.
  intros sq.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite !comp_assoc_sym.
  rewrite (comp_assoc (fmap[inj_right z] g')).
  rewrite <- sq.
  now rewrite !comp_assoc_sym.
Qed.

Lemma composite_ff'_comp_l {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cf; exact (composite_ff'_comp_swap (fst (cf x' y' g'))). Qed.

Lemma composite_ff'_comp_r {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central g' →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cg'; exact (composite_ff'_comp_swap (snd (cg' y z f))). Qed.

(** ** The centre Z(C) as a wide subcategory

    [central_id] and [central_comp] are exactly the closure conditions
    Construction/Subcategory.v asks of a subcollection of morphisms, so
    the central morphisms over ALL objects form a wide subcategory, the
    centre of the binoidal category (Power–Robinson, "Premonoidal
    categories and notions of computation", 1997).  The packaging
    mirrors [DeterministicSub]/[Det] of
    Structure/Monoidal/CopyDiscard/Deterministic.v. *)

Program Definition CentralSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => central f;
  scomp := fun _ _ _ _ _ _ _ _ cf cg => central_comp cf cg;
  sid   := fun _ _ => central_id
|}.

Lemma Centre_wide : Wide C CentralSub.
Proof. intro x; exact ttt. Qed.

(* The inclusion Z(C) ⟶ C is the generic faithful [Incl C CentralSub]
   from Construction/Subcategory.v.  Note that [Sub]'s homset compares
   first projections — [fun f g => `1 f ≈ `1 g] — so every equation
   between morphisms of the centre is literally an equation between the
   underlying morphisms of [C]; Structure/Premonoidal/Centre.v relies on
   this when it transports the coherence laws of a premonoidal [C] to
   its (monoidal) centre. *)

End CentralKit.

(* The centre as a category, with the base category explicit so that
   downstream files can write [Centre C] for the centre of [C].  Its
   objects are those of [C] tagged with the trivial [poly_unit] witness,
   and its morphisms are the central morphisms. *)
Definition Centre (C : Category) `{H : @Binoidal C} : Category :=
  Sub C (@CentralSub C H).
