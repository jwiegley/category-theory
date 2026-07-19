Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Ends in [Sets], computed directly *)

(* nLab:      https://ncatlab.org/nlab/show/end
   Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

   For a functor of mixed variance [F : C^op ∏ C ⟶ Sets] the end [∫_x F(x,x)]
   is realised here as a concrete setoid, with no recourse to
   function-extensionality.  The carrier is the setoid of "compatible
   families": a choice [s x : F(x,x)] for every object [x : C], subject to the
   wedge (dinaturality) constraint

     fmap[F] (id, f) (s x)  ≈  fmap[F] (op f, id) (s y)      for f : x ~> y.

   Both routes land in [F(x,y)]: the left applies the covariant action [F(x,f)]
   to [s x], the right the contravariant action [F(f,y)] to [s y].  The pair
   [(id, f)] is a morphism [(x,x) ~> (x,y)] of [C^op ∏ C] whose first component
   is an op-morphism, following the variance convention of Theory/Dinatural and
   Structure/Wedge; the pair [(op f, id)] is the morphism [(y,y) ~> (x,y)].

   The equivalence on this carrier is pointwise: two families are identified
   when they agree at every object up to that object's [≈].  Because the apex
   is a setoid, this equivalence is carried by the object itself rather than by
   a quotient type, so the construction is [funext]-free.

   The universal wedge has the projection [s ↦ s x] as its leg at [x]; the wedge
   condition is exactly the family's own constraint.  The end UMP sends a
   competing wedge [W] to the mediator [e ↦ (fun x => wedge_map[W] e)], whose
   compatibility constraint is [W]'s own wedge law read at [e]; commuting and
   uniqueness are both pointwise.  This yields [Sets_End F : End F] for every
   [F : C^op ∏ C ⟶ Sets].

   As with every Sets-valued (co)limit in this development the indexing
   category's object and hom levels are constrained to sit below Sets' carrier
   level, so that the family type [∀ x, F(x,x)] and its constraint fit as a
   setoid carrier; these smallness constraints are inferred by universe
   polymorphism and recorded on [Sets_End]. *)

Section SetsEnd.

Context {C : Category}.
Context (F : C^op ∏ C ⟶ Sets).

(* The end carrier: compatible families on the diagonal.  The second component
   is the wedge constraint, phrased with the two mixed-variance actions of [F].
   Each pair is annotated with its [C^op ∏ C] hom type so that the product-
   category objects are determined without higher-order unification. *)
Definition end_family : Type :=
  { s : ∀ x : C, F (x, x)
  & ∀ (x y : C) (f : x ~{C}~> y),
      fmap[F] ((@id (C^op) x, f) : (x, x) ~{C^op ∏ C}~> (x, y)) (s x)
        ≈ fmap[F] ((op f, @id C y) : (y, y) ~{C^op ∏ C}~> (x, y)) (s y) }.

(* Pointwise equivalence of families: agreement at every object, up to the
   codomain setoid at that object. *)
Definition end_family_equiv (s t : end_family) : Type :=
  ∀ x : C, `1 s x ≈ `1 t x.

#[local] Obligation Tactic := idtac.

(* The end object as a [SetoidObject]: the family carrier under pointwise [≈].
   Reflexivity, symmetry and transitivity are inherited objectwise from the
   setoids [F(x,x)]. *)
Program Definition Sets_End_obj : SetoidObject := {|
  carrier   := end_family;
  is_setoid := {| equiv := end_family_equiv |}
|}.
Next Obligation.
  constructor.
  - intros s x; reflexivity.
  - intros s t H x; symmetry; exact (H x).
  - intros s t u H1 H2 x; transitivity (`1 t x); [exact (H1 x) | exact (H2 x)].
Qed.

(* The projection leg at [x]: evaluate a family at [x].  It respects the
   pointwise equivalence by definition. *)
Program Definition end_projection (x : C) :
  Sets_End_obj ~{Sets}~> F (x, x) := {|
  morphism := fun s => `1 s x
|}.
Next Obligation.
  intros x s t Hst; exact (Hst x).
Qed.

(* The universal wedge of the end: apex [Sets_End_obj] with the projection
   legs.  Its wedge condition is precisely the family constraint (the second
   component of each family), applied to the argument.  The wedge is assembled
   with the explicit constructor because [Structure/End] rebinds the name
   [wedge_obj] as its [End ~> Wedge] coercion, which shadows the record label. *)
Program Definition Sets_End_Wedge : Wedge F :=
  @Build_Wedge C Sets F Sets_End_obj (fun x => end_projection x) _.
Next Obligation.
  intros x y f s.
  exact (`2 s x y f).
Qed.

(* Compatibility constraint of the mediator.  Given a competing wedge [W] and
   an element [e] of its apex, the family [fun x => wedge_map[W] e] satisfies
   the end constraint because that constraint, read pointwise at [e], is
   exactly [W]'s own wedge law. *)
Lemma end_mediator_constraint (W : Wedge F) (e : Wedge_to_obj F W) :
  ∀ (x y : C) (f : x ~{C}~> y),
    fmap[F] ((@id (C^op) x, f) : (x, x) ~{C^op ∏ C}~> (x, y))
            (@wedge_map _ _ _ W x e)
      ≈ fmap[F] ((op f, @id C y) : (y, y) ~{C^op ∏ C}~> (x, y))
                (@wedge_map _ _ _ W y e).
Proof.
  intros x y f.
  exact (@ump_wedges _ _ _ W x y f e).
Qed.

(* The underlying function of the mediator: package the legs of [W] at [e] into
   a family, carrying the compatibility constraint above as its witness. *)
Definition end_mediator_fun (W : Wedge F) (e : Wedge_to_obj F W) :
  end_family :=
  (fun x => @wedge_map _ _ _ W x e; end_mediator_constraint W e).

(* The mediator as a setoid map [W ~> Sets_End_obj].  It respects [≈] because
   each leg [wedge_map[W]] does. *)
Program Definition Sets_End_mediator (W : Wedge F) :
  Wedge_to_obj F W ~{Sets}~> Sets_End_obj := {|
  morphism := end_mediator_fun W
|}.
Next Obligation.
  intros W e e' Hee' x.
  exact (proper_morphism (@wedge_map _ _ _ W x) e e' Hee').
Qed.

(* The end and its universal property.  For every wedge [W] the mediator above
   is the unique setoid map to the end recovering each leg of [W] by
   post-composition with the corresponding projection; commuting holds by
   reflexivity and uniqueness is the pointwise reading of the leg equations. *)
Program Definition Sets_End : End F := {|
  end_wedge := Sets_End_Wedge
|}.
Next Obligation.
  intro W.
  unshelve refine (Build_Unique _ _ _ (Sets_End_mediator W) _ _).
  - intros x e; reflexivity.
  - intros v Hv e x; symmetry; exact (Hv x e).
Qed.

End SetsEnd.

Arguments end_family {C} F.
Arguments Sets_End_obj {C} F.
Arguments Sets_End {C} F.
