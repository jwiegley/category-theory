Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(* Cat is the category of all small categories:

    objects               Categories
    arrows                Functors
    arrow equivalence     Natural Isomorphisms
    identity              Identity Functor
    composition           Horizontal composition of Functors *)

Program Instance Cat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects
}.

Record Isomorphism_FullyFaithful `(iso : C ≅ D) := {
  to_full       : Full (to iso);
  to_faithful   : Faithful (to iso);
  from_full     : Full (from iso);
  from_faithful : Faithful (from iso)
}.

Theorem Cat_Iso_FullyFaithful `(iso : C ≅ D) :
  let φ := to iso in
  let ψ := from iso in
  let η x := to (`1 (iso_from_to iso) x) in
  let μ x := to (`1 (iso_to_from iso) x) in
  (* jww (2018-10-25): Do these two preconditions follow from [iso]? *)
  (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
  (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
  Isomorphism_FullyFaithful iso.
Proof.
  construct.
  - construct.
    + exact (to (`1 (iso_from_to iso) y)
               ∘ fmap[from iso] g
               ∘ from (`1 (iso_from_to iso) x)).
    + abstract
        (proper;
         now rewrite X1).
    + abstract
        (simpl;
         rewrite fmap_id, id_right;
         now apply iso_to_from).
    + abstract
        (simpl;
         comp_left;
         comp_right;
         rewrite <- !comp_assoc;
         rewrite (comp_assoc (`1 (iso_from_to iso) y)⁻¹);
         rewrite (iso_from_to (`1 (iso_from_to iso) y)), id_left;
         now apply fmap_comp).
    + abstract
        (simpl;
         rewrite !fmap_comp;
         srewrite X;
         srewrite (`2 (iso_to_from iso));
         rewrite !comp_assoc;
         rewrite iso_to_from, id_left;
         srewrite_r X;
         rewrite <- comp_assoc;
         rewrite <- fmap_comp;
         rewrite iso_to_from, fmap_id, id_right;
         reflexivity).
  - construct.
    abstract
      (rewrite <- id_left;
       rewrite <- id_right;
       symmetry;
       rewrite <- id_left;
       rewrite <- id_right;
       symmetry;
       spose (`2 (iso_from_to iso)) as X2;
       rewrite <- (iso_to_from (`1 (iso_from_to iso) y));
       rewrite <- (iso_to_from (`1 (iso_from_to iso) x));
       rewrite <- !comp_assoc;
       rewrite (comp_assoc _ f _);
       rewrite (comp_assoc _ g _);
       rewrite (comp_assoc (_ ∘ _) _ _);
       rewrite (comp_assoc (_ ∘ _) _ _);
       rewrite <- (X2 x y f);
       rewrite <- (X2 x y g);
       comp_left;
       comp_right;
       now apply (@fmap_respects D C iso⁻¹)).
  - construct.
    + exact (to (`1 (iso_to_from iso) y)
               ∘ fmap[to iso] g
               ∘ from (`1 (iso_to_from iso) x)).
    + abstract
        (proper;
         now rewrite X1).
    + abstract
        (simpl;
         rewrite fmap_id, id_right;
         now apply iso_to_from).
    + abstract
        (simpl;
         comp_left;
         comp_right;
         rewrite <- !comp_assoc;
         rewrite (comp_assoc (`1 (iso_to_from iso) y)⁻¹);
         rewrite (iso_from_to (`1 (iso_to_from iso) y)), id_left;
         now apply fmap_comp).
    + abstract
        (simpl;
         rewrite !fmap_comp;
         srewrite X0;
         srewrite (`2 (iso_from_to iso));
         rewrite !comp_assoc;
         rewrite iso_to_from, id_left;
         srewrite_r X0;
         rewrite <- comp_assoc;
         rewrite <- fmap_comp;
         rewrite iso_to_from, fmap_id, id_right;
         reflexivity).
  - construct.
    abstract
      (rewrite <- id_left;
       rewrite <- id_right;
       symmetry;
       rewrite <- id_left;
       rewrite <- id_right;
       symmetry;
       spose (`2 (iso_to_from iso)) as X2;
       rewrite <- (iso_to_from (`1 (iso_to_from iso) y));
       rewrite <- (iso_to_from (`1 (iso_to_from iso) x));
       rewrite <- !comp_assoc;
       rewrite (comp_assoc _ f _);
       rewrite (comp_assoc _ g _);
       rewrite (comp_assoc (_ ∘ _) _ _);
       rewrite (comp_assoc (_ ∘ _) _ _);
       rewrite <- (X2 x y f);
       rewrite <- (X2 x y g);
       comp_left;
       comp_right;
       now apply (@fmap_respects C D (to iso))).
Defined.
