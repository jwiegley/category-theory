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

#[global]
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

Global Instance Cat_Iso_to_Faithful `(iso : C ≅ D) : Faithful (to iso).
Proof.
  construct.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_left.
  rewrite <- id_right.
  symmetry.
  spose (`2 (iso_from_to iso) x y) as X2.
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ f
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  { repeat apply compose_respects.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - symmetry. apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  transitivity (`1 (iso_from_to iso) y ∘ (`1 (iso_from_to iso) y)⁻¹ ∘ g
                 ∘ (`1 (iso_from_to iso) x ∘ (`1 (iso_from_to iso) x)⁻¹)).
  2: {
    repeat apply compose_respects.
    - apply (iso_to_from (`1 (iso_from_to iso) y)).
    - reflexivity.
    - apply (iso_to_from (`1 (iso_from_to iso) x)).
  }
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f _).
  rewrite (comp_assoc _ g _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite (comp_assoc (_ ∘ _) _ _).
  rewrite <- (X2 f).
  rewrite <- (X2 g).
  comp_left.
  comp_right.
  now apply (@fmap_respects D C iso⁻¹).
Qed.

Global Instance Cat_Iso_from_Faithful `(iso : C ≅ D) : Faithful (from iso).
Proof.
  apply (Cat_Iso_to_Faithful (iso_sym iso)).
Qed.

Section Cat_Iso_FullyFaithful.
  Local Obligation Tactic := simpl; intros.

  Program Definition Cat_Iso_FullyFaithful `(iso : C ≅ D) :
    let φ := to iso in
    let ψ := from iso in
    let η x := to (`1 (iso_from_to iso) x) in
    let μ x := to (`1 (iso_to_from iso) x) in
    (* jww (2018-10-25): Do these two preconditions follow from [iso]? *)
    (∀ x, fmap[φ] (η x) ≈ μ (φ x)) ->
    (∀ x, fmap[ψ] (μ x) ≈ η (ψ x)) ->
    Isomorphism_FullyFaithful iso :=
    let φ := to iso in
    let ψ := from iso in
    let η x := to (`1 (iso_from_to iso) x) in
    let μ x := to (`1 (iso_to_from iso) x) in
    fun H0 H1 =>
    {| to_full :=
         {| prefmap x y g := to (`1 (iso_from_to iso) y)
                 ∘ fmap[from iso] g
                 ∘ from (`1 (iso_from_to iso) x) |};
       from_full :=
         {| prefmap x y g := to (`1 (iso_to_from iso) y)
                 ∘ fmap[to iso] g
                 ∘ from (`1 (iso_to_from iso) x) |};
       to_faithful :=
         Cat_Iso_to_Faithful iso;
       from_faithful :=
         Cat_Iso_from_Faithful iso;
    |}.
  Next Obligation.
    proper. comp_right. comp_left. now rewrite X.
  Qed.
  Next Obligation.
    rewrite fmap_id, id_right.
    apply iso_to_from.
  Qed.
  Next Obligation.
    comp_right.
    comp_left.
    rewrite !fmap_comp.
    comp_left.
    rewrite comp_assoc.
    rewrite iso_from_to.
    cat.
  Qed.
  Next Obligation.
    rewrite !fmap_comp.
    srewrite H0.
    srewrite (`2 (iso_to_from iso)).
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    srewrite_r H0.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    transitivity (g ∘ id).
    - comp_left. rewrite iso_to_from. apply fmap_id.
    - apply id_right.
  Qed.
  Next Obligation.
    proper. comp_left. comp_right. now rewrite X.
  Qed.
  Next Obligation.
    cat. apply iso_to_from.
  Qed.
  Next Obligation.
    comp_right. comp_left.
    rewrite !fmap_comp.
    comp_left.
    rewrite comp_assoc.
    rewrite iso_from_to.
    cat.
  Qed.
  Next Obligation.
    simpl.
    rewrite !fmap_comp.
    srewrite H1.
    srewrite (`2 (iso_from_to iso)).
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    srewrite_r H1.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    rewrite iso_to_from, fmap_id, id_right.
    reflexivity.
  Qed.
End Cat_Iso_FullyFaithful.
