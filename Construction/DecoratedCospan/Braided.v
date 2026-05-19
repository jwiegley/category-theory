Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.

Generalizable All Variables.

(** * Braided and Symmetric Monoidal structure on [DecoratedCospanCat]

    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    Theorem 3.1.  This module assembles the [BraidedMonoidal] and
    [SymmetricMonoidal] instances on [DecoratedCospanCat] by layering
    decoration coherences on top of [Cospan_BraidedMonoidal] /
    [Cospan_SymmetricMonoidal] from [Construction/Cospan/Symmetric.v].

    ** Architecture

      [DecCospan_Braided_Coherent]      (braid naturality + hexagon)
      [DecCospan_Symmetric_Coherent]    (braid involution)

    Each coherence field states a [dec_cospan_equiv] between the
    decorated-cospan LHS and RHS of the matching Braided/Symmetric
    obligation, with the braiding built as [dec_mor_as_cospan paws]
    (the [paws] swap from [C]'s [Cocartesian] structure lifted to a
    decorated cospan via the canonical [id_decoration]).

    The cospan-level part is already proved in
    [Cospan_BraidedMonoidal] / [Cospan_SymmetricMonoidal]; the
    decoration-level part is the genuine content of the field, and
    typically requires [F] to be a SYMMETRIC lax monoidal functor
    (i.e. [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D]).  Concrete
    decoration instances supply explicit proofs from their chosen [F]. *)

Section DecoratedCospanBraided.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation Dtensor f g := (dec_cospan_tensor LM cospan_merge f g).
Notation Dcompose g f := (dec_cospan_compose HP LM cospan_merge g f).
Notation Did X := (dec_cospan_id id_decoration X).
Notation Dlift f := (dec_mor_as_cospan id_decoration f).

(** ** Coherence class for the Braided structure on [DecoratedCospanCat]

    The braiding on [DC] is [dec_mor_as_cospan paws]: the decorated lift
    of the C-coproduct swap, with the canonical [id_decoration] on the
    apex.  The Braided-class obligations are:

      - [braid_natural]   : the naturality square for [braid] is a
                            decorated-cospan equivalence;
      - [hexagon_identity], [hexagon_identity_sym] : the hexagon
                            coherence relating [braid] with
                            [tensor_assoc], in both forms.

    Each field below pairs the LHS and RHS of the corresponding
    obligation directly. *)

Class DecCospan_Braided_Coherent : Type := {

  (** Naturality of [braid] : as a decorated-cospan equation.
      Goal shape (matching [@braid_natural]):
        [bimap h f ∘ braid_{x,z} ≈ braid_{y,w} ∘ bimap f h]
      where the bimap is [dec_cospan_tensor] and braid is
      [Dlift paws]. *)
  dec_braid_natural_eq :
    forall {x y z w : C}
           (f : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w),
      dec_cospan_equiv
        (Dcompose (Dtensor h f) (Dlift (@paws C H_Coc x z)))
        (Dcompose (Dlift (@paws C H_Coc y w)) (Dtensor f h));

  (** Hexagon identity (to form).  LHS and RHS are both
      RIGHT-associated.  The corresponding [Monoidal] obligation is
      left-associated; the proof reassociates via
      [dec_cospan_compose_assoc] before applying this field. *)
  dec_hexagon_identity_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (to (@coprod_assoc C H_Coc y z x)))
           (Dcompose
              (Dlift (@paws C H_Coc x (y + z)%object))
              (Dlift (to (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Did y) (Dlift (@paws C H_Coc x z)))
           (Dcompose
              (Dlift (to (@coprod_assoc C H_Coc y x z)))
              (Dtensor (Dlift (@paws C H_Coc x y)) (Did z))));

  (** Hexagon identity (from form), RIGHT-associated. *)
  dec_hexagon_identity_sym_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (from (@coprod_assoc C H_Coc z x y)))
           (Dcompose
              (Dlift (@paws C H_Coc (x + y)%object z))
              (Dlift (from (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Dlift (@paws C H_Coc x z)) (Did y))
           (Dcompose
              (Dlift (from (@coprod_assoc C H_Coc x z y)))
              (Dtensor (Did x) (Dlift (@paws C H_Coc y z)))))
}.

Context `{DCBrC : DecCospan_Braided_Coherent}.

Set Default Proof Using "All".

(** ** [DecoratedCospan_BraidedMonoidal] : the BraidedMonoidal instance *)

Program Definition DecoratedCospan_BraidedMonoidal
  : @BraidedMonoidal DC := {|
  braided_is_monoidal := DecoratedCospan_Monoidal HP LM id_decoration cospan_merge;
  braid := fun X Y => Dlift (@paws C H_Coc X Y)
|}.
Next Obligation.
  (* braid_natural: arity-2 naturality.
     The Coq-level shape (after Bifunctor unfolds to [dec_cospan_tensor]):
       Dcompose (Dcompose (Dtensor h f) (Dlift paws)) ?
     We use the same pattern as in [Cospan_BraidedMonoidal] —
     re-associate the outer compose, fuse via tensor_compose_compat
     and tensor_respects, then apply the coherence field. *)
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
                h (Did _) (Did _) g). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge). }
  apply dec_cospan_equiv_sym.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
               (Did _) g h (Did _)).
    - apply dec_cospan_equiv_refl. }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl. }
  apply dec_cospan_equiv_sym.
  apply dec_braid_natural_eq.
Qed.
Next Obligation.
  (* Hexagon LHS and RHS are both left-associated in the Monoidal goal;
     the [dec_hexagon_identity_eq] coherence is right-associated.
     Reassociate both sides via [dec_cospan_compose_assoc_sym]. *)
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.
Next Obligation.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_sym_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.

(** ** Coherence class for the Symmetric structure on [DecoratedCospanCat]

    A single field: [braid ∘ braid ≈ id] on the decorated side.
    Cospan-level: [cospan_braid_invol_C] (from [Cospan_SymmetricMonoidal]). *)

Class DecCospan_Symmetric_Coherent : Type := {
  dec_braid_invol_eq :
    forall {x y : C},
      dec_cospan_equiv
        (Dcompose (Dlift (@paws C H_Coc x y))
                  (Dlift (@paws C H_Coc y x)))
        (Did (y + x)%object)
}.

Context `{DCSC : DecCospan_Symmetric_Coherent}.

(** ** [DecoratedCospan_SymmetricMonoidal] : the SymmetricMonoidal instance *)

Program Definition DecoratedCospan_SymmetricMonoidal
  : @SymmetricMonoidal DC := {|
  symmetric_is_braided := DecoratedCospan_BraidedMonoidal
|}.
Next Obligation.
  apply dec_braid_invol_eq.
Qed.

End DecoratedCospanBraided.

(** ** Discussion: when [F] must be symmetric

    The [DecCospan_Braided_Coherent] field [dec_braid_natural_eq]
    requires the decoration on the LHS — built by tensoring decorations
    via [lax_ap] then composing with the cospan-side [braid] — to agree
    with the decoration on the RHS.  In Fong's [F = Set] case (where
    decorations are global elements of [F N]) this is automatic; in the
    general monoidal-codomain case it requires [F] to be a SYMMETRIC
    lax monoidal functor, i.e. [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D].

    [DecCospan_Symmetric_Coherent]'s single field
    [dec_braid_invol_eq] follows on the cospan side from
    [paws_invol] (proved generically in [Cospan_SymmetricMonoidal]);
    its decoration side is the [id_decoration]-coherence on the
    identity cospan, i.e., the composite of two identity-style
    decorations through [paws ∘ paws ≈ id] collapses back to
    [id_decoration].

    Both coherence classes are populated trivially when [F = Δ I_D]
    (the constant lax-monoidal functor), in which case all decorations
    are [id : I_D ~> I_D] and every coherence reduces to refl. *)
