Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.

Generalizable All Variables.

(** * Braided and symmetric monoidal structure on [CospanCat C]

    Building on [Cospan_Monoidal] (in [Construction/Cospan/Hypergraph.v]),
    we equip [CospanCat C HP] with a braiding given by the cospan-lift of
    the C-coproduct swap [paws], and verify the symmetry axiom
    [braid ∘ braid ≈ id].  The hexagon coherence reduces to a C-level
    coproduct calculation between [paws] and [coprod_assoc]. *)

Section CospanSymmetric.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** ** C-level hexagon ([to] version)

    The braid-associator hexagon at the level of coproducts:

      α_{y,z,x} ∘ paws_{x+y,z} ∘ α_{x,y,z}
        ≈ cover id[y] paws_{x,z} ∘ α_{y,x,z} ∘ cover paws_{x,y} id[z]

    Both sides are morphisms [(x+y)+z ~> y+(z+x)]. *)

Lemma coprod_hexagon_aux {x y z : C} :
  to (@coprod_assoc C H_Coc y z x) ∘ paws ∘ to (@coprod_assoc C H_Coc x y z)
  ≈ cover id[y] paws ∘ to (@coprod_assoc C H_Coc y x z) ∘ cover paws id[z].
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl)  (x-leg) → both reduce to [inr ∘ inr] *)
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inl.
      rewrite paws_inl.
      rewrite assoc_to_inr.
      symmetry.
      rewrite (comp_assoc (cover paws id[z]) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl paws inl).
      rewrite paws_inl.
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc (cover id[y] paws) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr paws inl).
      rewrite paws_inl.
      reflexivity.
    + (* ∘ (inl ∘ inr)  (y-leg) → both reduce to [inl] *)
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc paws inr inl).
      rewrite paws_inr.
      rewrite assoc_to_inl_inl.
      symmetry.
      rewrite (comp_assoc (cover paws id[z]) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl paws inr).
      rewrite paws_inr.
      rewrite assoc_to_inl_inl.
      rewrite cover_inl, id_right.
      reflexivity.
  - (* ∘ inr  (z-leg) → both reduce to [inr ∘ inl] *)
    rewrite <- !comp_assoc.
    rewrite assoc_to_inr.
    rewrite (comp_assoc paws inr inr).
    rewrite paws_inr.
    rewrite assoc_to_inl_inr.
    symmetry.
    rewrite cover_inr.
    rewrite id_right.
    rewrite assoc_to_inr.
    rewrite (comp_assoc (cover id[y] paws) inr inr).
    rewrite cover_inr.
    rewrite <- (comp_assoc inr paws inr).
    rewrite paws_inr.
    reflexivity.
Qed.

(** ** C-level hexagon ([from] version)

    Dual: domain [x+(y+z)], codomain [(z+x)+y]:

      from α_{z,x,y} ∘ paws_{x+y, z} ∘ from α_{x,y,z}
        ≈ cover paws_{x,z} id[y] ∘ from α_{x,z,y} ∘ cover id[x] paws_{y,z}

    Proved directly via [coprod_ext] on [x+(y+z)]. *)

Lemma coprod_hexagon_aux_from {x y z : C} :
  from (@coprod_assoc C H_Coc z x y) ∘ paws ∘ from (@coprod_assoc C H_Coc x y z)
  ≈ cover paws id[y] ∘ from (@coprod_assoc C H_Coc x z y) ∘ cover id[x] paws.
Proof.
  apply coprod_ext.
  - (* ∘ inl   (x-leg)
       LHS: from α_{z,x,y} ∘ paws ∘ (inl∘inl)  [assoc_from_inl]
            = from α_{z,x,y} ∘ (paws ∘ inl) ∘ inl
            = from α_{z,x,y} ∘ inr ∘ inl       [paws_inl]
            = inl ∘ inr                         [assoc_from_inr_inl]
       RHS: cover paws id ∘ from α_{x,z,y} ∘ (cover id paws ∘ inl)
            = cover paws id ∘ from α_{x,z,y} ∘ (inl ∘ id)  [cover_inl]
            = cover paws id ∘ (inl ∘ inl)                  [assoc_from_inl]
            = (inl ∘ paws) ∘ inl                            [cover_inl]
            = inl ∘ inr                                     [paws_inl]    *)
    rewrite <- !comp_assoc.
    rewrite assoc_from_inl.
    rewrite (comp_assoc paws inl inl).
    rewrite paws_inl.
    rewrite assoc_from_inr_inl.
    symmetry.
    rewrite cover_inl, id_right.
    rewrite assoc_from_inl.
    rewrite (comp_assoc (cover paws id[y]) inl inl).
    rewrite cover_inl.
    rewrite <- (comp_assoc inl paws inl).
    rewrite paws_inl.
    reflexivity.
  - (* ∘ inr   need to further decompose y/z *)
    apply coprod_ext.
    + (* ∘ (inr ∘ inl)  (y-leg)
         LHS: from α_{z,x,y} ∘ paws ∘ (inl ∘ inr)    [assoc_from_inr_inl]
              = from α_{z,x,y} ∘ (paws ∘ inl) ∘ inr
              = from α_{z,x,y} ∘ (inr ∘ inr)         [paws_inl]
              = inr                                   [assoc_from_inr_inr]
         RHS: cover paws id ∘ from α_{x,z,y} ∘ (cover id paws ∘ (inr ∘ inl))
              = cover paws id ∘ from α_{x,z,y} ∘ (inr ∘ paws ∘ inl)   [cover_inr]
              = cover paws id ∘ from α_{x,z,y} ∘ (inr ∘ inr)          [paws_inl]
              = cover paws id ∘ inr                                    [assoc_from_inr_inr]
              = inr ∘ id                                              [cover_inr]
              = inr                                                                              *)
      rewrite <- !comp_assoc.
      rewrite assoc_from_inr_inl.
      rewrite (comp_assoc paws inl inr).
      rewrite paws_inl.
      rewrite assoc_from_inr_inr.
      symmetry.
      rewrite (comp_assoc (cover id[x] paws) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr paws inl).
      rewrite paws_inl.
      rewrite assoc_from_inr_inr.
      rewrite cover_inr, id_right.
      reflexivity.
    + (* ∘ (inr ∘ inr)  (z-leg)
         LHS: from α_{z,x,y} ∘ paws ∘ (inr)          [assoc_from_inr_inr]
              = from α_{z,x,y} ∘ (paws ∘ inr)
              = from α_{z,x,y} ∘ inl                  [paws_inr]
              = inl ∘ inl                              [assoc_from_inl]
         RHS: cover paws id ∘ from α_{x,z,y} ∘ (cover id paws ∘ (inr ∘ inr))
              = cover paws id ∘ from α_{x,z,y} ∘ (inr ∘ paws ∘ inr)   [cover_inr]
              = cover paws id ∘ from α_{x,z,y} ∘ (inr ∘ inl)          [paws_inr]
              = cover paws id ∘ (inl ∘ inr)                            [assoc_from_inr_inl]
              = (inl ∘ paws) ∘ inr                                     [cover_inl]
              = inl ∘ inl                                              [paws_inr]               *)
      rewrite <- !comp_assoc.
      rewrite assoc_from_inr_inr.
      rewrite paws_inr.
      rewrite assoc_from_inl.
      symmetry.
      rewrite (comp_assoc (cover id[x] paws) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr paws inr).
      rewrite paws_inr.
      rewrite assoc_from_inr_inl.
      rewrite (comp_assoc (cover paws id[y]) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl paws inr).
      rewrite paws_inr.
      reflexivity.
Qed.

(** ** Cospan-level braid naturality *)

Lemma cospan_braid_natural
      {x y z w : C}
      (f : CospanArrow x y) (h : CospanArrow z w) :
  cospan_equiv
    (cospan_compose HP (cospan_tensor h f)
                       (mor_as_cospan (paws : x + z ~{C}~> z + x)))
    (cospan_compose HP (mor_as_cospan (paws : y + w ~{C}~> w + y))
                       (cospan_tensor f h)).
Proof.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans;
    [apply (cospan_compose_mor_iso_left HP
              (cospan_tensor f h) (@coprod_comm C H_Coc y w))|].
  apply cospan_equiv_sym.
  unfold cospan_tensor; simpl.
  exists (@coprod_comm C H_Coc (cospan_apex h) (cospan_apex f)).
  simpl; split.
  - rewrite comp_assoc.
    rewrite cover_paws.
    rewrite <- comp_assoc.
    rewrite paws_invol.
    apply id_right.
  - apply cover_paws.
Defined.

(** ** [paws ∘ paws] lifted to cospans *)

Lemma cospan_braid_invol_C {x y : C} :
  cospan_equiv
    (cospan_compose HP (mor_as_cospan (paws : x + y ~{C}~> y + x))
                       (mor_as_cospan (paws : y + x ~{C}~> x + y)))
    (cospan_id (y + x)).
Proof.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_proper. apply paws_invol. }
  apply mor_as_cospan_id.
Defined.

(** ** Braided monoidal instance *)

#[export] Program Instance Cospan_BraidedMonoidal
  : @BraidedMonoidal (CospanCat C HP) := {|
  braided_is_monoidal := Cospan_Monoidal HP;
  braid := fun X Y => mor_as_cospan
              (@paws C H_Coc X Y : (@Coprod C H_Coc X Y) ~{C}~>
                                   (@Coprod C H_Coc Y X))
|}.
Next Obligation.
  (* braid_natural at arity 2. Recall:
     [cospan_compose_respects_aux] applied to [cospan_equiv (compose g f) (compose g' f')]
     leaves [Hf : f ≈ f'] FIRST then [Hg : g ≈ g'].

     Goal (cospan-equiv):
       cospan_compose HP (cospan_compose HP (h ⨂ id_y) (id_z ⨂ g)) paws
       ≈ cospan_compose HP (cospan_compose HP paws (id_y ⨂ h)) (g ⨂ id_z)

     Outer compose: g_outer = inner-compose, f_outer = paws_or_g_id_z. *)
  (* On LHS: outer is [compose (compose ...) paws], so f_outer = paws. We want to
     rewrite the inner [compose] (which is g_outer). Apply respects_aux with
     refl on f_outer (paws). *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.   (* f_outer : paws ≈ paws *)
    - apply cospan_equiv_sym.
      apply (cospan_tensor_compose_compat HP h (cospan_id z) (cospan_id y) g). }
  (* LHS is now: cospan_compose (cospan_tensor (h ∘ id_z) (id_y ∘ g)) paws. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.   (* f_outer : paws ≈ paws *)
    - apply cospan_tensor_respects.
      + apply cospan_id_right.
      + apply cospan_id_left. }
  (* LHS = cospan_compose (cospan_tensor h g) paws.  Now RHS. *)
  apply cospan_equiv_sym.
  (* RHS: outer compose is [compose (compose paws (id_y ⨂ h)) (g ⨂ id_z)].
     Reassociate to [compose paws (compose (id_y ⨂ h) (g ⨂ id_z))] via sym of
     cospan_compose_assoc paws (id_y⨂h) (g⨂id_z). *)
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym.
    apply (cospan_compose_assoc HP (mor_as_cospan paws)
             (cospan_tensor (cospan_id y) h) (cospan_tensor g (cospan_id z))). }
  (* Now it's cospan_compose paws (compose (id_y ⨂ h) (g ⨂ id_z)).
     We want to fuse the inner compose into a tensor of compositions. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_sym.
      apply (cospan_tensor_compose_compat HP (cospan_id y) g h (cospan_id z)).
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_id_left.
      + apply cospan_id_right.
    - apply cospan_equiv_refl. }
  (* RHS = cospan_compose paws (cospan_tensor g h).  Dispatch. *)
  apply cospan_equiv_sym.
  apply cospan_braid_natural.
Defined.
Next Obligation.
  (* hexagon_identity.
     Goal: cospan_compose (cospan_compose α paws) α
           ≈ cospan_compose (cospan_compose (id⨂paws) α) (paws⨂id)
     (composition is left-associated by Coq's [∘]).
     LHS: all mor_as_cospan. Outer-g = (compose α paws), outer-f = α.
     RHS: outer-g = (compose (id⨂paws) α), outer-f = (paws⨂id).        *)
  (* LHS: fuse the inner compose (mor_as_cospan α ∘ mor_as_cospan paws) → mor_as_cospan (α∘paws). *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.           (* Hf : α ≈ α *)
    - apply mor_as_cospan_compose. }     (* Hg : compose α paws ≈ mor_as_cospan (α ∘ paws) *)
  (* Now LHS = cospan_compose (mor_as_cospan (α∘paws)) (mor_as_cospan α).  Fuse. *)
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  (* Now on top: RHS. Reduce (cospan_id _) to (mor_as_cospan id). *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    (* outer-f = paws⨂id → cover paws id (as mor_as_cospan via tensor_mor_as_cospan) *)
    - apply cospan_tensor_respects.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_sym, mor_as_cospan_id.
    (* outer-g = compose (id⨂paws) α : nested *)
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.         (* inner-f : α *)
      + apply cospan_tensor_respects.    (* inner-g : id⨂paws *)
        * apply cospan_equiv_sym, mor_as_cospan_id.
        * apply cospan_equiv_refl. }
  (* All tensors are now of mor_as_cospans; fuse via cospan_tensor_mor_as_cospan. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_tensor_mor_as_cospan. }
  (* Now: compose (compose (mor_as_cospan (cover id paws)) α) (mor_as_cospan (cover paws id))
     Fuse the adjacent mor_as_cospan composes. *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  (* C-level goal:
       (α ∘ paws) ∘ α ≈ (cover id paws ∘ α) ∘ cover paws id
     Matches [coprod_hexagon_aux] up to symmetry. *)
  symmetry.
  apply coprod_hexagon_aux.
Defined.
Next Obligation.
  (* hexagon_identity_sym:
       Goal: cospan_compose (cospan_compose α⁻¹ paws) α⁻¹
             ≈ cospan_compose (cospan_compose (paws⨂id) α⁻¹) (id⨂paws)
     LHS: all mor_as_cospan (with α⁻¹ = mor_as_cospan (from α)). *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    (* outer-f = (id⨂paws) *)
    - apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl.
    (* outer-g = compose (paws⨂id) α⁻¹ *)
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_equiv_sym, mor_as_cospan_id. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  symmetry.
  apply coprod_hexagon_aux_from.
Defined.

(** ** Symmetric monoidal instance *)

#[export] Program Instance Cospan_SymmetricMonoidal
  : @SymmetricMonoidal (CospanCat C HP) := {|
  symmetric_is_braided := Cospan_BraidedMonoidal
|}.
Next Obligation.
  (* braid_invol : braid ∘ braid ≈ id  in CospanCat *)
  apply cospan_braid_invol_C.
Defined.

End CospanSymmetric.
