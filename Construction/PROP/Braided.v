Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The braided monoidal structure on the free PROP *)

(* nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   This file equips THE shared [Monoidal] record on [FreeCat S] — the
   [FreeCat_Monoidal S] of [Construction/PROP/Monoidal.v] — with the
   block braiding [T_braid m n], which crosses an [m]-wide bundle of
   wires past an [n]-wide bundle, yielding the [BraidedMonoidal]
   instance on the free PROP.  Downstream, the Symmetric, Strict and
   bundled PROP instances all project this single Monoidal record, so
   their agreement is definitional.

   Three proof fields are needed beyond the braid itself (writing
   [⊙ = T_comp], [⊕ = T_tens], [σ = T_braid], and [α] for the
   associator casts of [Structural.v]):

     - [braid_natural], the joint naturality square in the [ArityTwo]
       form of [Theory/Naturality.v]: for [g : x ⇒ y], [h : z ⇒ w],

         (h ⊕ id_y) ⊙ (id_z ⊕ g) ⊙ σ_{x,z}
           ≈ σ_{y,w} ⊙ (id_y ⊕ h) ⊙ (g ⊕ id_z).

       Fusing the adjacent half-identity tensors on each side
       ([tens_fuse_l] / [tens_fuse_r]) reduces the square to the
       primitive constructor [TE_braid_natural].  (The synonym lemma
       in [Construction/PROP/Naturality.v] is deliberately not
       imported here: its name [braid_natural] would shadow the
       [BraidedMonoidal] projection of the same name in the record
       literal below.)

     - [hexagon_identity], braiding [x] past the tensor [y ⨂ z]:

         α_{y,z,x} ⊙ σ_{x,y+z} ⊙ α_{x,y,z}
           ≈ (id_y ⊕ σ_{x,z}) ⊙ α_{y,x,z} ⊙ (σ_{x,y} ⊕ id_z).

       Its source is the [TE_braid_hex_right] axiom of [TermEq],
       stated there in [eq_rect] transport form; the transport
       bridges of [Construction/PROP/Monoidal.v] ([eq_rect_cod_cast],
       [eq_rect_dom_cast], [T_cast_sym_sym]) rewrite every transport
       as composition with a [T_cast], and one inverse-cast
       cancellation ([T_cast_inv_sym]) aligns the result with the
       class field.

     - [hexagon_identity_sym], braiding the tensor [x ⨂ y] past [z]
       along the inverse associators: the same recipe applied to
       [TE_braid_hex_left].

   All proof fields of the record are supplied from standalone, named
   lemmas (the [Free.v] discipline), so no Program obligations are
   generated and successor files — Symmetric, the bundled PROP
   instance, and the presentation layer — can reuse the very same
   lemmas. *)

Section FreeBraided.

Context (S : Signature).

Open Scope nat_scope.

(** ** Braid naturality in [ArityTwo] form

    The [braid_natural] field of [BraidedMonoidal] unfolds, through
    the [Mapping] instances of [Structure/Monoidal/Naturality.v], to
    the square below: each side tensors one morphism against a
    half-identity before composing with the braid.  [tens_fuse_l]
    collapses the left-hand pair to [h ⊕ g] and [tens_fuse_r] the
    right-hand pair to [g ⊕ h], after which the square is exactly
    [TE_braid_natural]. *)

Lemma free_braid_square {x y z w : nat} (g : Term S x y) (h : Term S z w) :
  TermEq S
    (T_comp (T_comp (T_tens h (T_id y)) (T_tens (T_id z) g)) (T_braid x z))
    (T_comp (T_comp (T_braid y w) (T_tens (T_id y) h)) (T_tens g (T_id z))).
Proof.
  apply TE_trans with (T_comp (T_tens h g) (T_braid x z)).
  - apply TE_comp_cong.
    + apply tens_fuse_l.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_braid y w) (T_tens g h)).
    + apply TE_braid_natural.
    + apply TE_sym.
      apply TE_trans with
        (T_comp (T_braid y w)
                (T_comp (T_tens (T_id y) h) (T_tens g (T_id z)))).
      * apply TE_assoc.
      * apply TE_comp_cong.
        -- apply TE_refl.
        -- apply tens_fuse_r.
Qed.

(** ** The right hexagon in [T_cast] form

    [TE_braid_hex_right x y z] asserts the hexagon for [σ_{x,y+z}]
    with its arity mismatches carried by [eq_rect] transports over
    [Nat.add_assoc] equations.  Converting the codomain transport on
    the left-hand side by [eq_rect_cod_cast] and the two domain
    transports on the right-hand side by [eq_rect_dom_cast] (plus
    [T_cast_sym_sym] to erase a double [eq_sym]) restates the axiom
    purely in terms of [T_cast] composites. *)

Lemma braid_hex_right_cast (x y z : nat) :
  TermEq S
    (T_comp (T_cast (eq_sym (Nat.add_assoc y z x))) (T_braid x (y + z)))
    (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                    (T_cast (eq_sym (Nat.add_assoc y x z))))
            (T_comp (T_tens (T_braid x y) (T_id z))
                    (T_cast (Nat.add_assoc x y z)))).
Proof.
  apply TE_trans with
    (eq_rect ((y + z) + x)
             (fun t => Term S (x + (y + z)) t)
             (T_braid x (y + z))
             (y + (z + x))
             (eq_sym (Nat.add_assoc y z x))).
  - apply TE_sym, eq_rect_cod_cast.
  - apply TE_trans with
      (T_comp
         (eq_rect (y + (x + z))
                  (fun s => Term S s (y + (z + x)))
                  (T_tens (T_id y) (T_braid x z))
                  ((y + x) + z)
                  (Nat.add_assoc y x z))
         (eq_rect ((x + y) + z)
                  (fun s => Term S s ((y + x) + z))
                  (T_tens (T_braid x y) (T_id z))
                  (x + (y + z))
                  (eq_sym (Nat.add_assoc x y z)))).
    + apply TE_braid_hex_right.
    + apply TE_comp_cong.
      * apply eq_rect_dom_cast.
      * rewrite <- (T_cast_sym_sym S (Nat.add_assoc x y z)).
        apply eq_rect_dom_cast.
Qed.

(** ** First hexagon identity

    The [hexagon_identity] field of [BraidedMonoidal] at [x y z],
    with every associator spelled as the [T_cast] of the matching
    [Nat.add_assoc] equation (the [to] direction is the [eq_sym]
    cast, per [FreeCat_tensor_assoc]).  Post-composing both sides of
    [braid_hex_right_cast] with the incoming associator and
    cancelling the resulting cast-inverse pair by [T_cast_inv_sym]
    yields the class field verbatim. *)

Lemma free_hexagon (x y z : nat) :
  TermEq S
    (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc y z x)))
                    (T_braid x (y + z)))
            (T_cast (eq_sym (Nat.add_assoc x y z))))
    (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                    (T_cast (eq_sym (Nat.add_assoc y x z))))
            (T_tens (T_braid x y) (T_id z))).
Proof.
  apply TE_trans with
    (T_comp (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                            (T_cast (eq_sym (Nat.add_assoc y x z))))
                    (T_comp (T_tens (T_braid x y) (T_id z))
                            (T_cast (Nat.add_assoc x y z))))
            (T_cast (eq_sym (Nat.add_assoc x y z)))).
  - apply TE_comp_cong.
    + apply braid_hex_right_cast.
    + apply TE_refl.
  - apply TE_trans with
      (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                      (T_cast (eq_sym (Nat.add_assoc y x z))))
              (T_comp (T_comp (T_tens (T_braid x y) (T_id z))
                              (T_cast (Nat.add_assoc x y z)))
                      (T_cast (eq_sym (Nat.add_assoc x y z))))).
    + apply TE_assoc.
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_trans with
          (T_comp (T_tens (T_braid x y) (T_id z))
                  (T_comp (T_cast (Nat.add_assoc x y z))
                          (T_cast (eq_sym (Nat.add_assoc x y z))))).
        -- apply TE_assoc.
        -- apply TE_trans with
             (T_comp (T_tens (T_braid x y) (T_id z))
                     (T_id ((x + y) + z))).
           ++ apply TE_comp_cong.
              ** apply TE_refl.
              ** apply T_cast_inv_sym.
           ++ apply TE_id_right.
Qed.

(** ** The left hexagon in [T_cast] form

    Mirror bridge: [TE_braid_hex_left x y z] is the hexagon for
    [σ_{x+y,z}], and its transports convert by the same three
    bridges.  Here the inverse associators appear, so the casts are
    the forward [Nat.add_assoc] equations (the [from] direction of
    [FreeCat_tensor_assoc]). *)

Lemma braid_hex_left_cast (x y z : nat) :
  TermEq S
    (T_comp (T_braid (x + y) z) (T_cast (Nat.add_assoc x y z)))
    (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                    (T_comp (T_tens (T_braid x z) (T_id y))
                            (T_cast (Nat.add_assoc x z y))))
            (T_tens (T_id x) (T_braid y z))).
Proof.
  apply TE_trans with
    (eq_rect ((x + y) + z)
             (fun s => Term S s (z + (x + y)))
             (T_braid (x + y) z)
             (x + (y + z))
             (eq_sym (Nat.add_assoc x y z))).
  - apply TE_sym.
    rewrite <- (T_cast_sym_sym S (Nat.add_assoc x y z)).
    apply eq_rect_dom_cast.
  - apply TE_trans with
      (T_comp
         (eq_rect ((z + x) + y)
                  (fun t => Term S (x + (z + y)) t)
                  (eq_rect ((x + z) + y)
                           (fun s => Term S s ((z + x) + y))
                           (T_tens (T_braid x z) (T_id y))
                           (x + (z + y))
                           (eq_sym (Nat.add_assoc x z y)))
                  (z + (x + y))
                  (eq_sym (Nat.add_assoc z x y)))
         (T_tens (T_id x) (T_braid y z))).
    + apply TE_braid_hex_left.
    + apply TE_comp_cong.
      * apply TE_trans with
          (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                  (eq_rect ((x + z) + y)
                           (fun s => Term S s ((z + x) + y))
                           (T_tens (T_braid x z) (T_id y))
                           (x + (z + y))
                           (eq_sym (Nat.add_assoc x z y)))).
        -- apply eq_rect_cod_cast.
        -- apply TE_comp_cong.
           ++ apply TE_refl.
           ++ rewrite <- (T_cast_sym_sym S (Nat.add_assoc x z y)).
              apply eq_rect_dom_cast.
      * apply TE_refl.
Qed.

(** ** Second hexagon identity

    The [hexagon_identity_sym] field of [BraidedMonoidal] at [x y z],
    phrased through the inverse associators.  Pre-composing both
    sides of [braid_hex_left_cast] with the outgoing inverse
    associator [T_cast (Nat.add_assoc z x y)], reassociating, and
    cancelling the cast-inverse pair by [T_cast_inv_sym] gives the
    class field. *)

Lemma free_hexagon_sym (x y z : nat) :
  TermEq S
    (T_comp (T_comp (T_cast (Nat.add_assoc z x y)) (T_braid (x + y) z))
            (T_cast (Nat.add_assoc x y z)))
    (T_comp (T_comp (T_tens (T_braid x z) (T_id y))
                    (T_cast (Nat.add_assoc x z y)))
            (T_tens (T_id x) (T_braid y z))).
Proof.
  apply TE_trans with
    (T_comp (T_cast (Nat.add_assoc z x y))
            (T_comp (T_braid (x + y) z) (T_cast (Nat.add_assoc x y z)))).
  - apply TE_assoc.
  - apply TE_trans with
      (T_comp (T_cast (Nat.add_assoc z x y))
              (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                              (T_comp (T_tens (T_braid x z) (T_id y))
                                      (T_cast (Nat.add_assoc x z y))))
                      (T_tens (T_id x) (T_braid y z)))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply braid_hex_left_cast.
    + apply TE_trans with
        (T_comp (T_comp (T_cast (Nat.add_assoc z x y))
                        (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                                (T_comp (T_tens (T_braid x z) (T_id y))
                                        (T_cast (Nat.add_assoc x z y)))))
                (T_tens (T_id x) (T_braid y z))).
      * apply TE_sym, TE_assoc.
      * apply TE_comp_cong.
        -- apply TE_trans with
             (T_comp (T_comp (T_cast (Nat.add_assoc z x y))
                             (T_cast (eq_sym (Nat.add_assoc z x y))))
                     (T_comp (T_tens (T_braid x z) (T_id y))
                             (T_cast (Nat.add_assoc x z y)))).
           ++ apply TE_sym, TE_assoc.
           ++ apply TE_trans with
                (T_comp (T_id ((z + x) + y))
                        (T_comp (T_tens (T_braid x z) (T_id y))
                                (T_cast (Nat.add_assoc x z y)))).
              ** apply TE_comp_cong.
                 --- apply T_cast_inv_sym.
                 --- apply TE_refl.
              ** apply TE_id_left.
        -- apply TE_refl.
Qed.

(** ** THE BraidedMonoidal record on [FreeCat S]

    [braided_is_monoidal] names the ONE shared [Monoidal] record
    [FreeCat_Monoidal S]; the braid is [T_braid] (recall that on
    objects the tensor is [Nat.add], so [m ⨂ n] and [m + n] agree
    definitionally); all proof fields are the standalone lemmas
    above.  Every field is explicit, so no Program obligations are
    generated. *)

Program Definition FreeCat_Braided : @BraidedMonoidal (FreeCat S) := {|
  braided_is_monoidal := FreeCat_Monoidal S;
  braid := fun m n => T_braid m n;
  braid_natural := fun x y g z w h => free_braid_square g h;
  hexagon_identity := fun x y z => free_hexagon x y z;
  hexagon_identity_sym := fun x y z => free_hexagon_sym x y z
|}.

End FreeBraided.

Arguments FreeCat_Braided S : assert.
