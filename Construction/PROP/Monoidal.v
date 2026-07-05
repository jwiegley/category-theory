Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Product.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Naturality.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The Monoidal structure on the free PROP *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   This file assembles THE [Monoidal] record on [FreeCat S]: the unit
   object is [0], the tensor is the parallel-composition bifunctor
   [FreeCat_Tensor] (addition on arities), and the structural
   isomorphisms are the [T_cast] isos of [Structural.v].  Every
   downstream instance on [FreeCat S] — Braided, Symmetric, Strict, and
   the bundled PROP — names this ONE record, so the strict/symmetric
   projections agree definitionally.

   The strict-PROP right-unit and associativity axioms of [TermEq] are
   stated in [eq_rect] transport form ([TE_tens_id0_right],
   [TE_tens_assoc]).  The [Monoidal] class instead wants naturality
   squares phrased through the [T_cast] structural maps.  The bridge
   lemmas below convert between the two spellings by quantifying over
   the arity equation and destructing it — which is exactly the
   generalisation that is unavailable once a fixed arity pins the
   transport proof (see the discussion at [Naturality.v]'s right-unit
   note).  With the bridges in hand, the previously-blocked right-unitor
   and associator naturality squares are ordinary consequences of the
   [TermEq] axioms.

   All proof fields of the record are supplied from standalone, named
   lemmas (the [Free.v] discipline), so no Program obligations are
   generated and successor files can reuse the very same lemmas. *)

Section FreeMonoidal.

Context (S : Signature).

Open Scope nat_scope.

(** ** Transport bridges: [eq_rect] spellings vs. [T_cast] composites

    A codomain transport is post-composition by the cast; a domain
    transport is pre-composition by the (inverted) cast.  Each proof
    destructs the arity equation, after which both sides collapse to
    an identity law of [TermEq]. *)

(** Codomain transport equals post-composition with [T_cast e]. *)
Lemma eq_rect_cod_cast {a b b' : nat} (e : b = b') (t : Term S a b) :
  TermEq S (eq_rect b (fun k => Term S a k) t b' e)
           (T_comp (T_cast e) t).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_left.
Qed.

(** Domain transport equals pre-composition with [T_cast (eq_sym e)]. *)
Lemma eq_rect_dom_cast {a a' b : nat} (e : a = a') (t : Term S a b) :
  TermEq S (eq_rect a (fun k => Term S k b) t a' e)
           (T_comp t (T_cast (eq_sym e))).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_right.
Qed.

(** Reverse-direction domain transport ([eq_rect_r]) equals
    pre-composition with [T_cast e] directly. *)
Lemma eq_rect_r_dom_cast {a a' b : nat} (e : a' = a) (t : Term S a b) :
  TermEq S (eq_rect_r (fun k => Term S k b) t e)
           (T_comp t (T_cast e)).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_right.
Qed.

(** Double [eq_sym] is invisible to [T_cast] (UIP on [nat]). *)
Lemma T_cast_sym_sym {m n : nat} (e : m = n) :
  T_cast (S:=S) (eq_sym (eq_sym e)) = T_cast e.
Proof. apply T_cast_irrelevant. Qed.

(** ** Cast shifting: moving a cast across a [TermEq] equation

    Solving [f ∘ cast ≈ g] for [f], and dually.  [cast_shift_l] and
    [cast_shift_r] are exported kit with no in-tree consumer yet: the
    from-direction naturality squares below are all derived through
    [cast_square_flip], which flips both casts of a square at once,
    rather than through these one-sided shifts. *)

Lemma cast_shift_l {a b c : nat} (e : a = b) (f : Term S b c) (g : Term S a c) :
  TermEq S (T_comp f (T_cast e)) g ->
  TermEq S f (T_comp g (T_cast (eq_sym e))).
Proof.
  destruct e; cbn; intros H.
  apply TE_trans with g.
  - apply TE_trans with (T_comp f (T_id a)).
    + apply TE_sym, TE_id_right.
    + exact H.
  - apply TE_sym, TE_id_right.
Qed.

Lemma cast_shift_r {a b c : nat} (e : b = c) (f : Term S a b) (g : Term S a c) :
  TermEq S (T_comp (T_cast e) f) g ->
  TermEq S f (T_comp (T_cast (eq_sym e)) g).
Proof.
  destruct e; cbn; intros H.
  apply TE_trans with g.
  - apply TE_trans with (T_comp (T_id b) f).
    + apply TE_sym, TE_id_left.
    + exact H.
  - apply TE_sym, TE_id_left.
Qed.

(** Flipping a naturality square along both casts: from
    [q ∘ cast ≈ cast ∘ p] conclude [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q].
    This turns every [to]-direction structural naturality square
    into its [from]-direction companion. *)
Lemma cast_square_flip {a b c d : nat} (e1 : a = b) (e2 : c = d)
      (p : Term S a c) (q : Term S b d) :
  TermEq S (T_comp q (T_cast e1)) (T_comp (T_cast e2) p) ->
  TermEq S (T_comp p (T_cast (eq_sym e1))) (T_comp (T_cast (eq_sym e2)) q).
Proof.
  destruct e1, e2; cbn; intros H.
  assert (Hqp : TermEq S q p).
  { apply TE_trans with (T_comp q (T_id a)).
    - apply TE_sym, TE_id_right.
    - apply TE_trans with (T_comp (T_id c) p).
      + exact H.
      + apply TE_id_left. }
  apply TE_trans with p.
  - apply TE_id_right.
  - apply TE_trans with q.
    + apply TE_sym, Hqp.
    + apply TE_sym, TE_id_left.
Qed.

(** ** Tensor fusion

    A tensor of morphisms decomposes as either sliding order of the
    two "half-identity" tensors; both composites fuse back to the
    plain tensor via the interchange law. *)

Lemma tens_fuse_l {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  TermEq S (T_comp (T_tens f (T_id d)) (T_tens (T_id a) g)) (T_tens f g).
Proof.
  apply TE_trans with (T_tens (T_comp f (T_id a)) (T_comp (T_id d) g)).
  - apply TE_interchange.
  - apply TE_tens_cong.
    + apply TE_id_right.
    + apply TE_id_left.
Qed.

Lemma tens_fuse_r {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  TermEq S (T_comp (T_tens (T_id b) g) (T_tens f (T_id c))) (T_tens f g).
Proof.
  apply TE_trans with (T_tens (T_comp (T_id b) f) (T_comp g (T_id c))).
  - apply TE_interchange.
  - apply TE_tens_cong.
    + apply TE_id_left.
    + apply TE_id_right.
Qed.

(** ** Right-unitor naturality in [T_cast] form

    The [to]-direction square [g ∘ ρ ≈ ρ ∘ (g ⊕ id₀)].  This is the
    statement [Naturality.v] could not derive at pinned arities; here
    the transport bridges convert [TE_tens_id0_right]'s [eq_rect]
    spelling wholesale. *)

Lemma right_unit_natural {x y : nat} (g : Term S x y) :
  TermEq S (T_comp g (T_cast (Nat.add_0_r x)))
           (T_comp (T_cast (Nat.add_0_r y)) (T_tens g (T_id 0))).
Proof.
  apply TE_sym.
  apply TE_trans with
    (eq_rect (y + 0) (fun k => Term S (x + 0) k)
             (T_tens g (T_id 0)) y (Nat.add_0_r y)).
  - apply TE_sym, eq_rect_cod_cast.
  - apply TE_trans with (eq_rect_r (fun k => Term S k y) g (Nat.add_0_r x)).
    + apply TE_tens_id0_right.
    + apply eq_rect_r_dom_cast.
Qed.

(** The [from]-direction square [(g ⊕ id₀) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]. *)
Lemma from_right_unit_natural {x y : nat} (g : Term S x y) :
  TermEq S (T_comp (T_tens g (T_id 0)) (T_cast (eq_sym (Nat.add_0_r x))))
           (T_comp (T_cast (eq_sym (Nat.add_0_r y))) g).
Proof.
  apply cast_square_flip, right_unit_natural.
Qed.

(** ** Associator naturality in [T_cast] form

    The [to]-direction square
      [(f ⊕ (g ⊕ h)) ∘ α ≈ α ∘ ((f ⊕ g) ⊕ h)],
    obtained from [TE_tens_assoc] through the transport bridges. *)

Lemma assoc_natural {m1 n1 m2 n2 m3 n3 : nat}
      (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (T_comp (T_tens f (T_tens g h)) (T_cast (eq_sym (Nat.add_assoc m1 m2 m3))))
    (T_comp (T_cast (eq_sym (Nat.add_assoc n1 n2 n3))) (T_tens (T_tens f g) h)).
Proof.
  apply TE_trans with
    (eq_rect_r (fun k => Term S k (n1 + (n2 + n3)))
               (T_tens f (T_tens g h))
               (eq_sym (Nat.add_assoc m1 m2 m3))).
  - apply TE_sym, eq_rect_r_dom_cast.
  - apply TE_trans with
      (eq_rect ((n1 + n2) + n3) (fun k => Term S ((m1 + m2) + m3) k)
               (T_tens (T_tens f g) h)
               (n1 + (n2 + n3))
               (eq_sym (Nat.add_assoc n1 n2 n3))).
    + apply TE_sym, TE_tens_assoc.
    + apply eq_rect_cod_cast.
Qed.

(** The [from]-direction square
      [((f ⊕ g) ⊕ h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕ (g ⊕ h))]. *)
Lemma from_assoc_natural {m1 n1 m2 n2 m3 n3 : nat}
      (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (T_comp (T_tens (T_tens f g) h) (T_cast (Nat.add_assoc m1 m2 m3)))
    (T_comp (T_cast (Nat.add_assoc n1 n2 n3)) (T_tens f (T_tens g h))).
Proof.
  rewrite <- (T_cast_sym_sym (Nat.add_assoc m1 m2 m3)).
  rewrite <- (T_cast_sym_sym (Nat.add_assoc n1 n2 n3)).
  apply cast_square_flip, assoc_natural.
Qed.

(** ** Triangle coherence

    [ρ ⊕ id ≈ (id ⊕ λ) ∘ α] on [(x + 0) + y].  Every arrow involved
    is a cast or an identity tensored with a cast, so both sides
    collapse to a single [T_cast] and UIP on [nat] closes the gap. *)

Lemma free_triangle (x y : nat) :
  TermEq S (T_tens (T_cast (Nat.add_0_r x)) (T_id y))
           (T_comp (T_tens (T_id x) (T_cast (Nat.add_0_l y)))
                   (T_cast (eq_sym (Nat.add_assoc x 0 y)))).
Proof.
  apply TE_trans with (T_cast (f_equal (fun k => k + y) (Nat.add_0_r x))).
  - apply T_tens_cast_id_right.
  - apply TE_sym.
    apply TE_trans with
      (T_comp (T_cast (f_equal (fun k => x + k) (Nat.add_0_l y)))
              (T_cast (eq_sym (Nat.add_assoc x 0 y)))).
    + apply TE_comp_cong.
      * apply T_tens_id_cast_left.
      * apply TE_refl.
    + apply TE_trans with
        (T_cast (eq_trans (eq_sym (Nat.add_assoc x 0 y))
                          (f_equal (fun k => x + k) (Nat.add_0_l y)))).
      * apply T_cast_compose.
      * rewrite (T_cast_irrelevant
                   (eq_trans (eq_sym (Nat.add_assoc x 0 y))
                             (f_equal (fun k => x + k) (Nat.add_0_l y)))
                   (f_equal (fun k => k + y) (Nat.add_0_r x))).
        apply TE_refl.
Qed.

(** ** Pentagon coherence

    [(id ⊕ α) ∘ α ∘ (α ⊕ id) ≈ α ∘ α] on [((x + y) + z) + w].  Same
    recipe as the triangle: collapse each tensor-with-identity via
    [CastTensor.v], fuse the compositions of casts via
    [T_cast_compose], and close with [T_cast_irrelevant]. *)

Lemma free_pentagon (x y z w : nat) :
  TermEq S
    (T_comp (T_comp (T_tens (T_id x) (T_cast (eq_sym (Nat.add_assoc y z w))))
                    (T_cast (eq_sym (Nat.add_assoc x (y + z) w))))
            (T_tens (T_cast (eq_sym (Nat.add_assoc x y z))) (T_id w)))
    (T_comp (T_cast (eq_sym (Nat.add_assoc x y (z + w))))
            (T_cast (eq_sym (Nat.add_assoc (x + y) z w)))).
Proof.
  apply TE_trans with
    (T_comp (T_comp (T_cast (f_equal (fun k => x + k)
                                     (eq_sym (Nat.add_assoc y z w))))
                    (T_cast (eq_sym (Nat.add_assoc x (y + z) w))))
            (T_cast (f_equal (fun k => k + w)
                             (eq_sym (Nat.add_assoc x y z))))).
  - apply TE_comp_cong.
    + apply TE_comp_cong.
      * apply T_tens_id_cast_left.
      * apply TE_refl.
    + apply T_tens_cast_id_right.
  - apply TE_trans with
      (T_comp (T_cast (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                (f_equal (fun k => x + k)
                                         (eq_sym (Nat.add_assoc y z w)))))
              (T_cast (f_equal (fun k => k + w)
                               (eq_sym (Nat.add_assoc x y z))))).
    + apply TE_comp_cong.
      * apply T_cast_compose.
      * apply TE_refl.
    + apply TE_trans with
        (T_cast (eq_trans (f_equal (fun k => k + w)
                                   (eq_sym (Nat.add_assoc x y z)))
                          (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                    (f_equal (fun k => x + k)
                                             (eq_sym (Nat.add_assoc y z w)))))).
      * apply T_cast_compose.
      * apply TE_sym.
        apply TE_trans with
          (T_cast (eq_trans (eq_sym (Nat.add_assoc (x + y) z w))
                            (eq_sym (Nat.add_assoc x y (z + w))))).
        -- apply T_cast_compose.
        -- rewrite (T_cast_irrelevant
                      (eq_trans (eq_sym (Nat.add_assoc (x + y) z w))
                                (eq_sym (Nat.add_assoc x y (z + w))))
                      (eq_trans (f_equal (fun k => k + w)
                                         (eq_sym (Nat.add_assoc x y z)))
                                (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                          (f_equal (fun k => x + k)
                                                   (eq_sym (Nat.add_assoc y z w)))))).
           apply TE_refl.
Qed.

(** ** THE shared Monoidal record on [FreeCat S]

    All fields explicit, no Program obligations.  The Braided,
    Symmetric, Strict, and PROP instances downstream all project this
    single record, so their agreement is definitional. *)

Program Definition FreeCat_Monoidal : @Monoidal (FreeCat S) := {|
  I            := 0;
  tensor       := FreeCat_Tensor S;
  unit_left    := fun x => FreeCat_unit_left S x;
  unit_right   := fun x => FreeCat_unit_right S x;
  tensor_assoc := fun x y z => FreeCat_tensor_assoc S x y z;
  to_unit_left_natural      := fun x y g => left_unit_natural S g;
  from_unit_left_natural    := fun x y g => left_unit_natural_from S g;
  to_unit_right_natural     := fun x y g => right_unit_natural g;
  from_unit_right_natural   := fun x y g => from_right_unit_natural g;
  to_tensor_assoc_natural   := fun _ _ _ _ _ _ g h i => assoc_natural g h i;
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i => from_assoc_natural g h i;
  triangle_identity := fun x y => free_triangle x y;
  pentagon_identity := fun x y z w => free_pentagon x y z w
|}.

End FreeMonoidal.

Arguments FreeCat_Monoidal S : assert.
