Require Import Category.Lib.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * The Monoidal structure on the free coloured PROP *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   This file assembles THE [Monoidal] record on [CFreeCat S]: the unit
   object is the empty colour word [[]], the tensor is the
   parallel-composition bifunctor [CFreeCat_Tensor] (concatenation on
   colour words), and the structural isomorphisms are the [CT_cast]
   isos of [Construction/ColouredPROP/Cast.v].  Every downstream
   instance on [CFreeCat S] — Braided, Symmetric, Strict, and the
   bundled coloured PROP of [Instance.v] — names this ONE record, so
   the strict/symmetric projections agree definitionally, and the
   [cprop_monoidal_coherence] field of [Construction/ColouredPROP.v]'s
   class can be discharged by [eq_refl].

   The strict-PROP right-unit and associativity axioms of
   [CTermEq] are stated in [eq_rect] transport form
   ([CTE_tens_id0_right], [CTE_tens_assoc]).  The [Monoidal] class
   instead wants naturality squares phrased through the [CT_cast]
   structural maps.  The bridge lemmas below convert between the two
   spellings by quantifying over the boundary equation and destructing
   it — which is exactly the generalisation that is unavailable once a
   fixed colour word pins the transport proof (see the right-unit note
   below, ported from the one-sorted donor's [Naturality.v]).  With
   the bridges in hand, the previously-blocked right-unitor and
   associator naturality squares are ordinary consequences of the
   [CTermEq] axioms.

   This file merges the one-sorted spine's donor pair
   [Construction/PROP/Naturality.v] + [Construction/PROP/Monoidal.v]:
   the naturality bank and the record that consumes it live together,
   the same layout compression as [Free.v] (Free + Tensor) and
   [Cast.v] (Cast + CastTensor + Structural).

   Decidability discipline (design decision D2): the boundary
   equations live on [list Colour], which has UIP only when [Colour]
   has decidable equality.  Every lemma below whose proof invokes the
   UIP layer of [Cast.v] ([CT_cast_id] / [CT_cast_irrelevant]) is
   conditional on the section decider [Cdec], carries an explicit
   [Proof using] clause naming it, and abstracts over it on section
   close.  The UIP-free majority (transport bridges, cast shifting,
   tensor fusion, the right-unit and associator naturality squares)
   needs no decidability at all.

   All proof fields of the record are supplied from standalone, named
   lemmas (the [Free.v] discipline), so no Program obligations are
   generated and successor files can reuse the very same lemmas. *)

Section CFreeMonoidal.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(** ** Transport bridges: [eq_rect] spellings vs. [CT_cast] composites

    A codomain transport is post-composition by the cast; a domain
    transport is pre-composition by the (inverted) cast.  Each proof
    destructs the boundary equation, after which both sides collapse
    to an identity law of [CTermEq].  No decidability is involved. *)

(** Codomain transport equals post-composition with [CT_cast e]. *)
Lemma ceq_rect_cod_cast {a b b' : list Colour}
  (t : CTerm S a b) (e : b = b') :
  CTermEq S (eq_rect b (fun k => CTerm S a k) t b' e)
            (CT_comp (CT_cast e) t).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_left.
Qed.

(** Domain transport equals pre-composition with [CT_cast (eq_sym e)]. *)
Lemma ceq_rect_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a = a') :
  CTermEq S (eq_rect a (fun k => CTerm S k b) t a' e)
            (CT_comp t (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(** Reverse-direction domain transport ([eq_rect_r]) equals
    pre-composition with [CT_cast e] directly. *)
Lemma ceq_rect_r_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a' = a) :
  CTermEq S (eq_rect_r (fun k => CTerm S k b) t e)
            (CT_comp t (CT_cast e)).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(** Double [eq_sym] is invisible to [CT_cast].  Unlike the one-sorted
    donor (which went through UIP on [nat]), destructing the equation
    closes this by reflexivity, so the lemma is decidability-free. *)
Lemma CT_cast_sym_sym {cs ds : list Colour} (e : cs = ds) :
  CT_cast (S := S) (eq_sym (eq_sym e)) = CT_cast e.
Proof. destruct e; reflexivity. Qed.

(** ** Cast shifting: moving a cast across a [CTermEq] equation

    Solving [f ∘ cast ≈ g] for [f], and dually.  [ccast_shift_l] and
    [ccast_shift_r] are exported kit with no in-tree consumer yet: the
    from-direction naturality squares below are all derived through
    [ccast_square_flip], which flips both casts of a square at once,
    rather than through these one-sided shifts. *)

Lemma ccast_shift_l {a b c : list Colour} (e : a = b)
  (f : CTerm S b c) (g : CTerm S a c) :
  CTermEq S (CT_comp f (CT_cast e)) g ->
  CTermEq S f (CT_comp g (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp f (CT_id a)).
    + apply CTE_sym, CTE_id_right.
    + exact H.
  - apply CTE_sym, CTE_id_right.
Qed.

Lemma ccast_shift_r {a b c : list Colour} (e : b = c)
  (f : CTerm S a b) (g : CTerm S a c) :
  CTermEq S (CT_comp (CT_cast e) f) g ->
  CTermEq S f (CT_comp (CT_cast (eq_sym e)) g).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp (CT_id b) f).
    + apply CTE_sym, CTE_id_left.
    + exact H.
  - apply CTE_sym, CTE_id_left.
Qed.

(** Flipping a naturality square along both casts: from
    [q ∘ cast ≈ cast ∘ p] conclude [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q].
    This turns every [to]-direction structural naturality square
    into its [from]-direction companion. *)
Lemma ccast_square_flip {a b c d : list Colour} (e1 : a = b) (e2 : c = d)
  (p : CTerm S a c) (q : CTerm S b d) :
  CTermEq S (CT_comp q (CT_cast e1)) (CT_comp (CT_cast e2) p) ->
  CTermEq S (CT_comp p (CT_cast (eq_sym e1))) (CT_comp (CT_cast (eq_sym e2)) q).
Proof.
  destruct e1, e2; cbn; intros H.
  assert (Hqp : CTermEq S q p).
  { apply CTE_trans with (CT_comp q (CT_id a)).
    - apply CTE_sym, CTE_id_right.
    - apply CTE_trans with (CT_comp (CT_id c) p).
      + exact H.
      + apply CTE_id_left. }
  apply CTE_trans with p.
  - apply CTE_id_right.
  - apply CTE_trans with q.
    + apply CTE_sym, Hqp.
    + apply CTE_sym, CTE_id_left.
Qed.

(** ** Tensor fusion

    A tensor of morphisms decomposes as either sliding order of the
    two "half-identity" tensors; both composites fuse back to the
    plain tensor via the interchange law. *)

Lemma ctens_fuse_l {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens f (CT_id d)) (CT_tens (CT_id a) g))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp f (CT_id a)) (CT_comp (CT_id d) g)).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_right.
    + apply CTE_id_left.
Qed.

Lemma ctens_fuse_r {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens (CT_id b) g) (CT_tens f (CT_id c)))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp (CT_id b) f) (CT_comp g (CT_id c))).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_left.
    + apply CTE_id_right.
Qed.

(** ** Left-unitor naturality in [CT_cast] form

    Goal (in [CFreeCat S]):
      g ∘ unit_left ≈ unit_left ∘ bimap id g
    expanded to [CTerm]:
      g ⊙c CT_cast (app_nil_l x) ≈ CT_cast (app_nil_l y) ⊙c (CT_id [] ⊕c g)

    [app_nil_l x : [] ++ x = x] is an OPAQUE stdlib proof of a
    DEFINITIONAL equation ([app] is left-strict, like [Nat.add]), so
    the cast does not reduce by computation; [CT_cast_id] (UIP on
    colour words, hence [Cdec]-conditional) rewrites it to the literal
    identity, after which the strict left-unit axiom
    [CTE_tens_id0_left] closes the square. *)

Lemma cleft_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_l x)))
            (CT_comp (CT_cast (app_nil_l y)) (CT_tens (CT_id []) g)).
Proof using Cdec.
  rewrite (CT_cast_id Cdec (app_nil_l x)).
  rewrite (CT_cast_id Cdec (app_nil_l y)).
  apply CTE_trans with g.
  - apply CTE_id_right.
  - apply CTE_sym.
    apply CTE_trans with (CT_tens (CT_id []) g).
    + apply CTE_id_left.
    + apply CTE_tens_id0_left.
Qed.

(** The [from]-direction square [bimap id g ∘ λ⁻¹ ≈ λ⁻¹ ∘ g], obtained
    by flipping the [to]-direction square through [ccast_square_flip];
    the [Cdec] dependency is inherited from [cleft_unit_natural]. *)
Lemma cleft_unit_natural_from {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens (CT_id []) g) (CT_cast (eq_sym (app_nil_l x))))
            (CT_comp (CT_cast (eq_sym (app_nil_l y))) g).
Proof using Cdec.
  apply ccast_square_flip, cleft_unit_natural.
Qed.

(** ** Simple corollaries of the strict-unit axioms *)

(** Tensoring an identity with [CT_id []] on the left collapses to a
    single identity term. *)
Lemma ctens_id0_id (n : list Colour) :
  CTermEq S (CT_tens (CT_id []) (CT_id n)) (CT_id n).
Proof. apply CTE_tens_id0_left. Qed.

(** Repeated tensor of [CT_id []] on the left is still [CT_id []]. *)
Lemma ctens_id0_id0 :
  CTermEq S (CT_tens (CT_id []) (CT_id [])) (CT_id []).
Proof. apply CTE_tens_id0_left. Qed.

(** ** Strict-PROP right-unit at the [CT_cast] level

    [CTE_tens_id0_right] states the right-unit law in [eq_rect]
    transport form.  We can extract its content as a [CT_cast]
    sandwich: pre/post-composing by appropriate casts gives a direct
    [CT_tens f (CT_id []) ↔ f]-style equation. *)

(* Note (ported from the one-sorted donor's [Naturality.v]): a clean
   [CT_cast]-form right-unit lemma — bridging [CTE_tens_id0_right]'s
   [eq_rect] transport form to a sandwiched [CT_cast] composition at a
   FIXED boundary — requires generalising over the right-summand
   word, which Coq cannot do while [f]'s type pins it.  This is a
   known limitation of the [CTE_tens_id0_right] axiom's [eq_rect]
   form when consumed pointwise.  For downstream use, prefer
   [CTE_tens_id0_left] (definitional case) and work with the
   right-unit case ONLY when the boundary is syntactically known — or
   go through the transport bridges above, which quantify over the
   boundary equation first and therefore CAN destruct it; that is
   precisely how [cright_unit_natural] below succeeds where the
   pointwise approach stalls.

   Like [ccast_shift_l]/[ccast_shift_r] above, the three pointwise
   lemmas that follow ([ctens_id0_right_at_0], [ctens_id0_right_at],
   [ctens_assoc_at]) are exported kit with no in-tree consumer: every
   naturality square below is derived through the transport bridges
   instead.  They are kept as the record of what the pointwise route
   does reach. *)

(** ** Right-unit at the trivial boundary ([[] ++ [] = []])

    When both boundaries are empty, the transport in
    [CTE_tens_id0_right] is along [app_nil_r []], an opaque proof of
    a definitional equation; UIP on colour words (via [Cdec]) rewrites
    it to [eq_refl], after which the [eq_rect] collapses by
    computation. *)

Lemma ctens_id0_right_at_0 (f : CTerm S [] []) :
  CTermEq S (CT_tens f (CT_id [])) f.
Proof using Cdec.
  pose proof (CTE_tens_id0_right f) as Hr.
  unfold eq_rect_r in Hr.
  rewrite (UIP_dec (list_eq_dec Cdec)
             (app_nil_r (@nil Colour)) eq_refl) in Hr.
  cbn in Hr.
  exact Hr.
Qed.

(** ** Boundary-specialised right-unit at any concrete boundaries *)

Lemma ctens_id0_right_at {m n : list Colour} (f : CTerm S m n) :
  CTermEq S
    (eq_rect (n ++ []) (fun k => CTerm S (m ++ []) k)
             (CT_tens f (CT_id [])) n (app_nil_r n))
    (eq_rect_r (fun k => CTerm S k n) f (app_nil_r m)).
Proof. exact (CTE_tens_id0_right f). Qed.

(** ** Tensor-associativity at any concrete boundaries *)

Lemma ctens_assoc_at {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (eq_rect ((n1 ++ n2) ++ n3)
             (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
             (CT_tens (CT_tens f g) h)
             (n1 ++ (n2 ++ n3))
             (eq_sym (app_assoc n1 n2 n3)))
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
Proof. exact (CTE_tens_assoc f g h). Qed.

(** ** Right-unitor naturality in [CT_cast] form

    The [to]-direction square [g ∘ ρ ≈ ρ ∘ (g ⊕c id_[])].  This is
    the statement the pointwise approach in the note above could not
    reach at pinned boundaries; here the transport bridges convert
    [CTE_tens_id0_right]'s [eq_rect] spelling wholesale, with no UIP
    involved. *)

Lemma cright_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_r x)))
            (CT_comp (CT_cast (app_nil_r y)) (CT_tens g (CT_id []))).
Proof.
  apply CTE_sym.
  apply CTE_trans with
    (eq_rect (y ++ []) (fun k => CTerm S (x ++ []) k)
             (CT_tens g (CT_id [])) y (app_nil_r y)).
  - apply CTE_sym, ceq_rect_cod_cast.
  - apply CTE_trans with (eq_rect_r (fun k => CTerm S k y) g (app_nil_r x)).
    + apply CTE_tens_id0_right.
    + apply ceq_rect_r_dom_cast.
Qed.

(** The [from]-direction square [(g ⊕c id_[]) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]. *)
Lemma cfrom_right_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens g (CT_id [])) (CT_cast (eq_sym (app_nil_r x))))
            (CT_comp (CT_cast (eq_sym (app_nil_r y))) g).
Proof.
  apply ccast_square_flip, cright_unit_natural.
Qed.

(** ** Associator naturality in [CT_cast] form

    The [to]-direction square
      [(f ⊕c (g ⊕c h)) ∘ α ≈ α ∘ ((f ⊕c g) ⊕c h)],
    obtained from [CTE_tens_assoc] through the transport bridges.
    Recall the stdlib orientation [app_assoc x y z :
    x ++ y ++ z = (x ++ y) ++ z], so the associator's [to] direction
    is the [eq_sym] cast (see [CFreeCat_tensor_assoc] in [Cast.v]). *)

Lemma cassoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens f (CT_tens g h))
             (CT_cast (eq_sym (app_assoc m1 m2 m3))))
    (CT_comp (CT_cast (eq_sym (app_assoc n1 n2 n3)))
             (CT_tens (CT_tens f g) h)).
Proof.
  apply CTE_trans with
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
  - apply CTE_sym, ceq_rect_r_dom_cast.
  - apply CTE_trans with
      (eq_rect ((n1 ++ n2) ++ n3)
               (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
               (CT_tens (CT_tens f g) h)
               (n1 ++ (n2 ++ n3))
               (eq_sym (app_assoc n1 n2 n3))).
    + apply CTE_sym, CTE_tens_assoc.
    + apply ceq_rect_cod_cast.
Qed.

(** The [from]-direction square
      [((f ⊕c g) ⊕c h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕c (g ⊕c h))]. *)
Lemma cfrom_assoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens (CT_tens f g) h) (CT_cast (app_assoc m1 m2 m3)))
    (CT_comp (CT_cast (app_assoc n1 n2 n3)) (CT_tens f (CT_tens g h))).
Proof.
  rewrite <- (CT_cast_sym_sym (app_assoc m1 m2 m3)).
  rewrite <- (CT_cast_sym_sym (app_assoc n1 n2 n3)).
  apply ccast_square_flip, cassoc_natural.
Qed.

(* Note on braid lemmas: the one-sorted donor's [Naturality.v] also
   re-exported [TE_braid_natural] / [TE_braid_invol] under the
   friendly names [braid_natural] / [braid_invol].  The coloured
   spine deliberately does NOT define such synonyms here:
   [Braided.v], the sole would-be consumer, works with the
   [CTE_braid_*] constructors directly, and re-exported synonyms in
   this file would shadow the donor's names for any file importing
   both spines (the one-sorted PROP files of [Construction/PROP/]
   likewise decline to import [Naturality.v]'s synonyms, for the same
   reason).  This comment records the decision. *)

(** ** Triangle coherence

    [ρ ⊕c id ≈ (id ⊕c λ) ∘ α] on [(x ++ []) ++ y].  Every arrow
    involved is a cast or an identity tensored with a cast, so both
    sides collapse to a single [CT_cast] via the tensor-cast fusion
    kit of [Cast.v] and [CT_cast_compose], and UIP on colour words
    (via [Cdec]) closes the gap between the two boundary proofs. *)

Lemma cfree_triangle (x y : list Colour) :
  CTermEq S (CT_tens (CT_cast (app_nil_r x)) (CT_id y))
            (CT_comp (CT_tens (CT_id x) (CT_cast (app_nil_l y)))
                     (CT_cast (eq_sym (app_assoc x [] y)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_cast (f_equal (fun ks => ks ++ y) (app_nil_r x))).
  - apply CT_tens_cast_id_right.
  - apply CTE_sym.
    apply CTE_trans with
      (CT_comp (CT_cast (f_equal (fun ks => x ++ ks) (app_nil_l y)))
               (CT_cast (eq_sym (app_assoc x [] y)))).
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (eq_sym (app_assoc x [] y))
                           (f_equal (fun ks => x ++ ks) (app_nil_l y)))).
      * apply CT_cast_compose.
      * rewrite (CT_cast_irrelevant Cdec
                   (eq_trans (eq_sym (app_assoc x [] y))
                             (f_equal (fun ks => x ++ ks) (app_nil_l y)))
                   (f_equal (fun ks => ks ++ y) (app_nil_r x))).
        apply CTE_refl.
Qed.

(** ** Pentagon coherence

    [(id ⊕c α) ∘ α ∘ (α ⊕c id) ≈ α ∘ α] on [((x ++ y) ++ z) ++ w].
    Same recipe as the triangle: collapse each tensor-with-identity
    via the tensor-cast fusion kit, fuse the compositions of casts via
    [CT_cast_compose], and close with [CT_cast_irrelevant]. *)

Lemma cfree_pentagon (x y z w : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_tens (CT_id x)
                               (CT_cast (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_tens (CT_cast (eq_sym (app_assoc x y z))) (CT_id w)))
    (CT_comp (CT_cast (eq_sym (app_assoc x y (z ++ w))))
             (CT_cast (eq_sym (app_assoc (x ++ y) z w)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_comp (CT_comp (CT_cast (f_equal (fun ks => x ++ ks)
                                        (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_cast (f_equal (fun ks => ks ++ w)
                               (eq_sym (app_assoc x y z))))).
  - apply CTE_comp_cong.
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CT_tens_cast_id_right.
  - apply CTE_trans with
      (CT_comp (CT_cast (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                  (f_equal (fun ks => x ++ ks)
                                           (eq_sym (app_assoc y z w)))))
               (CT_cast (f_equal (fun ks => ks ++ w)
                                 (eq_sym (app_assoc x y z))))).
    + apply CTE_comp_cong.
      * apply CT_cast_compose.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (f_equal (fun ks => ks ++ w)
                                    (eq_sym (app_assoc x y z)))
                           (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                     (f_equal (fun ks => x ++ ks)
                                              (eq_sym (app_assoc y z w)))))).
      * apply CT_cast_compose.
      * apply CTE_sym.
        apply CTE_trans with
          (CT_cast (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                             (eq_sym (app_assoc x y (z ++ w))))).
        -- apply CT_cast_compose.
        -- rewrite (CT_cast_irrelevant Cdec
                      (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                                (eq_sym (app_assoc x y (z ++ w))))
                      (eq_trans (f_equal (fun ks => ks ++ w)
                                         (eq_sym (app_assoc x y z)))
                                (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                          (f_equal (fun ks => x ++ ks)
                                                   (eq_sym (app_assoc y z w)))))).
           apply CTE_refl.
Qed.

(** ** THE shared Monoidal record on [CFreeCat S]

    All fields explicit, no Program obligations.  The Braided,
    Symmetric, Strict, and coloured-PROP instances downstream all
    project this single record, so their agreement is definitional
    and [Instance.v] can discharge the class's coherence field with
    [eq_refl] over it. *)

Program Definition CFreeCat_Monoidal : @Monoidal (CFreeCat S) := {|
  I            := ([] : list Colour);
  tensor       := CFreeCat_Tensor S;
  unit_left    := fun x => CFreeCat_unit_left S x;
  unit_right   := fun x => CFreeCat_unit_right S x;
  tensor_assoc := fun x y z => CFreeCat_tensor_assoc S x y z;
  to_unit_left_natural      := fun x y g => cleft_unit_natural g;
  from_unit_left_natural    := fun x y g => cleft_unit_natural_from g;
  to_unit_right_natural     := fun x y g => cright_unit_natural g;
  from_unit_right_natural   := fun x y g => cfrom_right_unit_natural g;
  to_tensor_assoc_natural   := fun _ _ _ _ _ _ g h i => cassoc_natural g h i;
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
                                 cfrom_assoc_natural g h i;
  triangle_identity := fun x y => cfree_triangle x y;
  pentagon_identity := fun x y z w => cfree_pentagon x y z w
|}.

End CFreeMonoidal.

Arguments CFreeCat_Monoidal {Colour} S Cdec : assert.

(* D2 WARNING: [CFreeCat_Monoidal S Cdec] depends on the colour
   decider [Cdec] through its UIP-conditional proof fields, so two
   DIFFERENT [Cdec] terms for the same colour type yield
   propositionally different (though pointwise-equal) [Monoidal]
   records.  Downstream files that assert definitional agreement over
   this record — in particular the [eq_refl] discharge of
   [cprop_monoidal_coherence] in [Instance.v] — require every
   instance site to fix ONE canonical [Cdec] per colour type; mixing
   deciders surfaces as an opaque unification error at exactly that
   [eq_refl].  The machine-checked Examples of [Instance.v] exist to
   catch such violations at their source. *)
