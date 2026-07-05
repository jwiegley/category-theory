Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

Open Scope nat_scope.

(** * Tietze moves for presentations of PROPs *)

(* nLab: https://ncatlab.org/nlab/show/generators+and+relations
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Tietze_transformations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   Two presentations of the same group are related by a finite sequence
   of TIETZE TRANSFORMATIONS: adding/removing a derivable relation, and
   adding/removing a definable generator.  The same calculus applies to
   presentations of PROPs by symmetric monoidal theories ([SMT], from
   [Construction/PROP/Presentation.v]), and this file develops its two
   "adding" moves together with the conservativity theorems that make
   them presentation-preserving:

   1.  SIGNATURE MORPHISMS ([T_map]): a [SubSig S T] acts on terms by
       structural recursion, giving a functor [InjFunctor : FreeCat S ⟶
       FreeCat T] that is strict symmetric monoidal — signature
       inclusions induce strict symmetric maps of free PROPs.  Unlike
       the tactic-built [T_inj] of [Term.v] (left untouched, related by
       the bridge [T_map_T_inj]), [T_map] is a computing [Fixpoint], so
       the functor laws hold by reflexivity.

   2.  SUMS OF SIGNATURES: the copairing of two valuations interprets a
       summand's image under [sig_inl]/[sig_inr] exactly as the summand
       itself ([interp_copair_inl]/[interp_copair_inr]).

   3.  TIETZE MOVE 1 ([AddEqn]): adding an equation DERIVABLE in a
       theory [E] yields a theory with the same congruence — the
       equivalence [AddEqn_derivable_conservative], both directions.

   4.  TIETZE MOVE 2 ([ext_smt]): adjoining a fresh generator [g] of
       arity [(m, n)] together with the defining equation [g ≈ w] for a
       word [w] of the base theory is CONSERVATIVE: base-signature
       terms are identified in the extension exactly when they were
       identified before ([ext_conservative]/[ext_reflects]).  The
       proof is by a syntactic retraction that substitutes [w] for the
       new generator; a semantic route through [interp] and a copaired
       valuation is possible but carries heavier dependencies, so the
       retraction is preferred here.

   Everything is elementary syntax: the only quotients involved are the
   [Prop]-valued congruences [TermEq] and [TermEqW], and the only
   proof-irrelevance used is axiom-free UIP on [nat] (via [T_cast_id]
   from [Construction/PROP/Cast.v]). *)

(** ** Signature morphisms acting on terms

    [T_map h] relabels every generator leaf through [h] and leaves the
    structural constructors untouched.  It COMPUTES on constructors —
    e.g. [T_map h (T_comp g f)] is definitionally [T_comp (T_map h g)
    (T_map h f)] — which the functor and monoidal-functor packaging
    below exploits: identity/composition preservation are [TE_refl]. *)

Fixpoint T_map {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) : Term T m n :=
  match t in Term _ m' n' return Term T m' n' with
  | T_id k      => T_id k
  | T_braid a b => T_braid a b
  | T_comp g f  => T_comp (T_map h g) (T_map h f)
  | T_tens f g  => T_tens (T_map h f) (T_map h g)
  | T_gen s     => T_gen (h _ _ s)
  end.

(** [T_map] agrees with the tactic-built [T_inj] of [Term.v] on the
    nose; [T_inj] itself is left untouched. *)
Lemma T_map_T_inj {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) :
  T_map h t = T_inj h t.
Proof.
  induction t; cbn; try reflexivity; now f_equal.
Qed.

(** Casts are fixed by every signature morphism (a Leibniz equality:
    both sides are the same [match] once [e] is destructed). *)
Lemma T_map_T_cast {S T : Signature} (h : SubSig S T) {a b : nat}
  (e : a = b) :
  T_map h (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(** *** Transport seams

    The strict-PROP axioms of [TermEq] carry their arity mismatches as
    [eq_rect] transports; [T_map] commutes with each transport shape by
    Leibniz equality (destruct the arity equation). *)

Lemma T_map_eq_rect_cod {S T : Signature} (h : SubSig S T)
  {a b b' : nat} (e : b = b') (t : Term S a b) :
  T_map h (eq_rect b (fun k : nat => Term S a k) t b' e)
  = eq_rect b (fun k : nat => Term T a k) (T_map h t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_map_eq_rect_dom {S T : Signature} (h : SubSig S T)
  {a a' b : nat} (e : a = a') (t : Term S a b) :
  T_map h (eq_rect a (fun k : nat => Term S k b) t a' e)
  = eq_rect a (fun k : nat => Term T k b) (T_map h t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_map_eq_rect_r_dom {S T : Signature} (h : SubSig S T)
  {a a' b : nat} (e : a' = a) (t : Term S a b) :
  T_map h (eq_rect_r (fun k : nat => Term S k b) t e)
  = eq_rect_r (fun k : nat => Term T k b) (T_map h t) e.
Proof. destruct e; reflexivity. Qed.

(** *** Soundness of relabelling

    [T_map h] carries every free equation of [TermEq S] to the
    corresponding free equation of [TermEq T].  The induction covers
    all nineteen constructors: the thirteen constructor-to-constructor
    cases reduce by computation, and the six transport-form cases first
    move [T_map] across the [eq_rect] seams by the Leibniz bridges
    above, then close with the same primitive constructor. *)

Lemma T_map_TermEq {S T : Signature} (h : SubSig S T) {m n : nat}
  {s t : Term S m n} :
  TermEq S s t → TermEq T (T_map h s) (T_map h t).
Proof.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply TE_refl.
  - (* TE_sym *)
    exact (TE_sym _ _ IHHT).
  - (* TE_trans *)
    exact (TE_trans _ _ _ IHHT1 IHHT2).
  - (* TE_comp_cong *)
    cbn [T_map]; apply TE_comp_cong; assumption.
  - (* TE_tens_cong *)
    cbn [T_map]; apply TE_tens_cong; assumption.
  - (* TE_id_left *)
    cbn [T_map]; apply TE_id_left.
  - (* TE_id_right *)
    cbn [T_map]; apply TE_id_right.
  - (* TE_assoc *)
    cbn [T_map]; apply TE_assoc.
  - (* TE_tens_id *)
    cbn [T_map]; apply TE_tens_id.
  - (* TE_interchange *)
    cbn [T_map]; apply TE_interchange.
  - (* TE_braid_invol *)
    cbn [T_map]; apply TE_braid_invol.
  - (* TE_braid_natural *)
    cbn [T_map]; apply TE_braid_natural.
  - (* TE_tens_id0_left *)
    cbn [T_map]; apply TE_tens_id0_left.
  - (* TE_tens_id0_right *)
    rewrite T_map_eq_rect_cod, T_map_eq_rect_r_dom.
    cbn [T_map]; apply TE_tens_id0_right.
  - (* TE_tens_assoc *)
    rewrite T_map_eq_rect_cod, T_map_eq_rect_r_dom.
    cbn [T_map]; apply TE_tens_assoc.
  - (* TE_braid_hex_left *)
    cbn [T_map].
    rewrite T_map_eq_rect_cod, !T_map_eq_rect_dom.
    cbn [T_map]; apply TE_braid_hex_left.
  - (* TE_braid_hex_right *)
    cbn [T_map].
    rewrite T_map_eq_rect_cod, !T_map_eq_rect_dom.
    cbn [T_map]; apply TE_braid_hex_right.
  - (* TE_braid_unit_left *)
    rewrite T_map_eq_rect_cod.
    cbn [T_map]; apply TE_braid_unit_left.
  - (* TE_braid_unit_right *)
    rewrite T_map_eq_rect_dom.
    cbn [T_map]; apply TE_braid_unit_right.
Qed.

(** ** Identity bookkeeping on terms

    The comparison maps of the induced monoidal functor below are all
    identities or tensors of identities, so its coherence squares are
    the same identity-collapsing equations that discharge the
    projection functor of [Presentation.v] — restated here over an
    arbitrary signature (the [Presentation.v] copies are pinned to the
    signature of an [SMT]). *)

(** An identity slides from one side of a morphism to the other. *)
Lemma tm_id_swap {S : Signature} {m n : nat} (t : Term S m n) :
  TermEq S (T_comp t (T_id m)) (T_comp (T_id n) t).
Proof.
  apply TE_trans with t.
  - apply TE_id_right.
  - apply TE_sym, TE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. *)
Lemma tm_comp_id_tens {S : Signature} (m n : nat) :
  TermEq S (T_comp (T_id (m + n)) (T_id (m + n))) (T_tens (T_id m) (T_id n)).
Proof.
  apply TE_trans with (T_id (m + n)).
  - apply TE_id_left.
  - apply TE_sym, TE_tens_id.
Qed.

(** Collapsing an identity and a tensor of identities after [t]. *)
Lemma tm_collapse_r {S : Signature} {m n p : nat} (t : Term S (m + n) p) :
  TermEq S (T_comp (T_comp t (T_id (m + n))) (T_tens (T_id m) (T_id n))) t.
Proof.
  apply TE_trans with (T_comp t (T_tens (T_id m) (T_id n))).
  - apply TE_comp_cong.
    + apply TE_id_right.
    + apply TE_refl.
  - apply TE_trans with (T_comp t (T_id (m + n))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_tens_id.
    + apply TE_id_right.
Qed.

(** Collapsing an identity and a tensor of identities before [t]. *)
Lemma tm_collapse_l {S : Signature} {m n p : nat} (t : Term S p (m + n)) :
  TermEq S (T_comp (T_comp (T_id (m + n)) (T_tens (T_id m) (T_id n))) t) t.
Proof.
  apply TE_trans with (T_comp (T_tens (T_id m) (T_id n)) t).
  - apply TE_comp_cong.
    + apply TE_id_left.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_id (m + n)) t).
    + apply TE_comp_cong.
      * apply TE_tens_id.
      * apply TE_refl.
    + apply TE_id_left.
Qed.

(** ** The induced functor of free PROPs

    A signature morphism [h : SubSig S T] induces [InjFunctor h :
    FreeCat S ⟶ FreeCat T] — identity on objects (arities), [T_map h]
    on morphisms — and the functor is STRICT SYMMETRIC monoidal: both
    comparison maps are identities on the nose, the object equalities
    are [eq_refl], and the braid square commutes because [T_map] fixes
    [T_braid].  This is the "signature morphisms induce strict
    symmetric maps of free PROPs" half of the Tietze calculus; the
    packaging mirrors the projection functor of [Presentation.v]. *)

Section SignatureMorphism.

Context {S T : Signature}.
Context (h : SubSig S T).

Definition InjFunctor : FreeCat S ⟶ FreeCat T :=
  Build_Functor (FreeCat S) (FreeCat T)
    (fun n : nat => n)
    (fun m n (t : Term S m n) => T_map h t)
    (fun m n s t Hst => T_map_TermEq h Hst)
    (fun x => TE_refl (T_id x))
    (fun x y z f g => TE_refl (T_comp (T_map h f) (T_map h g))).

(** The tensor-then-map and map-then-tensor composites related by the
    tensor comparison of the monoidal structure. *)
Definition Inj_ap_dom : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  FreeCat_Tensor T ◯ (InjFunctor ∏⟶ InjFunctor).

Definition Inj_ap_cod : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  InjFunctor ◯ FreeCat_Tensor S.

(** Both directions of the tensor comparison are families of
    identities — [T_map] computes through [T_tens], so the two functors
    have definitionally equal actions — and naturality is
    [tm_id_swap]. *)
Definition Inj_ap_to : Inj_ap_dom ⟹ Inj_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Inj_ap_dom Inj_ap_cod
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

Definition Inj_ap_from : Inj_ap_cod ⟹ Inj_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Inj_ap_cod Inj_ap_dom
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

(** The identity components are inverse up to [TermEq] (the identity
    natural transformation of a composite-with-tensor functor has
    components [T_tens (T_id _) (T_id _)]). *)
Program Definition Inj_ap_iso :
  Inj_ap_dom ≅[[FreeCat S ∏ FreeCat S, FreeCat T]] Inj_ap_cod := {|
  to   := Inj_ap_to;
  from := Inj_ap_from;
  iso_to_from := fun p => tm_comp_id_tens (fst p) (snd p);
  iso_from_to := fun p => tm_comp_id_tens (fst p) (snd p)
|}.

(** *** The coherence squares

    Each structural map of [FreeCat_Monoidal] is a [T_cast], which
    [T_map] fixes ([T_map_T_cast]); after that rewrite the squares are
    pure identity bookkeeping. *)

Lemma Inj_unit_left_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_l x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_l x))) (T_id (0 + x)))
            (T_tens (T_id 0) (T_id x))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_l x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Inj_unit_right_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_r x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_r x))) (T_id (x + 0)))
            (T_tens (T_id x) (T_id 0))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_r x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Inj_assoc_square (x y z : nat) :
  TermEq T
    (T_comp (T_comp (T_map h (T_cast (eq_sym (Nat.add_assoc x y z))))
                    (T_id ((x + y) + z)))
            (T_tens (T_id (x + y)) (T_id z)))
    (T_comp (T_comp (T_id (x + (y + z)))
                    (T_tens (T_id x) (T_id (y + z))))
            (T_cast (eq_sym (Nat.add_assoc x y z)))).
Proof.
  rewrite (T_map_T_cast h (eq_sym (Nat.add_assoc x y z))).
  apply TE_trans with (T_cast (eq_sym (Nat.add_assoc x y z))).
  - apply tm_collapse_r.
  - apply TE_sym, tm_collapse_l.
Qed.

Program Definition InjFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) InjFunctor := {|
  pure_iso := iso_id;
  ap_functor_iso := Inj_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z =>
    @tensor_assoc (FreeCat T) (FreeCat_Monoidal T) x y z;
  monoidal_unit_left  := fun x => Inj_unit_left_square x;
  monoidal_unit_right := fun x => Inj_unit_right_square x;
  monoidal_assoc := fun x y z => Inj_assoc_square x y z
|}.

(** Both comparison maps are identities on the nose, so the functor is
    STRICT monoidal with [eq_refl] object equalities.  As with
    [Presentation.v]'s projection, the two comparison fields are
    discharged in situ, keeping the record at a single universe
    instance. *)
Program Definition InjFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) InjFunctor := {|
  strict_functor_is_monoidal := InjFunctor_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (TE_refl _). Qed.
Next Obligation. exact (TE_refl _). Qed.

(** The braid-compatibility square: [T_map] fixes [T_braid], and both
    tensor comparisons are identities, so the square is one slide of an
    identity past the braid. *)
Lemma InjFunctor_braid (m n : nat) :
  fmap[InjFunctor] (@braid (FreeCat S) (FreeCat_Braided S) m n)
    ∘ to (@ap_iso _ _ _ _ InjFunctor InjFunctor_Monoidal m n)
  ≈[FreeCat T]
  to (@ap_iso _ _ _ _ InjFunctor InjFunctor_Monoidal n m)
    ∘ @braid (FreeCat T) (FreeCat_Braided T) m n.
Proof.
  exact (tm_id_swap (T_braid m n)).
Qed.

Program Definition InjFunctor_Braided :
  @BraidedMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Braided S) (FreeCat_Braided T) InjFunctor := {|
  braided_is_strong := InjFunctor_Monoidal
|}.
Next Obligation.
  exact (tm_id_swap (T_braid x y)).
Qed.

(** A braided monoidal functor between symmetric monoidal categories IS
    a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition InjFunctor_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Symmetric S) (FreeCat_Symmetric T) InjFunctor :=
  InjFunctor_Braided.

End SignatureMorphism.

Arguments InjFunctor {S T} h : assert.
Arguments InjFunctor_Monoidal {S T} h : assert.
Arguments InjFunctor_Strict {S T} h : assert.
Arguments InjFunctor_Braided {S T} h : assert.
Arguments InjFunctor_Symmetric {S T} h : assert.

(** ** Sums of signatures and copaired valuations

    The coproduct injections of [Sum_Sig], and the copairing of two
    valuations, satisfying the expected computation rules under
    [interp]: interpreting the [T_map]-image of a summand's term
    through the copaired valuation is interpreting the term through the
    summand's own valuation. *)

Definition sig_inl {S T : Signature} : SubSig S (Sum_Sig S T) :=
  fun _ _ s => Datatypes.inl s.

Definition sig_inr {S T : Signature} : SubSig T (Sum_Sig S T) :=
  fun _ _ t => Datatypes.inr t.

Definition copair_val {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) : Valuation P (Sum_Sig S T) :=
  fun m n g =>
    match g with
    | Datatypes.inl s => v m n s
    | Datatypes.inr t => w m n t
    end.

(** No decidability or reflection hypotheses are needed here: the
    induction never leaves the [Type]-valued hom equivalence. *)
Lemma interp_copair_inl {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term S m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inl t)
    ≈ interp P S v t.
Proof.
  induction t; cbn [T_map interp].
  - reflexivity.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - reflexivity.
Qed.

Lemma interp_copair_inr {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term T m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inr t)
    ≈ interp P T w t.
Proof.
  induction t; cbn [T_map interp].
  - reflexivity.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - reflexivity.
Qed.

(** ** Tietze move 1: adding a derivable equation

    Extending a theory [E] by ONE new equation [s ≈ t] between terms of
    a fixed arity.  The extended equation system is the two-constructor
    inductive below — an axiom of [E], or the new equation — which
    keeps the arity indices pinned by the constructor itself, so no
    transports (and no UIP) are needed anywhere in the conservativity
    proof. *)

Section AddEquation.

Context (E : SMT).
Context {m n : nat}.
Context (s t : Term (smt_sig E) m n).

Inductive add_eqn : ∀ a b : nat,
  Term (smt_sig E) a b → Term (smt_sig E) a b → Prop :=
  | ae_base {a b} (u u' : Term (smt_sig E) a b) :
      smt_eqs E a b u u' → add_eqn a b u u'
  | ae_new : add_eqn m n s t.

Definition AddEqn : SMT := {|
  smt_sig := smt_sig E;
  smt_eqs := add_eqn
|}.

(** Adding a DERIVABLE equation changes nothing: the congruence of the
    extended theory coincides with the congruence of [E].  Forward
    direction by induction — the new axiom's case is exactly the
    derivation [Hd] — and backward direction by axiom-inclusion
    monotonicity. *)
Theorem AddEqn_derivable_conservative (Hd : TermEqW E s t) :
  ∀ (a b : nat) (u u' : Term (smt_sig E) a b),
    TermEqW AddEqn u u' <-> TermEqW E u u'.
Proof.
  intros a b u u'.
  split; intros H.
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + destruct Hax as [a2 b2 u3 u4 Hax'|].
      * apply TEW_ax; exact Hax'.
      * exact Hd.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp E _ _ _ _ IHf IHg).
    + exact (TEW_tens E _ _ _ _ IHf IHg).
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + apply TEW_ax, ae_base; exact Hax.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp AddEqn _ _ _ _ IHf IHg).
    + exact (TEW_tens AddEqn _ _ _ _ IHf IHg).
Qed.

End AddEquation.

Arguments AddEqn E {m n} s t : assert.

(** ** Tietze move 2: definitional extension

    Adjoining to a theory [B] a FRESH generator of arity [(m, n)]
    together with the single defining equation identifying it with a
    word [w] of the base signature.  The extension is conservative:
    the retraction substituting [w] back for the new generator carries
    every derivation of the extended theory to a derivation of [B]. *)

Section Extension.

Context (B : SMT).
Context (m n : nat).
Context (w : Term (smt_sig B) m n).

(** The extended signature: the base plus one generator. *)
Definition ext_sig : Signature := Sum_Sig (smt_sig B) (Single_Sig m n).

(** The unique generator of [Single_Sig m n], with its arity
    equations.  All three are transparent so that they may participate
    in conversion, although the conservativity proof below only ever
    consumes the arity equations through UIP on [nat]. *)
Definition single_gen : Single_Sig m n m n.
Proof.
  unfold Single_Sig.
  rewrite !Nat.eqb_refl.
  exact tt.
Defined.

Definition single_dom {a b : nat} : Single_Sig m n a b → a = m.
Proof.
  unfold Single_Sig.
  destruct (Nat.eqb a m) eqn:Ha.
  - intros _.
    apply Nat.eqb_eq.
    exact Ha.
  - intros [].
Defined.

Definition single_cod {a b : nat} : Single_Sig m n a b → b = n.
Proof.
  unfold Single_Sig.
  destruct (Nat.eqb a m).
  - destruct (Nat.eqb b n) eqn:Hb.
    + intros _.
      apply Nat.eqb_eq.
      exact Hb.
    + intros [].
  - intros [].
Defined.

(** The fresh generator, as a generator of the extended signature. *)
Definition new_gen : ext_sig m n := Datatypes.inr single_gen.

(** The equations of the extended theory: the base axioms (embedded
    along [sig_inl]) plus the single defining equation. *)
Inductive ext_eqs : ∀ a b : nat,
  Term ext_sig a b → Term ext_sig a b → Prop :=
  | ee_base {a b} (s t : Term (smt_sig B) a b) :
      smt_eqs B a b s t →
      ext_eqs a b (T_map sig_inl s) (T_map sig_inl t)
  | ee_def : ext_eqs m n (T_gen new_gen) (T_map sig_inl w).

Definition ext_smt : SMT := {|
  smt_sig := ext_sig;
  smt_eqs := ext_eqs
|}.

(** *** The syntactic retraction

    Substitute [w] for the new generator, conjugated by the arity
    casts that reconcile the generator's typed arity [(a, b)] with the
    pinned [(m, n)]; base generators go back to themselves. *)

Definition ext_retract_gen {a b : nat} (g : ext_sig a b) :
  Term (smt_sig B) a b :=
  match g with
  | Datatypes.inl s => T_gen s
  | Datatypes.inr s => T_comp (T_cast (eq_sym (single_cod s)))
                              (T_comp w (T_cast (single_dom s)))
  end.

Fixpoint ext_retract {a b : nat} (t : Term ext_sig a b) :
  Term (smt_sig B) a b :=
  match t in Term _ a' b' return Term (smt_sig B) a' b' with
  | T_id k      => T_id k
  | T_braid c d => T_braid c d
  | T_comp g f  => T_comp (ext_retract g) (ext_retract f)
  | T_tens f g  => T_tens (ext_retract f) (ext_retract g)
  | T_gen g     => ext_retract_gen g
  end.

(** [ext_retract] fixes casts and commutes with the transport seams, just
    as [T_map] does. *)
Lemma retract_T_cast {a b : nat} (e : a = b) :
  ext_retract (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

Lemma retract_eq_rect_cod {a b b' : nat} (e : b = b')
  (t : Term ext_sig a b) :
  ext_retract (eq_rect b (fun k : nat => Term ext_sig a k) t b' e)
  = eq_rect b (fun k : nat => Term (smt_sig B) a k) (ext_retract t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma retract_eq_rect_dom {a a' b : nat} (e : a = a')
  (t : Term ext_sig a b) :
  ext_retract (eq_rect a (fun k : nat => Term ext_sig k b) t a' e)
  = eq_rect a (fun k : nat => Term (smt_sig B) k b) (ext_retract t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma retract_eq_rect_r_dom {a a' b : nat} (e : a' = a)
  (t : Term ext_sig a b) :
  ext_retract (eq_rect_r (fun k : nat => Term ext_sig k b) t e)
  = eq_rect_r (fun k : nat => Term (smt_sig B) k b) (ext_retract t) e.
Proof. destruct e; reflexivity. Qed.

(** The retraction is a left inverse of the embedding — a Leibniz
    equality, by term induction. *)
Lemma retract_map_inl {a b : nat} (t : Term (smt_sig B) a b) :
  ext_retract (T_map sig_inl t) = t.
Proof.
  induction t; cbn [T_map ext_retract ext_retract_gen sig_inl];
  try reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
Qed.

(** The retraction carries free equations to free equations — the same
    nineteen-case induction as [T_map_TermEq], with the [ext_retract]
    bridges across the transport seams. *)
Lemma retract_TermEq {a b : nat} {s t : Term ext_sig a b} :
  TermEq ext_sig s t → TermEq (smt_sig B) (ext_retract s) (ext_retract t).
Proof.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply TE_refl.
  - (* TE_sym *)
    exact (TE_sym _ _ IHHT).
  - (* TE_trans *)
    exact (TE_trans _ _ _ IHHT1 IHHT2).
  - (* TE_comp_cong *)
    cbn [ext_retract]; apply TE_comp_cong; assumption.
  - (* TE_tens_cong *)
    cbn [ext_retract]; apply TE_tens_cong; assumption.
  - (* TE_id_left *)
    cbn [ext_retract]; apply TE_id_left.
  - (* TE_id_right *)
    cbn [ext_retract]; apply TE_id_right.
  - (* TE_assoc *)
    cbn [ext_retract]; apply TE_assoc.
  - (* TE_tens_id *)
    cbn [ext_retract]; apply TE_tens_id.
  - (* TE_interchange *)
    cbn [ext_retract]; apply TE_interchange.
  - (* TE_braid_invol *)
    cbn [ext_retract]; apply TE_braid_invol.
  - (* TE_braid_natural *)
    cbn [ext_retract]; apply TE_braid_natural.
  - (* TE_tens_id0_left *)
    cbn [ext_retract]; apply TE_tens_id0_left.
  - (* TE_tens_id0_right *)
    rewrite retract_eq_rect_cod, retract_eq_rect_r_dom.
    cbn [ext_retract]; apply TE_tens_id0_right.
  - (* TE_tens_assoc *)
    rewrite retract_eq_rect_cod, retract_eq_rect_r_dom.
    cbn [ext_retract]; apply TE_tens_assoc.
  - (* TE_braid_hex_left *)
    cbn [ext_retract].
    rewrite retract_eq_rect_cod, !retract_eq_rect_dom.
    cbn [ext_retract]; apply TE_braid_hex_left.
  - (* TE_braid_hex_right *)
    cbn [ext_retract].
    rewrite retract_eq_rect_cod, !retract_eq_rect_dom.
    cbn [ext_retract]; apply TE_braid_hex_right.
  - (* TE_braid_unit_left *)
    rewrite retract_eq_rect_cod.
    cbn [ext_retract]; apply TE_braid_unit_left.
  - (* TE_braid_unit_right *)
    rewrite retract_eq_rect_dom.
    cbn [ext_retract]; apply TE_braid_unit_right.
Qed.

(** The retraction is sound for the whole extended theory: base axioms
    retract to themselves ([retract_map_inl]), and the defining
    equation retracts to the identity bookkeeping [cast ⊙ (w ⊙ cast) ≈
    w], where both casts are along loop equations on [nat] and vanish
    by [T_cast_id] (axiom-free UIP). *)
Lemma retract_sound {a b : nat} {s t : Term ext_sig a b} :
  TermEqW ext_smt s t → TermEqW B (ext_retract s) (ext_retract t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, retract_TermEq; exact Hfree.
  - destruct Hax as [a2 b2 u3 u4 Hax'|].
    + rewrite !retract_map_inl.
      apply TEW_ax; exact Hax'.
    + rewrite retract_map_inl.
      cbn [ext_retract ext_retract_gen new_gen].
      rewrite (T_cast_id (single_dom single_gen)).
      rewrite (T_cast_id (eq_sym (single_cod single_gen))).
      apply TEW_termeq.
      apply TE_trans with (T_comp w (T_id m)).
      * apply TE_id_left.
      * apply TE_id_right.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [ext_retract]; apply TEW_comp; assumption.
  - cbn [ext_retract]; apply TEW_tens; assumption.
Qed.

(** *** Conservativity, both directions *)

(** Base-signature terms identified in the extension were already
    identified in the base theory. *)
Theorem ext_conservative {a b : nat} (s t : Term (smt_sig B) a b) :
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t) →
  TermEqW B s t.
Proof.
  intros H.
  pose proof (retract_sound H) as Hr.
  rewrite !retract_map_inl in Hr.
  exact Hr.
Qed.

(** Conversely, every base identification survives the extension. *)
Theorem ext_reflects {a b : nat} {s t : Term (smt_sig B) a b} :
  TermEqW B s t →
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, T_map_TermEq; exact Hfree.
  - apply TEW_ax, ee_base; exact Hax.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [T_map]; apply TEW_comp; assumption.
  - cbn [T_map]; apply TEW_tens; assumption.
Qed.

(** The defining equation itself holds in the extended theory. *)
Example ext_definition_holds :
  TermEqW ext_smt (T_gen new_gen) (T_map sig_inl w) :=
  TEW_ax ext_smt _ _ ee_def.

(** The retraction computes on embedded generators, by [eq_refl]. *)
Example retract_fixes_base_gen {a b : nat} (s : smt_sig B a b) :
  ext_retract (T_map sig_inl (T_gen s)) = T_gen s := eq_refl.

End Extension.

Arguments ext_smt B m n w : assert.
Arguments new_gen B m n : assert.

(** ** Machine-checked sanity

    [T_map] computes on the structural constructors, so the functor
    action of [InjFunctor] is definitional. *)

Example T_map_fixes_id {S T : Signature} (h : SubSig S T) (k : nat) :
  T_map h (T_id k) = T_id k := eq_refl.

Example T_map_fixes_braid {S T : Signature} (h : SubSig S T) (a b : nat) :
  T_map h (T_braid a b) = T_braid a b := eq_refl.

Example T_map_computes_comp {S T : Signature} (h : SubSig S T)
  {a b c : nat} (g : Term S b c) (f : Term S a b) :
  T_map h (T_comp g f) = T_comp (T_map h g) (T_map h f) := eq_refl.

Example T_map_computes_tens {S T : Signature} (h : SubSig S T)
  {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  T_map h (T_tens f g) = T_tens (T_map h f) (T_map h g) := eq_refl.

Example InjFunctor_obj_id {S T : Signature} (h : SubSig S T) (k : nat) :
  fobj[InjFunctor h] k = k := eq_refl.

(** ** Follow-up material (deliberately not started here)

    Two natural continuations of this file are left for a successor:

    - a [TheoryMorphism] record — a [SubSig] between theory signatures
      whose action carries each axiom of the source theory to a
      derivable equation of the target, inducing a functor of
      PRESENTED categories through the quotient's universal property;

    - a [PresEquiv] record packaging a presentation equivalence as a
      pair of theory morphisms whose composites are pointwise
      derivably equal to the identities, with the Tietze moves above
      as its generating instances.

    Both ride only on machinery already present in this file and in
    [Construction/PROP/Presentation.v]. *)
