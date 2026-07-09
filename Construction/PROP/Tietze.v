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
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
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

   Two FINITE presentations of the same group are related by a finite
   sequence of TIETZE TRANSFORMATIONS: adding/removing a derivable
   relation, and adding/removing a definable generator.  The same
   calculus applies to presentations of PROPs by symmetric monoidal
   theories ([SMT], from [Construction/PROP/Presentation.v]), and this
   file develops its two "adding" moves together with the theorems
   that make them presentation-preserving: for move 1 the congruences
   coincide at every arity; for move 2 the embedding is conservative
   AND a section up to derivable equality, which pins the presented
   homs on both sides (the packaging as an equivalence of presented
   PROPs is deferred; see the trailer):

   1.  SIGNATURE MORPHISMS ([T_map]): a [SubSig S T] acts on terms by
       structural recursion, giving a functor [RelabelFunctor : FreeCat S ⟶
       FreeCat T] that is strict symmetric monoidal — signature
       morphisms induce strict symmetric maps of free PROPs (no
       injectivity of [h] is assumed or used: arbitrary
       boundary-preserving relabellings, including generator
       collapses, are covered).  Unlike
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
       retraction is preferred here.  The retraction is moreover a
       SECTION of the embedding up to derivable equality
       ([ext_retract_section]): every extended-signature term is
       [TermEqW]-equal to an embedded base term, so the extension adds
       no new morphisms, only a new name.

   Everything is elementary syntax: the only quotients involved are the
   [Prop]-valued congruences [TermEq] and [TermEqW], and the only
   proof-irrelevance used is axiom-free UIP on [nat] (via [T_cast_id]
   from [Construction/PROP/Cast.v]). *)

(** ** Signature morphisms acting on terms

    [T_map h] relabels every generator leaf through [h] and leaves the
    structural constructors untouched — the [T_subst] instance of
    [Construction/PROP/TermEq.v] whose generator action is [T_gen]
    after [h].  It COMPUTES on constructors — e.g. [T_map h (T_comp g
    f)] is definitionally [T_comp (T_map h g) (T_map h f)] — which the
    functor and monoidal-functor packaging below exploits:
    identity/composition preservation are [TE_refl]. *)

Definition T_map {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) : Term T m n :=
  T_subst (fun a b (s : S a b) => T_gen (h a b s)) t.

(** The instantiation is definitional, so every [T_subst]-level lemma
    specializes to [T_map] by conversion. *)
Example T_map_is_T_subst {S T : Signature} (h : SubSig S T) {m n : nat} :
  @T_map S T h m n
  = @T_subst S T (fun a b (s : S a b) => T_gen (h a b s)) m n := eq_refl.

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

(** *** Soundness of relabelling

    [T_map h] carries every free equation of [TermEq S] to the
    corresponding free equation of [TermEq T] — the nineteen-case
    preservation induction [T_subst_TermEq] of
    [Construction/PROP/TermEq.v], specialized (definitionally) to the
    relabelling substitution. *)

Lemma T_map_TermEq {S T : Signature} (h : SubSig S T) {m n : nat}
  {s t : Term S m n} :
  TermEq S s t → TermEq T (T_map h s) (T_map h t).
Proof.
  exact (T_subst_TermEq (fun a b (g : S a b) => T_gen (h a b g))).
Qed.

(** ** The induced functor of free PROPs

    A signature morphism [h : SubSig S T] induces [RelabelFunctor h :
    FreeCat S ⟶ FreeCat T] — identity on objects (arities), [T_map h]
    on morphisms — and the functor is STRICT SYMMETRIC monoidal: both
    comparison maps are identities on the nose, the object equalities
    are [eq_refl], and the braid square commutes because [T_map] fixes
    [T_braid].  This is the "signature morphisms induce strict
    symmetric maps of free PROPs" half of the Tietze calculus; the
    packaging mirrors the projection functor of [Presentation.v], and
    both discharge their coherence squares with the shared
    identity-bookkeeping lemmas [tm_id_swap] / [tm_comp_id_tens] /
    [tm_collapse_r] / [tm_collapse_l] of
    [Construction/PROP/TermEq.v]. *)

Section SignatureMorphism.

Context {S T : Signature}.
Context (h : SubSig S T).

Definition RelabelFunctor : FreeCat S ⟶ FreeCat T :=
  Build_Functor (FreeCat S) (FreeCat T)
    (fun n : nat => n)
    (fun m n (t : Term S m n) => T_map h t)
    (fun m n s t Hst => T_map_TermEq h Hst)
    (fun x => TE_refl (T_id x))
    (fun x y z f g => TE_refl (T_comp (T_map h f) (T_map h g))).

(** The tensor-then-map and map-then-tensor composites related by the
    tensor comparison of the monoidal structure. *)
Definition Relabel_ap_dom : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  FreeCat_Tensor T ◯ (RelabelFunctor ∏⟶ RelabelFunctor).

Definition Relabel_ap_cod : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  RelabelFunctor ◯ FreeCat_Tensor S.

(** Both directions of the tensor comparison are families of
    identities — [T_map] computes through [T_tens], so the two functors
    have definitionally equal actions — and naturality is
    [tm_id_swap]. *)
Definition Relabel_ap_to : Relabel_ap_dom ⟹ Relabel_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_dom Relabel_ap_cod
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

Definition Relabel_ap_from : Relabel_ap_cod ⟹ Relabel_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_cod Relabel_ap_dom
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

(** The identity components are inverse up to [TermEq] (the identity
    natural transformation of a composite-with-tensor functor has
    components [T_tens (T_id _) (T_id _)]). *)
Program Definition Relabel_ap_iso :
  Relabel_ap_dom ≅[[FreeCat S ∏ FreeCat S, FreeCat T]] Relabel_ap_cod := {|
  to   := Relabel_ap_to;
  from := Relabel_ap_from;
  iso_to_from := fun p => tm_comp_id_tens (fst p) (snd p);
  iso_from_to := fun p => tm_comp_id_tens (fst p) (snd p)
|}.

(** *** The coherence squares

    Each structural map of [FreeCat_Monoidal] is a [T_cast], which
    [T_map] fixes ([T_map_T_cast]); after that rewrite the squares are
    pure identity bookkeeping. *)

Lemma Relabel_unit_left_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_l x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_l x))) (T_id (0 + x)))
            (T_tens (T_id 0) (T_id x))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_l x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_unit_right_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_r x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_r x))) (T_id (x + 0)))
            (T_tens (T_id x) (T_id 0))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_r x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_assoc_square (x y z : nat) :
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

Program Definition RelabelFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  pure_iso := iso_id;
  ap_functor_iso := Relabel_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z =>
    @tensor_assoc (FreeCat T) (FreeCat_Monoidal T) x y z;
  monoidal_unit_left  := fun x => Relabel_unit_left_square x;
  monoidal_unit_right := fun x => Relabel_unit_right_square x;
  monoidal_assoc := fun x y z => Relabel_assoc_square x y z
|}.

(** Both comparison maps are identities on the nose, so the functor is
    STRICT monoidal with [eq_refl] object equalities.  As with
    [Presentation.v]'s projection, the two comparison fields are
    discharged in situ, keeping the record at a single universe
    instance. *)
Program Definition RelabelFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  strict_functor_is_monoidal := RelabelFunctor_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (TE_refl _). Qed.
Next Obligation. exact (TE_refl _). Qed.

(** The braid-compatibility square: [T_map] fixes [T_braid], and both
    tensor comparisons are identities, so the square is one slide of an
    identity past the braid. *)
Lemma RelabelFunctor_braid (m n : nat) :
  fmap[RelabelFunctor] (@braid (FreeCat S) (FreeCat_Braided S) m n)
    ∘ to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal m n)
  ≈[FreeCat T]
  to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal n m)
    ∘ @braid (FreeCat T) (FreeCat_Braided T) m n.
Proof.
  exact (tm_id_swap (T_braid m n)).
Qed.

Program Definition RelabelFunctor_Braided :
  @BraidedMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Braided S) (FreeCat_Braided T) RelabelFunctor := {|
  braided_is_strong := RelabelFunctor_Monoidal
|}.
Next Obligation.
  exact (tm_id_swap (T_braid x y)).
Qed.

(** A braided monoidal functor between symmetric monoidal categories IS
    a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition RelabelFunctor_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Symmetric S) (FreeCat_Symmetric T) RelabelFunctor :=
  RelabelFunctor_Braided.

End SignatureMorphism.

Arguments RelabelFunctor {S T} h : assert.
Arguments RelabelFunctor_Monoidal {S T} h : assert.
Arguments RelabelFunctor_Strict {S T} h : assert.
Arguments RelabelFunctor_Braided {S T} h : assert.
Arguments RelabelFunctor_Symmetric {S T} h : assert.

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
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - reflexivity.
Qed.

Lemma interp_copair_inr {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term T m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inr t)
    ≈ interp P T w t.
Proof.
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
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

(** Computing witnesses for the [Nat.eqb] equations of the singleton
    signature.  The standard library's [Nat.eqb_refl] and [Nat.eqb_eq]
    are Qed-opaque, so anything built on them is stuck at closed
    arities; these transparent fixpoints restore reduction. *)

Fixpoint nat_eqb_refl (x : nat) : Nat.eqb x x = true :=
  match x return Nat.eqb x x = true with
  | O => eq_refl
  | Datatypes.S k => nat_eqb_refl k
  end.

Fixpoint nat_eqb_eq (a b : nat) {struct a} : Nat.eqb a b = true → a = b :=
  match a, b return Nat.eqb a b = true → a = b with
  | O, O => fun _ => eq_refl
  | O, Datatypes.S b' => fun H =>
      match H in _ = c return if c then O = Datatypes.S b' else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', O => fun H =>
      match H in _ = c return if c then Datatypes.S a' = O else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', Datatypes.S b' => fun H =>
      f_equal Datatypes.S (nat_eqb_eq a' b' H)
  end.

(** The unique generator of [Single_Sig m n], with its arity
    equations.  All three definitions are TRANSPARENT and built on the
    computing witnesses above, so they reduce at closed arities
    ([single_gen] to [tt], the arity equations to [eq_refl]) and
    [ext_retract] computes on concrete definitional extensions — see
    [ext_retract_computes_on_new_gen] at the end of the file.  The
    conservativity proofs below remain transparency-indifferent: they
    consume the arity equations only through UIP on [nat]
    ([T_cast_id]). *)
Definition single_gen : Single_Sig m n m n :=
  match eq_sym (nat_eqb_refl m) in _ = c
    return (if c then if Nat.eqb n n then unit else Empty_set
            else Empty_set)
  with
  | eq_refl =>
      match eq_sym (nat_eqb_refl n) in _ = d
        return (if d then unit else Empty_set)
      with
      | eq_refl => tt
      end
  end.

Definition single_dom {a b : nat} : Single_Sig m n a b → a = m :=
  match Nat.eqb a m as c
    return (Nat.eqb a m = c →
            (if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → a = m)
  with
  | true  => fun Ha _ => nat_eqb_eq a m Ha
  | false => fun _ s => match s return a = m with end
  end eq_refl.

Definition single_cod {a b : nat} : Single_Sig m n a b → b = n :=
  match Nat.eqb a m as c
    return ((if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → b = n)
  with
  | true =>
      match Nat.eqb b n as d
        return (Nat.eqb b n = d → (if d then unit else Empty_set) → b = n)
      with
      | true  => fun Hb _ => nat_eqb_eq b n Hb
      | false => fun _ s => match s return b = n with end
      end eq_refl
  | false => fun s => match s return b = n with end
  end.

(** [Single_Sig m n] is a SINGLETON: any two generators of any one
    arity are equal.  This identifies a generator of the extended
    signature with [single_gen] in the section lemma below. *)
Lemma single_sig_singleton {a b : nat} (s s' : Single_Sig m n a b) :
  s = s'.
Proof.
  revert s s'.
  unfold Single_Sig.
  destruct (Nat.eqb a m), (Nat.eqb b n); intros s s'; now destruct s, s'.
Qed.

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

Definition ext_retract {a b : nat} (t : Term ext_sig a b) :
  Term (smt_sig B) a b :=
  T_subst (@ext_retract_gen) t.

(** The instantiation is definitional, so every [T_subst]-level lemma
    specializes to [ext_retract] by conversion. *)
Example ext_retract_is_T_subst {a b : nat} :
  @ext_retract a b
  = @T_subst ext_sig (smt_sig B) (@ext_retract_gen) a b := eq_refl.

(** [ext_retract] fixes casts, just as [T_map] does. *)
Lemma retract_T_cast {a b : nat} (e : a = b) :
  ext_retract (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(** The retraction is a left inverse of the embedding — a Leibniz
    equality, by term induction. *)
Lemma retract_map_inl {a b : nat} (t : Term (smt_sig B) a b) :
  ext_retract (T_map sig_inl t) = t.
Proof.
  induction t;
  cbn [T_map ext_retract T_subst ext_retract_gen sig_inl];
  try reflexivity.
  - now f_equal.
  - now f_equal.
Qed.

(** The retraction carries free equations to free equations — the
    nineteen-case preservation induction [T_subst_TermEq] of
    [Construction/PROP/TermEq.v], specialized (definitionally) to the
    retraction substitution. *)
Lemma retract_TermEq {a b : nat} {s t : Term ext_sig a b} :
  TermEq ext_sig s t → TermEq (smt_sig B) (ext_retract s) (ext_retract t).
Proof.
  exact (T_subst_TermEq (@ext_retract_gen)).
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
      cbn [ext_retract T_subst ext_retract_gen new_gen].
      rewrite (T_cast_id (single_dom single_gen)).
      rewrite (T_cast_id (eq_sym (single_cod single_gen))).
      apply TEW_termeq.
      apply TE_trans with (T_comp w (T_id m)).
      * apply TE_id_left.
      * apply TE_id_right.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [ext_retract T_subst]; apply TEW_comp; assumption.
  - cbn [ext_retract T_subst]; apply TEW_tens; assumption.
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
  - cbn [T_map T_subst]; apply TEW_comp; assumption.
  - cbn [T_map T_subst]; apply TEW_tens; assumption.
Qed.

(** The fullness ("section") leg: EVERY term of the extended
    signature is [TermEqW ext_smt]-equal to the embedding of its own
    retraction — the embedded base theory is not merely conservative
    but exhaustive.  Together with [ext_conservative]/[ext_reflects]
    this is the hom-level content of an equivalence between the base
    and extended presentations; the [PresEquiv] packaging is deferred
    (see the trailer).  By term induction: structural constructors are
    congruences, base generators are fixed, and the fresh generator is
    exactly the defining equation [ee_def] once [single_sig_singleton]
    pins it to [single_gen] and UIP on [nat] ([T_cast_id]) clears the
    arity casts. *)
Lemma ext_retract_section {a b : nat} (t : Term ext_sig a b) :
  TermEqW ext_smt t (T_map sig_inl (ext_retract t)).
Proof.
  induction t.
  - (* T_id *)
    apply TEW_termeq, TE_refl.
  - (* T_braid *)
    apply TEW_termeq, TE_refl.
  - (* T_comp *)
    cbn [ext_retract T_subst T_map].
    apply TEW_comp; assumption.
  - (* T_tens *)
    cbn [ext_retract T_subst T_map].
    apply TEW_tens; assumption.
  - (* T_gen *)
    destruct s as [s|s].
    + (* a base generator retracts to itself *)
      apply TEW_termeq, TE_refl.
    + (* the fresh generator: pin the arity, then [ee_def] *)
      pose proof (single_dom s) as ea.
      pose proof (single_cod s) as eb.
      subst.
      cbn [ext_retract T_subst ext_retract_gen].
      rewrite (T_cast_id (single_dom s)).
      rewrite (T_cast_id (eq_sym (single_cod s))).
      rewrite (single_sig_singleton s single_gen).
      apply TEW_trans with (t := T_map sig_inl w).
      * exact (TEW_ax ext_smt _ _ ee_def).
      * apply TEW_termeq, T_map_TermEq.
        apply TE_sym.
        apply TE_trans with (T_comp w (T_id m)).
        -- apply TE_id_left.
        -- apply TE_id_right.
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
    action of [RelabelFunctor] is definitional. *)

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

Example RelabelFunctor_obj_id {S T : Signature} (h : SubSig S T) (k : nat) :
  fobj[RelabelFunctor h] k = k := eq_refl.

(** A scratch definitional extension over the empty signature,
    witnessing that [ext_retract] REDUCES at closed arities — the
    transparent [single_gen]/[single_dom]/[single_cod] compute, so
    retracting the fresh generator yields its defining word framed by
    identity casts, by [eq_refl]. *)
Local Definition scratch_smt : SMT :=
  {| smt_sig := Empty_Sig; smt_eqs := fun _ _ _ _ => False |}.

Example ext_retract_computes_on_new_gen :
  ext_retract scratch_smt 1 1 (T_id 1) (T_gen (new_gen scratch_smt 1 1))
  = T_comp (T_id 1) (T_comp (T_id 1) (T_id 1)) := eq_refl.

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
