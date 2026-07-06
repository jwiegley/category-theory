Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(* [Instance.Fun] is Required but NOT Imported: its functor-category
   notation "[ C , D ]" (level 90) and ListNotations' "[]" have
   incompatible parsing prefixes, and this file needs the latter for
   colour words.  The one use of the functor category below names
   [Category.Instance.Fun.Fun] qualified. *)
Require Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Relabelling coloured-PROP terms along a signature morphism *)

(* nLab: https://ncatlab.org/nlab/show/generators+and+relations
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   A sub-signature embedding [h : CSubSig S T] ([Construction/
   ColouredPROP/Signature.v]) preserves generator boundaries on the
   nose, so it acts on typed string-diagram terms by pure structural
   recursion: relabel every generator leaf through [h] and leave the
   structural constructors untouched.  This file develops that action
   and its consequences, the coloured mirror of the signature-morphism
   half of [Construction/PROP/Tietze.v] (its [T_map] development, with
   [list Colour] replacing [nat], [++] replacing [Nat.add], and
   [app_nil_r] / [app_assoc] replacing [Nat.add_0_r] /
   [Nat.add_assoc]):

   1.  [CT_map h] is a computing [Fixpoint] — e.g. [CT_map h (CT_comp
       g f)] is definitionally [CT_comp (CT_map h g) (CT_map h f)] —
       so the functor packaging below discharges its identity and
       composition laws by [CTE_refl].  Because [h] preserves
       boundaries exactly, NO boundary-mismatch casts are needed to
       STATE [CT_map]'s action: the boundaries of a term and of its
       image agree on the nose.  ([CT_cast] does still appear in a
       few statements — [CT_map_CT_cast] and the coherence squares of
       item 5 — but there it is a first-class term being mapped, the
       monoidal structural map under study, never a repair of a
       boundary mismatch introduced by [CT_map] itself.)  (Per the
       note at the foot of [Signature.v], there is
       no tactic-built precursor to bridge to: the coloured spine has
       [CT_map] from day one.)

   2.  [CT_map] fixes casts ([CT_map_CT_cast]) and commutes with the
       three [eq_rect] transport shapes in which [CTermEq] states its
       strict-PROP axioms (the transport seams [CT_map_eq_rect_cod] /
       [CT_map_eq_rect_dom] / [CT_map_eq_rect_r_dom]) — each a Leibniz
       equality by destructing the boundary equation.

   3.  Soundness for the equational theory ([CT_map_CTermEq]): the
       induction covers all NINETEEN [CTermEq] constructors — the
       thirteen constructor-to-constructor cases reduce by
       computation, and the six transport-form cases first move
       [CT_map] across the [eq_rect] seams, then close with the same
       primitive constructor.

   4.  The identity-bookkeeping quartet [ctm_id_swap] /
       [ctm_comp_id_tens] / [ctm_collapse_r] / [ctm_collapse_l], over
       an arbitrary signature, feeding the comparison squares of the
       monoidal packaging.

   5.  The induced functor [CInjFunctor h : CFreeCat S ⟶ CFreeCat T]
       — identity on objects (colour words), [CT_map h] on morphisms —
       is STRICT SYMMETRIC monoidal: both comparison maps are
       identities on the nose, the object equalities are [eq_refl],
       and the braid square commutes because [CT_map] fixes
       [CT_braid].  Signature morphisms induce strict symmetric maps
       of free coloured PROPs ([CInjFunctor_Monoidal] /
       [CInjFunctor_Strict] / [CInjFunctor_Braided] /
       [CInjFunctor_Symmetric]).

   Everything is elementary syntax: the only relation involved is the
   [Prop]-valued congruence [CTermEq], and no proof irrelevance is
   used anywhere — the decidability discipline (D2) enters only
   through the shared [Monoidal] record [CFreeCat_Monoidal _ Cdec]
   that the packaged records name in their types.  Following the
   [Free.v] discipline, the records are explicit [Build_*]
   applications with standalone, named comparison lemmas. *)

(** ** The relabelling action on terms

    [CT_map h] relabels every generator leaf through [h] and leaves
    the structural constructors untouched.  It COMPUTES on
    constructors, which the functor and monoidal-functor packaging
    below exploits: identity/composition preservation are
    [CTE_refl]. *)

Fixpoint CT_map {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour}
  (t : CTerm S cs ds) : CTerm T cs ds :=
  match t in CTerm _ cs' ds' return CTerm T cs' ds' with
  | CT_id ks       => CT_id ks
  | CT_braid us vs => CT_braid us vs
  | CT_comp g f    => CT_comp (CT_map h g) (CT_map h f)
  | CT_tens f g    => CT_tens (CT_map h f) (CT_map h g)
  | CT_gen g       => CT_gen (h _ _ g)
  end.

(** Casts are fixed by every signature morphism (a Leibniz equality:
    both sides are the same [match] once [e] is destructed). *)
Lemma CT_map_CT_cast {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} (e : cs = ds) :
  CT_map h (CT_cast e) = CT_cast e.
Proof. destruct e; reflexivity. Qed.

(** *** Transport seams

    The strict-PROP axioms of [CTermEq] carry their boundary
    mismatches as [eq_rect] transports over [app_nil_r] / [app_assoc]
    equations; [CT_map] commutes with each transport shape by Leibniz
    equality (destruct the boundary equation). *)

Lemma CT_map_eq_rect_cod {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b b' : list Colour} (e : b = b')
  (t : CTerm S a b) :
  CT_map h (eq_rect b (fun k : list Colour => CTerm S a k) t b' e)
  = eq_rect b (fun k : list Colour => CTerm T a k) (CT_map h t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma CT_map_eq_rect_dom {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a a' b : list Colour} (e : a = a')
  (t : CTerm S a b) :
  CT_map h (eq_rect a (fun k : list Colour => CTerm S k b) t a' e)
  = eq_rect a (fun k : list Colour => CTerm T k b) (CT_map h t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma CT_map_eq_rect_r_dom {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a a' b : list Colour} (e : a' = a)
  (t : CTerm S a b) :
  CT_map h (eq_rect_r (fun k : list Colour => CTerm S k b) t e)
  = eq_rect_r (fun k : list Colour => CTerm T k b) (CT_map h t) e.
Proof. destruct e; reflexivity. Qed.

(** *** Soundness of relabelling

    [CT_map h] carries every free equation of [CTermEq S] to the
    corresponding free equation of [CTermEq T].  The induction covers
    all nineteen constructors: the thirteen
    constructor-to-constructor cases reduce by computation, and the
    six transport-form cases ([CTE_tens_id0_right], [CTE_tens_assoc],
    the two hexagons, and the two unit braids) first move [CT_map]
    across the [eq_rect] seams by the Leibniz bridges above, then
    close with the same primitive constructor. *)

Lemma CT_map_CTermEq {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} {s t : CTerm S cs ds} :
  CTermEq S s t → CTermEq T (CT_map h s) (CT_map h t).
Proof.
  intros HT.
  induction HT.
  - (* CTE_refl *)
    apply CTE_refl.
  - (* CTE_sym *)
    exact (CTE_sym _ _ IHHT).
  - (* CTE_trans *)
    exact (CTE_trans _ _ _ IHHT1 IHHT2).
  - (* CTE_comp_cong *)
    cbn [CT_map]; apply CTE_comp_cong; assumption.
  - (* CTE_tens_cong *)
    cbn [CT_map]; apply CTE_tens_cong; assumption.
  - (* CTE_id_left *)
    cbn [CT_map]; apply CTE_id_left.
  - (* CTE_id_right *)
    cbn [CT_map]; apply CTE_id_right.
  - (* CTE_assoc *)
    cbn [CT_map]; apply CTE_assoc.
  - (* CTE_tens_id *)
    cbn [CT_map]; apply CTE_tens_id.
  - (* CTE_interchange *)
    cbn [CT_map]; apply CTE_interchange.
  - (* CTE_braid_invol *)
    cbn [CT_map]; apply CTE_braid_invol.
  - (* CTE_braid_natural *)
    cbn [CT_map]; apply CTE_braid_natural.
  - (* CTE_tens_id0_left *)
    cbn [CT_map]; apply CTE_tens_id0_left.
  - (* CTE_tens_id0_right *)
    rewrite CT_map_eq_rect_cod, CT_map_eq_rect_r_dom.
    cbn [CT_map]; apply CTE_tens_id0_right.
  - (* CTE_tens_assoc *)
    rewrite CT_map_eq_rect_cod, CT_map_eq_rect_r_dom.
    cbn [CT_map]; apply CTE_tens_assoc.
  - (* CTE_braid_hex_left *)
    cbn [CT_map].
    rewrite CT_map_eq_rect_cod, !CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_hex_left.
  - (* CTE_braid_hex_right *)
    cbn [CT_map].
    rewrite CT_map_eq_rect_cod, !CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_hex_right.
  - (* CTE_braid_unit_left *)
    rewrite CT_map_eq_rect_cod.
    cbn [CT_map]; apply CTE_braid_unit_left.
  - (* CTE_braid_unit_right *)
    rewrite CT_map_eq_rect_dom.
    cbn [CT_map]; apply CTE_braid_unit_right.
Qed.

(** ** Identity bookkeeping on terms

    The comparison maps of the induced monoidal functor below are all
    identities or tensors of identities, so its coherence squares are
    identity-collapsing equations — stated here over an arbitrary
    signature (the donor's copies in [Construction/PROP/Tietze.v]
    were the same quartet over [nat] boundaries).

    DUPLICATION NOTE: [Construction/ColouredPROP/Presentation.v]
    carries the same quartet, statement-for-statement, as
    [cterm_id_swap] / [cterm_comp_id_tens] / [cterm_collapse_r] /
    [cterm_collapse_l], specialised to its section signature.  Any
    change here should be mirrored there; the natural shared home for
    a hoisted version would be [TermEq.v], which both files already
    import. *)

(** An identity slides from one side of a morphism to the other. *)
Lemma ctm_id_swap {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (t : CTerm S cs ds) :
  CTermEq S (CT_comp t (CT_id cs)) (CT_comp (CT_id ds) t).
Proof.
  apply CTE_trans with t.
  - apply CTE_id_right.
  - apply CTE_sym, CTE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. *)
Lemma ctm_comp_id_tens {Colour : Type} {S : CSignature Colour}
  (m n : list Colour) :
  CTermEq S (CT_comp (CT_id (m ++ n)) (CT_id (m ++ n)))
            (CT_tens (CT_id m) (CT_id n)).
Proof.
  apply CTE_trans with (CT_id (m ++ n)).
  - apply CTE_id_left.
  - apply CTE_sym, CTE_tens_id.
Qed.

(** Collapsing an identity and a tensor of identities after [t]. *)
Lemma ctm_collapse_r {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S (m ++ n) p) :
  CTermEq S (CT_comp (CT_comp t (CT_id (m ++ n)))
                     (CT_tens (CT_id m) (CT_id n))) t.
Proof.
  apply CTE_trans with (CT_comp t (CT_tens (CT_id m) (CT_id n))).
  - apply CTE_comp_cong.
    + apply CTE_id_right.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp t (CT_id (m ++ n))).
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply CTE_tens_id.
    + apply CTE_id_right.
Qed.

(** Collapsing an identity and a tensor of identities before [t]. *)
Lemma ctm_collapse_l {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S p (m ++ n)) :
  CTermEq S (CT_comp (CT_comp (CT_id (m ++ n))
                              (CT_tens (CT_id m) (CT_id n))) t) t.
Proof.
  apply CTE_trans with (CT_comp (CT_tens (CT_id m) (CT_id n)) t).
  - apply CTE_comp_cong.
    + apply CTE_id_left.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp (CT_id (m ++ n)) t).
    + apply CTE_comp_cong.
      * apply CTE_tens_id.
      * apply CTE_refl.
    + apply CTE_id_left.
Qed.

(** ** The induced functor of free coloured PROPs

    A signature morphism [h : CSubSig S T] induces [CInjFunctor h :
    CFreeCat S ⟶ CFreeCat T] — identity on objects (colour words),
    [CT_map h] on morphisms — and the functor is STRICT SYMMETRIC
    monoidal: both comparison maps are identities on the nose, the
    object equalities are [eq_refl], and the braid square commutes
    because [CT_map] fixes [CT_braid].  The packaging mirrors the
    one-sorted donor's [InjFunctor] tower of [Construction/PROP/
    Tietze.v], with the monoidal instances drawn from the ONE shared
    record [CFreeCat_Monoidal _ Cdec] (see the D2 WARNING at the foot
    of [Construction/ColouredPROP/Monoidal.v]: fix one canonical
    [Cdec] per colour type). *)

Section CSignatureMorphism.

Context {Colour : Type}.
Context (S T : CSignature Colour).
Context (h : CSubSig S T).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

Definition CInjFunctor : CFreeCat S ⟶ CFreeCat T :=
  Build_Functor (CFreeCat S) (CFreeCat T)
    (fun cs : list Colour => cs)
    (fun cs ds (t : CTerm S cs ds) => CT_map h t)
    (fun cs ds s t Hst => CT_map_CTermEq h Hst)
    (fun cs => CTE_refl (CT_id cs))
    (fun x y z f g => CTE_refl (CT_comp (CT_map h f) (CT_map h g))).

(** The tensor-then-map and map-then-tensor composites related by the
    tensor comparison of the monoidal structure. *)
Definition CInj_ap_dom : CFreeCat S ∏ CFreeCat S ⟶ CFreeCat T :=
  CFreeCat_Tensor T ◯ (CInjFunctor ∏⟶ CInjFunctor).

Definition CInj_ap_cod : CFreeCat S ∏ CFreeCat S ⟶ CFreeCat T :=
  CInjFunctor ◯ CFreeCat_Tensor S.

(** Both directions of the tensor comparison are families of
    identities — [CT_map] computes through [CT_tens], so the two
    functors have definitionally equal actions — and naturality is
    [ctm_id_swap]. *)
Definition CInj_ap_to : CInj_ap_dom ⟹ CInj_ap_cod :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) (CFreeCat T)
    CInj_ap_dom CInj_ap_cod
    (fun p => CT_id (fst p ++ snd p))
    (fun p q f => ctm_id_swap (CT_tens (CT_map h (fst f)) (CT_map h (snd f)))).

Definition CInj_ap_from : CInj_ap_cod ⟹ CInj_ap_dom :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) (CFreeCat T)
    CInj_ap_cod CInj_ap_dom
    (fun p => CT_id (fst p ++ snd p))
    (fun p q f => ctm_id_swap (CT_tens (CT_map h (fst f)) (CT_map h (snd f)))).

(** The identity components are inverse up to [CTermEq] (the identity
    natural transformation of a composite-with-tensor functor has
    components [CT_tens (CT_id _) (CT_id _)]). *)
Definition CInj_ap_iso :
  @Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S)
                  (CFreeCat T))
    CInj_ap_dom CInj_ap_cod :=
  @Build_Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S)
                        (CFreeCat T))
    CInj_ap_dom CInj_ap_cod
    CInj_ap_to CInj_ap_from
    (fun p => ctm_comp_id_tens (fst p) (snd p))
    (fun p => ctm_comp_id_tens (fst p) (snd p)).

(** *** The coherence squares

    Each structural map of [CFreeCat_Monoidal] is a [CT_cast], which
    [CT_map] fixes ([CT_map_CT_cast]); after that rewrite the squares
    are pure identity bookkeeping. *)

Lemma CInj_unit_left_square (x : list Colour) :
  CTermEq T (CT_cast (app_nil_l x))
    (CT_comp (CT_comp (CT_map h (CT_cast (app_nil_l x))) (CT_id ([] ++ x)))
             (CT_tens (CT_id []) (CT_id x))).
Proof.
  rewrite (CT_map_CT_cast h (app_nil_l x)).
  apply CTE_sym, ctm_collapse_r.
Qed.

Lemma CInj_unit_right_square (x : list Colour) :
  CTermEq T (CT_cast (app_nil_r x))
    (CT_comp (CT_comp (CT_map h (CT_cast (app_nil_r x))) (CT_id (x ++ [])))
             (CT_tens (CT_id x) (CT_id []))).
Proof.
  rewrite (CT_map_CT_cast h (app_nil_r x)).
  apply CTE_sym, ctm_collapse_r.
Qed.

Lemma CInj_assoc_square (x y z : list Colour) :
  CTermEq T
    (CT_comp (CT_comp (CT_map h (CT_cast (eq_sym (app_assoc x y z))))
                      (CT_id ((x ++ y) ++ z)))
             (CT_tens (CT_id (x ++ y)) (CT_id z)))
    (CT_comp (CT_comp (CT_id (x ++ (y ++ z)))
                      (CT_tens (CT_id x) (CT_id (y ++ z))))
             (CT_cast (eq_sym (app_assoc x y z)))).
Proof.
  rewrite (CT_map_CT_cast h (eq_sym (app_assoc x y z))).
  apply CTE_trans with (CT_cast (eq_sym (app_assoc x y z))).
  - apply ctm_collapse_r.
  - apply CTE_sym, ctm_collapse_l.
Qed.

(** The strong monoidal structure: the unit comparison is [iso_id],
    the tensor comparison is the identity family [CInj_ap_iso], and
    the three coherence squares are the lemmas above.  Both [Monoidal]
    instances are the shared records [CFreeCat_Monoidal _ Cdec]. *)
Definition CInjFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CInjFunctor :=
  @Build_MonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CInjFunctor
    iso_id
    CInj_ap_iso
    (fun x => iso_id)
    (fun x => iso_id)
    (fun x y z => @tensor_assoc (CFreeCat T) (CFreeCat_Monoidal T Cdec) x y z)
    (fun x => CInj_unit_left_square x)
    (fun x => CInj_unit_right_square x)
    (fun x y z => CInj_assoc_square x y z).

(** Both comparison maps are identities on the nose, so the functor is
    STRICT monoidal with [eq_refl] object equalities; the two
    comparison fields reduce to [CTE_refl]-grade goals. *)
Definition CInjFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CInjFunctor :=
  @Build_StrictMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal T Cdec) CInjFunctor
    CInjFunctor_Monoidal
    eq_refl
    (fun x y => eq_refl)
    (CTE_refl (CT_id []))
    (fun x y => CTE_refl (CT_id (x ++ y))).

(** The braid-compatibility square: [CT_map] fixes [CT_braid], and
    both tensor comparisons are identities, so the square is one slide
    of an identity past the braid. *)
Lemma CInjFunctor_braid (m n : list Colour) :
  fmap[CInjFunctor] (@braid (CFreeCat S) (CFreeCat_Braided S Cdec) m n)
    ∘ to (@ap_iso _ _ _ _ CInjFunctor CInjFunctor_Monoidal m n)
  ≈[CFreeCat T]
  to (@ap_iso _ _ _ _ CInjFunctor CInjFunctor_Monoidal n m)
    ∘ @braid (CFreeCat T) (CFreeCat_Braided T Cdec) m n.
Proof.
  exact (ctm_id_swap (CT_braid m n)).
Qed.

Definition CInjFunctor_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided T Cdec) CInjFunctor :=
  @Build_BraidedMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided T Cdec) CInjFunctor
    CInjFunctor_Monoidal
    (fun x y => ctm_id_swap (CT_braid x y)).

(** A braided monoidal functor between symmetric monoidal categories
    IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition CInjFunctor_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) (CFreeCat T)
    (CFreeCat_Symmetric S Cdec) (CFreeCat_Symmetric T Cdec) CInjFunctor :=
  CInjFunctor_Braided.

End CSignatureMorphism.

Arguments CInjFunctor {Colour S T} h : assert.
Arguments CInjFunctor_Monoidal {Colour S T} h Cdec : assert.
Arguments CInjFunctor_Strict {Colour S T} h Cdec : assert.
Arguments CInjFunctor_Braided {Colour S T} h Cdec : assert.
Arguments CInjFunctor_Symmetric {Colour S T} h Cdec : assert.

(** ** Machine-checked sanity

    [CT_map] computes on the structural constructors, so the functor
    action of [CInjFunctor] is definitional, and the sub-signature
    algebra of [Signature.v] is respected on the nose. *)

Example CT_map_fixes_id {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs : list Colour) :
  CT_map h (CT_id cs) = CT_id cs := eq_refl.

Example CT_map_fixes_braid {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs ds : list Colour) :
  CT_map h (CT_braid cs ds) = CT_braid cs ds := eq_refl.

Example CT_map_computes_comp {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b c : list Colour}
  (g : CTerm S b c) (f : CTerm S a b) :
  CT_map h (CT_comp g f) = CT_comp (CT_map h g) (CT_map h f) := eq_refl.

Example CT_map_computes_tens {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CT_map h (CT_tens f g) = CT_tens (CT_map h f) (CT_map h g) := eq_refl.

Example CT_map_relabels_gen {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) {cs ds : list Colour} (g : S cs ds) :
  CT_map h (CT_gen g) = CT_gen (h cs ds g) := eq_refl.

Example CT_map_id_sig {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (g : S cs ds) :
  CT_map (CSubSig_id S) (CT_gen g) = CT_gen g := eq_refl.

Example CT_map_compose_sig {Colour : Type} {S T U : CSignature Colour}
  (h2 : CSubSig T U) (h1 : CSubSig S T)
  {cs ds : list Colour} (g : S cs ds) :
  CT_map (CSubSig_compose h2 h1) (CT_gen g)
  = CT_map h2 (CT_map h1 (CT_gen g)) := eq_refl.

Example CInjFunctor_obj_id {Colour : Type} {S T : CSignature Colour}
  (h : CSubSig S T) (cs : list Colour) :
  fobj[CInjFunctor h] cs = cs := eq_refl.
