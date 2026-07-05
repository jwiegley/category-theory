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
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
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

From Coq Require Import Arith.

Generalizable All Variables.

(** * The universal property of the free PROP *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   Given a signature [S], a PROP [P], and a valuation [v] of the
   generators, this file packages the interpretation
   [interp : Term S m n → (⟦m⟧ ~{P}~> ⟦n⟧)] of
   [Construction/PROP/Interp.v] into a functor [InterpF : FreeCat S ⟶ P]
   and equips it with the full strict-symmetric-monoidal structure,
   then proves it UNIQUE among such functors: the free PROP [FreePROP S]
   is initial among PROPs with an [S]-valuation.

   The strictness comparisons of [InterpF] ride the PROP class fields
   VERBATIM: [strict_pure_obj] is [prop_unit_zero] and [strict_ap_obj]
   is [prop_tensor_plus] (machine-checked by [Example]s below), so the
   universal property really is stated against the strict object
   equalities every PROP carries.

   ** Design note: how "strict symmetric monoidal functor" is phrased

   A PROP carries two [Monoidal] structures on the same category — the
   strict path [MP P] and the braided/symmetric path [MB P] — related
   only by the propositional equality [prop_monoidal_coherence].  The
   Phase-1 classes [StrictMonoidalFunctor] (at [MP P]) and
   [BraidedMonoidalFunctor] (at [MB P]) therefore carry INDEPENDENT
   [MonoidalFunctor] fields over propositionally-different target
   monoidals, and a hypothesis pack made of one instance of each would
   be underdetermined (nothing would relate their two tensor
   comparisons).  Uniqueness is instead phrased against ONE
   [StrictMonoidalFunctor] plus [SymmetricStrict]: the braid
   compatibility square over that SAME [ap_iso], with the braiding
   re-indexed to the strict path by [strict_braid] (the transport of
   [Interp.v]).  For competitors arriving with a genuine Phase-1
   [BraidedMonoidalFunctor], the converse bridge
   [SymmetricStrict_of_Braided] converts (given the agreement of the
   two tensor comparisons across the coherence transport), and
   [InterpF_Braided] / [InterpF_Symmetric] deliver [InterpF] itself in
   the Phase-1 classes via the match-based [MonoidalFunctor_transport].

   ** Uniqueness

   [interp_unique] pins any [SymmetricStrict] competitor [G] that
   agrees with [v] on generators: the object agreement is a family
   [Hobj : ∀ n, G n = ⟦n⟧] of Leibniz equalities, and the morphism
   agreement is phrased by conjugating with [hom_cast] along it.  The
   theorem holds for an ARBITRARY such family — axiom-free UIP on
   [obj P] (the [ObjDecEq] class) makes any two proofs of the same
   object equality interchangeable — and the corollary
   [interp_unique_from_one] derives the whole family from the single
   datum [G 1 = ⟦1⟧] via the [G_obj] fixpoint.  [interp_unique2] is the
   resulting agreement of any two competitors.  The existence half is
   named as well: [InterpF_extends_valuation] records (by [eq_refl])
   that [InterpF] extends the valuation, and
   [InterpF_interp_unique_self] instantiates the hypothesis pack of
   [interp_unique] at [InterpF] itself, with [Hobj := eq_refl].

   The named coherence lemmas of section 2 ([interp_ap_natural],
   [interp_monoidal_unit_left/right], [interp_monoidal_assoc],
   [interp_braid_ap]) are deliberately standalone: their statements are
   purely target-side, so [Construction/PROP/Presentation/Universal.v]
   reuses them verbatim for the presented PROP. *)

(** ** Transporting a [MonoidalFunctor] across a [Monoidal] equality

    The coherence [prop_monoidal_coherence] of a PROP is a
    propositional equality between two [Monoidal] records on the same
    category.  A monoidal functor into one of them transports to the
    other by dependent elimination; as in the [BraidTransport] section
    of [Interp.v], every lemma about the transport destructs a VARIABLE
    equality, so the concrete coherence proof is never eliminated in
    any goal. *)

Definition MonoidalFunctor_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D} :
  @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N2 F :=
  match e in _ = N
        return @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N F
  with eq_refl => fun X => X end.

(** The tensor comparison of the transported functor is the original
    one, transported along the same equality.  Exported kit with no
    in-tree consumer yet: the braid-square transfers below are
    discharged by [SymmetricStrict_square_transport] and
    [SymmetricStrict_untransport], which move whole squares across the
    coherence rather than lone comparisons. *)
Lemma ap_iso_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D}
  (MF : @MonoidalFunctor C D MC N1 F) (x y : C) :
  to (@ap_iso C D MC N2 F (MonoidalFunctor_transport e MF) x y)
  = match e in _ = N
          return ((F x ⨂[N] F y)%object ~{D}~> F ((x ⨂[MC] y)%object))
    with eq_refl => to (@ap_iso C D MC N1 F MF x y) end.
Proof. destruct e; reflexivity. Qed.

Section Universal.

Context (S : Signature).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.
Context (v : Valuation P S).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(** ** 1. The interpretation functor

    Objects go to [prop_of_nat]; morphisms go through [interp].
    Respectfulness is exactly the soundness theorem of [Interp.v], and
    the functor laws hold by computation, because [interp] reduces on
    the [T_id] and [T_comp] constructors. *)

Lemma InterpF_fmap_id (n : nat) :
  interp P S v (T_id n) ≈ id[⟦n⟧].
Proof. reflexivity. Qed.

Lemma InterpF_fmap_comp {m n p : nat} (f : Term S n p) (g : Term S m n) :
  interp P S v (T_comp f g) ≈ interp P S v f ∘ interp P S v g.
Proof. reflexivity. Qed.

(* Built with an explicit [Build_Functor] so that the source and target
   categories are pinned (the [QuotientProj] discipline of
   [Construction/Quotient.v]); a bare record literal would try to infer
   them from the field values, which live in [nat] and [P]. *)
Definition InterpF : FreeCat S ⟶ P :=
  Build_Functor (FreeCat S) P
    (@prop_of_nat P)
    (fun m n t => interp P S v t)
    (fun m n s t Hst => interp_sound P S v Hst)
    InterpF_fmap_id
    (fun m n p f g => InterpF_fmap_comp f g).

(** Machine-checked: [InterpF] EXTENDS the valuation — every generator
    is sent to its assigned morphism, definitionally.  Together with
    [InterpF_interp_unique_self] below, this is the existence half of
    the universal property in named form. *)
Example InterpF_extends_valuation (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g) = v m n g := eq_refl.

(** ** 2. Named coherence lemmas

    Every statement is purely target-side (only [P]-morphisms appear),
    so [Presentation/Universal.v] can reuse them for the presented
    PROP, whose structural maps are the very same [T_cast] terms.

    The [_general] lemmas quantify over the object equalities: after
    destructing them, the single non-destructible residue is aligned
    with the canonical strict equality by [obj_uip] (axiom-free UIP on
    [obj P], from [ObjDecEq]). *)

(** Naturality of the tensor-comparison cast against [interp]: the
    conjugating cast of [⊞] cancels its inverse. *)
Lemma interp_ap_natural {m n m' n'} (f : Term S m m') (g : Term S n n') :
  interp P S v (T_tens f g) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus m' n')
        ∘ (interp P S v f ⨂[MP P] interp P S v g).
Proof.
  cbn [interp].
  unfold prop_tensor_hom.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** The inverse-direction square, by flipping across the casts. *)
Lemma interp_ap_natural_from {m n m' n'} (f : Term S m m') (g : Term S n n') :
  (interp P S v f ⨂[MP P] interp P S v g)
      ∘ id_cast (eq_sym (prop_tensor_plus m n))
    ≈ id_cast (eq_sym (prop_tensor_plus m' n'))
        ∘ interp P S v (T_tens f g).
Proof.
  apply id_cast_flip.
  apply interp_ap_natural.
Qed.

(** General left-unit coherence: with every comparison an [id_cast],
    the left-unitality square collapses to the strict unitor. *)
Lemma to_unit_left_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (u ⨂[MP P] w)%object = s) (d : s = w) :
  to (@unit_left P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id_cast eu ⨂[MP P] id[w]).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_left_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitl_cast.
Qed.

(** General right-unit coherence. *)
Lemma to_unit_right_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (w ⨂[MP P] u)%object = s) (d : s = w) :
  to (@unit_right P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id[w] ⨂[MP P] id_cast eu).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_right_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitr_cast.
Qed.

(** General associativity coherence. *)
Lemma to_assoc_cast_general {a b c ab bc u w : P}
  (eab : (a ⨂[MP P] b)%object = ab)
  (ebc : (b ⨂[MP P] c)%object = bc)
  (eu : (ab ⨂[MP P] c)%object = u)
  (ew : (a ⨂[MP P] bc)%object = w)
  (d : u = w) :
  id_cast d ∘ id_cast eu ∘ (id_cast eab ⨂[MP P] id[c])
    ≈ id_cast ew ∘ (id[a] ⨂[MP P] id_cast ebc)
        ∘ to (@tensor_assoc P (MP P) a b c).
Proof using OD P.
  destruct eab, ebc, eu, ew.
  rewrite !id_cast_refl.
  rewrite !bimap_id_id.
  rewrite (obj_uip d (strict_assoc_obj a b c)).
  rewrite !id_right, !id_left.
  apply strict_assoc_cast.
Qed.

(** The left-unitality field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_unit_left (x : nat) :
  to (@unit_left P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_l x))
        ∘ id_cast (prop_tensor_plus 0 x)
        ∘ (id_cast (@prop_unit_zero P) ⨂[MP P] id[⟦x⟧]).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_left_cast_general.
Qed.

(** The right-unitality field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_unit_right (x : nat) :
  to (@unit_right P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_r x))
        ∘ id_cast (prop_tensor_plus x 0)
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (@prop_unit_zero P)).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_right_cast_general.
Qed.

(** The associativity field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_assoc (x y z : nat) :
  interp P S v (T_cast (eq_sym (Nat.add_assoc x y z)))
      ∘ id_cast (prop_tensor_plus (x + y) z)
      ∘ (id_cast (prop_tensor_plus x y) ⨂[MP P] id[⟦z⟧])
    ≈ id_cast (prop_tensor_plus x (y + z))
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (prop_tensor_plus y z))
        ∘ to (@tensor_assoc P (MP P) ⟦x⟧ ⟦y⟧ ⟦z⟧).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_assoc_cast_general.
Qed.

(** The braid-compatibility square of [interp] against the target's
    strict-path braiding [strict_braid]. *)
Lemma interp_braid_ap (m n : nat) :
  interp P S v (T_braid m n) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus n m) ∘ strict_braid P ⟦m⟧ ⟦n⟧.
Proof.
  cbn [interp].
  unfold prop_braid.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** ** 3. The strong and strict monoidal structure on [InterpF]

    The tensor comparison is the [prop_tensor_plus] cast, packaged as
    a natural isomorphism in the functor category. *)

Definition InterpF_ap_dom : FreeCat S ∏ FreeCat S ⟶ P :=
  @tensor P (MP P) ◯ InterpF ∏⟶ InterpF.

Definition InterpF_ap_cod : FreeCat S ∏ FreeCat S ⟶ P :=
  InterpF ◯ @tensor (FreeCat S) (FreeCat_Monoidal S).

Definition InterpF_ap_to : InterpF_ap_dom ⟹ InterpF_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_dom InterpF_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural (fst f) (snd f)).

Definition InterpF_ap_from : InterpF_ap_cod ⟹ InterpF_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_cod InterpF_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from (fst f) (snd f)).

(** The two composites are the identity transformation, componentwise.
    (In the functor category the identity's component at [mn] is
    [fmap id], which on each side reduces to a tensor of identities.) *)
Lemma InterpF_ap_to_from (mn : FreeCat S ∏ FreeCat S) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P S v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma InterpF_ap_from_to (mn : FreeCat S ∏ FreeCat S) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P S v (T_id (fst mn)) ⨂[MP P] interp P S v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition InterpF_ap_iso :
  InterpF_ap_dom ≅[[FreeCat S ∏ FreeCat S, P]] InterpF_ap_cod := {|
  to := InterpF_ap_to;
  from := InterpF_ap_from;
  iso_to_from := InterpF_ap_to_from;
  iso_from_to := InterpF_ap_from_to
|}.

(** The strong monoidal structure.  All proof fields are the named
    lemmas of section 2; the derived-iso data fields are casts. *)
Program Definition InterpF_Monoidal :
  @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := InterpF_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left;
  monoidal_unit_right := interp_monoidal_unit_right;
  monoidal_assoc := interp_monoidal_assoc
|}.

(** The comparisons ARE the PROP's strictness equalities, verbatim. *)
Lemma InterpF_strict_pure_iso_id :
  to (@pure_iso _ _ _ _ InterpF InterpF_Monoidal)
    ≈ match @prop_unit_zero P in _ = T return @I P (MP P) ~{P}~> T
      with eq_refl => id end.
Proof. reflexivity. Qed.

Lemma InterpF_strict_ap_iso_id (x y : nat) :
  to (@ap_iso _ _ _ _ InterpF InterpF_Monoidal x y)
    ≈ match @prop_tensor_plus P x y in _ = T
            return ((InterpF x ⨂[MP P] InterpF y)%object ~{P}~> T)
      with eq_refl => id end.
Proof. reflexivity. Qed.

Program Definition InterpF_Strict :
  @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  strict_functor_is_monoidal := InterpF_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y;  (* ditto *)
  strict_pure_iso_id := InterpF_strict_pure_iso_id;
  strict_ap_iso_id := InterpF_strict_ap_iso_id
|}.

(** Machine-checked: the strict object comparisons of [InterpF_Strict]
    are the PROP class fields themselves. *)
Example InterpF_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ InterpF InterpF_Strict = @prop_unit_zero P
  := eq_refl.

Example InterpF_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ InterpF InterpF_Strict x y = @prop_tensor_plus P x y
  := eq_refl.

(** ** 4. Symmetry

    [SymmetricStrict G MG] is the braid-compatibility square of a
    monoidal functor [G] over ITS OWN tensor comparison, with the
    target braiding re-indexed to the strict path by [strict_braid].
    See the header for why uniqueness is phrased against this bundle
    rather than against the two independent Phase-1 classes. *)

Definition SymmetricStrict (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G) : Type :=
  ∀ m n : nat,
    fmap[G] (T_braid m n) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma InterpF_SymmetricStrict : SymmetricStrict InterpF InterpF_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap m n).
Qed.

(** *** Bridges to the Phase-1 braided/symmetric functor classes

    The braid square at the transported functor is the braid square at
    the original functor against the transported braid family; both
    lemmas destruct a VARIABLE [Monoidal] equality, so the concrete
    [prop_monoidal_coherence] is never eliminated in a goal. *)

Lemma SymmetricStrict_square_transport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (b : braid_family N2) (x y : nat) :
  fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y) →
  fmap[G] (T_braid x y)
      ∘ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
    ≈ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) y x)
        ∘ b (G x) (G y).
Proof.
  revert b; destruct e; intros b H.
  exact H.
Qed.

(** The converse direction: a braid square at the transported functor
    comes back to one at the original, against the transported braid. *)
Lemma SymmetricStrict_untransport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (MG' : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N2 G)
  (b : braid_family N2)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
       ≈ to (@ap_iso _ _ _ _ G MG' x y))
  (Hsq : ∀ x y : nat,
     fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG' x y)
       ≈ to (@ap_iso _ _ _ _ G MG' y x) ∘ b (G x) (G y)) :
  ∀ x y : nat,
    fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y).
Proof.
  revert MG' b Hap Hsq; destruct e; intros MG' b Hap Hsq x y.
  simpl in Hap.
  rewrite (Hap x y), (Hap y x).
  exact (Hsq x y).
Qed.

(** [InterpF] as a Phase-1 [BraidedMonoidalFunctor]: the underlying
    strong structure is [InterpF_Monoidal] transported across the
    coherence, and the braid square is [InterpF_SymmetricStrict]. *)
Program Definition InterpF_Braided :
  @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
    (@symmetric_is_braided P (@prop_symmetric P)) InterpF := {|
  braided_is_strong :=
    MonoidalFunctor_transport (@prop_monoidal_coherence P) InterpF_Monoidal
|}.
Next Obligation.
  exact (SymmetricStrict_square_transport (@prop_monoidal_coherence P)
           InterpF InterpF_Monoidal
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           x y (InterpF_SymmetricStrict x y)).
Qed.

(** [SymmetricMonoidalFunctor] is a [Definition] alias in Phase 1, so
    the instance is supplied explicitly rather than by class search. *)
Definition InterpF_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) P (FreeCat_Symmetric S)
    (@prop_symmetric P) InterpF := InterpF_Braided.

(** Competitors arriving with a Phase-1 [BraidedMonoidalFunctor]
    convert to [SymmetricStrict], given that their two tensor
    comparisons agree across the coherence transport. *)
Corollary SymmetricStrict_of_Braided
  (G : FreeCat S ⟶ P)
  (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G)
  (BG : @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
          (@symmetric_is_braided P (@prop_symmetric P)) G)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G
           (MonoidalFunctor_transport (@prop_monoidal_coherence P)
              (@strict_functor_is_monoidal _ _ _ _ G SG)) x y)
       ≈ to (@ap_iso _ _ _ _ G (@braided_is_strong _ _ _ _ G BG) x y)) :
  SymmetricStrict G SG.
Proof.
  exact (SymmetricStrict_untransport (@prop_monoidal_coherence P) G
           (@strict_functor_is_monoidal _ _ _ _ G SG)
           (@braided_is_strong _ _ _ _ G BG)
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           Hap
           (fun x y => @braid_compat _ _ _ _ G BG x y)).
Qed.

(** ** 5. Uniqueness

    The cast toolbox is the transport kit of
    [Construction/Quotient.v] — sliding a cast across an equation
    ([comp_cast_shift]), fusing nested cast conjugations
    ([id_cast_conj_fuse]), identifying conjugations along different
    proofs of the same object equalities ([id_cast_conj_irr], UIP),
    and round-tripping [hom_cast]s ([hom_cast_roundtrip]) — plus its
    monoidal extension [bimap_hom_cast] from
    [Construction/PROP/Interp.v]. *)

Section Uniqueness.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : S m n),
  fmap[G] (T_gen g)
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(** The tensor comparison of [SG], spelled as an [id_cast]. *)
Lemma G_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G SG x y). Qed.

(** Naturality of [SG]'s tensor comparison at a pair of terms. *)
Lemma G_ap_natural {m1 m2 n1 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  fmap[G] (T_tens f g)
      ∘ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
              m1 m2)
    ≈ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
            n1 n2)
        ∘ (fmap[G] f ⨂[MP P] fmap[G] g).
Proof.
  exact (naturality
           (to (@ap_functor_iso _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG)))
           (m1, m2) (n1, n2) (f, g)).
Qed.

(** Main uniqueness: any strict symmetric competitor agreeing with [v]
    on generators agrees with [interp] on every term, up to the
    [hom_cast] conjugation along the object family [Hobj].  The proof
    is a structural induction on terms; thanks to UIP on [obj P], it
    works for an ARBITRARY family [Hobj], with no coherence hypothesis
    relating its members. *)
Theorem interp_unique : ∀ m n (t : Term S m n),
  fmap[G] t ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (interp P S v t).
Proof using G HB Hgen Hobj OD P S SG v.
  intros m n t.
  induction t as [k | bm bn | cm cn cp tg IHg tf IHf
                  | m1 n1 m2 n2 tf IHf tg IHg | gm gn gs].
  - (* T_id *)
    cbn [interp].
    rewrite hom_cast_id.
    exact (@fmap_id (FreeCat S) P G k).
  - (* T_braid *)
    cbn [interp].
    unfold prop_braid.
    assert (Hb : fmap[G] (T_braid bm bn)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG bn bm)
                  ∘ strict_braid P (G bm) (G bn)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG bm bn))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply HB. }
    rewrite Hb.
    rewrite (strict_braid_cast P (eq_sym (Hobj bm)) (eq_sym (Hobj bn))).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_comp *)
    cbn [interp].
    rewrite <- (hom_cast_comp (eq_sym (Hobj cm)) (eq_sym (Hobj cn))
                  (eq_sym (Hobj cp))).
    rewrite <- IHg, <- IHf.
    exact (@fmap_comp (FreeCat S) P G cm cn cp tg tf).
  - (* T_tens *)
    cbn [interp].
    unfold prop_tensor_hom.
    assert (Ht : fmap[G] (T_tens tf tg)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG n1 n2)
                  ∘ (fmap[G] tf ⨂[MP P] fmap[G] tg)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG m1 m2))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply G_ap_natural. }
    rewrite Ht.
    rewrite IHf, IHg.
    rewrite (bimap_hom_cast P).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_gen *)
    apply Hgen.
Qed.

End Uniqueness.

(** *** Existence, machine-checked against the hypothesis pack

    [InterpF] itself — with its strict structure [InterpF_Strict], its
    braid square [InterpF_SymmetricStrict], and the object family
    [Hobj := eq_refl] (its object action is [prop_of_nat] on the nose)
    — satisfies the hypotheses of [interp_unique]: the generator
    agreement is [InterpF_extends_valuation] up to trivial casts, and
    instantiating the theorem at [InterpF] typechecks.  This is the
    named witness that the mediating functor of the existence half is
    itself pinned by the uniqueness half. *)

Example InterpF_generator_agreement (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g)
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (v m n g).
Proof. reflexivity. Qed.

Example InterpF_interp_unique_self (m n : nat) (t : Term S m n) :
  fmap[InterpF] t
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (interp P S v t).
Proof.
  exact (interp_unique InterpF InterpF_Strict InterpF_SymmetricStrict
           (fun k : nat => eq_refl) InterpF_generator_agreement m n t).
Qed.

(** *** Uniqueness from a single object datum

    The object family [Hobj] can be synthesised from the single
    equality [G 1 = ⟦1⟧]: zero-arity agreement is [strict_pure_obj]
    against [prop_unit_zero], and successor agreement peels one wire
    off with [strict_ap_obj] against [prop_tensor_plus], using the
    definitional facts [1 ⨂ k = 1 + k = S k] on the free side. *)

Section UniquenessFromOne.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint G_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1 (G_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary interp_unique_from_one
  (Hgen : ∀ m n (g : S m n),
     fmap[G] (T_gen g)
       ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    fmap[G] t ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n))
                         (interp P S v t).
Proof using G H1 HB OD P S SG v. exact (interp_unique G SG HB G_obj Hgen). Qed.

End UniquenessFromOne.

(** *** Agreement of competitors

    Any two strict symmetric functors that agree with [v] on the
    generators agree with each other on every term, after re-indexing
    both to the canonical objects. *)

Corollary interp_unique2
  (G1 : FreeCat S ⟶ P)
  (SG1 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G1)
  (HB1 : SymmetricStrict G1 SG1)
  (Hobj1 : ∀ n : nat, G1 n = ⟦n⟧)
  (Hgen1 : ∀ m n (g : S m n),
     fmap[G1] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj1 m)) (eq_sym (Hobj1 n)) (v m n g))
  (G2 : FreeCat S ⟶ P)
  (SG2 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G2)
  (HB2 : SymmetricStrict G2 SG2)
  (Hobj2 : ∀ n : nat, G2 n = ⟦n⟧)
  (Hgen2 : ∀ m n (g : S m n),
     fmap[G2] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj2 m)) (eq_sym (Hobj2 n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    hom_cast (Hobj1 m) (Hobj1 n) (fmap[G1] t)
      ≈ hom_cast (Hobj2 m) (Hobj2 n) (fmap[G2] t).
Proof using OD P S v.
  intros m n t.
  rewrite (interp_unique G1 SG1 HB1 Hobj1 Hgen1 m n t).
  rewrite (interp_unique G2 SG2 HB2 Hobj2 Hgen2 m n t).
  now rewrite !hom_cast_roundtrip.
Qed.

End Universal.

Arguments InterpF S P {HP OD} v : assert.
Arguments SymmetricStrict S P G MG : assert.
