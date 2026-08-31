(** * Base change along ℤ → R: the free R-module on an abelian group *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §IV.1, printed pp. 79–80 (PDF pp. 89–90) — adjunctions
              in hom-set form, whose running examples are the
              free/forgetful pairs; the unit is ⌊id⌋ and the whole
              content of such an example is naming the free construction
              and its insertion of generators.
   Book:      Mac Lane, ibid., §I.8, printed pp. 28–29 — the tensor
              product of abelian groups, which is the construction this
              file consumes (Instance/Ab/Tensor.v builds it).
   Book:      Riehl, "Category Theory in Context", Dover 2016, §4.1
              Example 4.1.10 — extension of scalars along a ring
              homomorphism is left adjoint to restriction of scalars.
              READ THE RELATION TO THAT EXAMPLE PRECISELY: hers runs
              between two MODULE categories, and this one runs out of
              [Ab].  See PRIOR ART below; the two are not instances of
              one another in this tree.
   nLab:      https://ncatlab.org/nlab/show/extension+of+scalars
   nLab:      https://ncatlab.org/nlab/show/free+module
   Wikipedia: https://en.wikipedia.org/wiki/Extension_of_scalars

   WHAT IS DELIVERED.

     - [ZExtObj R A : RModObject R], the abelian group R ⊗ A — the
       ℤ-tensor of Instance/Ab/Tensor.v — equipped with the scalar
       action r · (s ⊗ a) = (r s) ⊗ a.
     - [ZExtMap] and **[ZExt R : Ab ⟶ RMod R]**, the functor.
     - [zext_to] / [zext_from], the two transposes, and [zext_adj], the
       bijection as an [Isomorphism] of hom-setoids in [Sets].
     - **[zext_adjunction R : ZExt R ⊣ RMod_Forget_Ab R]**, an inhabitant
       of Theory/Adjunction.v's [Adjunction] record, built through
       [Build_Adjunction'] (whose two remaining naturality obligations
       both close by [reflexivity] — see the ledger below).
     - [zext_unit] and [zext_counit], with the reviewer check PINNED:
       **[zext_unit_is_gen] states that the adjunction's unit component
       at A, applied to a, IS [ts_gen 1 a], and it closes at [eq_refl]**.
     - A ℤ witness: [ZIntExt := ZExtObj Int_Ring (ring_ab Int_Ring)],
       i.e. ℤ ⊗ ℤ, with a computing evaluation map and non-degeneracy
       proved by MAPPING OUT.  Count those honestly: there are THREE
       lemmas but only TWO distinct propositions —
       [zext_int_unit_separates] is [exact zext_int_gens_distinct] and
       its statement is byte-identical, kept only because it is the one
       a reader looks for under that name.  Instance/Mod/Coextension.v's
       three ARE three distinct statements.

   NO COMMUTATIVITY HYPOTHESIS, AND THAT IS A THEOREM RATHER THAN A
   PREFERENCE.  The file's ONLY [Context] is [(R : RingObject)]; there is
   no [Rcomm]-style argument anywhere, and [About ZExtObj] /
   [About zext_adjunction] show the signatures taking a bare ring.  The
   two places a reader expects commutativity to be spent are exactly the
   two associativity clauses, and both go through on associativity alone:

     - [zext_act_assoc], the module law (r s) · x ≈ r · (s · x).  On a
       generator both sides are ((r s) t) ⊗ a and (r (s t)) ⊗ a, and the
       ONLY law consumed is [rig_mul_assoc].
     - [zext_from]'s [rm_map_smul] obligation, which is what makes the
       untranspose R-linear.  On a generator both sides are
       ((r s) · h a) and (r · (s · h a)), and the ONLY law consumed is
       [rm_smul_assoc] of the target module.

   This is a genuine contrast with Instance/Mod/Closed.v, whose own
   header localises its commutativity hypothesis to the single lemma
   [hm_smul_linear]: there r · φ must be shown LINEAR, and (r·φ)(s·v) is
   r · (s · φ v) where linearity demands s · (r · φ v), so the two
   scalars must be exchanged.  Here they never are — the scalar acts on
   the LEFT-HAND FACTOR of R ⊗ A and the module element never carries a
   scalar of its own, so no exchange is ever demanded.

   WHY A RING AND NOT A RIG.  [AbTensor] tensors two [AbObject]s, so the
   base must have additive inverses to be tensored at all.  [ring_neg] is
   spent NOWHERE in this file directly; its whole role is that
   [ring_ab R] is an object of [Ab].  A rig-level analogue would need a
   tensor of commutative monoids, which the tree does not have.

   WHAT IS REUSED, NOT REBUILT.

     - Instance/Ab/Tensor.v: [AbTensor], [Bilinear], [tensor_gen],
       [tensor_ump], **[tensor_hom_ext]**, and the relation constructors
       [te_gen], [te_bilin_l], [te_bilin_r], [te_trans], [te_sym].
     - Instance/Rng.v: [ring_ab], the additive group of a ring.
     - Instance/Mod.v: [RModObject], [RModHom], [RMod],
       **[RMod_Forget_Ab]** (the right adjoint, taken as given),
       [rm_smul_zero_r], [Ring_RMod], [Int_RMod].
     - Instance/Ab.v: [AbHom], [ab_cancel_l].
     - Instance/CMon.v: [cmon_hom_id] (:94) and [cmon_hom_compose]
       (:108) — declared there, not in Instance/Ab.v, which only uses
       them.
     - Structure/AbCategory.v: [ab_hom_add], the pointwise sum of two
       homomorphisms into an abelian group — which is what lets the
       right-distributivity law be stated as an agreement of two
       HOMOMORPHISMS and hence discharged by [tensor_hom_ext].
     - Theory/Adjunction.v: [Build_Adjunction'], [unit], [counit].

   NO INDUCTION IS PERFORMED, AND THAT IS MEASURED.  No [induction]
   tactic is invoked below; the only occurrences of the token anywhere in
   the file are the three in this paragraph, so [grep -n induction]
   returns exactly these lines.  Every module law, every functor law
   and both iso laws are an agreement of two HOMOMORPHISMS out of the
   tensor, discharged by [tensor_hom_ext] — the uniqueness half of the
   UMP — after checking generators; the one law that is not is
   [rm_smul_distr_l], which is literally [cmon_map_plus] of the mediator
   and holds by [reflexivity] because [tensor_med_fun] is a [Fixpoint].
   The single induction the development rests on lives in the donor.

   WHICH LEMMA SPENDS WHICH LAW.  Read as a ledger; nothing else of R is
   consumed, and in particular [rig_mul_zero_l], [rig_mul_zero_r] and
   [ring_neg] are spent nowhere directly.

     [zext_bilin]        respectfulness ← [rig_mul_respects]
                         additivity in the scalar ← [rig_distr_l]
                         additivity in the group ← [te_bilin_r] alone
     [zext_smul_scalar]  ← [rig_mul_respects]
     [zext_act_distr_r]  ← [rig_distr_r]
     [zext_act_assoc]    ← [rig_mul_assoc]        (associativity ONLY)
     [zext_act_one]      ← [rig_mul_one_l]
     [zext_gen_zero_r]   ← [ab_cancel_l] of the TENSOR (s ⊗ 0 ≈ 0 is not
                           a constructor of the quotient; it is derived)
     [zext_to]           zero ← [zext_gen_zero_r]; sum ← [te_bilin_r]
     [zext_map_bilin]    ← nothing of R; [te_bilin_l] and [cmon_map_plus]
                           of the given f
     [zext_lmul]         ← [rm_smul_respects], [rm_smul_zero_r],
                           [rm_smul_distr_l] of M
     [zext_from_bilin]   ← [rm_smul_respects], [rm_smul_distr_r],
                           [rm_smul_distr_l] of M
     [zext_from]         ← [rm_smul_assoc] of M   (associativity ONLY)
     [zext_adj] to∘from  ← [rm_smul_one] of M
     [zext_adj] from∘to  ← [rm_map_smul] of the given g, [rig_mul_one_r]
     [ZExtMap], [ZExt]'s [fmap_id] and [fmap_comp], and BOTH naturality
     obligations of [Build_Adjunction'] ← NOTHING; all [reflexivity].

   BOTH UNIT LAWS OF R ARE SPENT, AT DIFFERENT PLACES.  [rig_mul_one_l]
   closes the module law 1 · x ≈ x; [rig_mul_one_r] closes the round trip
   [zext_from (zext_to g)] ≈ g, where the residue is s · 1 in the scalar
   slot.  Over a non-commutative ring these are separate axioms, so this
   is a real observation and not bookkeeping.

   STRENGTHS, MEASURED STRICT-FIRST.  Eleven identifications close at
   [eq_refl] and are shipped as [Example]s:

     - the action on a generator ([zext_act_gen]);
     - **the unit at a: [ts_gen 1 a] ([zext_unit_is_gen])** — the
       reviewer check, and it is definitional rather than up to ≈;
     - the counit on a generator: s ⊗ m ↦ s · m
       ([zext_counit_is_smul]);
     - the adjunction's forward transpose IS [zext_to] and its backward
       transpose IS [zext_from] ([zext_adj_to_is_zext_to],
       [zext_adj_from_is_zext_from]) — so nothing downstream is reading a
       different map than the one the header names;
     - the functor's two actions ([zext_fobj_is_ZExtObj],
       [zext_fmap_is_ZExtMap]) and the right adjoint's object action
       ([zext_forget_is_rm_ab]);
     - over ℤ, [3 ⊗ 4 ↦ 12] and [0 ↦ 0] under the counit, and the unit
       at a computing to [1 ⊗ a].

   EXACTLY TWO IDENTIFICATIONS FALL BACK TO ≈, AND BOTH ARE ROUND TRIPS
   OF THE BIJECTION.  [zext_to (zext_from h)] evaluates to 1 · h a and
   [zext_from (zext_to g)] to (s · 1) ⊗ a; [rm_smul_one] and
   [rig_mul_one_r] are what remove the residues, and BOTH are abstract
   fields of a class, so neither side reduces and no downstream
   transparency would help.  Both are pinned as CONVERSION negatives with
   the ≈ forms beside them as controls.

   UNIVERSES, MEASURED AND ATTRIBUTED.  [ZExtObj] carries NO equation in
   its constraint block — the ring's three universes are only BOUNDED —
   while [ZExt] and [zext_adjunction] both carry [u = u1], identifying
   the ring's FIRST and THIRD universes.  Where that enters is measured
   rather than guessed, and it is NOT this file's: with the two levels
   declared strictly apart, [RMod Ru], [ring_ab Ru],
   [AbTensor (ring_ab Ru) Au], [ZExtObj Ru Au], [zext_act Ru Au],
   [zext_map_ab Ru fu], [RMod_Forget_Ab Ru], [Ab ⟶ RMod Ru] and
   Instance/Mod.v's own [Ring_RMod Ru] all elaborate, while
   [ZExtObj Ru Au : obj[RMod Ru]] is rejected — AND SO IS
   [Ring_RMod Ru : obj[RMod Ru]], at the same levels with the same
   message.  So the identification is Instance/Mod.v's, is met the moment
   any module is read as an OBJECT of [RMod R], and is inherited here
   rather than introduced.  It is not claimed unavoidable; no
   re-annotation was attempted.

   PRIOR ART, AND THREE FILES RECORD THIS EXACT ABSENCE.
   Instance/Ab/Free.v:87–91 says the tree "has only the forgetful
   direction ([RMod_Forget_Ab], Instance/Mod.v:300)";
   Instance/Mod/Quotient.v:139–145 says "an [AbObject] is not exhibited
   as a ℤ-module anywhere in the tree" and names
   Instance/Rng/Mod.v:675's [ZRestrict R : RMod R ⟶ RMod Int_Ring] as
   the near miss that is NOT it; Instance/Mod/Tensor.v:234 records the
   same.  A type-level sweep confirms it: before this file NO constant in
   the tree had type [Ab ⟶ RMod _] (zero hits), and no [AbTensor] is
   applied to a [ring_ab] anywhere else.

   BUT READ WHAT IS AND IS NOT DISCHARGED.  This file supplies a functor
   [Ab ⟶ RMod R] for every R, which is the direction those notes record
   as missing — yet at R := ℤ it sends A to ℤ ⊗ A, NOT to A carrying its
   own ℤ-action, and the two are isomorphic rather than equal (the
   carriers are [tsum] and A's own, pinned as CONVERSION negative 4 at
   the concrete witness).  So the reductions those three files want are
   NOT discharged here and nothing below claims they are.

   Distinct also from Instance/Mod/Extension.v, which is extension of
   scalars along an ARBITRARY ring homomorphism φ : R → S over
   Instance/Mod/Tensor.v's R-tensor, left adjoint to
   [Restrict φ : RMod S ⟶ RMod R].  Neither file is an instance of the
   other in this tree: at φ := ℤ → R that one's source is [RMod Int_Ring]
   and this one's is [Ab].  Say the obstruction precisely, because a
   blanket "no functor between those exists" would be FALSE and is
   refuted by this file's own ℤ witness: [RMod_Forget_Ab Int_Ring] is a
   functor [RMod Int_Ring ⟶ Ab], and [ZExt Int_Ring] is one the other
   way.  What is absent is the passage the reduction would need — an
   [Ab ⟶ RMod Int_Ring] carrying each abelian group ITS OWN ℤ-action,
   which is the absence quoted above and which [ZExt Int_Ring] is not,
   its carrier being ℤ ⊗ A rather than A's.  Nothing is shared, and
   that file is not
   [Require]d.  Distinct too from Instance/Mod/Free.v, whose [FreeMod] is
   left adjoint to [RMod_Forget : RMod R ⟶ Sets] — the free module on a
   SETOID, a different right adjoint.

   AXIOMS.  67/67 constants report "Closed under the global context"
   (43 source-declared plus 24 [Program] obligations that no source sweep
   sees; queried by fully qualified name).  Zero of the 67 names occur
   anywhere else in the tree, checked name by name.

   NEGATIVES.  Nine [Fail] commands: eight guarded negatives — three
   CONVERSION, one TYPING, four FORMABILITY — each beside an APPLIED
   positive control, plus one scope-free instrument check.  Each was
   stripped and compiled alone and its WHOLE error read; see the probe
   section at the end of the file for the classification.

   WHAT IS NOT DELIVERED.

     - No naturality of [zext_adj] in a THIRD variable and no
       identification of [ZExt] with any monoidal or bifunctorial
       structure; [AbTensor_Functor] is not consumed.
     - No comparison with Instance/Mod/Extension.v's [ExtendScalars] at
       any φ, and no bridge [Ab ≃ RMod Int_Ring]; consequently nothing
       here discharges the three absence notes quoted above.
     - No isomorphism ℤ ⊗ A ≅ A in [Ab], hence nothing says [ZExt ℤ] is
       equivalent to the identity; the ℤ witness pins ℤ ⊗ ℤ only through
       a map OUT of it.
     - No triangle identities restated in this file's own vocabulary
       (they are Theory/Adjunction.v's derived corollaries and are not
       specialised), and no uniqueness statement for the left adjoint.
     - No monad on [Ab] from the adjunction, no Eilenberg–Moore or
       Kleisli reading.
     - No normal form for the tensor, hence no basis, no rank and no
       decision procedure; every negative goes through a map OUT.
     - No right adjoint to [RMod_Forget_Ab] (coextension of scalars);
       the header's arithmetic for the coextension side —
       (r · (s · f))(t) = f(t (r s)) = ((r s) · f)(t), again
       associativity alone — is stated in issue #360 and is NOT
       formalised here.
     - No [RigObject] variant, no right-module or bimodule reading, and
       no instance registered for typeclass resolution: [ZExt] and
       [zext_adjunction] are plain [Definition]s. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section ZExtension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation TT A := (AbTensor (ring_ab R) A).
Local Notation ZG A s a := (@ts_gen (ring_ab R) A s a).

(** ** The scalar action *)

Program Definition zext_bilin (A : AbObject) (r : RS) :
  Bilinear (ring_ab R) A (TT A) := {|
  bilin_map := fun s a => ts_gen (rig_mul (ring_rig R) r s) a
|}.
Next Obligation.
  intros A r s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r (reflexivity r) s s' Hs) Ha).
Qed.
Next Obligation.
  intros A r s s' a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_l (ring_rig R) r s s') (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r s') a)).
Qed.
Next Obligation.
  intros A r s a a'.
  exact (@te_bilin_r (ring_ab R) A (rig_mul (ring_rig R) r s) a a').
Qed.

Definition zext_smul (A : AbObject) (r : RS) :
  AbHom (TT A) (TT A) := tensor_ump (zext_bilin A r).

Definition zext_act (A : AbObject) (r : RS)
  (x : carrier (cmon_setoid (TT A))) : carrier (cmon_setoid (TT A)) :=
  cmon_map (zext_smul A r) x.

Example zext_act_gen (A : AbObject) (r s : RS) (a : carrier A) :
  zext_act A r (ZG A s a) = ZG A (rig_mul (ring_rig R) r s) a := eq_refl.


(** ** The four module laws, each by agreement on generators *)

Lemma zext_smul_scalar (A : AbObject) (r r' : RS) :
  r ≈ r' → ∀ x, zext_act A r x ≈ zext_act A r' x.
Proof.
  intros Hr x.
  refine (tensor_hom_ext (zext_smul A r) (zext_smul A r') _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r' Hr s s (reflexivity s))
           (reflexivity a)).
Qed.

Lemma zext_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (zext_act A).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (zext_act A r y).
  - exact (proper_morphism (cmon_map (zext_smul A r)) x y Hxy).
  - exact (zext_smul_scalar A r r' Hr y).
Qed.

Lemma zext_act_distr_r (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (TT A) (zext_act A r x) (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_add (ring_rig R) r r'))
            (ab_hom_add (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_r (ring_rig R) r r' s) (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r' s) a)).
Qed.

Lemma zext_act_assoc (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_mul (ring_rig R) r r') x
    ≈ zext_act A r (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_assoc (ring_rig R) r r' s) (reflexivity a)).
Qed.

Lemma zext_act_one (A : AbObject) (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_one (ring_rig R)))
            (@cmon_hom_id (TT A)) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_l (ring_rig R) s) (reflexivity a)).
Qed.

Definition ZExtObj (A : AbObject) : RModObject R := {|
  rm_ab            := TT A;
  rm_smul          := zext_act A;
  rm_smul_respects := zext_act_respects A;
  rm_smul_distr_l  := fun r x y => cmon_map_plus (zext_smul A r) x y;
  rm_smul_distr_r  := zext_act_distr_r A;
  rm_smul_assoc    := zext_act_assoc A;
  rm_smul_one      := zext_act_one A
|}.

(** ** The arrow action, and the functor *)

Program Definition zext_map_bilin {A B : AbObject} (f : AbHom A B) :
  Bilinear (ring_ab R) A (TT B) := {|
  bilin_map := fun s a => ZG B s (cmon_map f a)
|}.
Next Obligation.
  intros A B f s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) B _ _ _ _ Hs
           (proper_morphism (cmon_map f) a a' Ha)).
Qed.
Next Obligation.
  intros A B f s s' a.
  exact (@te_bilin_l (ring_ab R) B s s' (cmon_map f a)).
Qed.
Next Obligation.
  intros A B f s a a'.
  exact (te_trans
           (@te_gen (ring_ab R) B _ _ _ _
              (reflexivity s) (cmon_map_plus f a a'))
           (@te_bilin_r (ring_ab R) B s (cmon_map f a) (cmon_map f a'))).
Qed.

Definition zext_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (TT A) (TT B) := tensor_ump (zext_map_bilin f).

Program Definition ZExtMap {A B : AbObject} (f : AbHom A B) :
  ZExtObj A ~{RMod R}~> ZExtObj B := {|
  rm_hom := zext_map_ab f
|}.
Next Obligation.
  intros A B f r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (zext_map_ab f) (zext_smul A r))
            (cmon_hom_compose (zext_smul B r) (zext_map_ab f)) _ x).
  intros s a; reflexivity.
Qed.

Program Definition ZExt : Ab ⟶ RMod R := {|
  fobj := ZExtObj;
  fmap := @ZExtMap
|}.
Next Obligation.
  intros A B f g Hfg x.
  refine (tensor_hom_ext (zext_map_ab f) (zext_map_ab g) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) B _ _ _ _ (reflexivity s) (Hfg a)).
Qed.
Next Obligation.
  intros A x.
  refine (tensor_hom_ext (zext_map_ab (@id Ab A))
            (@cmon_hom_id (TT A)) _ x).
  intros s a; reflexivity.
Qed.
Next Obligation.
  intros A B C f g x.
  refine (tensor_hom_ext (zext_map_ab (f ∘ g))
            (cmon_hom_compose (zext_map_ab f) (zext_map_ab g)) _ x).
  intros s a; reflexivity.
Qed.

(** ** The transposes *)

Lemma zext_gen_zero_r (A : AbObject) (s : RS) :
  (ZG A s (cmon_zero A) : carrier (cmon_setoid (TT A)))
    ≈ cmon_zero (TT A).
Proof.
  apply (ab_cancel_l (TT A) (ZG A s (cmon_zero A))).
  exact (te_trans
           (te_trans
              (te_sym (@te_bilin_r (ring_ab R) A s
                         (cmon_zero A) (cmon_zero A)))
              (@te_gen (ring_ab R) A _ _ _ _ (reflexivity s)
                 (cmon_plus_zero_l A (cmon_zero A))))
           (te_sym (cmon_plus_zero_r (TT A) (ZG A s (cmon_zero A))))).
Qed.

Program Definition zext_to {A : AbObject} {M : RModObject R}
  (g : ZExtObj A ~{RMod R}~> M) : A ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun a =>
    cmon_map (rm_hom g) (ZG A (rig_one (ring_rig R)) a) |}
|}.
Next Obligation.
  intros A M g a a' Ha; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@te_gen (ring_ab R) A _ _ _ _ (reflexivity _) Ha)).
Qed.
Next Obligation.
  intros A M g; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (TT A))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (zext_gen_zero_r A (rig_one (ring_rig R)))).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros A M g a b; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (TT A) (ZG A (rig_one (ring_rig R)) a)
                                    (ZG A (rig_one (ring_rig R)) b))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_bilin_r (ring_ab R) A (rig_one (ring_rig R)) a b)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition zext_lmul (M : RModObject R) (r : RS) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M r m |}
|}.
Next Obligation.
  intros M r m m' Hm.
  exact (rm_smul_respects M r r (reflexivity r) m m' Hm).
Qed.
Next Obligation. intros M r; simpl; exact (rm_smul_zero_r M r). Qed.
Next Obligation.
  intros M r m m'; simpl; exact (rm_smul_distr_l M r m m').
Qed.

Program Definition zext_from_bilin {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : Bilinear (ring_ab R) A (rm_ab M) := {|
  bilin_map := fun s a => rm_smul M s (cmon_map h a)
|}.
Next Obligation.
  intros A M h s s' Hs a a' Ha.
  exact (rm_smul_respects M s s' Hs _ _
           (proper_morphism (cmon_map h) a a' Ha)).
Qed.
Next Obligation.
  intros A M h s s' a.
  exact (rm_smul_distr_r M s s' (cmon_map h a)).
Qed.
Next Obligation.
  intros A M h s a a'.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map h a) (cmon_map h a'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus h a a')).
  - exact (rm_smul_distr_l M s (cmon_map h a) (cmon_map h a')).
Qed.

Program Definition zext_from {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : ZExtObj A ~{RMod R}~> M := {|
  rm_hom := tensor_ump (zext_from_bilin h)
|}.
Next Obligation.
  intros A M h r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (tensor_ump (zext_from_bilin h))
                              (zext_smul A r))
            (cmon_hom_compose (zext_lmul M r)
                              (tensor_ump (zext_from_bilin h))) _ x).
  intros s a.
  exact (rm_smul_assoc M r s (cmon_map h a)).
Qed.

(** ** The adjunction *)

Program Definition zext_adj_to (A : AbObject) (M : RModObject R) :
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |}
    ~{Sets}~>
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |} := {|
  morphism := fun g => zext_to g
|}.
Next Obligation. intros A M g g' Hg a; exact (Hg _). Qed.

Program Definition zext_adj_from (A : AbObject) (M : RModObject R) :
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |}
    ~{Sets}~>
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |} := {|
  morphism := fun h => zext_from h
|}.
Next Obligation.
  intros A M h h' Hh x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin h))
                         (tensor_ump (zext_from_bilin h')) _ x).
  intros s a.
  exact (rm_smul_respects M s s (reflexivity s) _ _ (Hh a)).
Qed.

Program Definition zext_adj (A : AbObject) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := ZExtObj A ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (ZExtObj A) M |}
    {| carrier := A ~{Ab}~> rm_ab M;
       is_setoid := @homset Ab A (rm_ab M) |} := {|
  to   := zext_adj_to A M;
  from := zext_adj_from A M
|}.
Next Obligation.
  intros A M h a.
  exact (rm_smul_one M (cmon_map h a)).
Qed.
Next Obligation.
  intros A M g x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin (zext_to g)))
                         (rm_hom g) _ x).
  intros s a.
  transitivity (cmon_map (rm_hom g)
                  (ZG A (rig_mul (ring_rig R) s
                           (rig_one (ring_rig R))) a)).
  - symmetry.
    exact (rm_map_smul g s (ZG A (rig_one (ring_rig R)) a)).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_gen (ring_ab R) A _ _ _ _
                (rig_mul_one_r (ring_rig R) s) (reflexivity a))).
Qed.

Definition zext_adjunction : ZExt ⊣ RMod_Forget_Ab R.
Proof.
  unshelve eapply (@Build_Adjunction' (RMod R) Ab ZExt
                     (RMod_Forget_Ab R) zext_adj).
  - intros A B M f g a; reflexivity.
  - intros A M N f g a; reflexivity.
Defined.

(** ** Unit, counit, and the strict readings *)

Definition zext_unit (A : AbObject) :
  A ~{Ab}~> rm_ab (ZExtObj A) :=
  @unit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A.

Definition zext_counit (M : RModObject R) :
  ZExtObj (rm_ab M) ~{RMod R}~> M :=
  @counit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction M.

(* THE REVIEWER CHECK.  The unit IS a |-> 1 (x) a, on the nose. *)
Example zext_unit_is_gen (A : AbObject) (a : carrier A) :
  cmon_map (zext_unit A) a = ZG A (rig_one (ring_rig R)) a := eq_refl.

Example zext_counit_is_smul (M : RModObject R) (s : RS)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom (zext_counit M)) (ZG (rm_ab M) s m)
    = rm_smul M s m := eq_refl.

Example zext_adj_to_is_zext_to (A : AbObject) (M : RModObject R)
  (g : ZExtObj A ~{RMod R}~> M) :
  to (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) g
    = zext_to g := eq_refl.

Example zext_adj_from_is_zext_from (A : AbObject) (M : RModObject R)
  (h : A ~{Ab}~> rm_ab M) :
  from (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) h
    = zext_from h := eq_refl.

Example zext_fobj_is_ZExtObj (A : AbObject) :
  fobj[ZExt] A = ZExtObj A := eq_refl.

Example zext_fmap_is_ZExtMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[ZExt] f = ZExtMap f := eq_refl.

Example zext_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End ZExtension.

(** ** A concrete witness over ℤ *)

Definition ZIntExt : RModObject Int_Ring :=
  ZExtObj Int_Ring (ring_ab Int_Ring).

Definition ZIntGen (s a : Z) : carrier (cmon_setoid (rm_ab ZIntExt)) :=
  @ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) s a.

Definition zext_int_eval : ZIntExt ~{RMod Int_Ring}~> Int_RMod :=
  zext_counit Int_Ring Int_RMod.

Example zext_int_eval_computes :
  cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4) = 12%Z := eq_refl.

Example zext_int_eval_zero :
  cmon_map (rm_hom zext_int_eval) (cmon_zero (rm_ab ZIntExt)) = 0%Z
  := eq_refl.

Example zext_int_unit_computes (a : Z) :
  cmon_map (zext_unit Int_Ring (ring_ab Int_Ring)) a = ZIntGen 1 a
  := eq_refl.

Lemma zext_int_gen_nonzero :
  ZIntGen 1 1 ≈ cmon_zero (rm_ab ZIntExt) → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_gens_distinct : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 2%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_unit_separates : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof. exact zext_int_gens_distinct. Qed.

(** ** Probes

    Every strength claim the header makes is pinned here, each negative
    beside an APPLIED positive control.  Each was stripped of its [Fail]
    and compiled alone, and its WHOLE error read: negatives 1, 2 and 4
    end in [cannot unify] (CONVERSION), negative 3 is a plain type
    mismatch with no [cannot unify] and no universe clause (TYPING), and
    negatives 5-8 end in [universe inconsistency: Cannot enforce rc = ra]
    (FORMABILITY). *)

Section ZExtProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (h : A ~{Ab}~> rm_ab M) (g : ZExtObj R A ~{RMod R}~> M).
Context (a : carrier A) (s : carrier (rig_setoid (ring_rig R))).

(* CONTROL for negative 1: the round trip DOES hold at ≈, and the proof
   term names the exact law that closes the gap. *)
Example zext_ctrl_to_from :
  cmon_map (zext_to R (zext_from R h)) a ≈ cmon_map h a
  := rm_smul_one M (cmon_map h a).

(* NEGATIVE 1 (CONVERSION).  [zext_to (zext_from h)] evaluates to
   1 · h a, and 1 · − is not the identity by conversion: [rm_smul_one]
   is an abstract field of [RModObject], so neither side reduces. *)
Fail Example zext_probe_to_from_strict :
  cmon_map (zext_to R (zext_from R h)) a = cmon_map h a := eq_refl.

(* CONTROL for negative 2. *)
Example zext_ctrl_from_to :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    ≈ cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a)
  := iso_from_to (zext_adj R A M) g _.

(* NEGATIVE 2 (CONVERSION).  The other round trip leaves an s · 1 in the
   scalar slot; [rig_mul_one_r] is what removes it, and it too is an
   abstract field. *)
Fail Example zext_probe_from_to_strict :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    = cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a) := eq_refl.

(* CONTROL for negative 3: the unit IS an arrow of [Ab]. *)
Check (zext_unit R A : A ~{Ab}~> rm_ab (ZExtObj R A)).

(* NEGATIVE 3 (TYPING).  It is NOT an arrow of [RMod R] — [A] is an
   [AbObject] and there is no coercion into [obj[RMod R]].  This is the
   shape of the adjunction, not an accident: the unit lives downstairs. *)
Fail Check (zext_unit R A : A ~{RMod R}~> rm_ab (ZExtObj R A)).

End ZExtProbeStrength.

(* CONTROL for negative 4: the comparison map exists and computes. *)
Check (cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4)).

(* NEGATIVE 4 (CONVERSION).  ℤ ⊗ ℤ is NOT ℤ on the nose — the carriers
   are [tsum] and [Z] — so [zext_int_gen_nonzero] is a statement about a
   genuinely constructed object and not about ℤ in disguise. *)
Fail Example zext_probe_int_strict : ZIntExt = Int_RMod := eq_refl.

Section ZExtProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{ra rb rc}) (Au Bu : AbObject).
Context (fu : Au ~{Ab}~> Bu).

(* CONTROLS.  With the ring's FIRST and THIRD universes declared strictly
   apart, all of these are formable — so the identification below is
   neither the tensor's, nor the category's, nor the forgetful functor's,
   nor the abelian-group-level arrow action's, nor the extension OBJECT's.
   Each is APPLIED to [Ru], which is the argument carrying the levels. *)
Check (RMod Ru).
Check (ring_ab Ru).
Check (AbTensor (ring_ab Ru) Au).
Check (ZExtObj Ru Au).
Check (zext_act Ru Au).
Check (zext_map_ab Ru fu).
Check (RMod_Forget_Ab Ru).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).

(* NEGATIVE 5 (FORMABILITY).  The identification enters exactly when the
   extension is READ AS AN OBJECT of [RMod R] — not when it is built. *)
Fail Check (ZExtObj Ru Au : obj[RMod Ru]).

(* NEGATIVE 6 (FORMABILITY).  THE DONOR, and it is not this file's.
   Instance/Mod.v's OWN [Ring_RMod] is rejected at the very same levels,
   with the very same message, so the pin is INHERITED. *)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

(* NEGATIVE 7 (FORMABILITY).  Hence the functor. *)
Fail Check (ZExt Ru).

(* NEGATIVE 8 (FORMABILITY).  And hence the headline. *)
Fail Check (zext_adjunction Ru).

End ZExtProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. *)
Fail Example zext_probe_instrument : (true = false) := eq_refl.
