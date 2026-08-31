(** * Coextension of scalars: the right adjoint of R-Mod → Ab *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §IV.2 Exercise 2, printed p. 90 (ledger item
              `maclane:IV.2:ex2`, issue #360) — the forgetful functor
              from R-modules to abelian groups has BOTH adjoints.  This
              file is the RIGHT one; the left one is the sibling
              described under PRIOR ART below.
   Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
              hom-set form, which is the presentation used here: the
              [Adjunction] record of Theory/Adjunction.v is a natural
              bijection of hom-setoids, and the unit and counit are its
              derived ⌊id⌋ and ⌈id⌉.
   Book:      Riehl, "Category Theory in Context", Dover 2016, §4.1
              Example 4.1.10 — restriction of scalars has a left adjoint
              (extension) and a right adjoint (coextension, also called
              coinduction).  READ THE RELATION PRECISELY: hers runs
              between two MODULE categories along a ring homomorphism,
              and this one runs into [Ab].  See PRIOR ART; the two are
              not instances of one another in this tree.
   nLab:      https://ncatlab.org/nlab/show/coextension+of+scalars
   nLab:      https://ncatlab.org/nlab/show/restriction+of+scalars
   Wikipedia: https://en.wikipedia.org/wiki/Change_of_rings

   WHAT IS DELIVERED.

     - [coex_group R A], the abelian group of additive maps R → A.  It
       is NOT built: it is Adjunction/Additive.v's [hom_ab] read at
       [Ab_AbEnriched], so carrier, zero, addition and negation are the
       enrichment's own — pinned by [coex_group_carrier],
       [coex_group_plus] and [coex_group_zero] at [eq_refl].
     - [CoextObj R A : RModObject R], that group made a LEFT R-module by
       TRANSLATION: (r · f)(s) = f (s r).
     - [CoextMap] and **[Coextension R : Ab ⟶ RMod R]**, the functor,
       whose arrow action is postcomposition.
     - [coex_to] / [coex_from], the two transposes, and [coex_adj], the
       bijection as an [Isomorphism] of hom-setoids in [Sets].
     - **[coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R]**, an
       inhabitant of Theory/Adjunction.v's [Adjunction] record, built
       through [Build_Adjunction'].
     - [coex_unit] and [coex_counit], with the reviewer check PINNED:
       **[coex_counit_is_eval_at_one] states that the counit at A,
       applied to φ, IS [cmon_map φ (rig_one R)] — EVALUATION AT 1 — and
       it closes at [eq_refl]**, not up to ≈.  The unit is dual and
       equally strict: [coex_unit_is_smul] gives m ↦ (s ↦ s · m).
     - A ℤ witness: [CoextInt], the additive endomorphisms of ℤ made a
       ℤ-module, with three non-degeneracy results proved by MAPPING OUT
       through the counit.

   NO COMMUTATIVITY HYPOTHESIS, AND THAT IS A THEOREM RATHER THAN A
   PREFERENCE.  The file's ONLY [Context] is [(R : RingObject)]; there
   is no commutativity argument anywhere, and [About CoextObj],
   [About Coextension] and [About coex_adjunction] all display a bare
   [forall R : RingObject].  The two places a reader expects
   commutativity to be spent are exactly the two associativity clauses,
   and both go through on associativity alone:

     - [coex_act_assoc], the module law (r r') · f ≈ r · (r' · f).  At s
       the two sides are f (s (r r')) and f ((s r) r'), and the ONLY law
       consumed is [rig_mul_assoc].
     - [coex_to]'s [rm_map_smul] obligation, which is what makes the
       forward transpose R-linear.  At s the two sides are
       g (s · (r · m)) and g ((s r) · m), and the ONLY law consumed is
       [rm_smul_assoc] of the source module.

   This is a genuine contrast with Instance/Mod/Closed.v, whose own
   header localises its commutativity hypothesis to [hm_smul_linear]:
   there r · φ must be shown LINEAR, and (r·φ)(s·v) is r · (s · φ v)
   where linearity demands s · (r · φ v), so the two scalars must be
   exchanged.  Here they never are.

   THE HANDEDNESS IS FORCED, AND THE SWAP IS PINNED AS A NEGATIVE.  The
   action translates on the RIGHT of the ring argument, (r · f)(s) =
   f (s r), and that is what makes the result a LEFT module: at s,
   ((r r') · f) is f (s (r r')) = f ((s r) r'), while (r · (r' · f)) is
   (r' · f)(s r) = f ((s r) r') — the same term after one
   re-bracketing.  The other spelling, f (r s), would give
   ((r r') · f)(s) = f ((r r') s) against (r · (r' · f))(s) = f ((r' r) s),
   which is an ANTI-action and hence a right module; over a commutative
   ring the two coincide and the distinction is invisible, which is
   exactly why it is pinned (CONVERSION negative 3).  No swap was
   needed: the handedness compiles as first written.  Classically this
   is the left action induced by the RIGHT action of R on itself, i.e.
   R read as an (R,R)-bimodule; that reading is NOT invoked below —
   Instance/Mod.v's [Ring_Bimodule] exists and is never consulted, and
   its [bm_compat] field is exactly the [rig_mul_assoc] spent directly.

   WHY A RING AND NOT A RIG.  [hom_ab] demands an [AbEnriched] category,
   and the negation it supplies on the hom-group is A's; the source
   [ring_ab R] must likewise be an object of [Ab].  So [ring_neg] is
   spent NOWHERE in this file directly; its whole role is that
   [ring_ab R] is an abelian group at all.  A rig-level analogue would
   need the [Preadditive] reading of a hom-setoid — the commutative
   monoid of homomorphisms.  What is absent is narrower than it first
   looks, and the wide claim would be false: Instance/FdVect/
   DoubleDual.v's [dual_cmon] (:185) and [dual_ab] (:199) ARE that
   reading, their plus and zero being [RMod_Preadditive]'s own [padd]
   and [pzero].  What the tree lacks is a GENERAL operator
   [Preadditive C → x → y → CMonObject] — [dual_cmon] is instance-level
   with its codomain fixed at [Ring_RMod] — and the NAME [hom_cmon],
   which occurs nowhere.

   WHAT IS REUSED, NOT REBUILT.

     - Adjunction/Additive.v: **[hom_ab]**, the hom-setoid of an
       Ab-enriched category read as an [AbObject].  This is the whole
       carrier; the file adds only the action.
     - Structure/AbCategory.v: [Ab_AbEnriched], and through it
       [ab_hom_add] / [ab_hom_zero] / [ab_hom_neg].
     - Instance/Rng.v: [ring_ab], the additive group of a ring.
     - Instance/Mod.v: [RModObject], [RModHom], [RMod],
       **[RMod_Forget_Ab]** (the LEFT adjoint of the delivered
       adjunction, taken as given), [rm_smul_zero_l], [rm_smul_zero_r],
       [Ring_RMod], [Int_RMod].
     - Instance/Ab.v: [AbHom], and Instance/CMon.v's [cmon_hom_compose],
       which is what makes the arrow action postcomposition on the nose.
     - Theory/Adjunction.v: [Build_Adjunction'], [unit], [counit].

   NO INDUCTION AND NO FIXPOINT.  Neither tactic nor keyword is invoked
   below.  A case-INSENSITIVE sweep for the first returns exactly two
   lines: this heading, and one word of the Riehl citation above.  A
   case-SENSITIVE sweep for the second, spelled as Coq spells it,
   returns none.  Nothing here is a quotient, so there is no elimination
   to perform: every obligation is an equation between two values of a
   hom-setoid, checked at an argument.  Correspondingly the file has no
   analogue of a universal-property "agreement on generators" step —
   the hard direction of the bijection is carried by the module laws of
   the source module instead.

   WHICH LEMMA SPENDS WHICH LAW.  Read as a ledger; nothing else of R is
   consumed, and in particular [rig_mul_zero_r], [rig_add_assoc],
   [rig_add_comm] and [ring_neg] are spent nowhere directly.

     [coex_act]          respectfulness ← [rig_mul_respects]
                         zero ← [rig_mul_zero_l], [cmon_map_zero] of f
                         additivity ← [rig_distr_r], [cmon_map_plus] of f
     [coex_act_respects] ← [rig_mul_respects]
     [coex_act_distr_l]  ← NOTHING; it closes by [reflexivity]
     [coex_act_distr_r]  ← [rig_distr_l], [cmon_map_plus] of f
     [coex_act_assoc]    ← [rig_mul_assoc]        (associativity ONLY)
     [coex_act_one]      ← [rig_mul_one_r]
     [coex_map_ab]       ← nothing of R; [cmon_map_zero] and
                           [cmon_map_plus] of the given f
     [CoextMap]'s [rm_map_smul], and [Coextension]'s [fmap_id] and
       [fmap_comp] ← NOTHING; all three close by [reflexivity]
     [coex_to_inner]     ← [rm_smul_respects], [rm_smul_zero_l],
                           [rm_smul_distr_r] of M
     [coex_to_ab]        ← [rm_smul_respects], [rm_smul_zero_r],
                           [rm_smul_distr_l] of M
     [coex_to]           ← [rm_smul_assoc] of M   (associativity ONLY)
     [coex_from]         ← NOTHING of R and NOTHING of M's action: only
                           the three [CMonHom] laws of the given h, each
                           read at [rig_one].  In particular the
                           R-linearity of h is NOT consumed by the
                           untranspose.
     [coex_adj] to∘from  ← [rm_map_smul] of h, then [rig_mul_one_l]
     [coex_adj] from∘to  ← [rm_smul_one] of M
     [Build_Adjunction']'s first naturality ← [rm_map_smul] of g;
       its second ← NOTHING, by [reflexivity]

   BOTH DISTRIBUTIVITY LAWS AND BOTH UNIT LAWS OF R ARE SPENT, AT
   DIFFERENT PLACES, AND OVER A NON-COMMUTATIVE RING THOSE ARE FOUR
   SEPARATE AXIOMS.  [rig_distr_r] is what makes r · f a homomorphism at
   all (additivity in the ring argument), while [rig_distr_l] is what
   makes the action additive in the SCALAR; [rig_mul_one_r] closes the
   module law 1 · f ≈ f, while [rig_mul_one_l] closes the round trip
   [coex_to (coex_from h)] ≈ h.  Neither pair could be collapsed without
   commutativity, so this is a real observation and not bookkeeping.

   STRENGTHS, MEASURED STRICT-FIRST.  Twenty identifications close at
   [eq_refl] and are shipped as [Example]s — twenty occurrences in CODE
   with comments and [Fail]s excluded, a figure a naive grep overstates
   by one because it also matches this paragraph:

     - the three data fields of the carrier ([coex_group_carrier],
       [coex_group_plus], [coex_group_zero]) — so the group is [hom_ab]
       on the nose and nothing was rebuilt;
     - the action at a point ([coex_act_at]) and the arrow action at a
       point ([coex_map_at]);
     - both transposes at a point ([coex_to_at], [coex_from_at]);
     - **the counit IS evaluation at 1 ([coex_counit_is_eval_at_one])**
       — the reviewer check, definitional rather than up to ≈ — and the
       unit IS m ↦ (s ↦ s · m) ([coex_unit_is_smul]);
     - the adjunction's forward transpose IS [coex_to] and its backward
       transpose IS [coex_from] ([coex_adj_to_is_coex_to],
       [coex_adj_from_is_coex_from]), so nothing downstream reads a
       different map than the one this header names;
     - the functor's two actions ([coex_fobj_is_CoextObj],
       [coex_fmap_is_CoextMap]) and the left adjoint's object action
       ([coex_forget_is_rm_ab]);
     - over ℤ, multiplication by n at a point, the counit computing to 3
       and to 0, and the action computing 2 · (·3) to 6;
     - and two probe controls, the handedness and the pointwise reading
       of left distributivity.

   EXACTLY THREE IDENTIFICATIONS FALL BACK TO ≈, AND THEIR CAUSES
   DIFFER.  Two are the round trips of the bijection: [coex_from
   (coex_to g)] evaluates to g (1 · m) and [coex_to (coex_from h)]
   evaluates the inner homomorphism at 1 · s; [rm_smul_one] and
   [rig_mul_one_l] are what remove the residues, and both are abstract
   fields of a class, so neither side reduces and no downstream
   transparency would help.  The third is different in kind and is
   measured as such: left distributivity holds POINTWISE at [eq_refl]
   (control beside negative 4), yet the two RECORDS are not convertible,
   because [coex_act] is a [Program Definition] whose [cmon_map_zero]
   and [cmon_map_plus] obligations are opaque and are built at different
   arguments on the two sides.  So there the DATA agrees on the nose and
   only the law fields separate.

   UNIVERSES, MEASURED AND ATTRIBUTED.  Scope this to the five
   constants named, because as a claim about the FILE all three clauses
   are false: the four [coex_ctrl_*] probe controls each carry ten
   equations [u = u0] .. [u = u9]; sixteen constants carry a strict
   constraint other than [u < u2]; and each of the five named carries
   [u <= u1] and [u0 <= u1], bounds between this file's OWN declared
   levels rather than against any donor.  Of [coex_act], [coex_group],
   [CoextObj], [Coextension] and [coex_adjunction], then: their only
   universe EQUATIONS are [u = u0] and [u = u1] — the ring's three
   universes collapse to one — carried identically by all five; the
   only STRICT constraint among them is [u < u2], which [coex_act]
   does not carry at all; and the rest of their blocks is a bound
   against [Basics.compose], [prod_rect], [ID], [projections] and
   [Logic_lemmas.equality].  Where the identification enters is measured
   rather than guessed, and it is NOT this file's.  With the ring's
   first and third universes declared strictly apart, [RMod Ru],
   [ring_ab Ru], [RMod_Forget_Ab Ru], [hom_ab Ab_AbEnriched Au Bu],
   [Ab ⟶ RMod Ru] and [Ring_RMod Ru] all elaborate, while
   [AbHom (ring_ab Ru) Au] is REJECTED — so the wall is met already at
   the point where a ring's additive group is read as the source of a
   homomorphism of abelian groups, before any construction of this file
   is reached, and before [Ab]-the-category is mentioned.  A SECOND and
   INDEPENDENT donor is pinned beside it: Instance/Mod.v's own
   [Ring_RMod Ru : obj[RMod Ru]] is rejected at the very same levels
   with the very same message, and it mentions neither [Ab] nor
   anything here, so the identification would still be met if the
   abelian side were repaired.  Neither is claimed unavoidable; no
   re-annotation was attempted.

   PRIOR ART, AND WHAT IT DOES AND DOES NOT SHARE WITH THIS FILE.

     - Instance/Mod/BaseChange.v, written in this same branch for the
       OTHER half of issue #360, delivers
       [ZExt R ⊣ RMod_Forget_Ab R]: extension of scalars along ℤ → R as
       A ↦ R ⊗ A, over Instance/Ab/Tensor.v's ℤ-tensor.  Together with
       the adjunction below that is the adjoint TRIPLE
       [ZExt R ⊣ RMod_Forget_Ab R ⊣ Coextension R] on ONE functor, which
       is exactly what `maclane:IV.2:ex2` asks for.  **The two files
       share no construction**: that one's carrier is [AbTensor] and
       this one's is [hom_ab], their declared name sets are disjoint,
       and neither defines an [Ltac].  Read that as "no OWN artifact in
       common" — the ordinary tactics are of course shared, and so are
       at least ten DONORS, not the two an earlier draft of this
       paragraph listed: [ring_ab], [RMod_Forget_Ab], [Build_Adjunction],
       [cmon_hom_compose], [Int_RMod], [Ring_RMod], [ab_hom_add],
       [rm_smul_zero_r], [AbHom], [RModObject], plus [unit]/[counit].
       This file does NOT [Require] it, so the two compile
       independently and the triple is NOT stated here as a single
       artifact — that statement would need both in one scope and is
       listed as not delivered.  (The description above is from reading
       that file, not from a check performed in this one.)
     - Instance/Mod/Extension.v (pre-existing, _CoqProject:338, issue
       #312) is a DIFFERENT pair over a different pair of categories:
       [ExtendScalars phi Hc ⊣ Restrict phi] between [RMod R] and
       [RMod S] along an arbitrary ring homomorphism, over
       Instance/Mod/Tensor.v's R-tensor and under a [CentralImage]
       hypothesis.  Its own right-hand neighbour — the coextension
       Hom_R(S, −) along phi, right adjoint to [Restrict phi] — is built
       neither there nor here.  This file is not an instance of it: at
       phi : ℤ → R that file's restriction runs [RMod R ⟶ RMod Int_Ring]
       while this one's left adjoint runs [RMod R ⟶ Ab].  State the
       obstruction precisely: "the tree carries no functor relating
       [Ab] and [RMod Int_Ring]" would be FALSE — [RMod_Forget_Ab
       Int_Ring] is one, and this file uses it at that very ring in its
       own ℤ witness.  What is absent is an [Ab ⟶ RMod Int_Ring]
       carrying each abelian group ITS OWN ℤ-action, which is what
       Instance/Ab/Free.v, Instance/Mod/Quotient.v and
       Instance/Mod/Tensor.v each record.  Nothing is shared and that
       file is not [Require]d either.

   AXIOMS.  73/73 constants report "Closed under the global context"
   (49 source-declared plus 24 [Program] obligations that no source
   sweep sees, queried by fully qualified name).  Zero of the 73 names
   occur anywhere else in the tree, checked name by name.

   NEGATIVES.  Fifteen [Fail] commands: fourteen guarded negatives —
   five CONVERSION, two TYPING, seven FORMABILITY — each beside an
   APPLIED positive control, plus one scope-free instrument check.  Each
   was stripped of its [Fail] and compiled alone and its WHOLE error
   read; the classification is recorded at the probe section.  Every
   constant named inside a negative is also named outside one, so a
   rename cannot turn a guard vacuously green.

   WHAT IS NOT DELIVERED.

     - No coextension along an arbitrary ring homomorphism, so nothing
       here is a right adjoint to Instance/Rng/Mod.v's [Restrict phi];
       the base is [Ab] throughout.
     - No statement of the adjoint triple as one artifact, since
       Instance/Mod/BaseChange.v is deliberately not [Require]d, and no
       comparison of [Coextension] with anything in
       Instance/Mod/Extension.v.
     - No monad or comonad from the adjunction, and no Eilenberg–Moore
       or Kleisli reading.
     - No triangle identities restated in this file's own vocabulary
       (they are Theory/Adjunction.v's derived corollaries and are not
       specialised), and no uniqueness statement for the right adjoint.
     - No enriched reading: both hom-sets in play are abelian groups and
       Adjunction/Additive.v's [adj_hom_ab_iso] is one Require away, but
       it needs [AbEnriched (RMod R)], which the tree does not have
       (Instance/Mod.v:809 supplies only [RMod_Preadditive]).  So the
       bijection is NOT exhibited as an isomorphism in [Ab], and no
       additivity of either adjoint is claimed.
     - No isomorphism Hom_ℤ(ℤ, A) ≅ A, hence nothing says
       [Coextension Int_Ring] is equivalent to the identity; the ℤ
       witness pins Hom(ℤ, ℤ) only through maps OUT of it, and
       [CoextInt] is refuted equal to [Int_RMod] on the nose.
     - No [RigObject] variant, no right-module or bimodule reading, and
       no [Instance] registered for typeclass resolution: [CoextObj],
       [Coextension] and [coex_adjunction] are plain [Definition]s.
     - No finiteness, no basis, no rank and no decision procedure for
       equality in the coextension; every negative goes through a map
       OUT. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Adjunction.Additive.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section Coextension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation RG := (ring_ab R).

Definition coex_group (A : AbObject) : AbObject :=
  hom_ab Ab_AbEnriched RG A.

Example coex_group_carrier (A : AbObject) :
  carrier (cmon_setoid (coex_group A)) = (RG ~{Ab}~> A) := eq_refl.

Example coex_group_plus (A : AbObject) :
  cmon_plus (coex_group A) = @ab_hom_add RG A := eq_refl.

Example coex_group_zero (A : AbObject) :
  cmon_zero (coex_group A) = @ab_hom_zero RG A := eq_refl.

(** ** The scalar action: translation in the ring argument *)

Program Definition coex_act (A : AbObject) (r : RS) (f : AbHom RG A) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s =>
    cmon_map f (rig_mul (ring_rig R) s r) |}
|}.
Next Obligation.
  intros A r f s s' Hs.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_respects (ring_rig R) s s' Hs r r (reflexivity r))).
Qed.
Next Obligation.
  intros A r f; simpl.
  transitivity (cmon_map f (rig_zero (ring_rig R))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_zero_l (ring_rig R) r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A r f s s'; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s' r))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_r (ring_rig R) s s' r)).
  - exact (cmon_map_plus f _ _).
Qed.

Example coex_act_at (A : AbObject) (r s : RS) (f : AbHom RG A) :
  cmon_map (coex_act A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(** ** The four module laws *)

Lemma coex_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (coex_act A).
Proof.
  intros r r' Hr f g Hfg s; simpl.
  transitivity (cmon_map f (rig_mul (ring_rig R) s r')).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_respects (ring_rig R) s s (reflexivity s) r r' Hr)).
  - exact (Hfg _).
Qed.

Lemma coex_act_distr_l (A : AbObject) (r : RS) (f g : AbHom RG A) :
  coex_act A r (cmon_plus (coex_group A) f g)
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r g).
Proof. intro s; reflexivity. Qed.

Lemma coex_act_distr_r (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r' f).
Proof.
  intro s; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s r'))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_l (ring_rig R) s r r')).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma coex_act_assoc (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_mul (ring_rig R) r r') f
    ≈ coex_act A r (coex_act A r' f).
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (symmetry (rig_mul_assoc (ring_rig R) s r r'))).
Qed.

Lemma coex_act_one (A : AbObject) (f : AbHom RG A) :
  coex_act A (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_one_r (ring_rig R) s)).
Qed.

Definition CoextObj (A : AbObject) : RModObject R := {|
  rm_ab            := coex_group A;
  rm_smul          := coex_act A;
  rm_smul_respects := coex_act_respects A;
  rm_smul_distr_l  := coex_act_distr_l A;
  rm_smul_distr_r  := coex_act_distr_r A;
  rm_smul_assoc    := coex_act_assoc A;
  rm_smul_one      := coex_act_one A
|}.

(** ** The arrow action: postcomposition, and the functor *)

Program Definition coex_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (coex_group A) (coex_group B) := {|
  cmon_map := {| morphism := fun phi =>
    (cmon_hom_compose f phi : AbHom RG B) |}
|}.
Next Obligation.
  intros A B f phi phi' Hphi s; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hphi s)).
Qed.
Next Obligation.
  intros A B f s; simpl.
  exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f phi psi s; simpl.
  exact (cmon_map_plus f _ _).
Qed.

Example coex_map_at {A B : AbObject} (f : AbHom A B)
  (phi : AbHom RG A) (s : RS) :
  cmon_map (cmon_map (coex_map_ab f) phi) s
    = cmon_map f (cmon_map phi s) := eq_refl.

Program Definition CoextMap {A B : AbObject} (f : AbHom A B) :
  CoextObj A ~{RMod R}~> CoextObj B := {|
  rm_hom := coex_map_ab f
|}.
Next Obligation. intros A B f r phi s; reflexivity. Qed.

Program Definition Coextension : Ab ⟶ RMod R := {|
  fobj := CoextObj;
  fmap := @CoextMap
|}.
Next Obligation.
  intros A B f g Hfg phi s; simpl.
  exact (Hfg _).
Qed.
Next Obligation. intros A phi s; reflexivity. Qed.
Next Obligation. intros A B C f g phi s; reflexivity. Qed.

(** ** The two transposes *)

Program Definition coex_to_inner {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s => cmon_map g (rm_smul M s m) |}
|}.
Next Obligation.
  intros A M g m s s' Hs.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s' Hs m m (reflexivity m))).
Qed.
Next Obligation.
  intros A M g m; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_l M m)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m s s'; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s' m))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_r M s s' m)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to_ab {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : AbHom (rm_ab M) (coex_group A) := {|
  cmon_map := {| morphism := fun m => coex_to_inner g m |}
|}.
Next Obligation.
  intros A M g m m' Hm s; simpl.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s (reflexivity s) m m' Hm)).
Qed.
Next Obligation.
  intros A M g s; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_r M s)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m n s; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s n))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_l M s m n)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : M ~{RMod R}~> CoextObj A := {|
  rm_hom := coex_to_ab g
|}.
Next Obligation.
  intros A M g r m s; simpl.
  symmetry.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_assoc M s r m)).
Qed.

Program Definition coex_from {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A) : AbHom (rm_ab M) A := {|
  cmon_map := {| morphism := fun m =>
    cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) |}
|}.
Next Obligation.
  intros A M h m m' Hm.
  exact (proper_morphism (cmon_map (rm_hom h)) m m' Hm
           (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h; simpl.
  exact (cmon_map_zero (rm_hom h) (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h m n; simpl.
  exact (cmon_map_plus (rm_hom h) m n (rig_one (ring_rig R))).
Qed.

Example coex_to_at {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M)))
  (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_to g)) m) s
    = cmon_map g (rm_smul M s m) := eq_refl.

Example coex_from_at {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (coex_from h) m
    = cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) := eq_refl.

(** ** The hom-set bijection and the adjunction *)

Program Definition coex_adj_to (M : RModObject R) (A : AbObject) :
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |}
    ~{Sets}~>
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  morphism := fun g => coex_to g
|}.
Next Obligation. intros M A g g' Hg m s; exact (Hg _). Qed.

Program Definition coex_adj_from (M : RModObject R) (A : AbObject) :
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |}
    ~{Sets}~>
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |} := {|
  morphism := fun h => coex_from h
|}.
Next Obligation. intros M A h h' Hh m; exact (Hh m _). Qed.

Program Definition coex_adj (M : RModObject R) (A : AbObject) :
  @Isomorphism Sets
    {| carrier := rm_ab M ~{Ab}~> A;
       is_setoid := @homset Ab (rm_ab M) A |}
    {| carrier := M ~{RMod R}~> CoextObj A;
       is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  to   := coex_adj_to M A;
  from := coex_adj_from M A
|}.
Next Obligation.
  intros M A h m s; simpl.
  transitivity (cmon_map (coex_act A s (cmon_map (rm_hom h) m))
                  (rig_one (ring_rig R))).
  - exact (rm_map_smul h s m (rig_one (ring_rig R))).
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom h) m)) _ _
             (rig_mul_one_l (ring_rig R) s)).
Qed.
Next Obligation.
  intros M A g m; simpl.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_one M m)).
Qed.

Definition coex_adjunction : RMod_Forget_Ab R ⊣ Coextension.
Proof.
  unshelve eapply (@Build_Adjunction' Ab (RMod R) (RMod_Forget_Ab R)
                     Coextension coex_adj).
  - intros M N A f g m s; simpl.
    exact (proper_morphism (cmon_map f) _ _ (rm_map_smul g s m)).
  - intros M A B f g m s; reflexivity.
Defined.

(** ** Unit, counit, and the strict readings *)

Definition coex_unit (M : RModObject R) :
  M ~{RMod R}~> CoextObj (rm_ab M) :=
  @unit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction M.

Definition coex_counit (A : AbObject) :
  rm_ab (CoextObj A) ~{Ab}~> A :=
  @counit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction A.

(* THE REVIEWER CHECK.  The counit IS evaluation at 1, on the nose. *)
Example coex_counit_is_eval_at_one (A : AbObject) (phi : AbHom RG A) :
  cmon_map (coex_counit A) phi
    = cmon_map phi (rig_one (ring_rig R)) := eq_refl.

Example coex_unit_is_smul (M : RModObject R)
  (m : carrier (cmon_setoid (rm_ab M))) (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_unit M)) m) s = rm_smul M s m
  := eq_refl.

Example coex_adj_to_is_coex_to (M : RModObject R) (A : AbObject)
  (g : rm_ab M ~{Ab}~> A) :
  to (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
        coex_adjunction M A) g = coex_to g := eq_refl.

Example coex_adj_from_is_coex_from (M : RModObject R) (A : AbObject)
  (h : M ~{RMod R}~> CoextObj A) :
  from (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
          coex_adjunction M A) h = coex_from h := eq_refl.

Example coex_fobj_is_CoextObj (A : AbObject) :
  fobj[Coextension] A = CoextObj A := eq_refl.

Example coex_fmap_is_CoextMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Coextension] f = CoextMap f := eq_refl.

Example coex_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End Coextension.

(** ** A concrete witness over ℤ *)

(** The coextension of ℤ along ℤ: the abelian group of additive
    endomorphisms of ℤ, made a ℤ-module by translation. *)
Definition CoextInt : RModObject Int_Ring :=
  CoextObj Int_Ring (ring_ab Int_Ring).

(** Multiplication by [n], obtained as the unit at [Int_RMod] rather
    than hand-built: [coex_unit] sends m to (s ↦ s · m). *)
Definition coex_int_mul (n : Z) :
  carrier (cmon_setoid (rm_ab CoextInt)) :=
  cmon_map (rm_hom (coex_unit Int_Ring Int_RMod)) n.

Example coex_int_mul_at (n s : Z) :
  cmon_map (coex_int_mul n) s = (s * n)%Z := eq_refl.

(** The comparison map out: evaluation at 1, which is the counit. *)
Definition coex_int_eval :
  rm_ab CoextInt ~{Ab}~> ring_ab Int_Ring :=
  coex_counit Int_Ring (ring_ab Int_Ring).

Example coex_int_eval_computes :
  cmon_map coex_int_eval (coex_int_mul 3) = 3%Z := eq_refl.

Example coex_int_eval_zero :
  cmon_map coex_int_eval (cmon_zero (rm_ab CoextInt)) = 0%Z := eq_refl.

Example coex_int_act_computes :
  cmon_map coex_int_eval
    (rm_smul CoextInt 2%Z (coex_int_mul 3)) = 6%Z := eq_refl.

Lemma coex_int_nonzero : coex_int_mul 1 ≈ cmon_zero (rm_ab CoextInt) →
  False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

Lemma coex_int_muls_distinct : coex_int_mul 3 ≈ coex_int_mul 5 → False.
Proof.
  intro Hz.
  assert (Hev : (3%Z = 5%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(** The action is not trivial: 2 · (multiplication by 3) is not
    (multiplication by 3). *)
Lemma coex_int_act_nontrivial :
  rm_smul CoextInt 2%Z (coex_int_mul 3) ≈ coex_int_mul 3 → False.
Proof.
  intro Hz.
  assert (Hev : (6%Z = 3%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(** ** Probes

    Every strength claim the header makes is pinned here, each negative
    beside an APPLIED positive control.  Each was stripped of its [Fail]
    and compiled alone, and its WHOLE error read: negatives 1-4 and 7
    end in [cannot unify] (CONVERSION); negatives 5 and 6 are plain type
    mismatches with no [cannot unify] and no universe clause (TYPING);
    negatives 8-14 end in
    [universe inconsistency: Cannot enforce rc = ra] (FORMABILITY).
    Fifteen [Fail] commands in all: fourteen guarded negatives and one
    scope-free instrument check. *)

Section CoexProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (g : rm_ab M ~{Ab}~> A) (h : M ~{RMod R}~> CoextObj R A).
Context (f f' : ring_ab R ~{Ab}~> A).
Context (m : carrier (cmon_setoid (rm_ab M))).
Context (r s : carrier (rig_setoid (ring_rig R))).

(* CONTROL for negative 1: the round trip DOES hold at ≈, and the proof
   term names the exact law that closes the gap. *)
Example coex_ctrl_from_to :
  cmon_map (coex_from R (coex_to R g)) m ≈ cmon_map g m
  := proper_morphism (cmon_map g) _ _ (rm_smul_one M m).

(* NEGATIVE 1 (CONVERSION).  [coex_from (coex_to g)] evaluates to
   g (1 · m), and 1 · − is not the identity by conversion:
   [rm_smul_one] is an abstract field of [RModObject], so neither side
   reduces and no downstream transparency would help. *)
Fail Example coex_probe_from_to_strict :
  cmon_map (coex_from R (coex_to R g)) m = cmon_map g m := eq_refl.

(* CONTROL for negative 2. *)
Example coex_ctrl_to_from :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    ≈ cmon_map (cmon_map (rm_hom h) m) s
  := iso_to_from (coex_adj R M A) h m s.

(* NEGATIVE 2 (CONVERSION).  The other round trip evaluates the inner
   homomorphism at 1 · s rather than at s; [rig_mul_one_l] removes the
   residue and is likewise an abstract field. *)
Fail Example coex_probe_to_from_strict :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    = cmon_map (cmon_map (rm_hom h) m) s := eq_refl.

(* CONTROL for negative 3: the handedness that is actually built. *)
Example coex_ctrl_handedness :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(* NEGATIVE 3 (CONVERSION).  The OTHER handedness — translation on the
   left, (r · f)(s) = f (r s) — is a different map.  Over a
   non-commutative ring the two genuinely differ, and it is the built
   one that gives a LEFT module. *)
Fail Example coex_probe_handedness_swapped :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) r s) := eq_refl.

(* CONTROL for negative 4: the underlying FUNCTIONS agree on the nose,
   which is why [coex_act_distr_l] closes by [reflexivity]. *)
Example coex_ctrl_distr_l_pointwise :
  cmon_map (coex_act R A r (cmon_plus (coex_group R A) f f')) s
    = cmon_map (cmon_plus (coex_group R A)
                  (coex_act R A r f) (coex_act R A r f')) s := eq_refl.

(* NEGATIVE 4 (CONVERSION).  The two RECORDS are nevertheless distinct:
   [coex_act] is a [Program Definition], so each side carries its own
   opaque [cmon_map_zero] and [cmon_map_plus] obligations, built at
   different arguments.  So what separates them is exactly the law
   fields, the data having been shown to agree just above. *)
Fail Example coex_probe_distr_l_record :
  coex_act R A r (cmon_plus (coex_group R A) f f')
    = cmon_plus (coex_group R A)
        (coex_act R A r f) (coex_act R A r f') := eq_refl.

(* CONTROL for negative 5: the counit IS an arrow of [Ab]. *)
Check (coex_counit R A : rm_ab (CoextObj R A) ~{Ab}~> A).

(* NEGATIVE 5 (TYPING).  It is NOT an arrow of [RMod R] — [A] is an
   [AbObject] and there is no coercion into [obj[RMod R]].  This is the
   shape of the adjunction rather than an accident: for a RIGHT adjoint
   the counit lives upstairs, in [Ab]. *)
Fail Check (coex_counit R A : CoextObj R A ~{RMod R}~> A).

(* CONTROL for negative 6: the adjunction as delivered. *)
Check (coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R).

(* NEGATIVE 6 (TYPING).  The direction is not negotiable: coextension is
   the RIGHT adjoint, so the forgetful functor sits on the left. *)
Fail Check (coex_adjunction R : Coextension R ⊣ RMod_Forget_Ab R).

End CoexProbeStrength.

(* CONTROL for negative 7: the comparison map out exists and computes. *)
Check (cmon_map coex_int_eval (coex_int_mul 3)).

(* NEGATIVE 7 (CONVERSION).  Hom(ℤ, ℤ) is NOT ℤ on the nose — the
   carriers are [AbHom (ring_ab Int_Ring) (ring_ab Int_Ring)] and [Z] —
   so [coex_int_muls_distinct] is a statement about a genuinely
   constructed object and not about ℤ in disguise. *)
Fail Example coex_probe_int_strict : CoextInt = Int_RMod := eq_refl.

Section CoexProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{ra rb rc}) (Au Bu : AbObject).

(* CONTROLS.  With the ring's FIRST and THIRD universes declared strictly
   apart, all of these are formable, each APPLIED to the argument that
   carries the levels — so the identification below is neither the module
   category's, nor [ring_ab]'s, nor the forgetful functor's, nor
   [hom_ab]'s, nor the functor TYPE's. *)
Check (RMod Ru).
Check (ring_ab Ru).
Check (RMod_Forget_Ab Ru).
Check (hom_ab Ab_AbEnriched Au Bu).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).
Check (obj[RMod Ru]).

(* NEGATIVE 8 (FORMABILITY).  THE DONOR, and it is neither this file's
   nor [Ab]-the-category's: the wall is met already at [AbHom], i.e. the
   moment a ring's additive group is read as the SOURCE of a
   homomorphism of abelian groups.  That is where [coex_group] begins,
   and everything below inherits it. *)
Fail Check (AbHom (ring_ab Ru) Au).

(* NEGATIVE 9 (FORMABILITY).  The same wall met the other way round. *)
Fail Check (ring_ab Ru : obj[Ab]).

(* NEGATIVE 10 (FORMABILITY).  Hence the scalar action. *)
Fail Check (coex_act Ru Au).

(* NEGATIVE 11 (FORMABILITY).  Hence the carrier. *)
Fail Check (coex_group Ru Au).

(* NEGATIVE 12 (FORMABILITY).  A SECOND, INDEPENDENT donor:
   Instance/Mod.v's own [Ring_RMod] is rejected at the very same levels
   with the very same message, and it mentions neither [Ab] nor this
   file.  So the identification would be met here even if the abelian
   side were repaired. *)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

(* NEGATIVE 13 (FORMABILITY).  Hence the functor. *)
Fail Check (Coextension Ru).

(* NEGATIVE 14 (FORMABILITY).  And hence the headline. *)
Fail Check (coex_adjunction Ru).

End CoexProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. *)
Fail Example coex_probe_instrument : (true = false) := eq_refl.
