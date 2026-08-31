(** * (R-Mod, ⊗, R) is symmetric monoidal CLOSED: the tensor-hom adjunction *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §IV.1, printed p. 80 — the hom-set form of an adjunction, of
              which "⊗ is left adjoint to Hom" is the running example.
   Book:      Mac Lane, ibid., §IV.6, printed p. 98 — the tensor-hom
              adjunction proper: for a commutative ring R the bijection
              Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X)), natural in all three
              variables.
   nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
   nLab:      https://ncatlab.org/nlab/show/closed+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

   Instance/Mod/Monoidal.v supplied the ⊗ half — the bifunctor [ModTensor],
   the unitors, the associator, both coherence laws, the braiding and the
   symmetry.  Its own header says in terms that the closed structure is a
   companion file's business (Instance/Mod/Monoidal.v:280-282):

     "NO CLOSED STRUCTURE.  The internal hom, the tensor-hom adjunction
      and any [SymMonClosed] instance are a companion file's business,
      not this one's; nothing here mentions an exponent."

   This file is that companion.  Delivered:

     - [HomMod V W], the internal hom: the module of R-linear maps V ⟶ W
     - [hm_curry] / [hm_uncurry] with BOTH round trips
     - [exp_iso_Mod], the bijection as an isomorphism of hom-setoids in
       [Sets]; [eval_Mod], evaluation; [ump_exponents_Mod], the universal
       property in existence-and-uniqueness form
     - **[RMod_SymMonClosed]**, the headline: an inhabitant of
       Structure/Monoidal/StarAutonomous.v's [SymMonClosed] class, whose
       underlying symmetric monoidal structure IS Monoidal.v's
       [ModSymmetric]
     - [ihom_post] / [ihom_pre], the internal hom's two arrow actions, and
       the SIX naturality squares — three variables, each read through the
       forward leg and through the backward leg

   COMMUTATIVITY, AND WHERE IT IS SPENT.  Everything is stated over an
   arbitrary [RingObject] together with an explicit commutativity
   hypothesis, the same proposition after elaboration as Instance/Rng.v:398's
   [CRng_Sub] predicate so that an object of [CRng] supplies it by
   projection and Instance/Rng.v:412's [Int_Ring_commutative] discharges it
   at ℤ:

     Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
                 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

   Commutativity is spent in EXACTLY ONE PROOF, [hm_smul_linear]: the claim
   that r · φ is still LINEAR when φ is.  Unfolded, (r·φ)(s·v) is
   r · (s · φ v) and linearity demands s · (r · φ v); [Rcomm] is what turns
   one into the other, and nothing else in the file reaches for it.

   THAT IS MACHINE-MEASURED, NOT ASSERTED.  Lib.v:13 sets
   [Default Proof Using "Type"], which keeps only the section variables a
   lemma's STATEMENT mentions.  [Rcomm] appears in no statement in
   Section [InternalHom] — so the build DEMANDS the annotation
   `Proof using R Rcomm` on [hm_smul_linear] and rejects it on none of its
   siblings.  The annotation is kept for that reason and must not be
   removed; deleting it makes the file fail at that lemma's [Qed] with

     The following section variable is used but not declared: Rcomm.

   The instrument is also readable from OUTSIDE the proof, and the probe
   section at the end pins it as a TYPING negative: [hm_smul_linear] takes
   [Rcomm] as an ARGUMENT, so `@hm_smul_linear R V W r f` is ill-typed,
   while `@hm_smul_zero R V W r f` and `@hm_smul_plus R V W r f` — the two
   siblings, same section, same statement shape — elaborate.

   A FINER MEASUREMENT THE HEADER WOULD OTHERWISE MISS.  [Rcomm] is needed
   only to make the linear maps into an OBJECT of [RMod R].  Currying
   itself is commutativity-free, and that is visible in the signatures the
   same instrument produces: [cur_fun R {V W X} f v w] and
   [cur_at R {V W X} f v] — the map w ↦ f (v ⊗ w) together with the proof
   that it is a module homomorphism W ⟶ X — take NO [Rcomm].  Only
   [hm_curry], whose codomain is [HomMod], does.

   PRIOR ART, AND [HomMod] IS NOT A FIRST SIGHTING.  Instance/FdVect/
   DoubleDual.v:267's [DualMod] is ALREADY the W := R case of this internal
   hom.  That is an identification, not an analogy: its carrier
   (DoubleDual.v:179, the carrier field of the record opened at :178) is
   `RModHom V (Ring_RMod (field_ring F))`, which is
   [hm_setoid]'s carrier at W := Ring_RMod; and since Instance/Mod.v:849's
   [Ring_RMod] has `rm_smul := rig_mul (ring_rig R)` and
   `rm_smul_assoc := rig_mul_assoc`, its scalar action r · φ is this file's
   pointwise action on the nose, its [dual_smul_linear] (DoubleDual.v:236)
   is [hm_smul_linear] with the same three rewrites in the same order, and
   its own header at DoubleDual.v:209 already localises "the one use of
   commutativity" to exactly that lemma.  So [HomMod] GENERALISES an
   existing construction in two independent directions — an arbitrary
   target module W in place of the base ring, and an arbitrary
   [RingObject] with an explicit [Rcomm] in place of a [FieldObject] — and
   the localisation of commutativity is INHERITED rather than discovered.
   What is new here is the tensor-hom adjunction over it, which
   DoubleDual.v does not have (its own header, DoubleDual.v:106, records
   that the library then had no monoidal structure to state it against).

   NO BRAID IS NEEDED, AND THAT IS A FACT ABOUT THE CLASS'S ORIENTATION.
   Structure/Monoidal/StarAutonomous.v:115 declares

     exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z

   with `eval' {x y} : (x ⇒ y) ⨂ x ~> y` at :120.  Read at x := V, y := W,
   z := X this is Hom(V ⊗ W, X) ≅ Hom(V, Hom(W, X)), which is the module
   theorist's own statement, and evaluation puts the internal hom on the
   LEFT of the tensor — so [uncur_bilinear]'s underlying map is the
   two-variable (φ, w) ↦ φ w with its arguments already in the order the
   class wants.  Had the class put the internal hom on the right, or had
   the tensor's variance run the other way, the symmetry [ModBraid] would
   have had to be inserted; here it is not, and no [ModBraid] occurs
   anywhere below.  (The symmetry is still present in the STRUCTURE — it
   is what [smc_is_symmetric] carries — it is simply not consumed by the
   adjunction.)

   NATURALITY IN THREE VARIABLES, AND THE ASYMMETRY BETWEEN THE TWO LEGS.
   Each of the three squares is stated twice, once through the forward leg
   [hm_curry] and once through the backward leg [hm_uncurry], because the
   two cost different things and reporting only one would misdescribe the
   result.

     FORWARD ([cur_natural_V], [cur_natural_W], [cur_natural_X]): each is
     `Proof. intros v w; reflexivity. Qed.` — the two sides are pointwise
     the SAME TERM.  Currying is definitional on generators, and
     [mt_fmap] computes there, so there is nothing to prove.

     BACKWARD ([unc_natural_V], [unc_natural_W], [unc_natural_X]): each
     needs one application of [tensor_hom_ext] and then [reflexivity].
     [hm_uncurry] is a [tensor_med], i.e. a [Fixpoint] over [MTerm]; two
     such recursions are pointwise equal at every generator but are not
     the same term at a variable tensor, so extensionality is what closes
     the gap.

   BOTH DIRECTIONS MATTER.  The forward triviality on its own could be
   mistaken for the naturality statement being vacuous; the backward
   squares show it is not — they are true, they are not conversions, and
   the probe section pins the failed strict form of one of them beside its
   generator-level control, so the difference is machine-checked rather
   than described.

   ONE CORRECTION TO THE ROUTE, AND IT MADE EVERY PROOF CHEAPER.
   Instance/Mod/Tensor.v exposes the mediator twice: [tensor_med] (:664),
   whose generator equation is `eq_refl` (:687), and [tensor_factor]
   (:840), a bare alias for it (:846, `tensor_factor β = tensor_med β` by
   `eq_refl`) whose companion [tensor_factor_commutes] (:848) is a `Qed`
   lemma stating an `≈`.  Routing through the second makes every step
   opaque; this file uses the first throughout.  The consequences are
   measured below rather than claimed:

     - [hm_uncurry_gen] holds at LEIBNIZ `=` by `eq_refl` (the uncurried
       map's value at a generator IS φ applied to the argument);
     - [hm_curry_uncurry] is `Proof. intros v w; reflexivity. Qed.`;
     - [hm_uncurry_curry] is one [tensor_hom_ext] then `reflexivity`;
     - [eval_Mod_gen] holds at Leibniz `=` by `eq_refl`;
     - [ump_uniq] is a one-line `exact (Hh (mt_gen v w))` — no chain;
     - the three backward naturality squares need [tensor_hom_ext] and
       NOTHING ELSE.

   THE JOIN WITH Instance/Mod/Monoidal.v, AND ONE MISMATCH CHECKED RATHER
   THAN ASSUMED.  The tensor's action on arrows is that file's [mt_fmap],
   not a second copy: [mt_fmap] is `tensor_med (mt_bimap f g)` where
   [mt_bimap]'s underlying map is (v, w) ↦ mval f v ⊗ mval g w, and
   [ModTensor]'s `fmap` is `fun p q fg => mt_fmap (fst fg) (snd fg)`, so
   `bimap h id` reduces to `mt_fmap h id` by iota.  That is checked, not
   supposed: [smc_bimap] below records it at `eq_refl`, together with
   [smc_tensor] recording `fobj[tensor] (V, W) = TensorMod V W`.

   HOW THE FIELDS SLOT IN.  Every one of [SymMonClosed]'s four explicit
   fields is filled by `:=` with NO tactic and NO transport, and the three
   DEFINED fields — [curry'], [uncurry'], [eval'], which the class supplies
   with bodies rather than taking as arguments — return this file's own
   constants at `eq_refl`: [smc_curry], [smc_uncurry], [smc_eval].  So
   `eval'` is [eval_Mod] on the nose, and a consumer who reaches for the
   class's vocabulary gets the terms proved about here rather than an
   opaque repackaging.

   WHAT THE INSTANCE IS THE FIRST OF, STATED AT THE STRENGTH IT IS
   MEASURED.  A whole-tree sweep for the token [SymMonClosed] AT THE PARENT
   COMMIT — before this file and its sibling existed — returns six files:
   the class's own (Structure/Monoidal/StarAutonomous.v), three that take it
   as a HYPOTHESIS (Structure/Monoidal/Dual.v, Test/ProbeDual359.v,
   Structure/Closed.v's prose), and two comment mentions
   (Instance/FdVect/DoubleDual.v:105-108, Structure/Monoidal/Symmetric.v:83).
   The revision matters: sweeping at THIS commit returns eight, the two
   extra being this file and Instance/Mod/Monoidal.v, so a sweep that names
   a sibling introduced by the same commit is reporting its own arrival.
   None of the six declares an inhabitant, and
   Structure/Monoidal/Dual.v:227-229 says
   so in its own words: "Nothing here exhibits a [SymMonClosed] instance,
   so every result is a conditional".  [RMod_SymMonClosed] is therefore the
   first.  The sibling class [ClosedMonoidal] has exactly one inhabitant,
   Instance/Coq.v:179's [Coq_ClosedMonoidal], which is
   `CCC_ClosedMonoidal` and so cartesian by construction.

   MEASUREMENTS RECORDED.  93/93 constants closed under the global context
   — the count is [Print Module]'s, which lists 61 source-declared names
   together with the 32 [Program] obligations no source sweep sees, and the
   file declares no [Record], [Class] or [Inductive], so there is no
   unlisted [Build_*].  ([Print Module] wraps the module name onto its own
   line, so split its output on `:= Struct` rather than on the header, and
   count DISTINCT names rather than occurrences.)  Read the GRADE: that is
   a ONE-TIME measurement, not a standing gate.  The commit that lands this
   file registers it in `_CoqProject` and puts fifteen of its constants
   into the `print-assumptions` target; the other 78 were measured once, by
   hand.  With Instance/Mod/Monoidal.v's 123 that is 216 across the pair,
   and the 112 source-declared names of the two together collide with
   nothing in tree.

   WHAT IS NOT THEREBY CLAIMED.  This file does NOT prove that ⊗ is not a
   categorical product in [RMod R], so "the first non-cartesian closed
   monoidal witness" is NOT established here.  The obstacle is concrete
   rather than rhetorical: Instance/Mod/Coproduct.v:308 registers
   [RMod_Cartesian], so [RMod R] genuinely has products, and separating
   them from ⊗ would need a rank argument (over ℤ, Instance/Mod/Tensor.v's
   [Int_tensor_iso] gives ℤ ⊗ ℤ ≅ ℤ, and one would then have to refute
   ℤ ≅ ℤ × ℤ).  What IS true and measured is the weaker pair of facts in
   the preceding paragraph.

   UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE BLOCK.  The headline's
   constraint block contains NO equation — `RMod_SymMonClosed@{u u0}` has
   `u0 < u` and bounds — while its BINDER reads `R : RingObject@{u0 u0 u0}`,
   all three of the ring's universes identified by reuse of one level
   variable.  Reading the block alone reports no identification and is
   wrong; this is the trap the tree records at Instance/Mod/Monoidal.v and
   at Structure/Ring.v's [dup_left].  The identification is INHERITED and
   the probe section localises it:

     FREE at `R : RingObject@{ra rb rc}` with `ra < rc` declared —
     [RMod], [TensorMod], [tensor_gen], [HomMod], [ihom_post];
     REJECTED there — [tensor_med] (the donor, Instance/Mod/Tensor.v:664),
     [mt_fmap], [hm_curry], [ModSymmetric], [RMod_SymMonClosed].

   So [tensor_med] is A donor, rejected ALONE with [TensorMod] and
   [tensor_gen] accepted at the very same levels; whether it is the only
   one is NOT established, and no repair was attempted.

   A SECOND, INDEPENDENT OBSERVATION, AND IT LOCALISES THE OTHER HALF —
   NOT IN THIS FILE.  The two identifications a [RingObject@{a b c}] can
   acquire here are FIRST=THIRD and FIRST=SECOND, and they come from
   different places.  The first is what the probe section above pins.  The
   second is NOT the closed half's: [tensor_med] and every ingredient of
   [hm_curry] — [cur_fun], [cur_at], [cur_at_smul], [cur_out_zero],
   [cur_out_plus], [cur_out_smul] — read `RingObject@{a b a}`, and so,
   measured rather than assumed, do [hm_curry] itself and its [Program]
   obligation [hm_curry_obligation_1].  So no constant this file declares
   identifies the first two.
   The equation `u = u0` visible in [RMod_SymMonClosed]'s BINDER is
   therefore inherited whole from Instance/Mod/Monoidal.v's [ModMonoidal],
   which that file's header localises to its own packaging, and the probe
   section below guards the split: under a declared `Constraint rb < ra` —
   which violates FIRST=SECOND while leaving FIRST=THIRD alone —
   [hm_curry], [HomMod], [exp_iso_Mod] and [ump_exponents_Mod] all
   elaborate, while [ModMonoidal], [ModSymmetric] and the headline
   [RMod_SymMonClosed] are all rejected.  Read the constraint BLOCK
   flattened when checking this: [Print] wraps it, and the equations that
   matter here sit past the first line.  Nothing is repaired and nothing
   is claimed unavoidable.

   WHAT IS NOT DELIVERED.

     - No proof that ⊗ is not the categorical product of [RMod R], hence
       no claim of a first non-cartesian witness (see above).
     - No [StarAutonomous] instance.  [RMod R] has no dualizing object in
       tree and none is sought; the file supplies what
       Structure/Monoidal/Dual.v needs as a HYPOTHESIS and stops there.
     - No [Adjunction] record.  The bijection is delivered as an
       isomorphism of hom-setoids in [Sets], naturally in each variable
       separately; it is NOT packaged as `− ⊗ W ⊣ HomMod W −` in
       Theory/Adjunction.v's shape, and no functor `RMod R ⟶ RMod R` for
       either side is built.
     - Consequently no unit, no counit, and no triangle identities; and
       nothing about preservation of colimits by − ⊗ W.
     - No enriched reading: [RMod R] is not exhibited as enriched over
       itself, and [HomMod] is not related to Construction/Enriched.v.
     - No bifunctoriality of [HomMod].  [ihom_post] and [ihom_pre] are its
       two arrow actions and are proved natural where used, but they are
       not assembled into `(RMod R)^op ∏ RMod R ⟶ RMod R`, so the six
       squares are lemmas about arrows rather than about a bifunctor.
     - No naturality in the RING, and no interaction with
       Instance/Rng/Mod.v's restriction of scalars.
     - No non-commutative variant.  Over a general R the correct statement
       is a bimodule one; nothing here approaches it, and the file does
       not exhibit a ring where the construction FAILS.
     - No relation to Instance/Ab/Monoidal.v at R = ℤ (the ℤ-module
       structure of an [AbObject] is not in tree), and no relation to
       Instance/Mod/Free.v's free module or to
       Instance/FdVect/DoubleDual.v's dual functor beyond the prose
       identification above.
     - No universe repair; the identification is measured and pinned, not
       lifted, and nothing here is annotated.
     - No [Instance] registration.  Like Instance/Mod/Monoidal.v's three
       structures, [RMod_SymMonClosed] is a plain [Definition]: registering
       it would leave typeclass resolution an unsolvable commutativity
       subgoal at an abstract ring. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Monoidal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.AbCategory.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Engineering note (c): [mt_eq_Equivalence] (Instance/Mod/Tensor.v:479) is
   a Lemma, not an Instance, so [transitivity] and setoid [rewrite] cannot
   see it on goals that have unfolded to [mt_eq] — and the error names the
   wrong culprit when they cannot. *)
#[local] Existing Instance mt_eq_Equivalence.

(** ** The internal hom

    The module of R-linear maps V ⟶ W.  Carrier, addition, zero and
    negation are Instance/Mod.v's own hom-algebra; the ACTION is the
    pointwise (r · φ) v := r · φ v, and that is where commutativity
    lands. *)

Section InternalHom.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

(* Negation of a module homomorphism.  Instance/Mod.v supplies
   [rmod_hom_add] and [rmod_hom_zero] but no negation, and the obvious name
   [rmod_hom_neg] is taken by Instance/FdVect/DoubleDual.v:158 — hence the
   local name. *)
Program Definition hm_neg {M N : RModObject R} (f : RModHom M N) :
  RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(* The carrier setoid: two homomorphisms agree when they agree pointwise. *)
Definition hm_setoid (V W : RModObject R) : SetoidObject := {|
  carrier   := RModHom V W;
  is_setoid := @RModHom_Setoid R V W
|}.

Program Definition hm_cmon (V W : RModObject R) : CMonObject := {|
  cmon_setoid := hm_setoid V W;
  cmon_zero   := @rmod_hom_zero R V W;
  cmon_plus   := @rmod_hom_add R V W
|}.
Next Obligation.
  intros V W f f' Hf g g' Hg v; simpl.
  now rewrite (Hf v), (Hg v).
Qed.
Next Obligation. intros V W f g h v; simpl; apply cmon_plus_assoc. Qed.
Next Obligation. intros V W f g v; simpl; apply cmon_plus_comm. Qed.
Next Obligation. intros V W f v; simpl; apply cmon_plus_zero_l. Qed.

Program Definition hm_ab (V W : RModObject R) : AbObject := {|
  ab_cmon := hm_cmon V W;
  ab_neg  := @hm_neg V W
|}.
Next Obligation.
  intros V W f g Hfg v; simpl.
  now rewrite (Hfg v).
Qed.
Next Obligation. intros V W f v; simpl; apply ab_neg_left. Qed.

(** *** The pointwise action, and the one use of commutativity

    Preservation of zero and of addition are annihilation and
    distributivity in W, and neither mentions [Rcomm] — the two lemmas
    below are what the probe section uses as controls.  The remaining
    clause, that r · φ is still LINEAR, is the one that does. *)

Lemma hm_smul_zero (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  rm_smul W r (cmon_map (rm_hom f) (cmon_zero V)) ≈ cmon_zero W.
Proof.
  rewrite (cmon_map_zero (rm_hom f)).
  apply rm_smul_zero_r.
Qed.

Lemma hm_smul_plus (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ v w, rm_smul W r (cmon_map (rm_hom f) (cmon_plus V v w))
           ≈ cmon_plus W (rm_smul W r (cmon_map (rm_hom f) v))
                         (rm_smul W r (cmon_map (rm_hom f) w)).
Proof.
  intros v w.
  rewrite (cmon_map_plus (rm_hom f) v w).
  apply rm_smul_distr_l.
Qed.

(* THE ONE USE OF COMMUTATIVITY IN THE WHOLE FILE.

   The `Proof using R Rcomm` annotation is LOAD-BEARING and is the
   instrument the header describes: Lib.v:13 sets
   [Default Proof Using "Type"], [Rcomm] occurs in no statement here, and
   without the annotation this lemma fails at [Qed] with "The following
   section variable is used but not declared: Rcomm."  Do not remove it,
   and do not silence it with `Set Default Proof Using "All"` — that would
   destroy the measurement rather than pass it. *)
Lemma hm_smul_linear (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ s v, rm_smul W r (cmon_map (rm_hom f) (rm_smul V s v))
           ≈ rm_smul W s (rm_smul W r (cmon_map (rm_hom f) v)).
Proof using R Rcomm.
  intros s v.
  rewrite (rm_map_smul f s v).
  rewrite <- (rm_smul_assoc W r s (cmon_map (rm_hom f) v)).
  rewrite (Rcomm r s).
  apply (rm_smul_assoc W s r (cmon_map (rm_hom f) v)).
Qed.

Program Definition hm_smul (V W : RModObject R)
        (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  RModHom V W := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v =>
                          rm_smul W r (cmon_map (rm_hom f) v) |};
    cmon_map_zero := hm_smul_zero V W r f;
    cmon_map_plus := hm_smul_plus V W r f
  |};
  rm_map_smul := hm_smul_linear V W r f
|}.
Next Obligation.
  intros V W r f v w Hvw; simpl.
  now rewrite Hvw.
Qed.

(** *** The internal hom module

    Every module law below is the corresponding law of W read at each
    vector; none of them needs [Rcomm] again. *)
Program Definition HomMod (V W : RModObject R) : RModObject R := {|
  rm_ab   := hm_ab V W;
  rm_smul := hm_smul V W
|}.
Next Obligation.
  intros V W r s Hrs f g Hfg v; simpl.
  now rewrite Hrs, (Hfg v).
Qed.
Next Obligation. intros V W r f g v; simpl; apply rm_smul_distr_l. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_assoc. Qed.
Next Obligation. intros V W f v; simpl; apply rm_smul_one. Qed.

(* The carrier IS the hom-set, on the nose. *)
Example HomMod_carrier (V W : RModObject R) :
  carrier (cmon_setoid (HomMod V W)) = RModHom V W := eq_refl.

End InternalHom.

(** ** Currying and uncurrying

    [hm_curry] sends f : V ⊗ W ⟶ X to v ↦ (w ↦ f (v ⊗ w)); [hm_uncurry]
    factors the bilinear map (v, w) ↦ (g v) w through the tensor.  Both
    round trips are below, and both are cheap for the reason the header
    gives: [tensor_med] computes on generators. *)

Section Adjunction.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH := (HomMod R Rcomm).

Section Curry.

Context {V W X : RModObject R}.
Context (f : TensorMod V W ~{RMod R}~> X).

(* [mval] is Instance/Mod/Monoidal.v's name for the underlying function of
   a module homomorphism; it is imported, not redeclared. *)
Definition cur_fun (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid W)) : carrier (cmon_setoid X) :=
  mval f (mt_gen v w).

(* w ↦ f (v ⊗ w) is a module homomorphism W ⟶ X: each clause is one
   clause of [tensor_gen] pushed through f. *)

Lemma cur_at_zero (v : carrier (cmon_setoid V)) :
  cur_fun v (cmon_zero W) ≈ cmon_zero X.
Proof.
  unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_r tensor_gen v).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_at_plus (v : carrier (cmon_setoid V)) :
  ∀ w w', cur_fun v (cmon_plus W w w')
            ≈ cmon_plus X (cur_fun v w) (cur_fun v w').
Proof.
  intros w w'; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v w'))).
  - apply proper_morphism, (rbl_add_r tensor_gen v w w').
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_at_smul (v : carrier (cmon_setoid V)) :
  ∀ r w, cur_fun v (rm_smul W r w) ≈ rm_smul X r (cur_fun v w).
Proof.
  intros r w; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_r tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition cur_at (v : carrier (cmon_setoid V)) : RModHom W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_fun v |};
    cmon_map_zero := cur_at_zero v;
    cmon_map_plus := cur_at_plus v
  |};
  rm_map_smul := cur_at_smul v
|}.
Next Obligation.
  intros v w w' Hw; unfold cur_fun, mval; simpl.
  apply proper_morphism, (rbl_respects tensor_gen); [reflexivity | exact Hw].
Qed.

(* And v ↦ cur_at v is a module homomorphism V ⟶ IH W X: the same three
   clauses of [tensor_gen] in the OTHER variable. *)

Lemma cur_out_zero : cur_at (cmon_zero V) ≈ cmon_zero (IH W X).
Proof.
  intro w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_l tensor_gen w).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_out_plus : ∀ v v',
  cur_at (cmon_plus V v v') ≈ cmon_plus (IH W X) (cur_at v) (cur_at v').
Proof.
  intros v v' w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v' w))).
  - apply proper_morphism, (rbl_add_l tensor_gen v v' w).
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_out_smul : ∀ r v,
  cur_at (rm_smul V r v) ≈ rm_smul (IH W X) r (cur_at v).
Proof.
  intros r v w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_l tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition hm_curry : V ~{RMod R}~> IH W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_at |};
    cmon_map_zero := cur_out_zero;
    cmon_map_plus := cur_out_plus
  |};
  rm_map_smul := cur_out_smul
|}.
Next Obligation.
  intros v v' Hv w; simpl; unfold cur_fun, mval.
  apply proper_morphism, (rbl_respects tensor_gen); [exact Hv | reflexivity].
Qed.

End Curry.

Arguments hm_curry {V W X} f.

Section Uncurry.

Context {V W X : RModObject R}.
Context (g : V ~{RMod R}~> IH W X).

(* (v, w) ↦ (g v) w is bilinear: linearity in w is g v's own linearity,
   linearity in v is g's, read at w. *)
Program Definition uncur_bilinear : RBilinear V W X := {|
  rbl_map := fun v w => mval (mval g v) w
|}.
Next Obligation.
  intros v v' Hv w w' Hw; simpl; unfold mval.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom g) v)) w').
  - apply proper_morphism, Hw.
  - exact (proper_morphism (cmon_map (rm_hom g)) v v' Hv w').
Qed.
Next Obligation.
  intros v v' w; simpl.
  exact (cmon_map_plus (rm_hom g) v v' w).
Qed.
Next Obligation.
  intros v w w'; simpl.
  apply (cmon_map_plus (rm_hom (cmon_map (rm_hom g) v)) w w').
Qed.
Next Obligation.
  intros r v w; simpl.
  exact (rm_map_smul g r v w).
Qed.
Next Obligation.
  intros r v w; simpl.
  apply (rm_map_smul (cmon_map (rm_hom g) v) r w).
Qed.

Definition hm_uncurry : TensorMod V W ~{RMod R}~> X :=
  tensor_med uncur_bilinear.

End Uncurry.

Arguments hm_uncurry {V W X} g.

(* The uncurried map's value at a generator is φ applied to the argument,
   at LEIBNIZ equality.  This is [tensor_med]'s own `eq_refl` generator
   equation (Instance/Mod/Tensor.v:687) instantiated, and it is what makes
   everything below cheap. *)
Example hm_uncurry_gen {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) v w :
  mval (hm_uncurry g) (mt_gen v w) = mval (mval g v) w := eq_refl.

(* Round trip one: extensionality, then the generator computation. *)
Lemma hm_uncurry_curry {V W X : RModObject R}
  (f : TensorMod V W ~{RMod R}~> X) : hm_uncurry (hm_curry f) ≈ f.
Proof.
  refine (tensor_hom_ext (hm_uncurry (hm_curry f)) f _).
  intros v w; reflexivity.
Qed.

(* Round trip two: pointwise definitional, no extensionality needed. *)
Lemma hm_curry_uncurry {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) : hm_curry (hm_uncurry g) ≈ g.
Proof. intros v w; reflexivity. Qed.

End Adjunction.

(** ** The bijection, evaluation, and the universal property *)

Section ExpIso.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH  := (HomMod R Rcomm).
Notation cur := (hm_curry R Rcomm).
Notation unc := (hm_uncurry R Rcomm).

Program Definition exp_to (V W X : RModObject R) :
  {| carrier := TensorMod V W ~{RMod R}~> X |}
    ~{Sets}~> {| carrier := V ~{RMod R}~> IH W X |} := {|
  morphism := @hm_curry R Rcomm V W X
|}.
Next Obligation.
  intros V W X f f' Hf v w; simpl.
  exact (Hf (mt_gen v w)).
Qed.

Program Definition exp_from (V W X : RModObject R) :
  {| carrier := V ~{RMod R}~> IH W X |}
    ~{Sets}~> {| carrier := TensorMod V W ~{RMod R}~> X |} := {|
  morphism := @hm_uncurry R Rcomm V W X
|}.
Next Obligation.
  intros V W X g g' Hg.
  refine (tensor_hom_ext (unc g) (unc g') _).
  intros v w; exact (Hg v w).
Qed.

Program Definition exp_iso_Mod (V W X : RModObject R) :
  @Isomorphism Sets
    {| carrier := TensorMod V W ~{RMod R}~> X |}
    {| carrier := V ~{RMod R}~> IH W X |} := {|
  to   := exp_to V W X;
  from := exp_from V W X
|}.
Next Obligation.
  intros V W X g; exact (hm_curry_uncurry R Rcomm g).
Qed.
Next Obligation.
  intros V W X f; exact (hm_uncurry_curry R Rcomm f).
Qed.

(** Evaluation is the uncurried identity — which is exactly what the class
    takes [eval'] to be, so [smc_eval] below is `eq_refl`. *)
Definition eval_Mod (W X : RModObject R) :
  TensorMod (IH W X) W ~{RMod R}~> X :=
  unc (@id (RMod R) (IH W X)).

Example eval_Mod_gen (W X : RModObject R)
  (phi : carrier (cmon_setoid (IH W X))) (w : carrier (cmon_setoid W)) :
  mval (eval_Mod W X) (mt_gen phi w) = mval phi w := eq_refl.

(* The beta law.  [mt_fmap] is Instance/Mod/Monoidal.v's arrow action, and
   `bimap h id` reduces to it — see [smc_bimap] below. *)
Lemma ump_beta (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X) :
  f ≈ eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext f
            (eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

(* Uniqueness: evaluate the hypothesis at a generator.  Nothing else. *)
Lemma ump_uniq (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X)
  (h : V ~{RMod R}~> IH W X) :
  f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W) → cur f ≈ h.
Proof.
  intros Hh v w.
  exact (Hh (mt_gen v w)).
Qed.

Theorem ump_exponents_Mod (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  ∃! h : V ~{RMod R}~> IH W X,
    f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W).
Proof.
  exists (cur f).
  - exact (ump_beta V W X f).
  - intros h Hh; exact (ump_uniq V W X f h Hh).
Qed.

End ExpIso.

(** ** THE HEADLINE

    Every field is filled by `:=` with no tactic and no transport.  The
    underlying symmetric monoidal structure is Instance/Mod/Monoidal.v's
    [ModSymmetric] itself, not a copy; the internal hom is [HomMod]; the
    bijection is [exp_iso_Mod]; the universal property is
    [ump_exponents_Mod].  A plain [Definition] rather than an [Instance],
    for the reason the header gives. *)

Definition RMod_SymMonClosed (R : RingObject)
  (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
      rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a) :
  @SymMonClosed (RMod R) := {|
  smc_is_symmetric := ModSymmetric Rcomm;
  exponent_obj     := HomMod R Rcomm;
  exp_iso          := @exp_iso_Mod R Rcomm;
  ump_exponents'   := @ump_exponents_Mod R Rcomm
|}.

(** *** What the class returns, measured at [eq_refl]

    Seven identifications.  Three of them concern the class's DEFINED
    fields — [curry'], [uncurry'] and [eval'] have bodies rather than being
    arguments, so a consumer could have received a repackaging; these
    record that they receive this file's own constants instead.  Two more
    check the join with Instance/Mod/Monoidal.v: the tensor's object action
    and the reduction of `bimap h id` to [mt_fmap h id]. *)

Section Slot.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation SMC := (RMod_SymMonClosed R Rcomm).

Example smc_symmetric :
  @smc_is_symmetric (RMod R) SMC = ModSymmetric Rcomm := eq_refl.

Example smc_exponent (V W : RModObject R) :
  @exponent_obj (RMod R) SMC V W = HomMod R Rcomm V W := eq_refl.

Example smc_curry (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  @curry' (RMod R) SMC V W X f = hm_curry R Rcomm f := eq_refl.

Example smc_uncurry (V W X : RModObject R)
  (g : V ~{RMod R}~> HomMod R Rcomm W X) :
  @uncurry' (RMod R) SMC V W X g = hm_uncurry R Rcomm g := eq_refl.

Example smc_eval (W X : RModObject R) :
  @eval' (RMod R) SMC W X = eval_Mod R Rcomm W X := eq_refl.

Example smc_tensor (V W : RModObject R) :
  fobj[@tensor (RMod R) SMC] (V, W) = TensorMod V W := eq_refl.

Example smc_bimap (V W X : RModObject R)
  (h : V ~{RMod R}~> HomMod R Rcomm W X) :
  @bimap _ _ _ (@tensor (RMod R) SMC) _ _ _ _ h (@id (RMod R) W)
    = mt_fmap h (@id (RMod R) W) := eq_refl.

End Slot.

(** ** Naturality in all three variables

    The internal hom's two arrow actions, and then the six squares.  See
    the header for why both legs are stated. *)

Section Naturality.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH   := (HomMod R Rcomm).
Notation cur  := (hm_curry R Rcomm).
Notation unc  := (hm_uncurry R Rcomm).

(* Postcomposition: covariant in the target. *)
Program Definition ihom_post {W X X' : RModObject R}
  (k : X ~{RMod R}~> X') : IH W X ~{RMod R}~> IH W X' := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W X X' k phi |} |}
|}.
Next Obligation.
  intros W X X' k phi psi Hphi w; simpl; unfold Basics.compose.
  apply proper_morphism, (Hphi w).
Qed.
Next Obligation.
  intros W X X' k w; simpl; unfold Basics.compose.
  apply (cmon_map_zero (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k phi psi w; simpl; unfold Basics.compose.
  apply (cmon_map_plus (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k r phi w; simpl; unfold Basics.compose.
  apply (rm_map_smul k).
Qed.

(* Precomposition: contravariant in the source.  Every clause is
   [reflexivity] — precomposition moves no structure. *)
Program Definition ihom_pre {W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) : IH W X ~{RMod R}~> IH W' X := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W' W X phi j |} |}
|}.
Next Obligation.
  intros W W' X j phi psi Hphi w; simpl; unfold Basics.compose.
  exact (Hphi _).
Qed.
Next Obligation. intros W W' X j w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j phi psi w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j r phi w; simpl; reflexivity. Qed.

(** *** The three FORWARD squares

    Each holds by [reflexivity]: the two sides are pointwise the same
    term.  Note that this is agreement in the hom-SETOID; the whole
    morphism records are NOT Leibniz-equal, and the probe section pins
    that. *)

(* (a) In V, contravariantly: precomposing with i ⊗ id downstairs is
       precomposing with i upstairs. *)
Theorem cur_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap i (@id (RMod R) W)) ≈ cur f ∘ i.
Proof. intros v w; reflexivity. Qed.

(* (b) In W, contravariantly: precomposing with id ⊗ j downstairs is
       postcomposing with [ihom_pre j] upstairs. *)
Theorem cur_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap (@id (RMod R) V) j) ≈ ihom_pre j ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(* (c) In X, covariantly: postcomposing with k downstairs is
       postcomposing with [ihom_post k] upstairs. *)
Theorem cur_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (f : TensorMod V W ~{RMod R}~> X) :
  cur (k ∘ f) ≈ ihom_post k ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(** *** The three BACKWARD squares

    NOT definitional.  Both sides are recursions over [MTerm] — the
    left-hand one built from a single bilinear map, the right-hand one a
    composite — so they agree at every generator but are different terms
    at a variable tensor.  Each needs one [tensor_hom_ext] and then
    [reflexivity], and nothing else: no [tensor_factor_commutes], no
    transitivity chain. *)

Theorem unc_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (g : V ~{RMod R}~> IH W X) :
  unc (g ∘ i) ≈ unc g ∘ mt_fmap i (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext (unc (g ∘ i))
            (unc g ∘ mt_fmap i (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (g : V ~{RMod R}~> IH W X) :
  unc (ihom_pre j ∘ g) ≈ unc g ∘ mt_fmap (@id (RMod R) V) j.
Proof.
  refine (tensor_hom_ext (unc (ihom_pre j ∘ g))
            (unc g ∘ mt_fmap (@id (RMod R) V) j) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (g : V ~{RMod R}~> IH W X) :
  unc (ihom_post k ∘ g) ≈ k ∘ unc g.
Proof.
  refine (tensor_hom_ext (unc (ihom_post k ∘ g)) (k ∘ unc g) _).
  intros v w; reflexivity.
Qed.

End Naturality.

(** ** Acceptance tests over ℤ

    ℤ is commutative (Instance/Rng.v:412's [Int_Ring_commutative]), so the
    whole structure is inhabited at a concrete base.  The bilinear map is
    Instance/Mod/Tensor.v:905's own [Int_mul_bilinear] — nothing is
    rebuilt — and every Example below closes by `eq_refl`: these are
    computations, not equational arguments. *)

Local Notation Zc := Int_Ring_commutative.
Local Notation ZIH := (HomMod Int_Ring Zc).
Local Notation zg := (@mt_gen Int_Ring Int_RMod Int_RMod).

Definition Int_Mod_SymMonClosed : @SymMonClosed (RMod Int_Ring) :=
  RMod_SymMonClosed Int_Ring Int_Ring_commutative.

(* The ℤ-linear endomorphisms of ℤ, as a ℤ-module. *)
Definition ZEnd : RModObject Int_Ring := ZIH Int_RMod Int_RMod.

(* The pointwise action COMPUTES: (3 · id) 5 = 15. *)
Example Zsmul_computes :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z = 15%Z
  := eq_refl.

(* Two elements of the internal hom that are provably distinct, so it is
   not a subsingleton and the computations above are not degenerate. *)
Example ZEnd_nontrivial :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 1%Z
    ≈ mval (@id (RMod Int_Ring) Int_RMod) 1%Z → False.
Proof. simpl; discriminate. Qed.

Definition Zmul_tensor_hom :
  TensorMod Int_RMod Int_RMod ~{RMod Int_Ring}~> Int_RMod :=
  tensor_med Int_mul_bilinear.

(* Currying computes: cur(multiplication) at 2, applied to 3, is 6. *)
Example Zcur_computes :
  mval (mval (hm_curry Int_Ring Zc Zmul_tensor_hom) 2%Z) 3%Z = 6%Z
  := eq_refl.

(* And so does the round trip, at a generator. *)
Example Zuncur_computes :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 4%Z 5%Z) = 20%Z := eq_refl.

(* Evaluation computes, through the file's own [eval_Mod] ... *)
Example Zeval_computes :
  mval (eval_Mod Int_Ring Zc Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 15%Z := eq_refl.

(* ... and through the CLASS's [eval'], which is the same term. *)
Example Zsmc_eval :
  mval (@eval' (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 4%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 20%Z := eq_refl.

Example Zsmc_exp :
  @exponent_obj (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod
    = ZEnd := eq_refl.

(** ** Probes

    THIRTEEN negatives of THREE KINDS — two TYPING, three CONVERSION,
    eight FORMABILITY — kept lexically apart, each beside an APPLIED
    positive control, plus a scope-free instrument check.  With
    Instance/Mod/Monoidal.v's eight that is twenty-one negatives across the
    pair, in four kinds; the two instrument checks are guards and are not
    counted among them, so the two files carry twenty-three [Fail]
    commands in all.  A [Fail] that succeeds prints nothing under this
    repository's [coqc], so each negative below
    was stripped of its [Fail] and compiled alone, and its failure KIND
    read off the WHOLE error message rather than the tail: the TYPING two
    report a bare type mismatch with no `cannot unify` and no universe
    clause, the CONVERSION three end in `cannot unify`, and the
    FORMABILITY eight end in a universe inconsistency naming the levels
    the probe section declared — `Cannot enforce rc = ra because
    ra < rc` for the five that test FIRST=THIRD, and `Cannot enforce
    rb = ra because rb < ra` for the three that test FIRST=SECOND. *)

(* INSTRUMENT CHECK — scope-free, guards that [Fail] is doing anything. *)
Fail Example mod_closed_instrument : (true = false) := eq_refl.

(** *** Kind 1: TYPING *)

Section ProbeTyping.

Context (R : RingObject).
Context (V W : RModObject R).
Context (r : carrier (rig_setoid (ring_rig R))).
Context (f : RModHom V W).

(* NEGATIVE 1.  The [Default Proof Using] instrument, read from outside
   the proof: [hm_smul_linear] carries [Rcomm] as an ARGUMENT, so [V]
   lands in the commutativity slot and the application is ill-typed. *)
Fail Check (@hm_smul_linear R V W r f).

(* CONTROLS.  Its two siblings — same section, same statement shape, same
   [Program] block — do not, because their PROOFS do not use it. *)
Check (@hm_smul_zero R V W r f).
Check (@hm_smul_plus R V W r f).

End ProbeTyping.

(* NEGATIVE 2.  Engineering note: [mt_gen] at a hom-module needs explicit
   indices — the inner generator elaborates before the outer tensor is
   known, and the error blames the second argument. *)
Fail Check (mt_gen (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(* CONTROL: the annotated form. *)
Check (@mt_gen Int_Ring ZEnd Int_RMod
         (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(** *** Kind 2: CONVERSION *)

(* NEGATIVE 3.  The round trip is an `≈`, not a Leibniz identity of
   morphism records: [hm_uncurry (hm_curry f)] is a [tensor_med] over
   [uncur_bilinear], while [Zmul_tensor_hom] is one over
   [Int_mul_bilinear], and the two bilinear records are different terms. *)
Fail Example probe_rt_strict :
  hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom)
    = Zmul_tensor_hom := eq_refl.

(* CONTROL: at a generator it IS a Leibniz identity, so the obstruction is
   exactly extensionality and not the generator computation. *)
Example probe_rt_gen :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 2%Z 3%Z)
    = mval Zmul_tensor_hom (zg 2%Z 3%Z) := eq_refl.

Section ProbeConversion.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).
Context (V V' W X : RModObject R).
Context (i : V' ~{RMod R}~> V).
Context (g : V ~{RMod R}~> HomMod R Rcomm W X).
Context (v : carrier (cmon_setoid V')) (w : carrier (cmon_setoid W)).

(* NEGATIVE 4.  [unc_natural_V] at Leibniz strength: refuted.  This is
   what the [tensor_hom_ext] in its proof is buying. *)
Fail Example probe_unc_nat_strict :
  hm_uncurry R Rcomm (g ∘ i)
    = hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W) := eq_refl.

(* CONTROL: the same statement at a generator, at Leibniz `=`. *)
Example probe_unc_nat_gen :
  mval (hm_uncurry R Rcomm (g ∘ i)) (mt_gen v w)
    = mval (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
           (mt_gen v w) := eq_refl.

(* NEGATIVE 5.  The FORWARD square is `≈` by [reflexivity], but the two
   morphism RECORDS are still not Leibniz-equal — so "holds by
   [reflexivity]" must not be over-read as "is the same term". *)
Fail Example probe_cur_nat_strict :
  hm_curry R Rcomm (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
    = hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i := eq_refl.

(* CONTROL: pointwise, at Leibniz `=`, which is what [cur_natural_V]'s
   [reflexivity] actually discharges. *)
Example probe_cur_nat_at :
  mval (mval (hm_curry R Rcomm
                (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))) v) w
    = mval (mval (hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i) v) w
  := eq_refl.

End ProbeConversion.

(** *** Kind 3: FORMABILITY (universes)

    The header's measurement, guarded.  A library file CAN carry a
    section-local [Universes]/[Constraint] block without constraining
    itself — Instance/Fun/Group.v establishes that, and the two
    Test/Probe files that claimed otherwise are corrected there — so the
    probes live here rather than in a separate file.  All five controls
    are APPLIED, at the very levels where the five negatives are
    rejected. *)

Section ProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{ra rb rc}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(* CONTROLS: formable with the ring's first and third universes declared
   strictly apart. *)
Check (RMod Ru).
Check (TensorMod V W).
Check (@tensor_gen Ru V W).
Check (HomMod Ru Rcu V W).
Check (@ihom_post Ru Rcu V W W).

(* NEGATIVE 6.  The DONOR.  [tensor_med] (Instance/Mod/Tensor.v:664)
   already identifies the ring's first and third universes, while
   [TensorMod] and [tensor_gen] above do not — so the identification is
   the mediator's, not the tensor object's nor the generator's. *)
Fail Check (@tensor_med Ru V W).

(* NEGATIVE 7.  Instance/Mod/Monoidal.v's arrow action inherits it. *)
Fail Check (@mt_fmap Ru V W).

(* NEGATIVE 8.  Hence this file's currying. *)
Fail Check (@hm_curry Ru Rcu V W W).

(* NEGATIVE 9.  Instance/Mod/Monoidal.v's symmetric structure.  The ring
   is given EXPLICITLY: written `ModSymmetric Rcu` this probe is a FALSE
   GUARD — it still fails, but on an unresolved implicit (`?R`) with a
   plain type mismatch and no universe clause at all, so it would say
   nothing about the constraint.  Compare the trap
   Structure/Limit/Product/Finite.v records. *)
Fail Check (@ModSymmetric Ru Rcu).

(* NEGATIVE 10.  And therefore the headline.  Note the binder/block trap:
   `RMod_SymMonClosed@{u u0}`'s constraint block carries no equation at
   all, and only the binder `R : RingObject@{u0 u0 u0}` reveals this. *)
Fail Check (RMod_SymMonClosed Ru Rcu).

End ProbeUniverses.

(** The OTHER identification, guarded separately.

    The section above declares the ring's FIRST and THIRD universes apart
    and so tests only that equation.  This one declares the FIRST and
    SECOND apart, which is the identification the header attributes to
    Instance/Mod/Monoidal.v's [ModMonoidal] rather than to anything
    declared here.  Without this section that attribution would be
    measured and unguarded, and nothing in the build would notice an
    upstream annotation changing it. *)

Section ProbeMiddleUniverse.

Universes ra rb rc.
Constraint rb < ra.

Context (Ru : RingObject@{ra rb rc}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(* CONTROLS: nothing this file declares identifies the ring's first two
   universes, so all four are formable with them declared strictly apart.
   Each is APPLIED to [Ru], which is the argument carrying the levels. *)
Check (@hm_curry Ru Rcu V W W).
Check (HomMod Ru Rcu V W).
Check (@exp_iso_Mod Ru Rcu).
Check (@ump_exponents_Mod Ru Rcu).

(* NEGATIVE 11.  The donor: Instance/Mod/Monoidal.v's packaged monoidal
   structure, which identifies the first two where none of its own
   components does. *)
Fail Check (@ModMonoidal Ru Rcu).

(* NEGATIVE 12.  Inherited by the symmetric packaging. *)
Fail Check (@ModSymmetric Ru Rcu).

(* NEGATIVE 13.  And hence by the headline — whose own constraint block
   is still empty, the equation living in the binder alone. *)
Fail Check (@RMod_SymMonClosed Ru Rcu).

End ProbeMiddleUniverse.
