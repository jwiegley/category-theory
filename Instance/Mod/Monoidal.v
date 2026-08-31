(** * (R-Mod, ⊗, R): the symmetric monoidal structure of a module category *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §VII.1, printed p. 163 — the roster of tensor-product monoidal
              categories, of which "K-modules over a commutative ring K" is
              the row Instance/Ab/Monoidal.v's own SCOPE note defers.
   Book:      Mac Lane, ibid., §IV.1 printed p. 80 and §IV.6 printed p. 98 —
              the tensor-hom adjunction, whose ⊗ half is what this file
              supplies.
   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
   nLab:      https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

   Instance/Mod/Tensor.v built the object V ⊗ V' by generators and relations
   together with its universal property, and then said in terms what it did
   NOT build (Instance/Mod/Tensor.v:218-223):

     "NO BIFUNCTORIALITY.  Instance/Ab/Tensor.v's [AbTensor_Functor] has no
      counterpart here: nothing below makes ⊗ a functor
      [RMod R ∏ RMod R ⟶ RMod R], and no monoidal structure on [RMod R] is
      attempted.  (Both would be [tensor_hom_ext] plus computations on
      generators, exactly as there.)"

   This file discharges that, and the parenthetical forecast is accurate.
   Delivered:

     - [ModTensor : RMod R ∏ RMod R ⟶ RMod R], the tensor bifunctor
     - [ModUnitLeft], [ModUnitRight], the two unitors as isomorphisms
     - [ModAssoc] over [mod_assoc_to] / [mod_assoc_fr], the associator
     - [ModMonoidal], with both naturality directions for each structural
       isomorphism and both coherence laws
     - [ModBraid], [ModBraided], [ModSymmetric], with both hexagons and the
       involution

   GENERALITY, AND WHY THE BASE IS NOT [CRng].  Everything is stated over an
   arbitrary [RingObject] together with an EXPLICIT commutativity hypothesis

     Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
                 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

   which is, after elaboration, the predicate of Instance/Rng.v:398's
   [CRng_Sub], so an object of [CRng] supplies it by projection and
   Instance/Rng.v:412's [Int_Ring_commutative] discharges it at ℤ.  Indexing
   by [CRng] instead would have been the wrong move twice over: the module
   category the tree actually has is [RMod R] for a [RingObject] R, so a
   [CRng]-indexed statement would have to project its first component back
   out at every use, and — more to the point — carrying the hypothesis
   separately is what makes it MEASURABLE.  With commutativity a named
   variable rather than a field of the base object, the discharged signature
   of each constant records whether that constant used it, which is the
   instrument the paragraph on commutativity below relies on.

   THE PENTAGON IS DEFINITIONAL.  This is the file's most surprising fact and
   the reason the coherence half is short.  Instance/Mod/Tensor.v's mediator
   is [tensor_med_fun], a [Fixpoint] matching on the constructors of [MTerm];
   so the associator does not merely satisfy an equation on generators, it
   COMPUTES on them — [mod_assoc_to] sends the term `(a ⊗ b) ⊗ c` to the term
   `a ⊗ (b ⊗ c)` by reduction alone.  Both routes around the pentagon
   therefore carry `((a ⊗ b) ⊗ c) ⊗ d` to the very same [MTerm], namely
   `a ⊗ (b ⊗ (c ⊗ d))`, and the obligation closes with `simpl; apply mt_refl`
   once extensionality has exposed a fourfold generator.  The same holds of
   the two associator naturality squares, of braid naturality, of both
   hexagons and of the braid involution.  [mod_pentagon_computes] below
   records the collapse concretely over ℤ, as a Leibniz `eq_refl` between the
   two composites applied to `((2 ⊗ 3) ⊗ 5) ⊗ 7` — the acceptance test rather
   than the header is what checks this claim.

   Note the register precisely: [mt_refl], not [reflexivity].  `≈` on
   [TensorMod] is the [Type]-valued [mt_eq], whose reflexivity is a DERIVED
   lemma rather than a constructor, so after [simpl] the tactic [reflexivity]
   does not close the goal and names no useful culprit; [apply mt_refl] does.

   ONLY THREE OBLIGATIONS CARRY MATHEMATICAL CONTENT.  Of [ModMonoidal]'s
   eight fields, five close by conversion once the extensionality principles
   have reduced them to generators (`simpl; apply mt_refl`): both associator
   naturality squares, both `from`-direction unitor squares, and the
   pentagon.  What is left is exactly three:

     - [to_unit_left_natural] and [to_unit_right_natural], each of which is
       one application of Instance/Mod.v's [rm_map_smul] — the statement that
       a module homomorphism commutes with the action.  These are the only
       fields where the unitor's `to` leg, which multiplies, meets an
       arbitrary morphism.
     - [triangle_identity], which is Instance/Mod/Tensor.v's
       [tensor_balanced] — that a scalar may be moved across the tensor sign,
       `(r · a) ⊗ b ≈ a ⊗ (r · b)`.  That equation is the one place where the
       two unitors have to agree about which factor absorbs the scalar, and
       it is emphatically NOT definitional: over ℤ the two sides of the
       triangle reach the literally different terms `6 ⊗ 5` and `3 ⊗ 10`.
       [probe_balanced_conversion] pins that.

   Both the [BraidedMonoidal] and the [SymmetricMonoidal] layers add no
   content-bearing obligation at all; all four of their fields are `mt_refl`.

   THE GENERATOR-SLOT GADGET.  [tensor_hom_ext] says that two homomorphisms
   out of V ⊗ V' agreeing on generators agree everywhere, but the coherence
   laws are stated at ITERATED tensors, where the left (or right) factor of a
   generator is itself an arbitrary formal expression.  The obvious route is
   to induct through that factor, which is what Instance/Ab/Monoidal.v does:
   its [AgreeOnL] / [AgreeOnR] predicates with their eight closure lemmas
   occupy [Section GeneratorClosure], lines 603-700 of that file, and the
   three principles that iterate them to depth two and three occupy lines
   709-775 — 98 and 67 lines, so 165 in all (measured on that file at the
   revision this one was written against).  The contiguous SPAN 603-775 is
   173, but the eight lines between the two ranges belong to neither, so 165
   is the like-for-like figure and 173 would pad the denominator.

   The route taken here instead makes generator insertion a first-class
   module homomorphism.  [gen_r b : A ~> A ⊗ B] is `a ↦ a ⊗ b` and [gen_l a]
   is `b ↦ a ⊗ b`; each is a homomorphism precisely because the canonical map
   is bilinear, so its four obligations are the generator former's congruence
   rule, its additivity rule, the derived [tensor_zero_l], and one clause of
   [tensor_gen]'s bilinearity — no induction anywhere.  With them, reaching
   a nested generator becomes COMPOSITION rather than induction: to compare
   f and g on `(v ⊗ w) ⊗ x`, apply [tensor_hom_ext] once to peel the outer
   tensor and then again to `f ∘ gen_r x` and `g ∘ gen_r x`, which are
   honest module homomorphisms out of V ⊗ W.  [tensor_hom_ext_l],
   [tensor_hom_ext_r] and [tensor_hom_ext_ll] are five, five and seven lines
   of proof respectively.

   Measured on the same basis — comments and blank lines included — the
   whole gadget layer, from [mval] through [tensor_hom_ext_ll], is 129 lines
   against the Ab side's 165.  Read that comparison narrowly.  56 of the 129
   are the uniform four-way obligation body repeated across the eight
   [Program] obligations of [gen_r] and [gen_l], following
   Instance/Mod/Tensor.v:664's own idiom, so the substantive remainder is 73;
   and the two developments quotient by different relations, so no claim is
   made that the Ab-side machinery could have been written this way.  It was
   not re-attempted.

   WHERE COMMUTATIVITY IS SPENT.  In exactly three places, and all three have
   the same shape, `r · (s · v) ≈ s · (r · v)`:

     - [act_bilin]'s [rbl_smul_r] clause.  The action R × V → V is additive
       and R-linear in the left variable for free, but linear in the RIGHT
       variable — `r · (s · v) ≈ s · (r · v)` — only because R commutes.
     - [act_bilin_r]'s [rbl_smul_l] clause, the mirror image.
     - [rmod_hom_smul]'s [rm_map_smul] clause: `r · f(−)` is a module
       homomorphism, not merely an additive map, again only for commutative
       R.  This is what lets the associator's outer bilinear maps state their
       scalar clauses as equalities of HOMOMORPHISMS and so reduce them to
       generators via [tensor_hom_ext].

   Everything else is commutativity-free, and that is arranged structurally
   rather than asserted: [mval], [gen_r], [gen_l], the three
   [tensor_hom_ext_*] principles, [mt_bimap], [mt_fmap], [ModTensor],
   [braid_bilin], [ModBraid], and the associator's two inner legs
   ([assoc_in], [mod_assoc_fr_in]) are all declared in sections that do not
   bind [Rcomm] at all, so no proof in them could have used it.

   The consequence was VERIFIED AT THE SIGNATURES, by reading the discharged
   [Arguments] lines rather than the source: [ModUnitLeft {R} Rcomm V],
   [mod_assoc_to {R} Rcomm {V W X}], [rmod_hom_smul {R} Rcomm {M N} r f],
   [ModMonoidal {R} Rcomm] and [ModSymmetric {R} Rcomm] take the hypothesis,
   while [ModTensor {R}], [gen_r {R A B} b], [gen_l {R A B} a],
   [mval {R V W} f v], [ModBraid {R} V W], [assoc_in {R V W X} x],
   [mod_assoc_fr_in {R V W X} v] and [tensor_hom_ext_ll {R V W X Y K} f g]
   do not.  The TYPING negatives below pin the contrast from the failing
   side.  That the BRAIDING itself is commutativity-free is worth stating
   separately: the symmetry of ⊗ is a fact about the two-variable
   presentation of the tensor, not about R.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  Nothing here is annotated,
   so what follows is what inference assigned; it was read off [About], and
   off BOTH the binder and the constraint block, since in this library the
   two routinely disagree.  The finding is an asymmetry between the
   components and the assembly.  Every component leaves the [RingObject]'s
   first two universes merely BOUNDED — [ModTensor@{u u0 u1 u2}] carries
   `u0 <= u` together with `u = u1`, and so do [gen_r], [ModBraid],
   [ModUnitLeft], [ModUnitRight] and [ModAssoc].  [rmod_hom_smul] belongs
   with them as a control but not as an instance of that shape: measured,
   its block carries NO equation at all and no `u0 <= u`, only
   `u <= u1`, `u0 <= u1` and `u1 <= u2`, so it makes the point a fortiori.
   The
   assembled [ModMonoidal@{u u0 u1 u2}] instead carries `u = u0`,
   IDENTIFYING them, and [ModBraided] and [ModSymmetric] inherit it.

   The identification belongs to no one donor, and that is measured rather
   than attributed.  Under a declared `Constraint rp < ru` — which satisfies
   the bound while violating the equation — ELEVEN separate applications
   elaborate at `RingObject@{ru rp rq}`: [RMod Ru], [Ring_RMod Ru],
   [@Monoidal (RMod Ru)], [ModTensor], [gen_r], [gen_l], [ModBraid],
   [ModUnitLeft], [ModUnitRight], [ModAssoc] and [rmod_hom_smul] — including
   the [Monoidal] class itself and the unit object, the two obvious suspects
   — while [ModMonoidal] is rejected with
   "Cannot enforce rp = ru because rp < ru".
   The equation is therefore introduced by the PACKAGING and not by any
   field it packages.  No mechanism beyond that is claimed, no annotation was
   attempted, and the identification is NOT claimed unavoidable:
   Instance/Ab/Monoidal.v's design note 5 is the in-tree precedent for
   exactly such an identification turning out to be a minimization artifact
   that explicit declarations lift.

   PLACEMENT.  The gadget layer is arguably Instance/Mod/Tensor.v's — it
   mentions nothing this file introduces, and [tensor_hom_ext] is already
   there.  It lives here only so that Tensor.v is left untouched.  A later
   editor moving [mval], [gen_r], [gen_l] and the three extensionality
   lemmas upstream would change nothing below except the import list.

   The four [Ltac]s ([tens_ext] and siblings) are declared at top level
   because tactic notations do not survive a [Section].  They are named for
   this file's idiom rather than generically, since [Ltac] names are global;
   the sweep recorded below found no other use of any of them in tree.

   ENGINEERING NOTES, each of which cost a compile cycle.

     (a) `apply tensor_hom_ext` FAILS, and NOT for the reason one first
         guesses.  The goal `f ≈ g` in [RMod R] does unfold to
         `∀ a : TensorMod V W, f a ≈ g a`, so the hom-setoid is not the
         obstacle.  What [apply] reports (measured, with the statement below
         restated in a scratch file) is
         `Unable to unify "?M ?t ≈ ?M' ?t" with "∀ a, f a ≈ g a"` — a
         HIGHER-ORDER unification failure, the lemma's `cmon_map (rm_hom ?f)`
         presenting as an applied metavariable while `f` and `g` are still
         unknown.  Supplying them makes the head rigid, so the [Ltac]s below
         use `match goal with |- ?f ≈ ?g => refine (tensor_hom_ext f g _)
         end`.
     (b) [mt_eq_Equivalence] (Instance/Mod/Tensor.v:479) is a [Lemma], not an
         [Instance], so setoid [rewrite] and [transitivity] cannot see it and
         the resulting error names the wrong culprit.  Nothing below needs
         it; a consumer that does should add
         `#[local] Existing Instance mt_eq_Equivalence.`
     (c) [mt_gen] and [mte_gen] at a NESTED tensor need explicit `@`
         annotation.  Measured: writing `mt_gen (mt_gen v w) x` with the
         module arguments implicit is rejected with
         `The term "mt_gen v w" has type "MTerm V W" while it is expected to
         have type "carrier ?V"` — the inner generator is elaborated before
         the outer tensor is known, and a bare [MTerm] does not unify with a
         projection out of an unknown module.  This is the same trap
         Instance/Ab/Monoidal.v records at its [tensor_hom_ext2], and it is
         pinned as a TYPING negative below.
     (d) [Program] silently discharges [rbl_respects] by instance resolution
         when the map is literally [rm_smul], because Tensor.v:286 exports
         that field as an instance.  The obligation numbering then SHIFTS and
         the remaining proofs land on the wrong goals.  [act_bilin] therefore
         supplies [rbl_respects] explicitly; [act_bilin_r], whose map is
         [rm_smul] with its arguments swapped, is not caught by resolution
         and does not need to.
     (e) The records taking [Rcomm] are [Program Definition] and NOT
         [Instance].  Registering [ModMonoidal] would leave typeclass
         resolution an unsolvable commutativity subgoal at every use over an
         abstract ring.  (Instance/Ab/Monoidal.v's design note 4 registers
         its structures because [@Monoidal Ab] has no other inhabitant and
         needs no hypothesis; neither reason applies here.)  Consumers pass
         the structure explicitly, as the acceptance tests below do.
     (f) Name collisions found and avoided.  `assoc_to` is taken by
         Construction/Day.v:1279, hence [mod_assoc_to] / [mod_assoc_fr];
         `rmod_hom_neg` is taken by Instance/FdVect/DoubleDual.v:158, hence the
         scaling map is [rmod_hom_smul] and no negation map is declared; and
         `probe_instrument`, the obvious name for the probe section's
         instrument check, is taken by Test/ProbePolynomial.v:85, hence
         [mod_monoidal_instrument].  That last one matters even though the
         name sits inside a [Fail] and so creates no constant: the
         `print-assumptions` gate loads many files into one scope, where a
         shared name silently audits the wrong constant.  A sweep of all 62
         names this file declares — the constants from its own `.glob`
         rather than guessed, and the four [Ltac]s read off the source,
         since the `.glob` records no [Ltac] entry at all — found no other
         occurrence of any of the rest anywhere in tree.

   MEASUREMENTS RECORDED.  123/123 constants closed under the global context
   — the count is [Print Module]'s, which lists 51 source-declared names
   together with the 72 [Program] obligations no source sweep sees, and the
   file declares no [Record], [Class] or [Inductive], so there is no unlisted
   [Build_*].  (It renders the opaque constants as [Parameter]; that is a
   display convention, not an axiom.)  Read the GRADE: that is a ONE-TIME
   measurement, not a standing gate.  The commit that lands this file
   registers it in `_CoqProject` and puts eight of its constants into the
   `print-assumptions` target, so the build compiles the file and re-audits
   those eight on every run; the other 115 were measured once, by hand.

   The probe section carries EIGHT negatives in FOUR kinds (3 typing, 2
   conversion, 1 resolution, 2 formability) together with a scope-free
   instrument check — nine [Fail] commands in all, the instrument being a
   guard rather than a negative.  Each of the eight is
   stripped of its [Fail], compiled alone and its failure kind read off the
   whole error message.  Rename-simulated 9/9 on the constants a negative
   names and this file declares — [ModUnitLeft], [mod_assoc_to], [ZMod],
   [zz2], [zz3], [zz5], [mval], [ModMonoidal], [ModSymmetric] — each renamed
   AT ITS DEFINITION SITE, since a whole-file rename is a no-op by
   construction and would report a false clean bill; all nine broke the file
   at a NON-[Fail] line, so no guard is vacuous.  The [UniverseProbe]
   section's local [Universes] and [Constraint] declarations were measured
   NOT to leak: a downstream file reusing the same level names with the
   OPPOSITE constraint still elaborates.

   WHAT IS NOT DELIVERED.

     - NO CLOSED STRUCTURE.  The internal hom, the tensor-hom adjunction and
       any [SymMonClosed] instance are a companion file's business, not this
       one's; nothing here mentions an exponent.
     - NO PROOF THAT ⊗ IS NOT THE CATEGORICAL PRODUCT.  It is not, but no
       separation is machine-checked here, so this file does NOT establish
       "the tree's first non-cartesian monoidal witness" — that phrase would
       need a refutation nobody has written.  What is claimed instead is
       narrower and is evidence of two weaker kinds: a sweep for the
       SPELLINGS `@Monoidal … RMod` and `Monoidal (RMod` returns nothing, and
       Instance/Mod/Tensor.v:220 disclaims the structure in its own prose.
       Neither rules out some generic construction inhabiting
       [@Monoidal (RMod R)] under another name.
     - NO [Instance] REGISTRATION, for reason (e) above; [ModMonoidal],
       [ModBraided] and [ModSymmetric] are plain [Program Definition]s and do
       not participate in resolution.
     - NO NATURALITY IN R.  Nothing says how the structure varies along a
       ring homomorphism, and no comparison with Instance/Rng/Mod.v's
       restriction of scalars is attempted.
     - NO COMPARISON WITH Instance/Ab/Monoidal.v.  Over R = ℤ the two
       monoidal structures ought to agree, but the ℤ-module structure of an
       [AbObject] is not in tree (Instance/Mod/Tensor.v records the same gap
       for the underlying tensors), so no comparison functor is built.
     - NO UNIVERSE REPAIR.  The identification recorded above is measured and
       pinned, not lifted.  No constant in this file carries a universe
       annotation, and whether declarations in the style of
       Instance/Ab/Monoidal.v's design note 5 would free [ModMonoidal] is
       untested; so is whether the restriction bites at any category a
       consumer would want.
     - NO MONOIDS, ALGEBRAS OR BIMODULES over the structure, and no graded or
       differential-graded variants — the sibling rows of Mac Lane's §VII.1
       roster. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The generator-slot gadget

    Nothing in this section binds a commutativity hypothesis, so nothing in
    it can have used one.  See the header's paragraph on placement: this
    layer is arguably Instance/Mod/Tensor.v's and lives here only to leave
    that file untouched. *)

Section GenSlots.

Context {R : RingObject}.

(* The underlying function of a module homomorphism. *)
Definition mval {V W : RModObject R} (f : V ~{RMod R}~> W)
  (v : carrier (cmon_setoid V)) : carrier (cmon_setoid W) :=
  cmon_map (rm_hom f) v.

(* a ↦ a ⊗ b, as a module homomorphism A ~> A ⊗ B.  One uniform body serves
   all four obligations so the proof does not depend on the order [Program]
   emits them in — the Instance/Mod/Tensor.v:664 idiom. *)
Program Definition gen_r {A B : RModObject R}
  (b : carrier (cmon_setoid B)) : A ~{RMod R}~> TensorMod A B := {|
  rm_hom := {| cmon_map := {| morphism := fun a => mt_gen a b |} |}
|}.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.

(* b ↦ a ⊗ b, as a module homomorphism B ~> A ⊗ B. *)
Program Definition gen_l {A B : RModObject R}
  (a : carrier (cmon_setoid A)) : B ~{RMod R}~> TensorMod A B := {|
  rm_hom := {| cmon_map := {| morphism := fun b => mt_gen a b |} |}
|}.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.

(* Extensionality reaching through a left-nested tensor.  Two applications
   of [tensor_hom_ext]: the outer one peels the outer factor, and the inner
   one is applied to the honest homomorphisms `f ∘ gen_r x` and `g ∘ gen_r x`
   out of V ⊗ W.  No induction. *)
Lemma tensor_hom_ext_l {V W X K : RModObject R}
  (f g : TensorMod (TensorMod V W) X ~{RMod R}~> K) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid W))
     (x : carrier (cmon_setoid X)),
     mval f (@mt_gen R (TensorMod V W) X (mt_gen v w) x)
       ≈ mval g (@mt_gen R (TensorMod V W) X (mt_gen v w) x))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros s x.
  exact (tensor_hom_ext (f ∘ gen_r x) (g ∘ gen_r x)
           (fun v w => H v w x) s).
Qed.

(* Extensionality reaching through a right-nested tensor. *)
Lemma tensor_hom_ext_r {V W X K : RModObject R}
  (f g : TensorMod V (TensorMod W X) ~{RMod R}~> K) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid W))
     (x : carrier (cmon_setoid X)),
     mval f (@mt_gen R V (TensorMod W X) v (mt_gen w x))
       ≈ mval g (@mt_gen R V (TensorMod W X) v (mt_gen w x)))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros v t.
  exact (tensor_hom_ext (f ∘ gen_l v) (g ∘ gen_l v)
           (fun w x => H v w x) t).
Qed.

(* Extensionality reaching a fourfold left-nested generator: what the
   pentagon needs.  Three applications, still no induction. *)
Lemma tensor_hom_ext_ll {V W X Y K : RModObject R}
  (f g : TensorMod (TensorMod (TensorMod V W) X) Y ~{RMod R}~> K) :
  (∀ (a : carrier (cmon_setoid V)) (b : carrier (cmon_setoid W))
     (c : carrier (cmon_setoid X)) (d : carrier (cmon_setoid Y)),
     mval f (@mt_gen R (TensorMod (TensorMod V W) X) Y
               (@mt_gen R (TensorMod V W) X (mt_gen a b) c) d)
       ≈ mval g (@mt_gen R (TensorMod (TensorMod V W) X) Y
                   (@mt_gen R (TensorMod V W) X (mt_gen a b) c) d))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros s d.
  refine (tensor_hom_ext (f ∘ gen_r d) (g ∘ gen_r d) _ s).
  intros t c.
  exact (tensor_hom_ext (f ∘ gen_r d ∘ gen_r c) (g ∘ gen_r d ∘ gen_r c)
           (fun a b => H a b c d) t).
Qed.

End GenSlots.

(* Engineering note (a): `apply tensor_hom_ext` does not unify.  These are
   declared at top level because [Ltac] does not survive a [Section]. *)
Ltac tens_ext :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext f g _) end.
Ltac tens_ext_l :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_l f g _) end.
Ltac tens_ext_r :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_r f g _) end.
Ltac tens_ext_ll :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_ll f g _) end.

(** ** The tensor bifunctor

    Commutativity-free, and structurally so: this section binds no [Rcomm].
    The arrow action factors the bilinear map (v, w) ↦ f v ⊗ g w through the
    tensor, and all three functor laws are computations on generators. *)

Section ModTensorFunctor.

Context {R : RingObject}.

(* The bilinear map (v, w) ↦ f v ⊗ g w. *)
Program Definition mt_bimap {V V' W W' : RModObject R}
  (f : V ~{RMod R}~> W) (g : V' ~{RMod R}~> W') :
  RBilinear V V' (TensorMod W W') := {|
  rbl_map := fun v w => mt_gen (mval f v) (mval g w)
|}.
Next Obligation.
  intros V V' W W' f g v v' Hv w w' Hw.
  exact (mte_gen (proper_morphism _ _ _ Hv) (proper_morphism _ _ _ Hw)).
Qed.
Next Obligation.
  intros V V' W W' f g v v' w.
  refine (mte_trans (mte_gen (cmon_map_plus (rm_hom f) v v')
                             (reflexivity _)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros V V' W W' f g v w w'.
  refine (mte_trans (mte_gen (reflexivity _)
                             (cmon_map_plus (rm_hom g) w w')) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros V V' W W' f g r v w.
  refine (mte_trans (mte_gen (rm_map_smul f r v) (reflexivity _)) _).
  exact (rbl_smul_l tensor_gen r (mval f v) (mval g w)).
Qed.
Next Obligation.
  intros V V' W W' f g r v w.
  refine (mte_trans (mte_gen (reflexivity _) (rm_map_smul g r w)) _).
  exact (rbl_smul_r tensor_gen r (mval f v) (mval g w)).
Qed.

Definition mt_fmap {V V' W W' : RModObject R}
  (f : V ~{RMod R}~> W) (g : V' ~{RMod R}~> W') :
  TensorMod V V' ~{RMod R}~> TensorMod W W' :=
  tensor_med (mt_bimap f g).

Program Definition ModTensor : RMod R ∏ RMod R ⟶ RMod R := {|
  fobj := fun p => TensorMod (fst p) (snd p);
  fmap := fun p q fg => mt_fmap (fst fg) (snd fg)
|}.
Next Obligation.
  intros [V V'] [W W'] [f g] [f' g'] [Hf Hg].
  refine (tensor_hom_ext (mt_fmap f g) (mt_fmap f' g') _).
  intros v w.
  exact (mte_gen (Hf v) (Hg w)).
Qed.
Next Obligation.
  intros [V V'].
  refine (tensor_hom_ext (mt_fmap id id) id _).
  intros v w.
  exact (mt_refl _).
Qed.
Next Obligation.
  intros [V V'] [W W'] [X X'] [f g] [f' g'].
  refine (tensor_hom_ext (mt_fmap (f ∘ f') (g ∘ g'))
                         (mt_fmap f g ∘ mt_fmap f' g') _).
  intros v w.
  exact (mt_refl _).
Qed.

End ModTensorFunctor.

(** ** The braiding map

    Placed here, before commutativity is ever bound, because the fact is
    worth making structural: the symmetry of ⊗ is a statement about the
    two-variable presentation of the tensor and does not use commutativity
    of R.  Only the [BraidedMonoidal] PACKAGING below needs [Rcomm], and
    only because it contains the monoidal structure. *)

Section ModBraidMap.

Context {R : RingObject}.

Program Definition braid_bilin (V W : RModObject R) :
  RBilinear V W (TensorMod W V) := {|
  rbl_map := fun a b => mt_gen b a
|}.
Next Obligation.
  intros V W a a' Ha b b' Hb; exact (mte_gen Hb Ha).
Qed.
Next Obligation.
  intros V W a a' b; exact (mte_add_r b a a').
Qed.
Next Obligation.
  intros V W a b b'; exact (mte_add_l b b' a).
Qed.
Next Obligation.
  intros V W r a b; exact (rbl_smul_r tensor_gen r b a).
Qed.
Next Obligation.
  intros V W r a b; exact (rbl_smul_l tensor_gen r b a).
Qed.

Definition ModBraid (V W : RModObject R) :
  TensorMod V W ~{RMod R}~> TensorMod W V :=
  tensor_med (braid_bilin V W).

End ModBraidMap.

(** ** Scaling a homomorphism

    The first of the three places commutativity is spent.  For general R the
    map `m ↦ r · f m` is additive but need not commute with the action; the
    last obligation is `r · (s · v) ≈ s · (r · v)`, and [Rcomm] is what
    supplies it.  The associator needs this because its outer bilinear maps
    state their scalar clauses as equations between HOMOMORPHISMS, which is
    what lets [tensor_hom_ext] reduce them to generators. *)

Section HomSmul.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition rmod_hom_smul {M N : RModObject R}
  (r : carrier (rig_setoid (ring_rig R))) (f : M ~{RMod R}~> N) :
  M ~{RMod R}~> N := {|
  rm_hom := {| cmon_map := {|
    morphism := fun m => rm_smul N r (mval f m) |} |}
|}.
Next Obligation.
  intros M N r f a b Hab.
  exact (rm_smul_respects N _ _ (reflexivity r) _ _
           (proper_morphism _ _ _ Hab)).
Qed.
Next Obligation.
  intros M N r f; simpl.
  unfold mval.
  rewrite (cmon_map_zero (rm_hom f)).
  exact (rm_smul_zero_r N r).
Qed.
Next Obligation.
  intros M N r f a b; simpl.
  unfold mval.
  rewrite (cmon_map_plus (rm_hom f) a b).
  exact (rm_smul_distr_l N r _ _).
Qed.
(* COMMUTATIVITY, use 1 of 3. *)
Next Obligation.
  intros M N r f s m; simpl.
  unfold mval.
  rewrite (rm_map_smul f s m).
  rewrite <- (rm_smul_assoc N r s _).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc N s r _).
Qed.

End HomSmul.

(** ** The unitors

    [ModUnitLeft] factors the action R × V → V through the tensor; its
    inverse sends v to 1 ⊗ v.  One round trip is [rm_smul_one]; the other is
    [tensor_balanced] followed by [rig_mul_one_r].  The other two of the
    three uses of commutativity are here, one in each of the two bilinear
    maps, and each is the clause asserting linearity in the variable the
    action does NOT naturally act on. *)

Section Unitors.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Local Notation Runit := (Ring_RMod R).

(* The action R × V → V as a bilinear map.  [rbl_respects] is supplied
   explicitly: see engineering note (d) — left to [Program] it is closed by
   instance resolution and the obligation numbering shifts. *)
Program Definition act_bilin (V : RModObject R) :
  RBilinear Runit V V := {|
  rbl_map := fun r v => rm_smul V r v;
  rbl_respects := rm_smul_respects V
|}.
Next Obligation. intros V r r' v; exact (rm_smul_distr_r V r r' v). Qed.
Next Obligation. intros V r v v'; exact (rm_smul_distr_l V r v v'). Qed.
Next Obligation. intros V s r v; exact (rm_smul_assoc V s r v). Qed.
(* COMMUTATIVITY, use 2 of 3. *)
Next Obligation.
  intros V s r v.
  rewrite <- (rm_smul_assoc V r s v).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc V s r v).
Qed.

Program Definition ModUnitLeft (V : RModObject R) :
  @Isomorphism (RMod R) (TensorMod Runit V) V := {|
  to   := tensor_med (act_bilin V);
  from := @gen_l R Runit V (rig_one (ring_rig R))
|}.
Next Obligation.
  intros V v; simpl; exact (rm_smul_one V v).
Qed.
Next Obligation.
  intros V.
  refine (tensor_hom_ext (@gen_l R Runit V (rig_one (ring_rig R))
                            ∘ tensor_med (act_bilin V)) id _).
  intros r v; simpl.
  refine (mte_trans (mte_sym (@tensor_balanced R Runit V r
                              (rig_one (ring_rig R)) v)) _).
  exact (@mte_gen R Runit V _ _ _ _
           (rig_mul_one_r (ring_rig R) r) (reflexivity v)).
Qed.

Program Definition act_bilin_r (V : RModObject R) :
  RBilinear V Runit V := {|
  rbl_map := fun v r => rm_smul V r v
|}.
Next Obligation.
  intros V v v' Hv r r' Hr.
  exact (rm_smul_respects V _ _ Hr _ _ Hv).
Qed.
Next Obligation. intros V v v' r; exact (rm_smul_distr_l V r v v'). Qed.
Next Obligation. intros V v r r'; exact (rm_smul_distr_r V r r' v). Qed.
(* COMMUTATIVITY, use 3 of 3. *)
Next Obligation.
  intros V s v r.
  rewrite <- (rm_smul_assoc V r s v).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc V s r v).
Qed.
Next Obligation. intros V s v r; exact (rm_smul_assoc V s r v). Qed.

Program Definition ModUnitRight (V : RModObject R) :
  @Isomorphism (RMod R) (TensorMod V Runit) V := {|
  to   := tensor_med (act_bilin_r V);
  from := @gen_r R V Runit (rig_one (ring_rig R))
|}.
Next Obligation.
  intros V v; simpl; exact (rm_smul_one V v).
Qed.
Next Obligation.
  intros V.
  refine (tensor_hom_ext (@gen_r R V Runit (rig_one (ring_rig R))
                            ∘ tensor_med (act_bilin_r V)) id _).
  intros v r; simpl.
  refine (mte_trans (@tensor_balanced R V Runit r v
                       (rig_one (ring_rig R))) _).
  exact (@mte_gen R V Runit _ _ _ _
           (reflexivity v) (rig_mul_one_r (ring_rig R) r)).
Qed.

End Unitors.

(** ** The associator: the inner legs

    For a fixed third (resp. first) factor these are ordinary factorizations
    of a bilinear map, and they use no commutativity — hence a section that
    does not bind it.  Only the OUTER bilinear maps, whose scalar clauses are
    equations between homomorphisms, reach for [rmod_hom_smul]. *)

Section AssociatorLegs.

Context {R : RingObject}.
Context {V W X : RModObject R}.

(* Congruence for the generator former at the two nestings — engineering
   note (c): without the explicit indices the inner generator elaborates
   before the outer tensor is known. *)
Local Notation mgR a b :=
  (@mte_gen R V (TensorMod W X) _ _ _ _ a b).
Local Notation mgL a b :=
  (@mte_gen R (TensorMod V W) X _ _ _ _ a b).

(* For a fixed x, the bilinear map (v, w) ↦ v ⊗ (w ⊗ x). *)
Program Definition assoc_in_bilin (x : carrier (cmon_setoid X)) :
  RBilinear V W (TensorMod V (TensorMod W X)) := {|
  rbl_map := fun v w => mt_gen v (mt_gen w x)
|}.
Next Obligation.
  intros x v v' Hv w w' Hw.
  exact (mgR Hv (mte_gen Hw (reflexivity x))).
Qed.
Next Obligation.
  intros x v v' w; exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros x v w w'.
  refine (mte_trans (mgR (reflexivity v) (mte_add_l w w' x)) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros x r v w.
  exact (rbl_smul_l (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.
Next Obligation.
  intros x r v w.
  refine (mte_trans (mgR (reflexivity v)
                       (rbl_smul_l tensor_gen r w x)) _).
  exact (rbl_smul_r (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.

Definition assoc_in (x : carrier (cmon_setoid X)) :
  TensorMod V W ~{RMod R}~> TensorMod V (TensorMod W X) :=
  tensor_med (assoc_in_bilin x).

(* For a fixed v, the bilinear map (w, x) ↦ (v ⊗ w) ⊗ x. *)
Program Definition mod_assoc_fr_in_bilin (v : carrier (cmon_setoid V)) :
  RBilinear W X (TensorMod (TensorMod V W) X) := {|
  rbl_map := fun w x => mt_gen (mt_gen v w) x
|}.
Next Obligation.
  intros v w w' Hw x x' Hx.
  exact (mgL (mte_gen (reflexivity v) Hw) Hx).
Qed.
Next Obligation.
  intros v w w' x.
  refine (mte_trans (mgL (mte_add_r v w w') (reflexivity x)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros v w x x'; exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros v r w x.
  refine (mte_trans (mgL (rbl_smul_r tensor_gen r v w) (reflexivity x)) _).
  exact (rbl_smul_l (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.
Next Obligation.
  intros v r w x.
  exact (rbl_smul_r (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.

Definition mod_assoc_fr_in (v : carrier (cmon_setoid V)) :
  TensorMod W X ~{RMod R}~> TensorMod (TensorMod V W) X :=
  tensor_med (mod_assoc_fr_in_bilin v).

End AssociatorLegs.

(** ** The associator

    Named [mod_assoc_to] / [mod_assoc_fr] because `assoc_to` is taken by
    Construction/Day.v:1279.  Both round trips reduce to generators through
    [tensor_hom_ext_l] and [tensor_hom_ext_r] and close by [mt_refl]: the
    two maps are mutually inverse BY COMPUTATION, not by an equational
    argument. *)

Section Associator.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).
Context {V W X : RModObject R}.

Local Notation mgR a b :=
  (@mte_gen R V (TensorMod W X) _ _ _ _ a b).
Local Notation mgL a b :=
  (@mte_gen R (TensorMod V W) X _ _ _ _ a b).

Program Definition mod_assoc_to_bilin :
  RBilinear (TensorMod V W) X (TensorMod V (TensorMod W X)) := {|
  rbl_map := fun s x => mval (@assoc_in R V W X x) s
|}.
Next Obligation.
  intros s s' Hs x x' Hx.
  transitivity (mval (@assoc_in R V W X x) s').
  - exact (proper_morphism _ _ _ Hs).
  - refine (tensor_hom_ext (@assoc_in R V W X x)
              (@assoc_in R V W X x') _ s').
    intros v w.
    exact (mgR (reflexivity v) (mte_gen (reflexivity w) Hx)).
Qed.
Next Obligation.
  intros s s' x.
  exact (cmon_map_plus (rm_hom (@assoc_in R V W X x)) s s').
Qed.
Next Obligation.
  intros s x x'.
  refine (tensor_hom_ext (@assoc_in R V W X (cmon_plus X x x'))
            (rmod_hom_add (@assoc_in R V W X x)
                          (@assoc_in R V W X x')) _ s).
  intros v w; simpl.
  refine (mte_trans (mgR (reflexivity v) (mte_add_r w x x')) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros r s x; exact (rm_map_smul (@assoc_in R V W X x) r s).
Qed.
Next Obligation.
  intros r s x.
  refine (tensor_hom_ext (@assoc_in R V W X (rm_smul X r x))
            (rmod_hom_smul Rcomm r (@assoc_in R V W X x)) _ s).
  intros v w; simpl; unfold mval; simpl.
  refine (mte_trans (mgR (reflexivity v)
                       (rbl_smul_r tensor_gen r w x)) _).
  exact (rbl_smul_r (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.

Definition mod_assoc_to :
  TensorMod (TensorMod V W) X ~{RMod R}~> TensorMod V (TensorMod W X) :=
  tensor_med mod_assoc_to_bilin.

Program Definition mod_assoc_fr_bilin :
  RBilinear V (TensorMod W X) (TensorMod (TensorMod V W) X) := {|
  rbl_map := fun v t => mval (@mod_assoc_fr_in R V W X v) t
|}.
Next Obligation.
  intros v v' Hv t t' Ht.
  transitivity (mval (@mod_assoc_fr_in R V W X v) t').
  - exact (proper_morphism _ _ _ Ht).
  - refine (tensor_hom_ext (@mod_assoc_fr_in R V W X v)
              (@mod_assoc_fr_in R V W X v') _ t').
    intros w x.
    exact (mgL (mte_gen Hv (reflexivity w)) (reflexivity x)).
Qed.
Next Obligation.
  intros v v' t.
  refine (tensor_hom_ext (@mod_assoc_fr_in R V W X (cmon_plus V v v'))
            (rmod_hom_add (@mod_assoc_fr_in R V W X v)
                          (@mod_assoc_fr_in R V W X v')) _ t).
  intros w x; simpl.
  refine (mte_trans (mgL (mte_add_l v v' w) (reflexivity x)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros v t t'.
  exact (cmon_map_plus (rm_hom (@mod_assoc_fr_in R V W X v)) t t').
Qed.
Next Obligation.
  intros r v t.
  refine (tensor_hom_ext (@mod_assoc_fr_in R V W X (rm_smul V r v))
            (rmod_hom_smul Rcomm r (@mod_assoc_fr_in R V W X v)) _ t).
  intros w x; simpl; unfold mval; simpl.
  refine (mte_trans (mgL (rbl_smul_l tensor_gen r v w) (reflexivity x)) _).
  exact (rbl_smul_l (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.
Next Obligation.
  intros r v t; exact (rm_map_smul (@mod_assoc_fr_in R V W X v) r t).
Qed.

Definition mod_assoc_fr :
  TensorMod V (TensorMod W X) ~{RMod R}~> TensorMod (TensorMod V W) X :=
  tensor_med mod_assoc_fr_bilin.

Program Definition ModAssoc :
  @Isomorphism (RMod R) (TensorMod (TensorMod V W) X)
                        (TensorMod V (TensorMod W X)) := {|
  to   := mod_assoc_to;
  from := mod_assoc_fr
|}.
Next Obligation.
  refine (tensor_hom_ext_r (mod_assoc_to ∘ mod_assoc_fr) id _).
  intros v w x; exact (mt_refl _).
Qed.
Next Obligation.
  refine (tensor_hom_ext_l (mod_assoc_fr ∘ mod_assoc_to) id _).
  intros v w x; exact (mt_refl _).
Qed.

End Associator.

(** ** The monoidal structure

    Five of the eight fields close by `simpl; apply mt_refl` — both
    associator naturality squares, both `from`-direction unitor squares, and
    the PENTAGON.  The three that carry content are marked below. *)

Section ModMonoidalStructure.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition ModMonoidal : @Monoidal (RMod R) := {|
  I            := Ring_RMod R;
  tensor       := ModTensor;
  unit_left    := fun x => ModUnitLeft Rcomm x;
  unit_right   := fun x => ModUnitRight Rcomm x;
  tensor_assoc := fun x y z => ModAssoc Rcomm
|}.
(* CONTENT 1 of 3: [to_unit_left_natural], one [rm_map_smul]. *)
Next Obligation.
  intros x y g; tens_ext; intros r a; simpl.
  exact (rm_map_smul g r a).
Qed.
Next Obligation.
  intros x y g a; simpl; apply mt_refl.
Qed.
(* CONTENT 2 of 3: [to_unit_right_natural], one [rm_map_smul]. *)
Next Obligation.
  intros x y g; tens_ext; intros a r; simpl.
  exact (rm_map_smul g r a).
Qed.
Next Obligation.
  intros x y g a; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z w v u g h i; tens_ext_l; intros a b c; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z w v u g h i; tens_ext_r; intros a b c; simpl; apply mt_refl.
Qed.
(* CONTENT 3 of 3: [triangle_identity], one [tensor_balanced].  This is the
   one place the two unitors must agree about which factor absorbs a
   scalar, and it is NOT definitional — see [probe_balanced_conversion]. *)
Next Obligation.
  intros x y; tens_ext_l; intros a r b; simpl.
  exact (tensor_balanced r a b).
Qed.
(* THE PENTAGON, definitional once the fourfold generator is exposed. *)
Next Obligation.
  intros x y z w; tens_ext_ll; intros a b c d; simpl; apply mt_refl.
Qed.

End ModMonoidalStructure.

(** ** Braided and symmetric

    Every field here is [mt_refl]: braid naturality, both hexagons and the
    involution are computations on generators.  [Rcomm] enters only through
    the contained monoidal structure — [ModBraid] itself, built above, takes
    no commutativity argument. *)

Section ModBraiding.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition ModBraided : @BraidedMonoidal (RMod R) := {|
  braided_is_monoidal := ModMonoidal Rcomm;
  braid               := ModBraid
|}.
Next Obligation.
  intros x y g z w h; tens_ext; intros a b; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z; tens_ext_l; intros a b c; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z; tens_ext_r; intros a b c; simpl; apply mt_refl.
Qed.

Program Definition ModSymmetric : @SymmetricMonoidal (RMod R) := {|
  symmetric_is_braided := ModBraided
|}.
Next Obligation.
  intros x y; tens_ext; intros a b; simpl; apply mt_refl.
Qed.

End ModBraiding.

(** ** Acceptance tests over ℤ

    ℤ is a commutative ring (Instance/Rng.v:412's [Int_Ring_commutative]), so
    the whole structure is inhabited at a concrete base.  Every example below
    closes by [eq_refl]: these are computations, not equational arguments. *)

Definition Int_Mod_Monoidal : @Monoidal (RMod Int_Ring) :=
  ModMonoidal Int_Ring_commutative.

Definition Int_Mod_Braided : @BraidedMonoidal (RMod Int_Ring) :=
  ModBraided Int_Ring_commutative.

Definition Int_Mod_Symmetric : @SymmetricMonoidal (RMod Int_Ring) :=
  ModSymmetric Int_Ring_commutative.

Definition ZMod : RModObject Int_Ring := Ring_RMod Int_Ring.

Definition zz2 : carrier (cmon_setoid ZMod) := 2%Z.
Definition zz3 : carrier (cmon_setoid ZMod) := 3%Z.
Definition zz5 : carrier (cmon_setoid ZMod) := 5%Z.
Definition zz7 : carrier (cmon_setoid ZMod) := 7%Z.

(* The unit object is ℤ as a module over itself, on the nose. *)
Example mod_unit_is_Ring_RMod :
  @I (RMod Int_Ring) Int_Mod_Monoidal = Ring_RMod Int_Ring := eq_refl.

(* The tensor bifunctor's object action is [TensorMod], on the nose. *)
Example mod_tensor_is_TensorMod :
  fobj[@tensor (RMod Int_Ring) Int_Mod_Monoidal] (ZMod, ZMod)
    = TensorMod ZMod ZMod := eq_refl.

(* The associator computes on a concrete generator. *)
Example mod_assoc_computes :
  mval (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod)
       (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
          (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5)
  = @mt_gen Int_Ring ZMod (TensorMod ZMod ZMod) zz2 (mt_gen zz3 zz5)
  := eq_refl.

(* The left unitor computes: 2 ⊗ 7 ↦ 2 * 7 = 14. *)
Example mod_unit_left_computes :
  mval (to (ModUnitLeft Int_Ring_commutative ZMod))
       (@mt_gen Int_Ring ZMod ZMod zz2 zz7) = 14%Z := eq_refl.

(* The braiding computes. *)
Example mod_braid_computes :
  mval (@ModBraid Int_Ring ZMod ZMod) (@mt_gen Int_Ring ZMod ZMod zz2 zz3)
  = @mt_gen Int_Ring ZMod ZMod zz3 zz2 := eq_refl.

(* The fourfold generator ((2 ⊗ 3) ⊗ 5) ⊗ 7, the pentagon's input. *)
Definition zquad :
  carrier (cmon_setoid
    (TensorMod (TensorMod (TensorMod ZMod ZMod) ZMod) ZMod)) :=
  @mt_gen Int_Ring (TensorMod (TensorMod ZMod ZMod) ZMod) ZMod
    (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
       (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5) zz7.

(* THE PENTAGON, as a computation.  Both routes around it carry the fourfold
   generator to the very same [MTerm]; this is the header's central claim,
   checked rather than asserted. *)
Example mod_pentagon_computes :
  mval (mt_fmap (@id (RMod Int_Ring) ZMod)
          (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod)
        ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
            ZMod (TensorMod ZMod ZMod) ZMod
        ∘ mt_fmap (@mod_assoc_to Int_Ring Int_Ring_commutative
                     ZMod ZMod ZMod) (@id (RMod Int_Ring) ZMod)) zquad
  = mval (@mod_assoc_to Int_Ring Int_Ring_commutative
            ZMod ZMod (TensorMod ZMod ZMod)
        ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
            (TensorMod ZMod ZMod) ZMod ZMod) zquad
  := eq_refl.

(* And the common value is the fully right-nested generator. *)
Example mod_pentagon_value :
  mval (@mod_assoc_to Int_Ring Int_Ring_commutative
          ZMod ZMod (TensorMod ZMod ZMod)
      ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
          (TensorMod ZMod ZMod) ZMod ZMod) zquad
  = @mt_gen Int_Ring ZMod (TensorMod ZMod (TensorMod ZMod ZMod))
      zz2 (@mt_gen Int_Ring ZMod (TensorMod ZMod ZMod)
             zz3 (@mt_gen Int_Ring ZMod ZMod zz5 zz7))
  := eq_refl.

(** ** Probes

    Under this repo's [coqc] a [Fail] that succeeds prints NOTHING, so each
    negative below was stripped of its [Fail], compiled alone, and its
    failure kind read off the WHOLE error message before being recorded here.
    Four kinds occur and they are genuinely distinguishable by the error
    text, not merely by label:

      TYPING       — "has type … while it is expected to have type …",
                     with no further clause
      CONVERSION   — the same, closing with "(cannot unify … and …)"
      RESOLUTION   — "contains unresolved implicit arguments … Cannot infer
                     this placeholder"
      FORMABILITY  — "(universe inconsistency: Cannot enforce … because …)"

    They are kept lexically apart below.  Every negative sits beside an
    APPLIED control that must succeed — never a bare [Check] of an
    unapplied constant, which would elaborate at any levels and discriminate
    nothing — so a rename or a signature change breaks this section loudly
    instead of turning a guard vacuously green. *)

(* Instrument check: the [Fail] mechanism is live and scope-free in this
   file.  If this ever stops failing, every negative below is worthless.
   Named for this file rather than [probe_instrument], which
   Test/ProbePolynomial.v:85 already declares — the collision hazard
   engineering note (f) records. *)
Fail Example mod_monoidal_instrument : (true = false) := eq_refl.

(** *** TYPING negatives

    Three, of two subjects.  The first two are where commutativity is a real
    argument: [ModUnitLeft] and [mod_assoc_to] take [Rcomm] explicitly while
    [gen_r], [gen_l], [ModBraid], [ModTensor], [assoc_in] and
    [mod_assoc_fr_in] do not, so feeding the module where the hypothesis is
    expected is rejected.  That is the signature-level form of the header's
    claim about where commutativity is spent, and it is what makes the claim
    a measurement rather than a reading of the source.  The third is
    engineering note (c), the nested-generator annotation trap. *)

(* Supplying the module where [Rcomm] is expected. *)
Fail Check (@ModUnitLeft Int_Ring ZMod).

(* Control: the same application with [Rcomm] in place. *)
Check (@ModUnitLeft Int_Ring Int_Ring_commutative ZMod).

Fail Check (@mod_assoc_to Int_Ring ZMod ZMod ZMod).

Check (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod).

(* Engineering note (c), pinned: a nested [mt_gen] with its module arguments
   left implicit is rejected — the inner generator elaborates first and a
   bare [MTerm] does not unify with `carrier ?V`.  This is why every nested
   generator in this file is `@`-annotated. *)
Fail Check (mt_gen (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5).

(* Control: the same term with the outer indices supplied. *)
Check (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
         (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5).

(* Controls on the commutativity-FREE side: these are complete applications
   with no [Rcomm] anywhere, at the same ring. *)
Check (@gen_r Int_Ring ZMod ZMod zz3).
Check (@gen_l Int_Ring ZMod ZMod zz3).
Check (@ModBraid Int_Ring ZMod ZMod).
Check (@ModTensor Int_Ring).
Check (@assoc_in Int_Ring ZMod ZMod ZMod zz5).
Check (@mod_assoc_fr_in Int_Ring ZMod ZMod ZMod zz2).

(** *** CONVERSION negatives — the three content-bearing obligations

    Five of [ModMonoidal]'s eight fields close by conversion.  These pin that
    the other three do not: each of the three facts they consume is refuted
    at [eq_refl] and holds only up to `≈`. *)

(* [triangle_identity]'s content, [tensor_balanced].  Even at closed integer
   scalars the two sides are literally different terms — `6 ⊗ 5` against
   `3 ⊗ 10` — so the triangle is not a computation. *)
Fail Example probe_balanced_conversion :
  @mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
    = @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5)
  := eq_refl.

(* Control: the same statement at `≈`, which is [tensor_balanced].  The
   ascription is needed because [TensorMod]'s setoid is a projection rather
   than a registered instance, so `≈` on a bare [MTerm] has nothing to
   resolve against. *)
Example probe_balanced_equiv :
  (@mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
     : carrier (cmon_setoid (TensorMod ZMod ZMod)))
    ≈ @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5).
Proof. exact (@tensor_balanced Int_Ring ZMod ZMod 2%Z zz3 zz5). Qed.

(* Control, sharpening the diagnosis: the two sides ARE distinct terms, the
   left one reducing to `6 ⊗ 5` and the right to `3 ⊗ 10`. *)
Example probe_balanced_lhs :
  @mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
    = @mt_gen Int_Ring ZMod ZMod 6%Z zz5 := eq_refl.

Example probe_balanced_rhs :
  @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5)
    = @mt_gen Int_Ring ZMod ZMod zz3 10%Z := eq_refl.

(* The two [to_unit_*_natural] fields' content, [rm_map_smul]: a module
   homomorphism commutes with the action.  For an arbitrary [g] this is a
   proof field of the record, not a computation. *)
Fail Example probe_map_smul_conversion
  {V W : RModObject Int_Ring} (g : V ~{RMod Int_Ring}~> W)
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid V)) :
  mval g (rm_smul V r a) = rm_smul W r (mval g a) := eq_refl.

(* Control: the same statement at `≈`, which is [rm_map_smul]. *)
Example probe_map_smul_equiv
  {V W : RModObject Int_Ring} (g : V ~{RMod Int_Ring}~> W)
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid V)) :
  mval g (rm_smul V r a) ≈ rm_smul W r (mval g a).
Proof. exact (rm_map_smul g r a). Qed.

(* Control: the SAME shape at a concrete [g], where it does reduce.  This is
   what makes the negative above about arbitrary morphisms rather than about
   the shape of the statement. *)
Example probe_map_smul_concrete
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid ZMod)) :
  mval (@id (RMod Int_Ring) ZMod) (rm_smul ZMod r a)
    = rm_smul ZMod r (mval (@id (RMod Int_Ring) ZMod) a) := eq_refl.

(** *** RESOLUTION negative — [Rcomm] is not found by inference

    Engineering note (e): the structures are [Program Definition]s and not
    [Instance]s, so nothing supplies the commutativity hypothesis
    automatically.  This pins that leaving it to be inferred fails at an
    abstract ring, where no commutativity is in scope.  Its error text names
    an unresolved placeholder and contains neither "cannot unify" nor
    "universe inconsistency", which is what separates it from the two
    groups above and the one below. *)

Section ResolutionProbe.

Context {R : RingObject}.

Fail Definition probe_no_resolution : @Monoidal (RMod R) := ModMonoidal _.

(* Control: with the hypothesis in hand the very same body elaborates. *)
Definition probe_with_hypothesis
  (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
      rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a) :
  @Monoidal (RMod R) := ModMonoidal Rcomm.

(* Control: the commutativity-free half needs nothing at all, at the same
   abstract ring. *)
Definition probe_tensor_free : RMod R ∏ RMod R ⟶ RMod R := ModTensor.

End ResolutionProbe.

(** *** FORMABILITY negatives — the packaging identifies two universes

    The measurement the header records.  Under a declared `rp < ru` — which
    satisfies the bound every component carries while violating the equation
    the assembly carries — [ModMonoidal] and [ModSymmetric] are rejected with
    a genuine universe inconsistency, while ELEVEN applied controls elaborate
    at exactly those levels, and two more show the same two constants
    accepted at ℤ.  Two of the controls are the obvious suspects:
    [@Monoidal (RMod Ru)], the class being assembled, and [Ring_RMod Ru], the
    unit object it is assembled with.  Two more, [ModUnitLeft] and
    [ModAssoc], are commutativity-CONSUMING, so the rejection is not about
    [Rcomm] either.  What is left is the packaging. *)

Section UniverseProbe.

Universes ru rp rq.
Constraint rp < ru.

Context (Ru : RingObject@{ru rp rq}).

(* Controls: the ambient category, the unit object, and the class itself. *)
Check (RMod Ru).
Check (Ring_RMod Ru).
Check (@Monoidal (RMod Ru)).

(* Controls: every commutativity-free component. *)
Check (@ModTensor Ru).
Check (@gen_r Ru).
Check (@gen_l Ru).
Check (@ModBraid Ru).

(* Controls: every commutativity-consuming component. *)
Check (@rmod_hom_smul Ru).
Check (@ModUnitLeft Ru).
Check (@ModUnitRight Ru).
Check (@ModAssoc Ru).

(* The assembly, and the symmetric structure that contains it. *)
Fail Check (@ModMonoidal Ru).

Fail Check (@ModSymmetric Ru).

(* Controls, sharpest form: the very same two constants, applied at ℤ, whose
   three [RingObject] universes may be identified.  So the rejection above is
   about the levels and not about the constants. *)
Check (ModMonoidal Int_Ring_commutative).
Check (ModSymmetric Int_Ring_commutative).

End UniverseProbe.
