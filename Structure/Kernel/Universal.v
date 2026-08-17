Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Kernels as universal elements *)

(* nLab:      https://ncatlab.org/nlab/show/kernel
              https://ncatlab.org/nlab/show/universal+element
              https://ncatlab.org/nlab/show/representable+functor
              https://ncatlab.org/nlab/show/category+with+zero+morphisms
   Wikipedia: https://en.wikipedia.org/wiki/Kernel_(category_theory)

   [Structure/Kernel.v] defines the kernel of f : x ~> y as an equalizer of
   f against the zero morphism, and states its universal property in the
   zero-composite phrasing ([kernel_desc]): any h : d ~> x with f ∘ h ≈ 0
   factors uniquely through the kernel inclusion.  Read that clause with the
   quantifier over d out front and it is no longer a statement about one
   object but about a PRESHEAF: for each d the set

       Kill_f(d)  =  { h : d ~> x  |  f ∘ h ≈ 0 }

   of maps into x that f kills, contravariant in d by precomposition
   (nLab, "kernel": "the kernel of f is the representing object of the
   functor sending d to the set of morphisms h : d → x such that
   f ∘ h = 0").  [kernel_desc] then says exactly that the pair ⟨k, i⟩ --
   the kernel object together with its inclusion, which is an ELEMENT of
   Kill_f(k) because f ∘ i ≈ 0 -- is a universal element of that presheaf
   in the sense of Mac Lane's Definition 2 of §III.1 (CWM 2nd ed., p. 57):
   every element of every Kill_f(d) is (Kill_f u)(i) for a unique
   u : d ~> k.

   This file proves the two readings equivalent, using the class
   [AUniversalElement] of Theory/Universal/Element.v (issue #303) rather
   than a bespoke unique-factorization clause.  "Equivalent" is delivered
   at three different strengths, which are three different claims and are
   kept apart below: the two passages with their round trips (no universe
   restriction), the representability statement Hom(─, k) ≅ Kill_f in
   [C^op, Sets] (no universe restriction), and the bundling of the two
   record types as an isomorphism of SETOIDS in [Sets] (which carries
   one, and which the concrete witnesses therefore do not use).  The
   catalog files the result as maclane:III.1:remark4.  NOTE ON
   ATTRIBUTION: nothing below quotes the wording of that remark, and no
   claim is made here about what Mac Lane wrote at that spot; what is
   cited above is §III.1's Definition 2, which the file does use, and the
   nLab's statement of the kernel's universal property, which is what the
   file proves.

   Where the notion sits, and why the presheaf packaging is the durable one

   Text:  Mac Lane, "Categories for the Working Mathematician", Springer
          1998, §III.1 (pp. 55-59), §VIII.1
   Text:  Riehl, "Category Theory in Context", Dover 2016, §2.4
   Text:  Awodey, "Category Theory", Oxford 2010, §2.9
   Paper: Kan, "Adjoint functors", Trans. Amer. Math. Soc. 87, 1958

   The kernel is the oldest universal construction in algebra and the one
   whose element-free rendering cost the most.  In group theory a kernel
   is a SUBSET -- the preimage of the identity -- and the categorical
   definition has to say the same thing without mentioning elements or
   the identity.  Two moves accomplish it.  The first is to replace "the
   identity of the target" by the zero morphism, which requires the
   ambient category to have one; the second is to replace "the subset of
   things sent to zero" by the universal property of the equalizer.  The
   present file performs a third: it puts the quantifier over the probing
   object back in front, which turns the universal property into the
   assertion that ONE presheaf is representable.

   That third move is not decoration.  A universal property stated as a
   factorization clause is a statement about the chosen object k; stated
   as representability it is a statement about the functor Kill_f, which
   exists whether or not k does.  So the presheaf is defined for every f
   in every category with zero morphisms, and "f has a kernel" becomes
   "Kill_f is representable" -- a property of an object of the presheaf
   category rather than a piece of data attached to f.  This is the form
   in which kernels generalize: the kernel presheaf of a map of sheaves is
   already a sheaf (a kernel is a limit, and limits of sheaves are
   computed presheaf-wise), and in a general topos the subobject it names
   is defined by exactly this representability -- Mac Lane's §VIII.1
   subobject classifier being the same device applied to monomorphisms
   rather than to killed maps.

   And it is the form that survives the loss of the zero morphism.  Mac
   Lane's Rng -- unital rings with unit-preserving homomorphisms -- has
   no zero object and no zero morphisms at all: a ring homomorphism must
   send 1 to 1, so the constant-zero map is a homomorphism only into the
   trivial ring, and there is no morphism whatever from the trivial ring
   to Z.  (Those are theorems, not remarks: [Rng_no_hom_zero_to_Z],
   [Rng_no_zero_morphisms] and [Rng_no_zero_object] in the companion file
   Structure/Kernel/Universal/Examples.v.)  Kernels in the categorical
   sense therefore do not exist in Rng; what does exist, for any parallel
   pair f, g, is the presheaf of maps on which f and g agree, and its
   representing object is the equalizer.  The two presheaves below --
   [KillPresheaf] over a zero-morphism structure and [ForkPresheaf] over
   a bare parallel pair -- are that observation made into definitions,
   and the [kill_fork_iso] between them is the exact statement of how
   much the zero morphism buys. *)

(* WHAT IS DELIVERED

   * [ZeroMorphisms], the pointed-hom structure: a chosen family
     [zmor : x ~> y] absorbing composition on both sides, i.e. a category
     with zero morphisms (nLab), a strictly weaker hypothesis than a zero
     object.  [ZeroMorphisms_of_ZeroObject] derives it from
     [Structure/ZeroObject.v]'s [ZeroObject], and the derivation is
     TRANSPARENT: [zmor] at the derived structure IS [zero_mor] by
     [eq_refl] ([zmor_is_zero_mor]), so [Structure/Kernel.v]'s [IsKernel]
     and this file's [IsKernelOf] are THE SAME TYPE by [eq_refl]
     ([IsKernel_is_IsKernelOf]) and every result below applies to the
     tree's existing kernels with no adapter.

   * DELIVERABLE 1.  [KillPresheaf f : C^op ⟶ Sets], the kill-f presheaf
     d ↦ { h : d ~> x | f ∘ h ≈ 0 } with precomposition as its action and
     a hom-setoid comparing only the underlying morphism; the two
     passages [kernel_aue] and [aue_kernel]; and the equivalence, at
     THREE DIFFERENT STRENGTHS, which are three different claims and are
     labelled as such:

       (1) UNIVERSE-FREE, and the form consumers should use: the two
           passages, with the underlying morphism surviving BOTH
           directions by [eq_refl] ([kernel_aue_morphism],
           [aue_kernel_morphism]) and the mediator surviving both up to
           `≈` ([kernel_round_mediator], [aue_kernel_round_mediator]).
           [kernel_aue_mediator] records the sharper fact that in one
           direction the mediator is the SAME TERM.  Nothing here
           restricts C.

       (2) THE REPRESENTABILITY STATEMENT, also universe-free:
           [kernel_representation], the natural isomorphism
           [Hom ─,k] ≅ [KillPresheaf f] in [C^op, Sets], and
           [kernel_Representable].  This is the issue's own phrasing of
           deliverable 1 and it DOES instantiate at [Ab].

       (3) BUNDLED AS AN ISOMORPHISM OF SETOIDS in [Sets] between
           { i : k ~> x & IsKernelOf i } and
           [AUniversalElement (KillPresheaf f) k]:
           [kernel_universal_element_iso].  Strongest as a statement --
           not a biconditional (which forgets the maps), not merely a
           pair of mutually inverse maps up to `≈` (which forgets
           respectfulness) -- but it CARRIES A UNIVERSE RESTRICTION, and
           the restriction excludes [Ab].  The measured signature and its
           structural cause are set out at the definition; the short form
           is that [obj[Sets]] identifies a setoid's carrier and relation
           universes while [KernelData]'s sit at C's object and proof
           universes respectively, and [Ab] is declared with its objects
           STRICTLY ABOVE its homs.  The restriction enters at THIS step
           and at no earlier one -- neither the presheaf nor the
           representation carries it, measured at [KillPresheaf] -- which
           is what makes (1) and (2) usable exactly where (3) is not.

     In neither direction does the WHOLE RECORD survive a round trip, and
     the file says exactly why: the kill shape (f ∘ h ≈ 0) and the fork
     shape (f ∘ h ≈ 0 ∘ h) are interchanged by [kill_fork] / [fork_kill],
     two [Qed]-opaque proof transformations, and [eq_desc] is
     proof-RELEVANT in its hypothesis, so the composite is not the
     identity term.  Pinned in Test/ProbeKernelUniversal.v.

   * The representability reading the issue asks for:
     [kernel_Representable] (an instance of [Functor/Representable.v]'s
     class at [KillPresheaf f], with [repr_obj] the kernel object by
     [eq_refl]) and [kernel_representation], the natural isomorphism
     [Hom ─,k] ≅ [KillPresheaf f] in [C^op, Sets] whose component at d
     carries u to i ∘ u by [eq_refl] ([kernel_representation_at]).  Both
     are routed through Theory/Universal/Element.v's DIRECT
     (Yoneda-free) constructions, for the reason that file's header
     gives: [Yoneda_Lemma] identifies the object, hom and proof universes
     of its category, and nothing here should inherit that.
     [kernel_iff_representable] is the biconditional "f has a kernel iff
     Kill_f is representable".

   * DELIVERABLE 2, in two grades.  [KillPresheaf] itself already needs
     only [ZeroMorphisms], hence no zero OBJECT.  Below that,
     [ForkPresheaf f g] needs nothing at all -- an arbitrary parallel
     pair in an arbitrary category -- and
     [equalizer_universal_element_iso] is the same theorem for
     equalizers.  [kill_fork_iso] is the natural isomorphism
     [KillPresheaf f] ≅ [ForkPresheaf f zmor] relating the two.

   * A MEASURED DIFFERENCE BETWEEN THE TWO PACKAGINGS, and it is the
     file's one genuinely delicate finding.  On the fork side one whole
     round trip IS [eq_refl] on the whole record
     ([aue_equalizer_round]) -- the two records' field types are
     convertible one for one, so both passages are [:=] with no tactic --
     while the other is not, and the ONLY obstruction is that [sigT] has
     no eta: [aue_equalizer_round_universal] records that the universal
     clause survives up to repacking p as (`1 p; `2 p), and the element
     survives outright.  On the kill side NEITHER round trip is
     [eq_refl], and the extra obstruction is precisely the [zmor ∘ h]
     reshaping.  So the fork packaging is definitionally tighter than the
     kill packaging, which is the opposite of what the naming suggests.

   WHAT IS NOT DELIVERED

   * NO COKERNEL DUAL.  Everything here would dualize to
     [Structure/Coequalizer.v]'s [IsCoequalizer] and a COpresheaf
     d ↦ { h : y ~> d | h ∘ f ≈ 0 }, whose universal element is a
     COUNIVERSAL element in the sense of Theory/Universal/Arrow/Dual.v.
     Theory/Universal/Element.v's header records that it delivers no
     dual of [AUniversalElement], and this file inherits that gap rather
     than filling it.

   * NO CLAIM THAT THE ISO IS A BIJECTION OF TYPES.  It is an
     isomorphism of SETOIDS, and both setoids compare only the
     underlying morphism.  The record-level negatives above are what
     that costs.

   * NO CLAIM THAT THE BUNDLED ISO'S UNIVERSE RESTRICTION IS
     UNAVOIDABLE.  What is measured is that THIS packaging does not
     instantiate at [Ab] or [Rng]; whether some other packaging of the
     same content would is not addressed, and the two universe-free forms
     above make the question moot for consumers.

   * NO SMALLNESS OR SIZE ANALYSIS.  [KillPresheaf] lands in whichever
     [Sets] the ambient universes force; nothing here is stated about
     local smallness (see Theory/Size.v).

   * NO UNIQUENESS-UP-TO-UNIQUE-ISO COROLLARY IN C.  Instantiating
     Theory/Universal/Element.v's [universal_element_unique] at
     [KillPresheaf f] yields the statement over C^op, where the
     isomorphism is an [@Isomorphism (C^op) k k'] rather than an
     isomorphism of C; restating it in C is a transport this file does
     not perform.  [equalizer_unique] (Structure/Equalizer/Fork.v)
     already supplies the bare isomorphism.

   * NO INSTANCE OF [HasKernels] IS BUILT for any category; the [Ab]
     witness in the companion file is a kernel of one morphism at a
     time, which is what [kernel_aue] consumes. *)

(** ** Zero morphisms without a zero object *)

(* A category with zero morphisms (nLab): a chosen morphism between every
   pair of objects, absorbing composition on both sides.  Equivalently a
   category enriched in pointed sets; the enrichment is not what is needed
   below, so the structure is stated elementarily.

   This is weaker than [ZeroObject]: a zero object supplies such a family by
   tunnelling ([zero_mor], and the two absorption laws are [zero_mor_left] /
   [zero_mor_right]), so [ZeroMorphisms_of_ZeroObject] gives one direction.
   BE PRECISE ABOUT THE OTHER: the converse non-implication -- a category
   with zero morphisms and no zero object -- is TRUE but is NOT WITNESSED
   here, and no such witness exists in the tree.  What the companion file
   proves for Rng is the different and weaker statement that a category can
   have NEITHER.  A cheap witness is available for anyone who wants it
   ([Construction/Deloop.v]'s [Deloop M] at a two-element monoid with an
   absorbing element has zero morphisms, and its single object has two
   endomorphisms so it is not a zero object); it is not built here, and
   until it is, "weaker" should be read as "not known here to be
   equivalent" rather than as a proved separation.

   The class is declared HERE rather than in a file of its own because
   nothing else in the tree consumes it yet; promoting it to
   Structure/ZeroMorphisms.v when a second consumer appears would be a
   move, not a redesign. *)
Class ZeroMorphisms (C : Category) := {
  zmor {x y : C} : x ~> y;
  zmor_absorb_l {x y z : C} (g : y ~> z) : g ∘ @zmor x y ≈ @zmor x z;
  zmor_absorb_r {x y z : C} (g : x ~> y) : @zmor y z ∘ g ≈ @zmor x z
}.

(* Given as a term rather than through [Program], so that the [zmor]
   projection reduces: [zmor_is_zero_mor] below is [eq_refl], and that is
   what makes [IsKernel] and [IsKernelOf] the same type. *)
#[export] Instance ZeroMorphisms_of_ZeroObject {C : Category}
  (Z : @ZeroObject C) : ZeroMorphisms C :=
  @Build_ZeroMorphisms C
    (fun x y => @zero_mor C Z x y)
    (fun x y z g => @zero_mor_left C Z x y z g)
    (fun x y z g => @zero_mor_right C Z x y z g).

(** ** The kill-f presheaf *)

Section KernelUniversal.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y : C}.
Context (f : x ~> y).

(* The elements of the presheaf at d: the maps into x that f kills.  The
   witness is DATA (`∃` is [sigT] in this library, Lib/Foundation.v:61), so
   [Kills d] is a type of PAIRS and the setoid below is what forgets the
   second component. *)
Definition Kills (d : C) : Type := { h : d ~> x & f ∘ h ≈ zmor }.

(* Two elements are identified when their underlying morphisms are: the
   proof that f kills them carries no further information.  This is
   Structure/UniversalProperty.v's [exists_setoid] shape, spelled out
   locally rather than imported, since that instance is declared
   [#[local]] there and re-exporting it would push a
   first-projection-only setoid onto every sigma in scope. *)
Program Definition Kills_Setoid (d : C) : Setoid (Kills d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

(* Contravariant by precomposition: if f kills h then it kills h ∘ u, by
   associativity and absorption. *)
Program Definition KillPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Kills d ; is_setoid := Kills_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Kills d => (`1 p ∘ u; _) |}
|}.
Next Obligation.
  rewrite comp_assoc, (`2 p).
  apply zmor_absorb_r.
Qed.

(* THE PRESHEAF'S OWN UNIVERSE BEHAVIOUR, measured rather than assumed,
   because two known hazards live in this neighbourhood and a reader
   arriving from either will want to know which one applies.  [About]
   under [Set Printing Universes] reports

       KillPresheaf@{u u0 u1}
         : ∀ {C : Category@{u u0 u0}}, … → Functor@{u u0 u0 u1 u0 u0}
       (* u u0 u1 |= u0 < u1, u0 <= compose.u{0,1,2},
                     u0 <= Projections.u{0,1}, u0 <= ID.u0 *)

   and three things follow.

   FIRST, THERE IS NO [u <= u0].  The presheaf places no ordering between
   C's OBJECT universe u and its hom universe u0, and neither does
   [kernel_representation] below (same binder, same absence).  Its
   codomain is [Sets@{u0 u1}] -- carrier universe EQUAL to C's hom/proof
   universe u0, object universe u1 strictly above.  This is exactly why
   the universe-free forms and the representability statement instantiate
   at [Ab] while [kernel_universal_element_iso] does not: the ordering
   constraint is not present here, and enters only at that one step (the
   diagnosis is spelled out at its definition).

   SECOND, THE CONCRETE-OBJECT [Set] PIN OF Theory/Universal/Element.v
   DOES NOT FIRE HERE, and this is worth recording as a negative result
   rather than left for the next reader to re-derive.  That file's header
   warns that a [Sets]-morphism out of a CONCRETE object whose
   [proper_morphism] is left to instance resolution pins the carrier
   universe of [Sets] to [Set].  [fmap[KillPresheaf f] u] is such a
   morphism with [proper_morphism] discharged by the obligation tactic --
   but its source is [fobj] at a VARIABLE d, not a concrete object, which
   is precisely the condition that donor note identifies.  Measured: no
   [Set] appears anywhere in the constraints of [KillPresheaf], [Kills],
   [Kills_Setoid], [ForkPresheaf], or that [fmap], and the morphism is
   fully polymorphic.  Nothing had to be done to avoid the pin.

   THIRD, AND THE ONE NOBODY WOULD REDISCOVER WITHOUT LOOKING: the
   binder is [Category@{u u0 u0}], so the presheaf IDENTIFIES C's hom and
   proof universes.  It costs nothing today -- every category in this
   library satisfies h <= p, and [Ab] and [Rng] are already declared with
   h = p, so no in-tree consumer can feel it -- but it is a genuine
   narrowing and it is stated here so that a future category with h
   strictly below p is not debugged from scratch. *)

(* The action, by conversion: this is what makes the universal-element
   clause below literally the descent clause of [kernel_desc]. *)
Lemma kill_fmap (d d' : C) (u : d' ~{C}~> d) (p : Kills d) :
  `1 (fmap[KillPresheaf] u p) = `1 p ∘ u.
Proof. reflexivity. Qed.

(** ** The two shapes of the kernel equation *)

(* [IsEqualizer]'s fork equation compares f ∘ h with (zmor ∘ h); the kill
   presheaf compares it with zmor.  The two are interchanged by absorption,
   and these two lemmas are the entire difference between the kernel
   packaging and the fork packaging of the next section.  They are [Qed],
   hence opaque, so their composite is not the identity term -- and that
   is why the record-level round trips below are not [eq_refl].  Making
   them [Defined] would not repair that: the composite would still be a
   [rewrite]-built term rather than the original proof, so the round trip
   would remain a genuine equation up to `≈` and nothing beyond
   readability would change. *)
Lemma kill_fork {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor) :
  f ∘ h ≈ zmor ∘ h.
Proof. rewrite Hh; symmetry; apply zmor_absorb_r. Qed.

Lemma fork_kill {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor ∘ h) :
  f ∘ h ≈ zmor.
Proof. rewrite Hh; apply zmor_absorb_r. Qed.

(* [Structure/Kernel.v]'s [IsKernel] restated over [ZeroMorphisms].  When
   the structure comes from a zero object the two are THE SAME TYPE; see
   [IsKernel_is_IsKernelOf] below. *)
Definition IsKernelOf {k : C} (i : k ~> x) : Type := IsEqualizer f zmor k i.

(** ** The two passages *)

(* A kernel is a universal element of the kill-f presheaf.  The element is
   the inclusion, carrying the proof that f kills it; the universal clause
   IS [eq_desc], with the hypothesis reshaped.

   Both passages are [:=] with no tactic: the fields' types are convertible
   one for one, since [k ~{C^op}~> d] IS [d ~{C}~> k] (Construction/
   Opposite.v takes [homset] on the nose) and the presheaf's `≈` unfolds to
   an equation between underlying morphisms.  What is NOT convertible is
   the pair of PROOFS, which is why the round trips below are stated up to
   `≈`. *)
Definition kernel_aue {k : C} {i : k ~> x} (K : IsKernelOf i)
  : AUniversalElement KillPresheaf k :=
  @Build_AUniversalElement (C^op) KillPresheaf k
    (existT _ i (fork_kill (fork_eq K)))
    (fun d p => eq_desc K (`1 p) (kill_fork (`2 p))).

Definition aue_kernel {k : C} (U : AUniversalElement KillPresheaf k)
  : IsKernelOf (`1 (@aue_elem (C^op) KillPresheaf k U)) :=
  {| fork_eq := kill_fork (`2 (@aue_elem (C^op) KillPresheaf k U))
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) KillPresheaf k U z (existT _ h (fork_kill Hh)) |}.

(* The underlying morphism survives both passages on the nose. *)
Corollary kernel_aue_morphism {k : C} {i : k ~> x} (K : IsKernelOf i) :
  `1 (@aue_elem (C^op) KillPresheaf k (kernel_aue K)) = i.
Proof. reflexivity. Qed.

Corollary aue_kernel_morphism {k : C} (U : AUniversalElement KillPresheaf k) :
  `1 (@aue_elem (C^op) KillPresheaf k
        (kernel_aue (aue_kernel U)))
    = `1 (@aue_elem (C^op) KillPresheaf k U).
Proof. reflexivity. Qed.

(* ... and so does the mediator: the unique factorization the universal
   element produces IS the one [eq_desc] produces, as a term. *)
Corollary kernel_aue_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (h : d ~> x) (Hh : f ∘ h ≈ zmor) :
  unique_obj (@aue_universal (C^op) KillPresheaf k (kernel_aue K) d (h; Hh))
    = unique_obj (eq_desc K h (kill_fork Hh)).
Proof. reflexivity. Qed.

(** ** The equivalence, universe-free: the two round trips *)

(* THE FORM CONSUMERS SHOULD USE.  These say everything the setoid
   isomorphism below says -- the morphism survives both passages
   ([kernel_aue_morphism] and [aue_kernel_morphism] above, by [eq_refl]) and
   the mediator survives both passages up to `≈` -- WITHOUT packaging the
   two record types as objects of [Sets], which is where the universe
   restriction documented at [kernel_universal_element_iso] comes from.
   Nothing in this pair restricts C, and the [Ab] instantiation in
   Structure/Kernel/Universal/Examples.v uses exactly these. *)

Lemma kernel_round_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  {z : C} (h : z ~> x) (Hh : f ∘ h ≈ zmor ∘ h) :
  unique_obj (eq_desc (aue_kernel (kernel_aue K)) h Hh)
    ≈ unique_obj (eq_desc K h Hh).
Proof.
  apply (uniqueness (eq_desc (aue_kernel (kernel_aue K)) h Hh)).
  exact (unique_property (eq_desc K h Hh)).
Qed.

Lemma aue_kernel_round_mediator {k : C} (U : AUniversalElement KillPresheaf k)
  (d : C) (p : Kills d) :
  unique_obj (@aue_universal (C^op) KillPresheaf k
                (kernel_aue (aue_kernel U)) d p)
    ≈ unique_obj (@aue_universal (C^op) KillPresheaf k U d p).
Proof.
  apply (uniqueness (@aue_universal (C^op) KillPresheaf k
                       (kernel_aue (aue_kernel U)) d p)).
  exact (unique_property (@aue_universal (C^op) KillPresheaf k U d p)).
Qed.

(** ** The equivalence, as an isomorphism of setoids *)

Definition KernelData (k : C) : Type := { i : k ~> x & IsKernelOf i }.

Program Definition KernelData_Setoid (k : C) : Setoid (KernelData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition KernelSetoid (k : C) : SetoidObject :=
  {| carrier := KernelData k ; is_setoid := KernelData_Setoid k |}.

Definition AUEKernelSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement KillPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) KillPresheaf k |}.

(* DELIVERABLE 1, BUNDLED.  An isomorphism in [Sets], i.e. of SETOIDS.  Both
   respectfulness obligations and both round-trip laws are the identity on
   the underlying morphism, so all four are discharged by the file's
   obligation tactic; [kernel_aue_morphism] and [aue_kernel_morphism]
   above record what they say.

   READ THE UNIVERSE SIGNATURE BEFORE REACHING FOR THIS.  Measured:

       kernel_universal_element_iso@{u u0 u1}
         : ∀ {C : Category@{u u0 u0}} …,  with  u <= u0

   -- the object universe of C must sit AT OR BELOW its hom universe, and
   the hom and proof universes must coincide.  That is a restriction on
   this packaging, and its cause is structural rather than incidental:
   [obj[Sets@{o so}]] is [SetoidObject@{o o}] (Instance/Sets.v:194), which
   IDENTIFIES a setoid's carrier universe with its relation universe, while
   [KernelData k]'s carrier sits at C's OBJECT universe (through [eq_desc]'s
   quantifier over the probing object) and its relation at C's PROOF
   universe.  Equating them forces o(C) <= p(C).

   THE CONSTRAINT ENTERS HERE AND NOWHERE EARLIER, which is the part
   worth knowing.  Neither [KillPresheaf] nor [kernel_representation]
   carries any [u <= u0] (measured; see the note at [KillPresheaf]), and
   the presheaf's codomain [Sets@{u0 u1}] already has its carrier universe
   fixed at C's HOM universe u0.  What this definition does is force
   [KernelSetoid], whose carrier sits at C's OBJECT universe, into that
   same [Sets] -- and the two can only be reconciled by u <= u0.  So the
   wall is not a property of the kernel/universal-element correspondence;
   it is the price of bundling the two record types as objects of ONE
   [Sets], and it is why the universe-free forms above are the ones the
   concrete witnesses use.

   Concrete categories generally do not satisfy it.  [Ab@{u u0} : Category@{u u0 u0}]
   is declared with [u0 < u] -- objects strictly above homs -- so this
   isomorphism does NOT instantiate at [Ab], and neither does its equalizer
   twin at [Rng]; both negatives are pinned in Test/ProbeKernelUniversal.v
   with a positive control at a category whose universes coincide.  Use
   [kernel_aue] / [aue_kernel] with [kernel_round_mediator] /
   [aue_kernel_round_mediator] instead, or [kernel_representation], none of
   which carry the restriction.  NOTE what is and is not shown: that this
   packaging does not reach [Ab] is measured; that no packaging could is
   NOT claimed. *)
Program Definition kernel_universal_element_iso (k : C)
  : @Isomorphism Sets (KernelSetoid k) (AUEKernelSetoid k) := {|
  to   := {| morphism := fun p : KernelData k => kernel_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement KillPresheaf k =>
               (`1 (@aue_elem (C^op) KillPresheaf k U); aue_kernel U) |}
|}.

(** ** Representability *)

(* The bundled form, and then [Functor/Representable.v]'s class.  Both are
   routed through Theory/Universal/Element.v's direct constructions rather
   than through [universal_element_representation], which inherits
   [Yoneda_Lemma]'s identification of the object, hom and proof universes
   (that file's header, measured there). *)
Definition kernel_UniversalElement {k : C} {i : k ~> x} (K : IsKernelOf i)
  : UniversalElement KillPresheaf :=
  UniversalElement_of_AUniversalElement (kernel_aue K).

Definition kernel_Representable {k : C} {i : k ~> x} (K : IsKernelOf i)
  : Representable KillPresheaf :=
  Representable_of_UniversalElement (kernel_UniversalElement K).

Corollary kernel_repr_obj {k : C} {i : k ~> x} (K : IsKernelOf i) :
  @repr_obj (C^op) KillPresheaf (kernel_Representable K) = k.
Proof. reflexivity. Qed.

(* The natural isomorphism itself: Hom(─, k) ≅ Kill_f in [C^op, Sets].
   [@Curried_Hom (C^op) k] IS [Hom ─,k], the presheaf Hom(─, k)
   (Functor/Hom.v:146 defines [Curried_CoHom C] as [Curried_Hom C^op]). *)
Definition kernel_representation {k : C} {i : k ~> x} (K : IsKernelOf i)
  : @Curried_Hom (C^op) k ≅[[C^op, Sets]] KillPresheaf :=
  ue_representation KillPresheaf k (kernel_aue K).

(* Its component at d carries u : d ~> k to i ∘ u, on the nose -- the
   comparison map of the kernel's universal property. *)
Corollary kernel_representation_at {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (u : d ~{C}~> k) :
  `1 (transform (to (kernel_representation K)) d u) = i ∘ u.
Proof. reflexivity. Qed.

(* "f has a kernel" iff "the kill-f presheaf is representable".  The
   backward leg reads the universal element off the representation by
   Mac Lane's Φ_r(id r) computation ([AUniversalElement_of_repr]) and then
   applies [aue_kernel]. *)
Definition kernel_of_representable (R : Representable KillPresheaf)
  : { k : C & { i : k ~> x & IsKernelOf i } } :=
  ( @repr_obj (C^op) KillPresheaf R
  ; ( `1 (@aue_elem (C^op) KillPresheaf (@repr_obj (C^op) KillPresheaf R)
            (AUniversalElement_of_repr KillPresheaf
               (@repr_obj (C^op) KillPresheaf R)
               (@represented (C^op) KillPresheaf R)))
    ; aue_kernel (AUniversalElement_of_repr KillPresheaf
                    (@repr_obj (C^op) KillPresheaf R)
                    (@represented (C^op) KillPresheaf R)) )).

Definition kernel_iff_representable
  : { k : C & { i : k ~> x & IsKernelOf i } } ↔ Representable KillPresheaf.
Proof.
  split.
  - intros [k [i K]]; exact (kernel_Representable K).
  - exact kernel_of_representable.
Defined.

End KernelUniversal.

Arguments Kills {C ZM x y} f d.
Arguments KillPresheaf {C ZM x y} f.
Arguments IsKernelOf {C ZM x y} f {k} i.

(** ** The zero-object case: [Structure/Kernel.v]'s kernels, unchanged *)

Section KernelUniversalZeroObject.

Context {C : Category}.
Context {Z : @ZeroObject C}.
Context {x y : C}.
Context (f : x ~> y).

(* The derived zero-morphism family IS the tunnelled zero morphism, by
   conversion -- the projection reduces because
   [ZeroMorphisms_of_ZeroObject] is a term, not a [Program] instance with
   opaque obligation fields. *)
Corollary zmor_is_zero_mor :
  @zmor C (ZeroMorphisms_of_ZeroObject Z) x y = @zero_mor C Z x y.
Proof. reflexivity. Qed.

(* ... hence the two kernel predicates are THE SAME TYPE, not merely
   equivalent ones.  Everything in the previous section therefore applies
   to [Structure/Kernel.v]'s kernels with no adapter; the two definitions
   below record that by taking an [IsKernel] where an [IsKernelOf] is
   expected. *)
Corollary IsKernel_is_IsKernelOf {k : C} (i : k ~> x) :
  @IsKernel C Z x y k f i = @IsKernelOf C (ZeroMorphisms_of_ZeroObject Z) x y f k i.
Proof. reflexivity. Qed.

Definition kernel_universal_element {k : C} {i : k ~> x} (K : IsKernel f i)
  : AUniversalElement (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f) k
  := kernel_aue f K.

Definition kernel_representable {k : C} {i : k ~> x} (K : IsKernel f i)
  : Representable (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f)
  := kernel_Representable f K.

End KernelUniversalZeroObject.

(** ** The zero-free packaging: an arbitrary parallel pair *)

(* Deliverable 2 at full strength.  Nothing in this section mentions a zero
   object, a zero morphism or any structure on C: [ForkPresheaf f g] is
   defined for any parallel pair, and its universal elements are exactly
   the equalizers of that pair.  This is the packaging that reaches Rng,
   where no zero morphism exists at all
   ([Rng_no_zero_morphisms], Structure/Kernel/Universal/Examples.v). *)

Section EqualizerUniversal.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

Definition Forks (d : C) : Type := { h : d ~> x & f ∘ h ≈ g ∘ h }.

Program Definition Forks_Setoid (d : C) : Setoid (Forks d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Program Definition ForkPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Forks d ; is_setoid := Forks_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Forks d => (`1 p ∘ u; _) |}
|}.
Next Obligation. rewrite !comp_assoc; now rewrite (`2 p). Qed.

(* Here the sigma's property IS the fork equation and the universal clause
   IS [eq_desc], with NO reshaping: both passages are [:=] and the field
   types are convertible one for one. *)
Definition equalizer_aue {k : C} {i : k ~> x} (E : IsEqualizer f g k i)
  : AUniversalElement ForkPresheaf k :=
  @Build_AUniversalElement (C^op) ForkPresheaf k
    (existT _ i (fork_eq E))
    (fun d p => eq_desc E (`1 p) (`2 p)).

Definition aue_equalizer {k : C} (U : AUniversalElement ForkPresheaf k)
  : IsEqualizer f g k (`1 (@aue_elem (C^op) ForkPresheaf k U)) :=
  {| fork_eq := `2 (@aue_elem (C^op) ForkPresheaf k U)
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) ForkPresheaf k U z (existT _ h Hh) |}.

(* ... and so ONE round trip is [eq_refl] ON THE WHOLE RECORD, which the
   kernel packaging cannot manage in either direction.  [IsEqualizer] is
   a record with primitive projections, so record eta applies; the
   [eq_desc] field closes by function eta. *)
Corollary aue_equalizer_round {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  aue_equalizer (equalizer_aue E) = E.
Proof. reflexivity. Qed.

(* The other round trip is NOT [eq_refl], and the ONLY obstruction is that
   [sigT] has no eta: the universal clause survives up to repacking the
   argument as (`1 p; `2 p), which this corollary states.  Both of the
   ELEMENT's projections survive too, though the packaged pair does not --
   [aue_equalizer_round_elem] states the first-projection equality, and the
   whole-element form is one of the pinned negatives, for exactly the same
   want of eta.  The negative is pinned in
   Test/ProbeKernelUniversal.v. *)
Corollary aue_equalizer_round_universal {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  @aue_universal (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U))
    = fun d p => @aue_universal (C^op) ForkPresheaf k U d (`1 p; `2 p).
Proof. reflexivity. Qed.

Corollary aue_equalizer_round_elem {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  `1 (@aue_elem (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U)))
    = `1 (@aue_elem (C^op) ForkPresheaf k U).
Proof. reflexivity. Qed.

(* The mediator survives that round trip too -- and here at LEIBNIZ
   equality, not merely up to `≈`, which is the sharper reading and the
   one the strict form was tried at first.  The kill-side analogue
   [aue_kernel_round_mediator] is only `≈`, and the gap between the two is
   exactly the [kill_fork] / [fork_kill] reshaping. *)
Lemma aue_equalizer_round_mediator {k : C}
  (U : AUniversalElement ForkPresheaf k) (d : C) (p : Forks d) :
  unique_obj (@aue_universal (C^op) ForkPresheaf k
                (equalizer_aue (aue_equalizer U)) d p)
    = unique_obj (@aue_universal (C^op) ForkPresheaf k U d p).
Proof.
  (* [destruct p] and not [reflexivity]: the two sides differ ONLY by the
     repacking (`1 p; `2 p), which is [sigT]'s missing eta -- and which the
     [destruct] supplies. *)
  destruct p; reflexivity.
Qed.

Definition EqualizerData (k : C) : Type := { i : k ~> x & IsEqualizer f g k i }.

Program Definition EqualizerData_Setoid (k : C) : Setoid (EqualizerData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition EqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := EqualizerData k ; is_setoid := EqualizerData_Setoid k |}.

Definition AUEEqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement ForkPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) ForkPresheaf k |}.

Program Definition equalizer_universal_element_iso (k : C)
  : @Isomorphism Sets (EqualizerSetoid k) (AUEEqualizerSetoid k) := {|
  to   := {| morphism := fun p : EqualizerData k => equalizer_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement ForkPresheaf k =>
               (`1 (@aue_elem (C^op) ForkPresheaf k U); aue_equalizer U) |}
|}.

(* The equalizer's representability, for symmetry with the kernel case. *)
Definition equalizer_Representable {k : C} {i : k ~> x}
  (E : IsEqualizer f g k i) : Representable ForkPresheaf :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement (equalizer_aue E)).

Corollary equalizer_repr_obj {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  @repr_obj (C^op) ForkPresheaf (equalizer_Representable E) = k.
Proof. reflexivity. Qed.

End EqualizerUniversal.

Arguments Forks {C x y} f g d.
Arguments ForkPresheaf {C x y} f g.

(** ** How much the zero morphism buys *)

(* The two presheaves are naturally isomorphic when a zero-morphism family
   is available: both components are the identity on the underlying
   morphism, and the only content is [kill_fork] / [fork_kill].  This is
   the exact statement of the relationship -- the kill shape is not more
   general, and not less; it is the fork shape at g := zmor, transported
   across a proof reshaping that costs the record-level round trips. *)

Program Definition kill_fork_iso {C : Category} {ZM : ZeroMorphisms C}
  {x y : C} (f : x ~> y)
  : KillPresheaf f ≅[[C^op, Sets]] ForkPresheaf f zmor := {|
  to   := {| transform := fun d =>
               {| morphism := fun p : Kills f d => (`1 p; kill_fork f (`2 p)) |} |};
  from := {| transform := fun d =>
               {| morphism := fun p : Forks f zmor d => (`1 p; fork_kill f (`2 p)) |} |}
|}.
