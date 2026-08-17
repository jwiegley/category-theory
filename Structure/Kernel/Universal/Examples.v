Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Kernel.Universal.
(* Last, matching Theory/Algebra/Rig.v's own placement of this import:
   after Category.Lib and after the [Sets]/[CMon] layer. *)
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * Witnesses for kernels as universal elements *)

(* Companion to Structure/Kernel/Universal.v.  Two witnesses, one positive
   and one negative, and they are the two halves of the same point.

   POSITIVE.  [Instance/Ab.v] already builds the kernel of a homomorphism
   of abelian groups as a SUB-SETOID -- [AbKernel f], with its inclusion
   [ab_kernel_incl f] -- and uses it as the probe object for the monic
   half of Mac Lane's §I.7 proposition.  What it never states is that this
   object IS a kernel in the categorical sense, i.e. that it satisfies
   [Structure/Kernel.v]'s [IsKernel].  [ab_kernel_IsKernel] supplies that,
   and with it the whole apparatus of the companion file lands on a
   concrete algebraic category: the kill-f presheaf of a homomorphism of
   abelian groups is representable, and its representing object is the
   subgroup of elements killed by f.

   (This corrects the issue's own "Current state", which says that none of
   the remark's concrete algebraic categories exists in tree to
   instantiate the result.  All four do -- Instance/Ab.v, Instance/Grp.v,
   Instance/Rng.v, Instance/Mod.v -- and Ab and RMod already carry
   concrete kernel OBJECTS.  What was genuinely missing is the universal
   property of those objects, which is supplied here.)

   The witness is proved non-degenerate rather than asserted to be so.
   [Ab_Z2] is Z/2 on [bool] under exclusive-or, [ab_parity] the parity
   homomorphism Z ⟶ Z/2, and its kernel is the even integers: a PROPER,
   NONTRIVIAL subgroup -- [ab_parity_kernel_has_two] exhibits two distinct
   elements of it and [ab_parity_kernel_proper] shows 1 is not one of
   them.  So neither the presheaf nor its representing object is a
   singleton, and the universal-element clause is not vacuously satisfied.
   The mediator computes: [ab_parity_med_computes] evaluates the unique
   factorization of the doubling map at 3 and gets 6, by [eq_refl].

   NEGATIVE.  [Rng_no_zero_morphisms] proves that Mac Lane's Rng -- unital
   rings, unit-preserving homomorphisms -- has NO zero-morphism family
   at all, hence no zero object, hence no kernels in the sense of
   Structure/Kernel.v.  The argument needs nothing about zero morphisms
   specifically: the terminal ring is the zero ring, in which 1 ≈ 0, and a
   homomorphism out of it into Z would carry that equation to 1 = 0 in Z.
   So the hom-set Rng(0-ring, Z) is EMPTY, and in particular contains no
   distinguished morphism.

   That is what makes the companion file's [ForkPresheaf] a necessity
   rather than a generalization for its own sake: over Rng the kill-f
   presheaf cannot even be written down, while the fork presheaf of a
   parallel pair can, and [equalizer_universal_element_iso] applies to it
   unchanged.  [Rng_fork_presheaf] records that the presheaf is formable
   at Rng, which is the whole content of the "survives without a zero
   object" clause.

   A UNIVERSE NOTE, since it dictates the shape of everything below.
   [Ab_Zero@{u}] carries ONE universe parameter where [Ab@{u u0}] carries
   two: it pins the second to [Set].  Inside a [Section], a
   [Context {A B : AbObject}] fixes that second universe rigidly before
   [Ab_Zero] is ever mentioned, and the later mention is then rejected
   ("Cannot enforce Set = ...", measured).  Every definition below is
   therefore stated at TOP LEVEL with its own [{A B : AbObject} (f)]
   binders, so that the objects' universes and [Ab_Zero]'s are unified in
   one elaboration.  This is a restriction inherited from Instance/Ab.v,
   not one introduced here, and nothing below shows it unavoidable. *)

(* WHAT IS DELIVERED

   * [ab_kernel_IsKernel] : [IsKernel f (ab_kernel_incl f)] for every
     homomorphism f of abelian groups -- new; Instance/Ab.v builds the
     object and the inclusion but proves no universal property of them.

   * [ab_kernel_aue], [ab_kernel_Representable], [ab_kernel_representation]:
     the companion file's constructions at [Ab], with the representing
     object and the universal element read back by [eq_refl].

   * [Ab_Z2], [ab_parity], and the non-degeneracy facts listed above.

   * [Rng_no_hom_zero_to_Z], [Rng_no_zero_morphisms], [Rng_no_zero_object],
     [Rng_fork_presheaf], [Rng_equalizer_aue] and [Rng_aue_equalizer].

   WHAT IS NOT DELIVERED

   * NO [HasKernels Ab] INSTANCE.  [ab_kernel_IsKernel] gives the kernel
     of each morphism separately, which is what [kernel_aue] consumes;
     bundling them into the class would add nothing to this file's point.

   * NO CLAIM ABOUT Grp, Rng or RMod BEYOND THE ABOVE.  Instance/Grp.v
     and Instance/Mod.v carry kernel objects too and the same proof shape
     would work there; it is not run here.

   * NO EQUALIZER WITNESS IN Rng.  [Rng_fork_presheaf] shows the presheaf
     is formable; whether Rng has equalizers is not addressed, and no
     universal element of that presheaf is exhibited.

   * NO CLAIM THAT [Ab_Z2] IS NEW.  Z/2 exists in tree several times over
     (Instance/Grp.v's [Z2], Construction/Deloop.v's [Bool_Xor_Grp]); none
     of them is an [AbObject], and converting would cost more than the
     six-line record below. *)

(** ** Ab: [AbKernel] is a kernel *)

(* The zero morphism of [Ab] evaluates to the zero element, by conversion:
   [Ab_Zero]'s coincidence isomorphism is [iso_id] (the chosen initial and
   terminal objects are literally the same term), so the tunnel through
   the zero object collapses with no rewriting. *)
Lemma ab_zero_mor_apply {X Y : AbObject} (a : carrier (cmon_setoid X)) :
  cmon_map (@zero_mor Ab Ab_Zero X Y) a = cmon_zero Y.
Proof. reflexivity. Qed.

(* The descent map: a homomorphism killed by f lands in the kernel, and
   the corestriction is a homomorphism because the kernel's zero and
   addition are those of A read on first projections.

   The hypothesis is stated ELEMENTWISE rather than as
   [f ∘ h ≈ zero_mor], for the universe reason in the header;
   [ab_kernel_IsKernel] feeds it from the [IsKernel] fork hypothesis,
   where the zero object is inferred once. *)
Program Definition ab_kernel_med {A B : AbObject} (f : A ~{Ab}~> B)
  {Z0 : AbObject} (h : Z0 ~{Ab}~> A)
  (Hh : ∀ a : carrier (cmon_setoid Z0), cmon_map f (cmon_map h a) ≈ cmon_zero B)
  : Z0 ~{Ab}~> AbKernel f :=
  {| cmon_map := {| morphism := fun a => (cmon_map h a; Hh a) |} |}.
Next Obligation. proper; simpl; now rewrite X. Qed.
Next Obligation. simpl; apply (cmon_map_zero h). Qed.
Next Obligation. simpl; apply (cmon_map_plus h). Qed.

(* [AbKernel f] with [ab_kernel_incl f] satisfies Structure/Kernel.v's
   [IsKernel].  The fork equation is the kernel elements' own defining
   property (the second projection); descent is [ab_kernel_med]; and
   uniqueness holds because the kernel's setoid compares first
   projections, which is exactly what the inclusion returns. *)
Definition ab_kernel_IsKernel {A B : AbObject} (f : A ~{Ab}~> B)
  : IsKernel f (ab_kernel_incl f).
Proof.
  unshelve econstructor.
  - (* f ∘ i ≈ zero_mor ∘ i, pointwise on kernel elements *)
    intro p; simpl.
    exact (`2 p).
  - (* descent *)
    intros Z0 h Hh.
    unshelve econstructor.
    + exact (ab_kernel_med f h (fun a => Hh a)).
    + intro a; reflexivity.
    + intros v Hv a; simpl.
      symmetry; exact (Hv a).
Defined.

(** ** ... hence a universal element of the kill-f presheaf *)

Definition ab_kernel_aue {A B : AbObject} (f : A ~{Ab}~> B)
  : AUniversalElement
      (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
      (AbKernel f) :=
  kernel_universal_element f (ab_kernel_IsKernel f).

Definition ab_kernel_Representable {A B : AbObject} (f : A ~{Ab}~> B)
  : Representable (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
  := kernel_representable f (ab_kernel_IsKernel f).

Definition ab_kernel_representation {A B : AbObject} (f : A ~{Ab}~> B)
  : @Curried_Hom (Ab^op) (AbKernel f)
      ≅[[Ab^op, Sets]]
    (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
  := kernel_representation f (ab_kernel_IsKernel f).

(* The representing object is the kernel group, on the nose. *)
Corollary ab_kernel_repr_obj {A B : AbObject} (f : A ~{Ab}~> B) :
  @repr_obj (Ab^op)
    (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
    (ab_kernel_Representable f)
  = AbKernel f.
Proof. reflexivity. Qed.

(* ... and the universal element is the inclusion, on the nose. *)
Corollary ab_kernel_aue_elem {A B : AbObject} (f : A ~{Ab}~> B) :
  `1 (@aue_elem (Ab^op)
        (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
        (AbKernel f) (ab_kernel_aue f))
  = ab_kernel_incl f.
Proof. reflexivity. Qed.

(* The equivalence itself, in the universe-free form: the passage back, and
   the two round trips.  The bundled [kernel_universal_element_iso] is NOT
   available here -- [Ab] puts its objects strictly above its homs, which
   that packaging forbids (documented at its definition, pinned in
   Test/ProbeKernelUniversal.v) -- so these three, together with
   [ab_kernel_representation] above, are what "equivalent" means at [Ab]. *)
Definition ab_aue_kernel {A B : AbObject} (f : A ~{Ab}~> B)
  (U : AUniversalElement
         (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
         (AbKernel f))
  : @IsKernelOf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f (AbKernel f)
      (`1 (@aue_elem (Ab^op)
             (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
             (AbKernel f) U))
  := aue_kernel f U.

(* The round trip on the kernel side, at [Ab].  Stated by instantiation
   rather than by re-typing the conclusion: writing the [∃!] out by hand
   leaves the hom-setoid instance of [z ~{Ab}~> AbKernel f] unresolved
   ("expected to have type ∃! y, ?P y", measured), while the general
   lemma's own statement carries it. *)
Definition ab_kernel_round {A B : AbObject} (f : A ~{Ab}~> B)
  {z : AbObject} (h : z ~{Ab}~> A)
  := kernel_round_mediator f (ab_kernel_IsKernel f) h.

(* ... and on the universal-element side. *)
Definition ab_aue_kernel_round {A B : AbObject} (f : A ~{Ab}~> B)
  (U : AUniversalElement
         (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
         (AbKernel f))
  := aue_kernel_round_mediator f U.

(** ** A non-degenerate instance: the even integers inside Z *)

(* Z/2 as an abelian group on [bool] under exclusive-or.  Negation is the
   identity, since every element is its own inverse. *)
Definition Ab_Z2 : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := {| cmon_setoid := {| carrier := bool
                                  ; is_setoid := eq_Setoid bool |}
                ; cmon_zero := false
                ; cmon_plus := xorb |};
    ab_neg := fun b => b
  |}.
  - (* cmon_plus_respects *) repeat intro; simpl in *; subst; reflexivity.
  - (* cmon_plus_assoc *)   intros a b c; now destruct a, b, c.
  - (* cmon_plus_comm *)    intros a b; now destruct a, b.
  - (* cmon_plus_zero_l *)  intros a; now destruct a.
  - (* ab_neg_respects *)   repeat intro; simpl in *; subst; reflexivity.
  - (* ab_neg_left *)       intros a; now destruct a.
Defined.

(* Z as an abelian group, through the ring layer of Instance/Rng.v. *)
Definition Ab_Z : AbObject := ring_ab Int_Ring.

(* The parity homomorphism.  Additivity is [Z.odd_add]. *)
Program Definition ab_parity : Ab_Z ~{Ab}~> Ab_Z2 :=
  {| cmon_map := {| morphism := Z.odd |} |}.
Next Obligation. apply Z.odd_add. Qed.

(* Its kernel is the even integers.  Membership is decidable and computes:
   both witnesses below are [eq_refl] on the underlying booleans. *)
Definition ab_even (n : Z) (H : Z.odd n = false)
  : carrier (cmon_setoid (AbKernel ab_parity)) := (n; H).

Definition ab_even_0 : carrier (cmon_setoid (AbKernel ab_parity)) :=
  ab_even 0%Z eq_refl.
Definition ab_even_2 : carrier (cmon_setoid (AbKernel ab_parity)) :=
  ab_even 2%Z eq_refl.

(* NONTRIVIAL: the kernel has at least two distinct elements, so it is not
   the zero group and the kill-f presheaf is not the constant singleton. *)
Lemma ab_parity_kernel_has_two : (ab_even_0 ≈ ab_even_2) → False.
Proof. simpl; unfold Z_eqT; discriminate. Qed.

(* PROPER: 1 is not in it, so the kernel is not all of Z either and the
   inclusion is not an isomorphism. *)
Lemma ab_parity_kernel_proper : Z.odd 1%Z = false → False.
Proof. discriminate. Qed.

(* Doubling, a map killed by parity, to exercise the descent clause. *)
Program Definition ab_double : Ab_Z ~{Ab}~> Ab_Z :=
  {| cmon_map := {| morphism := Z.mul 2 |} |}.
(* [change] first: the obligation tactic has already pushed [Z.mul 2]
   through [simpl] into its [match] form, which no [Z] lemma matches. *)
Next Obligation.
  unfold Z_eqT.
  change ((2 * (a + b))%Z = (2 * a + 2 * b)%Z).
  apply Z.mul_add_distr_l.
Qed.

Lemma ab_double_killed :
  ab_parity ∘ ab_double ≈ @zero_mor Ab Ab_Zero Ab_Z Ab_Z2.
Proof.
  intro n; simpl.
  change (Z.odd (2 * n)%Z = false).
  now rewrite Z.odd_mul.
Qed.

(* THE MEDIATOR COMPUTES.  The unique factorization of [ab_double] through
   the kernel of [ab_parity], evaluated at 3, is 6 -- by [eq_refl] on the
   underlying integer, with no reduction hint. *)
Definition ab_parity_med : Ab_Z ~{Ab}~> AbKernel ab_parity :=
  unique_obj (eq_desc (ab_kernel_IsKernel ab_parity) ab_double
                (fun n => ab_double_killed n)).

Example ab_parity_med_computes :
  `1 (cmon_map ab_parity_med 3%Z) = 6%Z.
Proof. reflexivity. Qed.

(* ... and it is the factorization: composing with the inclusion returns
   the doubling map. *)
Example ab_parity_med_factors :
  ab_kernel_incl ab_parity ∘ ab_parity_med ≈ ab_double.
Proof.
  exact (unique_property (eq_desc (ab_kernel_IsKernel ab_parity) ab_double
                            (fun n => ab_double_killed n))).
Qed.

(* The universal element of the kill-parity presheaf, named. *)
Definition ab_parity_universal_element
  : AUniversalElement
      (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) Ab_Z Ab_Z2 ab_parity)
      (AbKernel ab_parity)
  := ab_kernel_aue ab_parity.

(** ** Rng: no zero morphisms at all *)

(* A ring homomorphism preserves 1 and 0.  In the zero ring these coincide,
   so any homomorphism out of it into Z would give 1 = 0 there.  No appeal
   to zero morphisms is made: this shows the HOM-SET is empty. *)
Lemma Rng_no_hom_zero_to_Z (u : Zero_Ring ~{Rng}~> Int_Ring) : False.
Proof.
  pose proof (rig_map_one u) as H1.
  pose proof (rig_map_zero u) as H0.
  (* [rig_one Zero_Ring] and [rig_zero Zero_Ring] are the same term [ttt],
     so the two conclusions are about the same integer. *)
  simpl in H1, H0.
  unfold Z_eqT in H1, H0.
  rewrite H1 in H0.
  discriminate.
Qed.

(* Hence Rng carries no zero-morphism family: one would in particular
   supply a morphism from the zero ring to Z. *)
Theorem Rng_no_zero_morphisms : ZeroMorphisms Rng → False.
Proof.
  intro ZM.
  exact (Rng_no_hom_zero_to_Z (@zmor Rng ZM Zero_Ring Int_Ring)).
Qed.

(* ... and a fortiori no zero object, since a zero object supplies one. *)
Theorem Rng_no_zero_object : @ZeroObject Rng → False.
Proof.
  intro Z.
  exact (Rng_no_zero_morphisms (ZeroMorphisms_of_ZeroObject Z)).
Qed.

(* What DOES survive: the fork presheaf of a parallel pair, which needs no
   structure on the category whatever.  This is the "survives in categories
   without a zero object" clause, exhibited at the category that motivates
   it. *)
Definition Rng_fork_presheaf {R S : Rng} (u v : R ~{Rng}~> S)
  : Rng^op ⟶ Sets := ForkPresheaf u v.

(* ... and the passage: an equalizer in Rng is a universal element of it.
   The UNIVERSE-FREE form is used here deliberately -- the bundled
   [equalizer_universal_element_iso] does not instantiate at [Rng], for the
   reason documented at its definition and pinned in
   Test/ProbeKernelUniversal.v. *)
Definition Rng_equalizer_aue {R S : Rng} (u v : R ~{Rng}~> S) {k : Rng}
  {i : k ~> R} (E : IsEqualizer u v k i)
  : AUniversalElement (ForkPresheaf u v) k
  := equalizer_aue u v E.

Definition Rng_aue_equalizer {R S : Rng} (u v : R ~{Rng}~> S) {k : Rng}
  (U : AUniversalElement (ForkPresheaf u v) k)
  : IsEqualizer u v k (`1 (@aue_elem (Rng^op) (ForkPresheaf u v) k U))
  := aue_equalizer u v U.
