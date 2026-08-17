(** * Boundary probes for kernels as universal elements

    Companion to Structure/Kernel/Universal.v and its satellite
    Structure/Kernel/Universal/Examples.v (issue #304).  Those files make
    strength claims of four different grades -- some definitional, some
    only up to [≈], one a universe restriction, and one a contrast
    between two packagings -- and the negative side of each is a boundary
    no in-tree consumer would notice breaking.  They are pinned here.
    **If the [Fail] commands below stop failing, this file breaks the
    build.**

    Every negative is paired with a positive control that must SUCCEED: a
    [Fail] alone passes just as happily when a name has been renamed out
    from under it.  The instrument itself was checked out of band --
    wrapping [Fail] around a succeeding [Check] reports "The command has
    not failed!" and aborts compilation -- and each negative below was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended failure and not a syntax, scope or resolution error.  Where
    the stripped error is NOT of the form "cannot unify", the actual
    message is quoted at the probe.

    THE FOUR BOUNDARIES.

    (1) THE KILL PACKAGING IS NOT A RECORD-LEVEL BIJECTION, IN EITHER
    DIRECTION.  [kernel_aue] and [aue_kernel] preserve the underlying
    morphism by [eq_refl], and in one direction the mediator too; but
    neither whole record survives, and the obstruction is named: the kill
    shape (f ∘ h ≈ 0) and the fork shape (f ∘ h ≈ 0 ∘ h) are exchanged by
    the [Qed]-opaque [kill_fork] / [fork_kill], and [eq_desc] is
    proof-RELEVANT in its hypothesis, so even the [fork_eq] field alone
    does not come back.

    (2) THE FORK PACKAGING IS DEFINITIONALLY TIGHTER THAN THE KILL
    PACKAGING -- the opposite of what the naming suggests.  On the fork
    side one whole round trip IS [eq_refl] ([aue_equalizer_round]),
    because no reshaping happens; the other is not, and the ONLY
    obstruction there is that [sigT] has no eta, which
    [aue_equalizer_round_universal] states positively.

    (3) THE BUNDLED SETOID ISOMORPHISM CARRIES A UNIVERSE RESTRICTION THE
    UNIVERSE-FREE FORMS DO NOT.  [kernel_universal_element_iso] is stated
    over [C : Category@{u u0 u0}] with [u <= u0] -- objects at or below
    homs -- because [obj[Sets@{o so}]] is [SetoidObject@{o o}]
    (Instance/Sets.v:194), identifying a setoid's carrier and relation
    universes, while [KernelData]'s carrier sits at C's object universe
    and its relation at C's proof universe.  [Ab@{u u0}] is declared with
    [u0 < u], so neither it nor [Rng] can be substituted.  The passages,
    the round-trip lemmas and [kernel_representation] carry no such
    restriction and DO instantiate at [Ab]; the positive controls below
    are that pair.

    (4) THE TWO PRESHEAVES ARE DISTINCT TYPES.  [KillPresheaf f] and
    [ForkPresheaf f zmor] are naturally isomorphic ([kill_fork_iso]) with
    both components the identity on the underlying morphism, but they are
    not the same functor and their element types are not the same type,
    so the isomorphism is a construction and not a coercion. *)

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
Require Import Category.Structure.Kernel.Universal.Examples.

Local Open Scope category_scope.

Section KillProbes.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y k : C}.
Context (f : x ~> y).
Context (i : k ~> x).
Context (K : IsKernelOf f i).
Context (U : AUniversalElement (KillPresheaf f) k).

(** ** (1) The kill packaging preserves the morphism, not the record

    Positive controls: the morphism survives both passages by [eq_refl],
    the mediator survives one of them as a TERM, and both survive up to
    [≈]. *)

Check (kernel_aue_morphism f K).
Check (aue_kernel_morphism f U).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor) =>
         kernel_aue_mediator f K d h Hh).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor ∘ h) =>
         kernel_round_mediator f K h Hh).
Check (fun (d : C) (p : Kills f d) => aue_kernel_round_mediator f U d p).

(** Negative: the whole record does not come back on the kernel side.
    (Stripped: cannot unify [aue_kernel f (kernel_aue f K)] and [K].) *)
Fail Check (eq_refl : aue_kernel f (kernel_aue f K) = K).

(** Negative: not even the [fork_eq] field alone -- [kill_fork] and
    [fork_kill] are opaque, so their composite is not the identity term.
    (Stripped: cannot unify the two [fork_eq] terms.) *)
Fail Check (eq_refl : fork_eq (aue_kernel f (kernel_aue f K)) = fork_eq K).

(** Negative: nor on the universal-element side.  (Stripped: cannot unify
    [kernel_aue f (aue_kernel f U)] and [U].) *)
Fail Check (eq_refl : kernel_aue f (aue_kernel f U) = U).

(** Negative: and the mediator round trip on the kill side is genuinely
    only up to [≈] -- the Leibniz form fails, unlike its fork-side twin
    [aue_equalizer_round_mediator], which holds at [=].  (Stripped: cannot
    unify the two [unique_obj] terms.) *)
Fail Check (fun (d : C) (p : Kills f d) =>
              eq_refl
                : unique_obj (@aue_universal (C^op) (KillPresheaf f) k
                                (kernel_aue f (aue_kernel f U)) d p)
                  = unique_obj (@aue_universal (C^op) (KillPresheaf f) k U d p)).

End KillProbes.

Section ForkProbes.

Context {C : Category}.
Context {x y k : C}.
Context (f g : x ~> y).
Context (i : k ~> x).
Context (E : IsEqualizer f g k i).
Context (V : AUniversalElement (ForkPresheaf f g) k).

(** ** (2) The fork packaging IS a record-level identity, one way

    Positive controls: one whole round trip is [eq_refl] on the whole
    record, and on the other side the universal clause survives up to the
    [sigT] repacking, which is the only thing missing. *)

Check (aue_equalizer_round f g E).
Check (aue_equalizer_round_universal f g V).
Check (aue_equalizer_round_elem f g V).
Check (fun (d : C) (p : Forks f g d) => aue_equalizer_round_mediator f g V d p).

(** Negative: the other whole round trip is not [eq_refl].  (Stripped:
    cannot unify [equalizer_aue f g (aue_equalizer f g V)] and [V].) *)
Fail Check (eq_refl : equalizer_aue f g (aue_equalizer f g V) = V).

(** ** (4) The two presheaves are distinct types

    Positive control first: they are naturally isomorphic. *)

Check (fun (ZM : ZeroMorphisms C) => kill_fork_iso f).

(** Negative: and nevertheless not the same functor.  This one does NOT
    report "cannot unify"; stripped, the message is: the term [eq_refl]
    'has type "KillPresheaf f = KillPresheaf f" while it is expected to
    have type "KillPresheaf f = ForkPresheaf f zmor"'. *)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : KillPresheaf f = ForkPresheaf f zmor).

(** Negative: nor are their element types the same type.  Stripped, again
    without a "cannot unify" line: the term [eq_refl] 'has type
    "Kills f k = Kills f k" while it is expected to have type
    "Kills f k = Forks f zmor k"'. *)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : Kills f k = Forks f zmor k).

End ForkProbes.

(** ** (3) The universe restriction on the bundled isomorphism

    Positive control: at an abstract category -- where the elaborator is
    free to put the object universe at or below the hom universe -- both
    bundled isomorphisms exist. *)

Check (fun (C : Category) (ZM : ZeroMorphisms C) (x y : C) (f : x ~> y)
           (k : C) => @kernel_universal_element_iso C ZM x y f k).

Check (fun (C : Category) (x y : C) (f g : x ~> y) (k : C) =>
         @equalizer_universal_element_iso C x y f g k).

(** Negative: neither instantiates at a concrete algebraic category.
    These are UNIVERSE INCONSISTENCIES, not unification failures.
    Stripped, the first reports that [Ab] "has type
    Category@{a b b} while it is expected to have type Category@{c d d}",
    followed by "universe inconsistency: Cannot enforce b = d because
    b < a <= d" -- i.e. [Ab]'s own declaration [Ab@{u u0}] with [u0 < u]
    (objects strictly above homs) is exactly what is refused.  [@] is used
    throughout so that no implicit argument can make a command fail for an
    unrelated reason. *)

Fail Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (k : Ab) =>
              @kernel_universal_element_iso Ab
                (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f k).

Fail Check (fun (R S : Rng) (u v : R ~{Rng}~> S) (k : Rng) =>
              @equalizer_universal_element_iso Rng R S u v k).

(** Positive control, immediately: the universe-free forms DO reach [Ab],
    and so does the representability statement.  This is the pair that
    makes the restriction a measured fact about the bundled packaging
    rather than about the theorem. *)

Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_aue f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_representation f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_Representable f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_repr_obj f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (z : AbObject)
           (h : z ~{Ab}~> A) => ab_kernel_round f h).

(** ** The zero-object bridge is definitional, and Rng has no zero morphisms

    Positive controls: [zmor] at the derived structure IS [zero_mor], the
    two kernel predicates are the same type, and the [Ab] witness computes. *)

Check (fun (C : Category) (Z : @ZeroObject C) (x y : C) =>
         @zmor_is_zero_mor C Z x y).

Check (fun (C : Category) (Z : @ZeroObject C) (x y k : C) (f : x ~> y)
           (i : k ~> x) => @IsKernel_is_IsKernelOf C Z x y f k i).

Check (ab_parity_med_computes).
Check (ab_parity_kernel_has_two).
Check (ab_parity_kernel_proper).

(** Positive control on the negative theorem: Rng has no zero-morphism
    family, hence no zero object.  These are THEOREMS, not [Fail] probes --
    the difference matters, and is the reason the fork packaging exists. *)

Check (Rng_no_zero_morphisms : ZeroMorphisms Rng → False).
Check (Rng_no_zero_object : @ZeroObject Rng → False).

(** ... and the fork presheaf is nevertheless formable there. *)
Check (fun (R S : Rng) (u v : R ~{Rng}~> S) => Rng_fork_presheaf u v).
