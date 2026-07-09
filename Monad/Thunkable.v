Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Binoidal.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.
Require Import Category.Monad.Kleisli.Commutative.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(** * Thunkable Kleisli morphisms: Führmann's hierarchy over a strong monad

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    nLab: https://ncatlab.org/nlab/show/strong+monad
    Reference: Führmann, "Direct models of the computational
               lambda-calculus", MFPS XV, ENTCS 20, 1999
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938-971, 2019 (arXiv:1709.00322)

    A Kleisli morphism f : x ~> M y of a strong monad M is THUNKABLE
    (Führmann) when freezing its result into a returned computation is the
    same as returning the frozen computation:

        fmap[M] ret[M] ∘ f ≈ ret[M] ∘ f        (at x ~> M (M y))

    Operationally: running f and then wrapping the value is the same as
    wrapping the entire computation f unrun — f can be turned into a thunk
    without changing its meaning, so f carries no observable effect
    ordering of its own.  This file develops Führmann's hierarchy over the
    library's actual Kleisli premonoidal structure
    (Monad/Kleisli/Premonoidal.v), in three tiers:

    1. Over a bare strong monad on a symmetric monoidal base, the
       unconditional part of the hierarchy:

           pure  ⇒  thunkable  ⇒  central

       [pure_thunkable] is a two-line naturality computation, and
       [thunkable_central] runs both centrality squares of
       [kleisli_central_iff] through Führmann's reassociation lemmas
       ([dstr_reassoc_left] / [dstr_reassoc_left'] and their mirrors,
       Monad/Strong/Symmetric.v): rebracketing a double strength through
       an extra M-layer computes [dstr] when the layer is fmap ret and
       [dstr'] when it is a bare ret, and thunkability equates the two
       layers.  Thunkable morphisms contain the identities
       ([thunkable_id]) and are closed under Kleisli composition
       ([thunkable_comp]) and under postcomposition with pure maps
       ([thunkable_fmap_post]), so they form a wide subcategory [Thunk]
       of Kl(M) through Construction/Subcategory.v — sitting inside the
       centre Z(Kl(M)) (the [CentralSub] of Structure/Binoidal/Central.v
       at [Kleisli_Binoidal]) by [thunkable_central].

    2. Over a copy-discard base, the bridge into categorical probability:
       a thunkable morphism is copyable and discardable — the two
       Cho-Jacobs squares stated against the double strength — PROVIDED
       the base copy and discard are natural ([copy_nat], [discard_nat]).
       The engine is the slide lemma [thunkable_slide]: any G that is an
       algebra-map-on-returns (G ∘ ret ≈ ret ∘ g) slides across a
       thunkable f as the pure map g.  The two naturality hypotheses are
       genuinely needed and genuinely available: they hold automatically
       in cartesian bases ([CD_of_Cartesian] in
       Structure/Monoidal/CopyDiscard/Proofs.v, where copy is the natural
       diagonal), and the discard half holds in any Markov category
       ([discard_natural] in Structure/Monoidal/Markov.v).  They are NOT
       derivable in a bare [CopyDiscard] base: taking M := Id makes every
       morphism thunkable, so an unconditional implication would force
       every morphism of every copy-discard category to be a comonoid
       homomorphism — exactly the naturality that [CopyDiscard]
       deliberately never asks for (its negative space is what carves out
       the deterministic morphisms in the first place).

    3. Over a commutative strong monad on a copy-discard base, the honest
       form of the thunkable-determinism statement:
       [thunkable_deterministic] lands every thunkable Kleisli morphism in
       the Cho-Jacobs deterministic class of the descended copy-discard
       structure [Kleisli_CopyDiscard] (Monad/Kleisli/Commutative.v) —
       i.e. inside the wide subcategory [Det] of Kl(M) — and
       [pure_deterministic] transports base-deterministic morphisms along
       the pure functor.  The bridging lemmas [kl_copyable_eq] and
       [kl_discardable_eq] identify the two comonoid-homomorphism squares
       of Kl(M) with [copyable] and [discardable] on the nose.

    Strictness of the hierarchy (recorded as prose, not formalized):
    both inclusions of the thunkable class — inside the centre (tier 1)
    and inside the deterministic class (tier 3) — are strict in general.
    Central but not thunkable: for the writer monad M x = x × W over a
    nontrivial commutative monoid W (in Sets), M is commutative, so
    EVERY Kleisli morphism is central ([kleisli_all_central],
    Monad/Kleisli/Commutative.v), yet the map x ↦ (x, w) with w ≠ e is
    not thunkable, because thunkability forces the written w to equal e;
    Führmann (1999) draws the same separation for continuation monads.
    Deterministic but not thunkable: for the read-only state monad
    M x = x × x (reader along a two-element environment, in Sets), every
    Kleisli morphism is copyable and discardable, but only the morphisms
    that ignore the read value are thunkable (Moss & Perrone,
    "Probability monads with submonads of deterministic states",
    LICS 2022, Theorem 3.14 and Example 3.16).  The converse of
    [thunkable_deterministic] is therefore not provable, and the
    deterministic class is in general strictly larger than the thunkable
    one. *)

Section Thunkable.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Tier 1: thunkability over a bare strong monad.                  *)
(* ------------------------------------------------------------------ *)

(* Führmann's definition: f can be frozen into a thunk.  The equation
   lives at x ~> M (M y): on the left the computation runs and its value
   is returned; on the right the whole computation is returned unrun. *)
Definition thunkable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] ret[M] ∘ f ≈ ret[M] ∘ f.

(* Thunkability is a property of the ≈-class of a morphism. *)
Lemma thunkable_respects {x y : C} {f g : x ~> M y} :
  f ≈ g → thunkable f → thunkable g.
Proof.
  unfold thunkable.
  intros E tf.
  now rewrite <- E.
Qed.

(* The Kleisli identity is thunkable: both sides are the unit naturality
   square [fmap_ret] instantiated at the unit itself. *)
Lemma thunkable_id {x : C} : thunkable (ret[M] : x ~{C}~> M x).
Proof.
  unfold thunkable.
  symmetry.
  apply fmap_ret.
Qed.

(* Every pure morphism is thunkable: push the outer unit across f with
   [fmap_ret]. *)
Lemma pure_thunkable {x y : C} (f : x ~{C}~> y) : thunkable (kpure f).
Proof.
  unfold thunkable, kpure.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(* Thunkable morphisms are closed under Kleisli composition
   join ∘ fmap f ∘ g.  Both sides normalize to fmap f ∘ g: the left via
   naturality of join and [tf] under the doubled functor, collapsing with
   [join_fmap_ret]; the right by walking the unit leftwards across join
   and fmap f with [fmap_ret], meeting [tg], and cancelling with
   [join_ret] inside the fused fmap argument. *)
Lemma thunkable_comp {x y z : C} {f : y ~> M z} {g : x ~> M y} :
  thunkable f → thunkable g → thunkable (join[M] ∘ fmap[M] f ∘ g).
Proof.
  intros tf tg.
  unfold thunkable in *.
  transitivity (fmap[M] f ∘ g).
  - (* fmap ret ∘ (join ∘ fmap f ∘ g) ≈ fmap f ∘ g *)
    rewrite !comp_assoc.
    rewrite <- join_fmap_fmap.
    rewrite <- (comp_assoc join[M]).
    rewrite <- fmap_comp.
    rewrite tf.
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite join_fmap_ret.
    now rewrite id_left.
  - (* fmap f ∘ g ≈ ret ∘ (join ∘ fmap f ∘ g) *)
    symmetry.
    rewrite !comp_assoc.
    rewrite fmap_ret.
    rewrite <- (comp_assoc (fmap[M] join[M])).
    rewrite fmap_ret.
    rewrite <- !comp_assoc.
    rewrite <- tg.
    rewrite (comp_assoc (fmap[M] (fmap[M] f))).
    rewrite <- fmap_comp.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- fmap_ret.
    rewrite comp_assoc.
    rewrite join_ret.
    now rewrite id_left.
Qed.

(* Thunkable morphisms absorb pure postcomposition: fmap u ∘ f is again
   thunkable.  The unit walks across u by [fmap_ret], meets [tf], and
   walks back out across fmap u. *)
Lemma thunkable_fmap_post {x y z : C} (u : y ~{C}~> z) {f : x ~> M y} :
  thunkable f → thunkable (fmap[M] u ∘ f).
Proof.
  intro tf.
  unfold thunkable in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite fmap_ret.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite tf.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite <- comp_assoc.
Qed.

(* Führmann's theorem: every thunkable morphism is central in Kl(M).
   Through [kleisli_central_iff] each centrality square asks that [dstr]
   and [dstr'] agree on a tensor with f in one factor; the reassociation
   lemmas of Monad/Strong/Symmetric.v rewrite [dstr ∘ (f ⨂ g)] as the
   rebracketed word at (fmap ret ∘ f) ⨂ g and [dstr' ∘ (f ⨂ g)] as the
   same word at (ret ∘ f) ⨂ g, and thunkability of f equates the two
   insertions.  No commutativity of M enters. *)
Theorem thunkable_central {x y : C} (f : x ~> M y) :
  thunkable f → @central Kleisli Kleisli_Binoidal x y f.
Proof.
  intros tf.
  apply kleisli_central_iff; intros c d g.
  split.
  - rewrite <- (dstr_reassoc_left f g).
    rewrite <- (dstr_reassoc_left' f g).
    now rewrite tf.
  - rewrite <- (dstr'_reassoc_right g f).
    rewrite <- (dstr'_reassoc_right' g f).
    now rewrite tf.
Qed.

(* Feeding returned values into BOTH factors of the double strength
   leaves a single unit — [dstr_ret_ret] (Monad/Strong/Symmetric.v), the
   unit law of the lax monoidal structure that [dstr] puts on M, needed
   below for the copyability of thunkable morphisms. *)

(* ------------------------------------------------------------------ *)
(** ** The wide subcategory Thunk of thunkable morphisms.              *)
(* ------------------------------------------------------------------ *)

(* [thunkable_id] and [thunkable_comp] are exactly the closure conditions
   of Construction/Subcategory.v, read at the definitional Kleisli
   composite (@compose Kleisli is join ∘ fmap f ∘ g on the nose), so the
   thunkable morphisms over ALL objects form a wide subcategory of Kl(M),
   Führmann's category of thunkable maps.  The packaging mirrors
   [DeterministicSub]/[Det] of CopyDiscard/Deterministic.v and
   [CentralSub]/[Centre] of Structure/Binoidal/Central.v.

   Hierarchy note: the shom-collection of [ThunkableSub] includes into
   that of [CentralSub] at [Kleisli_Binoidal] — that inclusion IS
   [thunkable_central] — so Thunk sits inside the centre Z(Kl(M)) as wide
   subcategories of Kl(M); and every pure morphism [kpure f] lands in
   Thunk by [pure_thunkable]. *)

Program Definition ThunkableSub : Subcategory Kleisli := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => thunkable f;
  scomp := fun _ _ _ _ _ _ _ _ tf tg => thunkable_comp tf tg;
  sid   := fun _ _ => thunkable_id
|}.

Definition Thunk : Category := Sub Kleisli ThunkableSub.

Lemma Thunk_wide : Wide Kleisli ThunkableSub.
Proof. intro x; exact ttt. Qed.

(* The inclusion Thunk ⟶ Kl(M) is the generic faithful
   [Incl Kleisli ThunkableSub] from Construction/Subcategory.v. *)

(* ------------------------------------------------------------------ *)
(** ** Tier 2: copyability and discardability over a CD base.          *)
(* ------------------------------------------------------------------ *)

Section ThunkableCD.

Context `{CD : @CopyDiscard C _}.

(* The two naturality hypotheses.  [CopyDiscard] itself deliberately
   never demands them — their absence for general morphisms is what
   makes the deterministic subclass meaningful — but tier 2 genuinely
   needs them: with M := Id every morphism is thunkable, so deriving
   copyable/discardable from thunkable over a bare CD base would force
   every morphism of every copy-discard category into a comonoid
   homomorphism, which bare CD does not grant.  Both hypotheses hold in
   cartesian bases ([CD_of_Cartesian] in CopyDiscard/Proofs.v: copy is
   the natural diagonal, discard the eliminate of the terminal unit),
   and [discard_nat] alone holds in every Markov category
   ([discard_natural], Structure/Monoidal/Markov.v). *)

Hypothesis copy_nat : ∀ (x y : C) (u : x ~{C}~> y),
  copy[y] ∘ u ≈ (u ⨂ u) ∘ copy[x].

Hypothesis discard_nat : ∀ (x y : C) (u : x ~{C}~> y),
  discard[y] ∘ u ≈ discard[x].

(* The slide lemma, the engine of tier 2: if G agrees with the pure map
   g on returned values (G ∘ ret ≈ ret ∘ g), then G slides across any
   thunkable f as fmap g.  Proof: conjugate [tf] with fmap G, exchange
   G against g inside the fused functor argument with [algG], convert
   the surviving head fmap ret into a bare ret with
   [thunkable_fmap_post], and cancel the resulting unit under join with
   [join_ret]. *)
Lemma thunkable_slide {a b c : C} (f : a ~> M b) (tf : thunkable f)
      (G : M b ~{C}~> M c) (g : b ~{C}~> c)
      (algG : G ∘ ret[M] ≈ ret[M] ∘ g) :
  G ∘ f ≈ fmap[M] g ∘ f.
Proof.
  assert (E : ret[M] ∘ (fmap[M] g ∘ f) ≈ ret[M] ∘ (G ∘ f)).
  { transitivity (fmap[M] G ∘ (fmap[M] ret[M] ∘ f)).
    - rewrite <- (thunkable_fmap_post g tf).
      rewrite !comp_assoc.
      rewrite <- !fmap_comp.
      rewrite algG.
      reflexivity.
    - rewrite tf.
      rewrite comp_assoc.
      rewrite <- fmap_ret.
      now rewrite <- comp_assoc. }
  rewrite <- (id_left (G ∘ f)).
  rewrite <- (@join_ret C M _ c).
  rewrite <- comp_assoc.
  rewrite <- E.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* The Cho-Jacobs squares for a Kleisli morphism, stated at the double
   strength: copying the output of f agrees with running f twice on a
   copied input (combined by [dstr]), and discarding the output of f
   agrees with discarding its input outright. *)
Definition copyable {x y : C} (f : x ~> M y) : Type :=
  dstr ∘ (f ⨂ f) ∘ copy[x] ≈ fmap[M] copy[y] ∘ f.

Definition discardable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] discard[y] ∘ f ≈ ret[M] ∘ discard[x].

(* Thunkable morphisms are copyable: naturality of copy at f turns the
   copied-input side into (dstr ∘ copy[M y]) ∘ f, and that G slides
   across f as fmap copy[y] — its algebra-map equation is naturality of
   copy at ret followed by the double-strength unit law
   [dstr_ret_ret]. *)
Theorem thunkable_copyable {x y : C} (f : x ~> M y) :
  thunkable f → copyable f.
Proof using C CD M SM SMon copy_nat.
  intro tf.
  unfold copyable.
  rewrite <- comp_assoc.
  rewrite <- (copy_nat x (M y) f).
  rewrite comp_assoc.
  apply (thunkable_slide f tf (dstr ∘ copy[M y]) copy[y]).
  rewrite <- comp_assoc.
  rewrite (copy_nat y (M y) ret[M]).
  rewrite comp_assoc.
  rewrite dstr_ret_ret.
  reflexivity.
Qed.

(* Thunkable morphisms are discardable: the mirror argument, sliding
   G := ret ∘ discard[M y] across f as fmap discard[y]; both the
   algebra-map equation and the final collapse are [discard_nat]. *)
Theorem thunkable_discardable {x y : C} (f : x ~> M y) :
  thunkable f → discardable f.
Proof using C CD M SM SMon discard_nat.
  intro tf.
  unfold discardable.
  assert (algG : (ret[M] ∘ discard[M y]) ∘ ret[M] ≈ ret[M] ∘ discard[y]).
  { rewrite <- comp_assoc.
    now rewrite (discard_nat y (M y) ret[M]). }
  rewrite <- (thunkable_slide f tf (ret[M] ∘ discard[M y]) discard[y] algG).
  rewrite <- comp_assoc.
  now rewrite (discard_nat x (M y) f).
Qed.

(* Pure morphisms are copyable and discardable, through
   [pure_thunkable]. *)
Corollary pure_copyable {x y : C} (f : x ~{C}~> y) : copyable (kpure f).
Proof using C CD M SM SMon copy_nat.
  apply thunkable_copyable, pure_thunkable.
Qed.

Corollary pure_discardable {x y : C} (f : x ~{C}~> y) :
  discardable (kpure f).
Proof using C CD M SM SMon discard_nat.
  apply thunkable_discardable, pure_thunkable.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 3: the bridge to the deterministic class of Kl(M).         *)
(* ------------------------------------------------------------------ *)

Section ThunkableDeterministic.

(* When M is commutative, Kl(M) is itself a copy-discard category
   ([Kleisli_CopyDiscard], Monad/Kleisli/Commutative.v: copy and discard
   are the pure images of the base generators), and the Cho-Jacobs
   deterministic predicate of CopyDiscard/Deterministic.v applies to
   Kleisli morphisms.  This section identifies its two comonoid-
   homomorphism squares with [copyable] and [discardable], lands every
   thunkable morphism in the deterministic class — the honest form of
   the thunkable-determinism bridge; see the header for why the M := Id
   reading rules out an unconditional converse-free statement over bare
   CD — and transports base-deterministic morphisms along the pure
   functor. *)

Hypothesis comm : commutative_sm (M:=M).

(* The δ-square of the descended comonoid at f is exactly [copyable] f:
   the pure exchange laws strip the units, and the induced tensor
   computes the double strength ([kleisli_bimap_dstr]). *)
Lemma kl_copyable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure copy[y]) f
     ≈ @compose Kleisli _ _ _
         (f ⨂[Kleisli_Monoidal comm] f) (kpure copy[x]))
  ↔ copyable f.
Proof.
  split; intro E.
  - unfold copyable.
    rewrite kl_pure_post in E.
    rewrite kl_pure_pre in E.
    rewrite (kleisli_bimap_dstr comm f f) in E.
    symmetry; exact E.
  - rewrite kl_pure_post.
    rewrite kl_pure_pre.
    rewrite (kleisli_bimap_dstr comm f f).
    symmetry; exact E.
Qed.

(* The ε-square of the descended comonoid at f is exactly
   [discardable] f. *)
Lemma kl_discardable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure discard[y]) f ≈ kpure discard[x])
  ↔ discardable f.
Proof.
  split; intro E.
  - unfold discardable.
    rewrite kl_pure_post in E.
    exact E.
  - rewrite kl_pure_post.
    exact E.
Qed.

(* The bridge: every thunkable Kleisli morphism is deterministic in the
   Cho-Jacobs sense for the descended copy-discard structure on Kl(M) —
   i.e. it lies in the wide subcategory [Det] of Kl(M) built by
   CopyDiscard/Deterministic.v at [Kleisli_CopyDiscard].  Both comonoid-
   homomorphism squares are tier 2 through the [kl_*_eq]
   identifications. *)
Theorem thunkable_deterministic {x y : C} (f : x ~{Kleisli}~> y) :
  thunkable f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y f.
Proof using C CD M SM SMon comm copy_nat discard_nat.
  intro tf.
  split.
  - exact (snd (kl_copyable_eq f) (thunkable_copyable f tf)).
  - exact (snd (kl_discardable_eq f) (thunkable_discardable f tf)).
Qed.

(* The two squares of a pure image, as standalone transfers: the pure
   functor carries the base squares to Kl(M) through [kl_pure_comp] and
   [kl_pure_tensor]. *)
Lemma pure_hom_delta {x y : C} (f : x ~{C}~> y)
      (Fd : copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]) :
  @compose Kleisli _ _ _ (kpure copy[y]) (kpure f)
    ≈ @compose Kleisli _ _ _
        ((kpure f) ⨂[Kleisli_Monoidal comm] (kpure f)) (kpure copy[x]).
Proof.
  rewrite (kl_pure_tensor comm f f).
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  exact Fd.
Qed.

Lemma pure_hom_epsilon {x y : C} (f : x ~{C}~> y)
      (Fe : discard[y] ∘ f ≈ discard[x]) :
  @compose Kleisli _ _ _ (kpure discard[y]) (kpure f) ≈ kpure discard[x].
Proof.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact Fe.
Qed.

(* Determinism transports along the pure functor: a base-deterministic
   morphism has a deterministic pure image in Kl(M). *)
Theorem pure_deterministic {x y : C} (f : x ~{C}~> y) :
  @deterministic C SM CD x y f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y (kpure f).
Proof.
  intros [Fd Fe].
  split.
  - exact (pure_hom_delta f Fd).
  - exact (pure_hom_epsilon f Fe).
Qed.

End ThunkableDeterministic.

End ThunkableCD.

End Thunkable.
