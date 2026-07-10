Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Kernels and cokernels *)

(* nLab:      https://ncatlab.org/nlab/show/kernel
              https://ncatlab.org/nlab/show/cokernel
   Wikipedia: https://en.wikipedia.org/wiki/Kernel_(category_theory)
              https://en.wikipedia.org/wiki/Cokernel

   In a category with a zero object, the kernel of f : x ~> y is the
   equalizer of f with the zero morphism, and the cokernel of f is the
   coequalizer of f with the zero morphism (nLab; Wikipedia).  With the
   elementary presentations [IsEqualizer] (Structure/Equalizer/Fork.v) and
   [IsCoequalizer] (Structure/Coequalizer.v) in hand, both notions are one
   definition each: [IsKernel f i := IsEqualizer f zero_mor k i] and
   [IsCokernel f e := IsCoequalizer f zero_mor q e].

   The frozen plan sketched obtaining the cokernel by transfer along the
   opposite category, but Phase 8's covariant [IsCoequalizer] already lives
   directly in C, so the direct definition below is exactly the accessor
   form that plan asked for.

   The classical facts follow immediately from the donor lemmas: kernels
   are monomorphisms ([kernel_monic], via [equalizer_monic]) and cokernels
   are epimorphisms ([cokernel_epic], via [coequalizer_epic]).  The descent
   lemmas [kernel_desc] and [cokernel_desc] restate the universal
   properties in the zero-composite phrasing preferred downstream: any h
   with f ∘ h ≈ 0 factors uniquely through the kernel, and dually.  A
   monomorphism is *normal* when it arises as a kernel ([normal_mono]), an
   epimorphism *conormal* when it arises as a cokernel ([normal_epi]);
   these feed the abelian-category axioms.  Finally,
   [cokernel_regular_epi] records that every cokernel map is a regular
   epimorphism — it manifestly coequalizes the pair (f, 0) — which is the
   bridge Abelian.v uses to reach the strong-epi/mono factorization. *)

Section Kernel.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(* The kernel of f : x ~> y, presented elementarily: i : k ~> x equalizes
   f against the zero morphism. *)
Definition IsKernel {x y k : C} (f : x ~> y) (i : k ~> x) : Type :=
  IsEqualizer f zero_mor k i.

(* The cokernel of f : x ~> y, presented elementarily: e : y ~> q
   coequalizes f against the zero morphism. *)
Definition IsCokernel {x y q : C} (f : x ~> y) (e : y ~> q) : Type :=
  IsCoequalizer f zero_mor q e.

(* A category (with zero object) has kernels when every morphism carries
   a chosen kernel. *)
Class HasKernels := {
  kernel {x y : C} (f : x ~> y) : ∃ (k : C) (i : k ~> x), IsKernel f i
}.

(* Dually, it has cokernels when every morphism carries a chosen
   cokernel. *)
Class HasCokernels := {
  cokernel {x y : C} (f : x ~> y) : ∃ (q : C) (e : y ~> q), IsCokernel f e
}.

(** ** The defining composites are zero *)

(* The kernel inclusion is absorbed by f: from the fork equation
   f ∘ i ≈ zero_mor ∘ i, the right-hand side collapses by zero-morphism
   absorption. *)
Lemma kernel_comp_zero {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) : f ∘ i ≈ zero_mor.
Proof.
  rewrite (fork_eq K).
  apply zero_mor_right.
Qed.

(* Dually, the cokernel projection absorbs f: from the cofork equation
   e ∘ f ≈ e ∘ zero_mor, the right-hand side collapses by zero-morphism
   absorption. *)
Lemma cokernel_comp_zero {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : e ∘ f ≈ zero_mor.
Proof.
  rewrite (cofork K).
  apply zero_mor_left.
Qed.

(** ** Kernels are monic, cokernels are epic *)

(* Wikipedia: "every kernel is a monomorphism" — read off the equalizer. *)
Lemma kernel_monic {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) : Monic i.
Proof.
  exact (equalizer_monic f zero_mor K).
Qed.

(* Wikipedia: "every cokernel is an epimorphism" — read off the
   coequalizer. *)
Lemma cokernel_epic {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : Epic e.
Proof.
  exact (coequalizer_epic f zero_mor K).
Qed.

(** ** Descent in the zero-composite phrasing *)

(* Any h with f ∘ h ≈ 0 factors uniquely through the kernel.  The
   hypothesis of [eq_desc] reads f ∘ h ≈ zero_mor ∘ h; the adapter step
   converts the zero-composite hypothesis into that shape via absorption
   of zero morphisms under precomposition. *)
Lemma kernel_desc {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) {z : C} (h : z ~> x) (Hh : f ∘ h ≈ zero_mor) :
  ∃! u : z ~> k, i ∘ u ≈ h.
Proof.
  apply (eq_desc K).
  rewrite Hh.
  symmetry.
  apply zero_mor_right.
Qed.

(* Dually, any h with h ∘ f ≈ 0 descends uniquely through the cokernel.
   The hypothesis of [coeq_desc] reads h ∘ f ≈ h ∘ zero_mor; the adapter
   step converts the zero-composite hypothesis into that shape via
   absorption of zero morphisms under postcomposition. *)
Lemma cokernel_desc {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) {z : C} (h : y ~> z) (Hh : h ∘ f ≈ zero_mor) :
  ∃! u : q ~> z, u ∘ e ≈ h.
Proof.
  apply (coeq_desc K).
  rewrite Hh.
  symmetry.
  apply zero_mor_left.
Qed.

(** ** Normal monomorphisms and normal epimorphisms *)

(* A morphism is a normal monomorphism when it is the kernel of some
   morphism.  nLab: https://ncatlab.org/nlab/show/normal+monomorphism *)
Definition normal_mono {k x : C} (i : k ~> x) : Type :=
  ∃ (y : C) (f : x ~> y), IsKernel f i.

(* Dually, a normal (or conormal) epimorphism is the cokernel of some
   morphism.  nLab: https://ncatlab.org/nlab/show/normal+epimorphism *)
Definition normal_epi {y q : C} (e : y ~> q) : Type :=
  ∃ (x : C) (f : x ~> y), IsCokernel f e.

(** ** Cokernels are regular epimorphisms *)

(* Every cokernel map is a regular epimorphism: it coequalizes the
   parallel pair (f, 0) by definition.  This is the bridge Abelian.v uses
   to inherit the strong-epi/mono factorization from Structure/Regular.v
   ([regular_epi_strong]). *)
Definition cokernel_regular_epi {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : RegularEpi e := {|
  regepi_dom := x;
  regepi_p1 := f;
  regepi_p2 := zero_mor;
  regepi_is_coeq := K
|}.

End Kernel.
