Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.StrongEpi.

Generalizable All Variables.

(* Regular categories: kernel pairs, regular epimorphisms, and stability.

   nLab:      https://ncatlab.org/nlab/show/regular+category
   Wikipedia: https://en.wikipedia.org/wiki/Regular_category

   A regular category is a finitely complete category in which every kernel
   pair has a coequalizer, and regular epimorphisms are stable under
   pullback.  The kernel pair of f : x ~> y is the pullback of f along
   itself ([kernel_pair]); its two projections p1, p2 : x ×_y x ~> x are the
   categorical rendering of the relation "f a = f b" on x.  A regular
   epimorphism ([RegularEpi]) is a morphism that arises as the coequalizer
   of some parallel pair; in a regular category, every regular epimorphism
   is in fact the coequalizer of its own kernel pair.

   For the finite-completeness clause we package a terminal object together
   with all pullbacks ([regular_terminal], [regular_pullbacks]).  This is
   the standard economical presentation: binary products are pullbacks over
   the terminal object, and equalizers are pullbacks of the induced
   pairings, so a terminal object and pullbacks generate all finite limits.

   The theorems below place the regular epimorphisms among the epimorphism
   classes: every regular epimorphism is epic ([regular_epi_epic], read off
   [coequalizer_epic]) and moreover strong ([regular_epi_strong]) — it
   lifts uniquely against every monomorphism, which is the left
   orthogonality condition of Theory/Orthogonality.v.  Finally, the
   coequalizing map that [regular_coeq] supplies for a kernel pair is
   itself a regular epimorphism ([regular_epi_of_kernel_coeq]), packaged by
   pointing back at the kernel-pair projections it coequalizes. *)

(* The kernel pair of f : x ~> y is the pullback of f along itself: an
   object x ×_y x with projections p1, p2 : x ×_y x ~> x satisfying
   f ∘ p1 ≈ f ∘ p2, universal among such pairs.

   nLab: https://ncatlab.org/nlab/show/kernel+pair *)
Definition kernel_pair {C : Category} `{H : @HasPullbacks C} {x y : C}
  (f : x ~> y) : Pullback f f := pullback f f.

(* A regular epimorphism is a morphism f : x ~> y that coequalizes some
   parallel pair p1, p2 : d ~> x.  The witness records the pair together
   with the elementary coequalizer structure of Structure/Coequalizer.v.

   nLab: https://ncatlab.org/nlab/show/regular+epimorphism *)
Record RegularEpi {C : Category} {x y : C} (f : x ~> y) := {
  regepi_dom : C;
  regepi_p1 : regepi_dom ~> x;
  regepi_p2 : regepi_dom ~> x;
  regepi_is_coeq : IsCoequalizer regepi_p1 regepi_p2 y f
}.

(* A regular category: a terminal object and all pullbacks (hence all
   finite limits), coequalizers of kernel pairs, and pullback-stability of
   regular epimorphisms.  Stability is phrased on the chosen pullbacks:
   pulling a regular epimorphism f : x ~> z back along any g : y ~> z
   yields a regular epimorphism x ×_z y ~> y. *)
Class Regular (C : Category) := {
  regular_terminal  : @Terminal C;
  regular_pullbacks : @HasPullbacks C;

  (* every kernel pair has a coequalizer *)
  regular_coeq {x y : C} (f : x ~> y) :
    ∃ (q : C) (e : x ~> q),
      IsCoequalizer
        (pullback_fst f f (@kernel_pair C regular_pullbacks x y f))
        (pullback_snd f f (@kernel_pair C regular_pullbacks x y f))
        q e;

  (* regular epimorphisms are stable under pullback *)
  regular_stable {x y z : C} (f : x ~> z) (g : y ~> z) :
    RegularEpi f →
    RegularEpi (pullback_snd f g (@pullback C regular_pullbacks x y z f g))
}.

#[export] Existing Instance regular_terminal.
#[export] Existing Instance regular_pullbacks.

(* Every regular epimorphism is an epimorphism: coequalizing maps are epic
   (Wikipedia: "every coequalizer is an epimorphism"). *)
Lemma regular_epi_epic {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → Epic f.
Proof.
  intros [d p1 p2 E].
  exact (coequalizer_epic p1 p2 E).
Qed.

(* Every regular epimorphism is a strong epimorphism.  Given a monic
   m : u ~> v and a commuting square m ∘ a ≈ b ∘ f with f coequalizing
   p1, p2 : d ~> x, the top leg a coforks the pair — m absorbs into the
   square on both sides and f ∘ p1 ≈ f ∘ p2, so cancelling the monic m
   gives a ∘ p1 ≈ a ∘ p2 — hence a descends uniquely through f.  The
   descent is the diagonal filler: its upper triangle is the descent
   equation, its lower triangle follows by cancelling the epic f, and any
   filler satisfies the descent equation, so descent uniqueness applies. *)
Lemma regular_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → StrongEpi f.
Proof.
  intros [d p1 p2 E].
  constructor.
  - exact (coequalizer_epic p1 p2 E).
  - intros u v m Hm.
    constructor.
    intros a b comm.
    (* a coforks the pair p1, p2, by cancelling the monomorphism m:
       m ∘ (a ∘ p1) ≈ b ∘ (f ∘ p1) ≈ b ∘ (f ∘ p2) ≈ m ∘ (a ∘ p2). *)
    assert (Ha : a ∘ p1 ≈ a ∘ p2). {
      apply (@monic C u v m Hm).
      rewrite !comp_assoc.
      rewrite comm.
      rewrite <- !comp_assoc.
      rewrite (cofork E).
      reflexivity.
    }
    pose proof (coeq_desc E a Ha) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* upper triangle: the descent equation d ∘ f ≈ a *)
        exact (unique_property U).
      * (* lower triangle m ∘ d ≈ b, by cancelling the epimorphism f:
           (m ∘ d) ∘ f ≈ m ∘ (d ∘ f) ≈ m ∘ a ≈ b ∘ f. *)
        apply (@epic C x y f (coequalizer_epic p1 p2 E) v
                 (m ∘ unique_obj U) b).
        rewrite <- comp_assoc.
        rewrite (unique_property U).
        exact comm.
    + intros d' [Hd'f Hmd'].
      (* any filler satisfies d' ∘ f ≈ a, so descent uniqueness applies *)
      apply (uniqueness U).
      exact Hd'f.
Qed.

(* In a regular category, the coequalizing map supplied by [regular_coeq]
   for the kernel pair of f is itself a regular epimorphism: it manifestly
   coequalizes the kernel-pair projections. *)
Definition regular_epi_of_kernel_coeq {C : Category} {R : Regular C}
  {x y : C} (f : x ~> y) :
  RegularEpi (`1 (`2 (regular_coeq f))) := {|
  regepi_dom := Pull f f (kernel_pair f);
  regepi_p1  := pullback_fst f f (kernel_pair f);
  regepi_p2  := pullback_snd f f (kernel_pair f);
  regepi_is_coeq := `2 (`2 (regular_coeq f))
|}.
