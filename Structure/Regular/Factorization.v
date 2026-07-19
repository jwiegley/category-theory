Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Factorization.StrongEpi.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(* The (regular epi, mono) orthogonal factorization system of a regular
   category.

   nLab:      https://ncatlab.org/nlab/show/regular+category
              https://ncatlab.org/nlab/show/regular+epimorphism
              https://ncatlab.org/nlab/show/image
   Wikipedia: https://en.wikipedia.org/wiki/Regular_category

   In a regular category every morphism f : x ~> y factors as a regular
   epimorphism followed by a monomorphism — the image factorization — and
   the two classes are orthogonal, so the factorizations assemble into an
   orthogonal factorization system (Structure/Factorization.v) whose left
   class is the regular epimorphisms ([RegularEpiClass]) and whose right
   class is the monomorphisms ([MonoClass] of Theory/Morphisms/Classes.v).

   The factorization of f: take its kernel pair p1, p2 : x ×_y x ~> x (the
   pullback of f along itself) and the coequalizer e : x ~> q of p1, p2
   supplied by [regular_coeq].  Since f coforks its own kernel pair —
   f ∘ p1 ≈ f ∘ p2 is the pullback square — it descends across e to a
   comparison morphism m : q ~> y with m ∘ e ≈ f.  The left leg e is a
   regular epimorphism by construction ([regular_epi_of_kernel_coeq]); the
   heart of the theorem is that the comparison m is monic
   ([image_comparison_monic]), proved by the classical double-cover
   argument, which uses pullback-stability of regular epimorphisms twice:

   Given a, b : T ~> q with m ∘ a ≈ m ∘ b, pull e back along a, obtaining
   a regular-epic cover pi1 : P1 ~> T with e ∘ s1 ≈ a ∘ pi1; then pull e
   back along b ∘ pi1, obtaining a further regular-epic cover
   pi2 : P2 ~> P1 with e ∘ s2 ≈ (b ∘ pi1) ∘ pi2.  On the double cover P2
   the two legs s1 ∘ pi2, s2 : P2 ~> x are identified by f (compute with
   m ∘ e ≈ f and m ∘ a ≈ m ∘ b), so they factor through the kernel pair
   of f; and e coequalizes the kernel pair, so e ∘ (s1 ∘ pi2) ≈ e ∘ s2.
   Unwinding the two pullback squares then gives
   a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2), and pi1 ∘ pi2 is epic (regular
   epimorphisms are epic, and epimorphisms compose), so a ≈ b.

   Orthogonality of the two classes is exactly [regular_epi_strong] of
   Structure/Regular.v: every regular epimorphism lifts uniquely against
   every monomorphism.  The packaged system is [Regular_OFS]. *)

(* The class of regular epimorphisms, as a morphism class in the sense of
   Theory/Morphisms/Classes.v. *)
Definition RegularEpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => RegularEpi f.

(* The elementary coequalizer property transports along ≈ of the
   coequalizing map: the cofork equation rewrites, and equivalent maps
   carry exactly the same descents. *)
Lemma is_coequalizer_respects {C : Category} {x y q : C}
  (f g : x ~> y) (e e' : y ~> q) :
  e ≈ e' → IsCoequalizer f g q e → IsCoequalizer f g q e'.
Proof.
  intros Heq E.
  unshelve refine {| cofork := _; coeq_desc := _ |}.
  - (* e' absorbs the parallel pair because e does *)
    rewrite <- Heq.
    exact (cofork E).
  - intros z h Hh.
    pose proof (coeq_desc E h Hh) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + (* the descent across e also descends across e' *)
      rewrite <- Heq.
      exact (unique_property U).
    + intros v Hv.
      apply (uniqueness U).
      rewrite Heq.
      exact Hv.
Qed.

(* Being a regular epimorphism transports along ≈: the same parallel pair,
   with the transported coequalizer structure, is a witness. *)
Lemma regular_epi_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → RegularEpi f → RegularEpi g.
Proof.
  intros Heq H.
  destruct H as [d p1 p2 E].
  exact {| regepi_dom := d
         ; regepi_p1  := p1
         ; regepi_p2  := p2
         ; regepi_is_coeq := is_coequalizer_respects p1 p2 f g Heq E |}.
Qed.

(* Being a monomorphism transports along ≈: left cancellation of g reduces
   to left cancellation of f. *)
Lemma monic_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → Monic f → Monic g.
Proof.
  intros Heq Hm.
  constructor.
  intros z g1 g2 Hgg.
  apply (@monic C x y f Hm z g1 g2).
  rewrite Heq.
  exact Hgg.
Qed.

(* Every regular epimorphism is orthogonal to every monomorphism: regular
   epimorphisms are strong ([regular_epi_strong]), and strength is exactly
   the unique lifting property against monomorphisms. *)
Lemma regular_epi_mono_orthogonal {C : Category} {a b u v : C}
  (e : a ~> b) (m : u ~> v) :
  RegularEpi e → Monic m → e ⫫ m.
Proof.
  intros He Hm.
  destruct (regular_epi_strong e He) as [Hepic Hlift].
  exact (Hlift u v m Hm).
Qed.

Section RegularFactorization.

Context {C : Category}.
Context (R : Regular C).

(* The kernel pair of f, on the chosen pullbacks of the regular structure. *)
Definition image_kernel_pair {x y : C} (f : x ~> y) : Pullback f f :=
  @kernel_pair C (@regular_pullbacks C R) x y f.

(* The image object of f: the coequalizer of its kernel pair. *)
Definition image_obj {x y : C} (f : x ~> y) : C :=
  `1 (@regular_coeq C R x y f).

(* The coequalizing map onto the image. *)
Definition image_epi {x y : C} (f : x ~> y) : x ~> image_obj f :=
  `1 (`2 (@regular_coeq C R x y f)).

(* The elementary coequalizer structure carried by the image. *)
Definition image_is_coeq {x y : C} (f : x ~> y) :
  IsCoequalizer
    (pullback_fst f f (image_kernel_pair f))
    (pullback_snd f f (image_kernel_pair f))
    (image_obj f) (image_epi f) :=
  `2 (`2 (@regular_coeq C R x y f)).

(* f coforks its own kernel pair — the pullback square — so it descends
   uniquely across the coequalizing map. *)
Definition image_desc {x y : C} (f : x ~> y) :
  ∃! u : image_obj f ~> y, u ∘ image_epi f ≈ f :=
  coeq_desc (image_is_coeq f) f
    (pullback_commutes f f (image_kernel_pair f)).

(* The comparison morphism from the image into the codomain. *)
Definition image_mor {x y : C} (f : x ~> y) : image_obj f ~> y :=
  unique_obj (image_desc f).

(* The factorization equation: m ∘ e ≈ f. *)
Definition image_commutes {x y : C} (f : x ~> y) :
  image_mor f ∘ image_epi f ≈ f :=
  unique_property (image_desc f).

(* The left leg is a regular epimorphism: it coequalizes the kernel pair
   of f. *)
Definition image_epi_regular {x y : C} (f : x ~> y) :
  RegularEpi (image_epi f) :=
  @regular_epi_of_kernel_coeq C R x y f.

(* The image-factorization theorem: the comparison morphism out of the
   image is monic.  This is the double-cover argument sketched in the
   header: pulling the coequalizing map e back along a and then along
   b ∘ pi1 produces a composite regular-epic cover of the common domain of
   a and b, on which a and b agree because their difference is detected by
   the kernel pair of f and erased by e. *)
Lemma image_comparison_monic {x y : C} (f : x ~> y) : Monic (image_mor f).
Proof using C R.
  constructor.
  intros T a b Hab.
  (* (i) pull e back along a; stability covers T by a regular epi pi1 *)
  pose (P1 := @pullback C (@regular_pullbacks C R) x T (image_obj f)
                (image_epi f) a).
  pose (s1 := pullback_fst (image_epi f) a P1).
  pose (pi1 := pullback_snd (image_epi f) a P1).
  assert (Hc1 : image_epi f ∘ s1 ≈ a ∘ pi1). {
    exact (pullback_commutes (image_epi f) a P1).
  }
  assert (Hpi1 : RegularEpi pi1). {
    exact (@regular_stable C R x T (image_obj f) (image_epi f) a
             (image_epi_regular f)).
  }
  (* (ii) pull e back along b ∘ pi1; stability covers P1 by a regular
     epi pi2 *)
  pose (P2 := @pullback C (@regular_pullbacks C R) x
                (Pull (image_epi f) a P1) (image_obj f)
                (image_epi f) (b ∘ pi1)).
  pose (s2 := pullback_fst (image_epi f) (b ∘ pi1) P2).
  pose (pi2 := pullback_snd (image_epi f) (b ∘ pi1) P2).
  assert (Hc2 : image_epi f ∘ s2 ≈ (b ∘ pi1) ∘ pi2). {
    exact (pullback_commutes (image_epi f) (b ∘ pi1) P2).
  }
  assert (Hpi2 : RegularEpi pi2). {
    exact (@regular_stable C R x (Pull (image_epi f) a P1) (image_obj f)
             (image_epi f) (b ∘ pi1) (image_epi_regular f)).
  }
  (* (iii) the two legs of the double cover into x agree under f:
       f ∘ (s1 ∘ pi2) ≈ m ∘ e ∘ s1 ∘ pi2 ≈ m ∘ a ∘ pi1 ∘ pi2
         ≈ m ∘ b ∘ pi1 ∘ pi2 ≈ m ∘ e ∘ s2 ≈ f ∘ s2 *)
  assert (Hcone : f ∘ (s1 ∘ pi2) ≈ f ∘ s2). {
    transitivity ((image_mor f ∘ image_epi f) ∘ (s1 ∘ pi2)).
    - apply compose_respects.
      + symmetry.
        exact (image_commutes f).
      + reflexivity.
    - transitivity ((image_mor f ∘ image_epi f) ∘ s2).
      + rewrite <- !comp_assoc.
        rewrite Hc2.
        rewrite (comp_assoc (image_epi f) s1 pi2).
        rewrite Hc1.
        rewrite !comp_assoc.
        rewrite Hab.
        reflexivity.
      + apply compose_respects.
        * exact (image_commutes f).
        * reflexivity.
  }
  (* the legs therefore factor through the kernel pair of f *)
  pose proof (ump_pullbacks f f (image_kernel_pair f) _
                (s1 ∘ pi2) s2 Hcone) as Uw.
  destruct (unique_property Uw) as [Hw1 Hw2].
  (* (iv) e coequalizes the kernel pair, so the legs agree under e *)
  assert (Hes : image_epi f ∘ (s1 ∘ pi2) ≈ image_epi f ∘ s2). {
    transitivity
      (image_epi f
         ∘ (pullback_fst f f (image_kernel_pair f) ∘ unique_obj Uw)).
    - apply compose_respects.
      + reflexivity.
      + symmetry.
        exact Hw1.
    - transitivity
        (image_epi f
           ∘ (pullback_snd f f (image_kernel_pair f) ∘ unique_obj Uw)).
      + rewrite !comp_assoc.
        rewrite (cofork (image_is_coeq f)).
        reflexivity.
      + apply compose_respects.
        * reflexivity.
        * exact Hw2.
  }
  (* unwinding the two pullback squares identifies a and b on the double
     cover *)
  assert (Hfinal : a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2)). {
    rewrite !comp_assoc.
    rewrite <- Hc1.
    rewrite <- (comp_assoc (image_epi f) s1 pi2).
    rewrite Hes.
    exact Hc2.
  }
  (* (v) the double cover is epic, so a ≈ b *)
  assert (Hepi : Epic (pi1 ∘ pi2)). {
    apply epi_compose.
    - exact (regular_epi_epic pi1 Hpi1).
    - exact (regular_epi_epic pi2 Hpi2).
  }
  apply (@epic C _ T (pi1 ∘ pi2) Hepi (image_obj f) a b).
  exact Hfinal.
Qed.

(* The image factorization of f, as an (E, M)-factorization for E the
   regular epimorphisms and M the monomorphisms. *)
Definition regular_factorization {x y : C} (f : x ~> y) :
  Factorization f (@RegularEpiClass C) (@MonoClass C) := {|
  fact_mid  := image_obj f;
  fact_e    := image_epi f;
  fact_e_in := image_epi_regular f;
  fact_m    := image_mor f;
  fact_m_in := image_comparison_monic f;
  fact_comm := image_commutes f
|}.

(* The (regular epi, mono) orthogonal factorization system of a regular
   category. *)
Definition Regular_OFS : OFS (@RegularEpiClass C) (@MonoClass C) := {|
  ofs_e_respects := @regular_epi_respects C;
  ofs_m_respects := @monic_respects C;
  ofs_factor     := @regular_factorization;
  ofs_orth       := @regular_epi_mono_orthogonal C
|}.

End RegularFactorization.
