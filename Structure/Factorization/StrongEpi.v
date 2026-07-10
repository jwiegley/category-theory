Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.

Generalizable All Variables.

(* Strong epimorphisms.

   nLab:      https://ncatlab.org/nlab/show/strong+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   An epimorphism f : x ~> y is *strong* when it is left orthogonal to every
   monomorphism: for every monic m : u ~> v, every commuting square

            p
        x ----> u
        |       |
      f |       | m
        v       v
        y ----> v
            q

   (that is, m ∘ p ≈ q ∘ f) has a unique diagonal filler d : y ~> u with
   d ∘ f ≈ p and m ∘ d ≈ q. Strong epimorphisms sit between the split and
   the plain epimorphisms: every split epimorphism is strong
   (split_epi_strong), the class is closed under composition
   (strong_epi_compose) and under right cancellation — if f ∘ g is strong
   then so is f (strong_epi_cancel) — and a morphism that is both a strong
   epimorphism and a monomorphism is an isomorphism
   (strong_epi_mono_is_iso). These are exactly the closure properties
   enjoyed by the left class of an orthogonal factorization system, of
   which (strong epi, mono) is the motivating example. *)

Record StrongEpi {C : Category} {x y : C} (f : x ~> y) := {
  strong_epic : Epic f;
  strong_lift {u v : C} (m : u ~> v) : Monic m → f ⫫ m
}.

(* Strong epimorphisms are closed under composition: the epic parts compose
   by epi_compose, and the lifting parts compose because the left
   orthogonality class is closed under composition (ortho_left_compose). *)
Lemma strong_epi_compose {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi f → StrongEpi g → StrongEpi (f ∘ g).
Proof.
  intros [Hfe Hfl] [Hge Hgl].
  constructor.
  - exact (epi_compose Hfe Hge).
  - intros u v m Hm.
    apply ortho_left_compose.
    + exact (Hgl _ _ m Hm).
    + exact (Hfl _ _ m Hm).
Qed.

(* Right cancellation: if a composite f ∘ g is a strong epimorphism, then so
   is its left factor f. The epic part right-cancels through the composite;
   a lifting problem for f against a monic m is whiskered with g into a
   lifting problem for f ∘ g, solved there, and the filler is checked
   against the original square by cancelling m. *)
Lemma strong_epi_cancel {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi (f ∘ g) → StrongEpi f.
Proof.
  intros [He Hl].
  constructor.
  - (* Epic f: from g1 ∘ f ≈ g2 ∘ f conclude g1 ∘ (f ∘ g) ≈ g2 ∘ (f ∘ g)
       and cancel the composite. *)
    constructor.
    intros w g1 g2 Hgg.
    apply (@epic C x z (f ∘ g) He w g1 g2).
    rewrite !comp_assoc.
    rewrite Hgg.
    reflexivity.
  - (* f ⫫ m for every monomorphism m. *)
    intros u v m Hm.
    constructor.
    intros p q comm.
    (* Whiskering the square with g yields a square over f ∘ g. *)
    assert (comm' : m ∘ (p ∘ g) ≈ q ∘ (f ∘ g)). {
      rewrite !comp_assoc.
      rewrite comm.
      reflexivity.
    }
    pose proof (@ortho_lift _ _ _ _ _ (f ∘ g) m (Hl _ _ m Hm)
                  (p ∘ g) q comm') as U.
    destruct (unique_property U) as [Ue Um].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* d ∘ f ≈ p, by cancelling the monomorphism m:
           m ∘ (d ∘ f) ≈ (m ∘ d) ∘ f ≈ q ∘ f ≈ m ∘ p. *)
        apply (@monic C u v m Hm).
        rewrite comp_assoc.
        rewrite Um.
        rewrite comm.
        reflexivity.
      * exact Um.
    + intros d' [Hd'f Hmd'].
      (* Any filler of the f-square also fills the whiskered square, so it
         coincides with the lift obtained there. *)
      apply (uniqueness U).
      split.
      * rewrite comp_assoc.
        rewrite Hd'f.
        reflexivity.
      * exact Hmd'.
Qed.

(* Every split epimorphism is strong: it is epic (retractions_are_epic),
   and the section provides the filler p ∘ retract directly, with the monic
   on the right forcing both the lower triangle and uniqueness. *)
Lemma split_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  Retraction f → StrongEpi f.
Proof.
  intros Hr.
  constructor.
  - exact (retractions_are_epic _ _ f Hr).
  - intros u v m Hm.
    constructor.
    intros p q comm.
    destruct Hr as [r rcomp].
    unshelve refine {| unique_obj := p ∘ r |}.
    + split.
      * (* (p ∘ r) ∘ f ≈ p, by cancelling m:
           m ∘ ((p ∘ r) ∘ f) ≈ ((q ∘ f) ∘ r) ∘ f ≈ q ∘ f ≈ m ∘ p. *)
        apply (@monic C u v m Hm).
        rewrite !comp_assoc.
        rewrite comm.
        rewrite <- (comp_assoc q f r).
        rewrite rcomp.
        rewrite id_right.
        reflexivity.
      * (* m ∘ (p ∘ r) ≈ (q ∘ f) ∘ r ≈ q ∘ id ≈ q *)
        rewrite comp_assoc.
        rewrite comm.
        rewrite <- comp_assoc.
        rewrite rcomp.
        apply id_right.
    + intros d' [Hd'f Hmd'].
      (* Fillers are unique because m is monic: m ∘ (p ∘ r) ≈ q ≈ m ∘ d'. *)
      apply (@monic C u v m Hm).
      rewrite Hmd'.
      rewrite comp_assoc.
      rewrite comm.
      rewrite <- comp_assoc.
      rewrite rcomp.
      apply id_right.
Qed.

(* A morphism that is both a strong epimorphism and a monomorphism is an
   isomorphism: lifting the identity square f ∘ id ≈ id ∘ f against f
   itself (which is monic by hypothesis) produces a two-sided inverse. *)
Lemma strong_epi_mono_is_iso {C : Category} {x y : C} (f : x ~> y) :
  StrongEpi f → Monic f → IsIsomorphism f.
Proof.
  intros [He Hl] Hm.
  assert (comm : f ∘ id ≈ id ∘ f). {
    cat.
  }
  pose proof (@ortho_lift _ _ _ _ _ f f (Hl _ _ f Hm) id id comm) as U.
  destruct (unique_property U) as [Ul Ur].
  (* Ul : unique_obj U ∘ f ≈ id (left inverse);
     Ur : f ∘ unique_obj U ≈ id (right inverse). *)
  exact {| two_sided_inverse := unique_obj U;
           is_right_inverse  := Ur;
           is_left_inverse   := Ul |}.
Qed.
