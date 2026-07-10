Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

(* Orthogonality of morphisms (the unique lifting property).

   nLab:      https://ncatlab.org/nlab/show/orthogonality
   Wikipedia: https://en.wikipedia.org/wiki/Lifting_property

   A morphism e : a ~> b is (left) orthogonal to m : x ~> y, written e ⫫ m,
   when every commuting square

            u
        a ----> x
        |       |
      e |       | m
        v       v
        b ----> y
            v

   (that is, m ∘ u ≈ v ∘ e) has a unique diagonal filler d : b ~> x with
   d ∘ e ≈ u and m ∘ d ≈ v. Orthogonality is the uniqueness-strengthened
   form of the weak lifting property that underlies weak factorization
   systems; with the uniqueness clause it characterizes the two classes of
   an orthogonal factorization system (nLab: orthogonal factorization
   system). Here we record the notion itself together with the closure
   properties of the left class that need no (co)limits: isomorphisms are
   orthogonal to everything (on either side), and the left class is closed
   under composition and under retracts in the arrow category.

   Stability of the left class under cobase change (pushout) needs the
   pullback/pushout toolkit and lives there: [ortho_left_cobase_change] in
   Theory/Morphisms/Stability.v. *)

(* The ∃!-with-∧ shape below mirrors [ump_pullbacks] in Structure/Pullback.v:
   [∃!] is the Type-valued [Unique] record of Lib/Setoid.v, and [∧] is the
   Type-valued conjunction, so fillers can be extracted and used in
   definitions. *)

Class Orthogonal {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) := {
  ortho_lift {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
    ∃! d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v)
}.

Notation "e ⫫ m" := (Orthogonal e m) (at level 70) : category_theory_scope.

(* Any isomorphism is left orthogonal to every morphism: the filler of a
   square (u, v) over e is u ∘ e⁻¹, and any filler d' recovers it via
   d' ≈ d' ∘ e ∘ e⁻¹ ≈ u ∘ e⁻¹. *)
Lemma iso_ortho_left {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) :
  IsIsomorphism e → e ⫫ m.
Proof.
  intros He.
  constructor; intros u v comm.
  unshelve refine {| unique_obj := u ∘ @two_sided_inverse _ _ _ e He |}.
  - split.
    + (* (u ∘ e⁻¹) ∘ e ≈ u *)
      rewrite <- comp_assoc.
      rewrite (@is_left_inverse _ _ _ e He).
      cat.
    + (* m ∘ (u ∘ e⁻¹) ≈ v *)
      rewrite comp_assoc.
      rewrite comm.
      rewrite <- comp_assoc.
      rewrite (@is_right_inverse _ _ _ e He).
      cat.
  - intros d' [Hd'e Hmd'].
    (* u ∘ e⁻¹ ≈ d' *)
    rewrite <- Hd'e.
    rewrite <- comp_assoc.
    rewrite (@is_right_inverse _ _ _ e He).
    cat.
Qed.

(* Dually, any isomorphism is right orthogonal to every morphism: the filler
   is m⁻¹ ∘ v, and uniqueness follows by cancelling m on the left. *)
Lemma iso_ortho_right {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) :
  IsIsomorphism m → e ⫫ m.
Proof.
  intros Hm.
  constructor; intros u v comm.
  unshelve refine {| unique_obj := @two_sided_inverse _ _ _ m Hm ∘ v |}.
  - split.
    + (* (m⁻¹ ∘ v) ∘ e ≈ u *)
      rewrite <- comp_assoc.
      rewrite <- comm.
      rewrite comp_assoc.
      rewrite (@is_left_inverse _ _ _ m Hm).
      cat.
    + (* m ∘ (m⁻¹ ∘ v) ≈ v *)
      rewrite comp_assoc.
      rewrite (@is_right_inverse _ _ _ m Hm).
      cat.
  - intros d' [Hd'e Hmd'].
    (* m⁻¹ ∘ v ≈ d', by composing m⁻¹ with m ∘ d' ≈ v *)
    rewrite <- Hmd'.
    rewrite comp_assoc.
    rewrite (@is_left_inverse _ _ _ m Hm).
    cat.
Qed.

(* The left class is closed under composition: a square over e2 ∘ e1 lifts
   first through e1 (against the top-right corner v ∘ e2) and then through
   e2; uniqueness threads back the same way. *)
Lemma ortho_left_compose {C : Category} {a b c x y : C}
  (e1 : a ~> b) (e2 : b ~> c) (m : x ~> y) :
  e1 ⫫ m → e2 ⫫ m → (e2 ∘ e1) ⫫ m.
Proof.
  intros H1 H2.
  constructor; intros u v comm.
  (* The outer square, reassociated as a square over e1. *)
  assert (comm1 : m ∘ u ≈ (v ∘ e2) ∘ e1). {
    rewrite <- comp_assoc.
    exact comm.
  }
  pose proof (@ortho_lift _ _ _ _ _ e1 m H1 u (v ∘ e2) comm1) as U1.
  destruct (unique_property U1) as [U1e U1m].
  (* The lift through e1 forms a square over e2; lift again. *)
  pose proof (@ortho_lift _ _ _ _ _ e2 m H2 (unique_obj U1) v U1m) as U2.
  destruct (unique_property U2) as [U2e U2m].
  unshelve refine {| unique_obj := unique_obj U2 |}.
  - split.
    + (* d2 ∘ (e2 ∘ e1) ≈ u *)
      rewrite comp_assoc.
      rewrite U2e.
      exact U1e.
    + exact U2m.
  - intros d [Hde Hdm].
    (* Any filler d of the outer square: d ∘ e2 fills the e1-square, so
       d ∘ e2 ≈ d1 by e1-uniqueness; then d fills the e2-square, so d ≈ d2
       by e2-uniqueness. *)
    apply (uniqueness U2); split.
    + symmetry.
      apply (uniqueness U1); split.
      * rewrite <- comp_assoc.
        exact Hde.
      * rewrite comp_assoc.
        rewrite Hdm.
        reflexivity.
    + exact Hdm.
Qed.

(* The left class is closed under retracts in the arrow category: if e' is a
   retract of e — witnessed by a section (ia, ib) and a retraction (ra, rb)
   of arrows with ra ∘ ia ≈ id, rb ∘ ib ≈ id, e ∘ ia ≈ ib ∘ e' and
   e' ∘ ra ≈ rb ∘ e — then e ⫫ m entails e' ⫫ m: a square over e' is
   whiskered by (ra, rb) into a square over e, lifted there, and the filler
   is restricted along ib. *)
Lemma ortho_left_retract {C : Category} {a b a' b' x y : C}
  (e : a ~> b) (e' : a' ~> b') (m : x ~> y)
  (ia : a' ~> a) (ib : b' ~> b) (ra : a ~> a') (rb : b ~> b')
  (ra_ia : ra ∘ ia ≈ id) (rb_ib : rb ∘ ib ≈ id)
  (sq_i : e ∘ ia ≈ ib ∘ e') (sq_r : e' ∘ ra ≈ rb ∘ e) :
  e ⫫ m → e' ⫫ m.
Proof.
  intros He.
  constructor; intros u v comm.
  (* The whiskered square over e commutes:
     m ∘ (u ∘ ra) ≈ (v ∘ e') ∘ ra ≈ v ∘ (rb ∘ e) ≈ (v ∘ rb) ∘ e. *)
  assert (comm0 : m ∘ (u ∘ ra) ≈ (v ∘ rb) ∘ e). {
    rewrite comp_assoc.
    rewrite comm.
    rewrite <- comp_assoc.
    rewrite sq_r.
    rewrite comp_assoc.
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e m He (u ∘ ra) (v ∘ rb) comm0) as U.
  destruct (unique_property U) as [Ue Um].
  unshelve refine {| unique_obj := unique_obj U ∘ ib |}.
  - split.
    + (* (d ∘ ib) ∘ e' ≈ u, via ib ∘ e' ≈ e ∘ ia *)
      rewrite <- comp_assoc.
      rewrite <- sq_i.
      rewrite comp_assoc.
      rewrite Ue.
      rewrite <- comp_assoc.
      rewrite ra_ia.
      cat.
    + (* m ∘ (d ∘ ib) ≈ v *)
      rewrite comp_assoc.
      rewrite Um.
      rewrite <- comp_assoc.
      rewrite rb_ib.
      cat.
  - intros g [Hge Hgm].
    (* Any filler g of the e'-square: g ∘ rb fills the e-square, so
       g ∘ rb ≈ d by e-uniqueness, whence g ≈ g ∘ rb ∘ ib ≈ d ∘ ib. *)
    assert (Hgrb : unique_obj U ≈ g ∘ rb). {
      apply (uniqueness U); split.
      - (* (g ∘ rb) ∘ e ≈ u ∘ ra, via rb ∘ e ≈ e' ∘ ra *)
        rewrite <- comp_assoc.
        rewrite <- sq_r.
        rewrite comp_assoc.
        rewrite Hge.
        reflexivity.
      - rewrite comp_assoc.
        rewrite Hgm.
        reflexivity.
    }
    rewrite Hgrb.
    rewrite <- comp_assoc.
    rewrite rb_ib.
    cat.
Qed.
