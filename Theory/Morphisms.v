Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Morphisms.

Context {C : Category}.

Open Scope type_scope.

(* Special classes of morphisms and their relationships: idempotents and
   involutions, sections and retractions (split mono/epi), epimorphisms and
   monomorphisms, and the implications between them. Throughout, the laws use
   the hom-setoid equivalence `≈` rather than Coq's `=`. *)

(* nLab: https://ncatlab.org/nlab/show/idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Idempotence

   An endomorphism `f : x ~> x` is idempotent when `f ∘ f ≈ f` (idem). *)

Class Idempotent `(f : x ~> x) := {
  idem : f ∘ f ≈ f             (* idempotency law: f ∘ f ≈ f *)
}.

(* nLab: https://ncatlab.org/nlab/show/involution
   Wikipedia: https://en.wikipedia.org/wiki/Involution_(mathematics)

   An endomorphism `f : x ~> x` is involutive when it is its own inverse,
   `f ∘ f ≈ id` (invol). *)

Class Involutive `(f : x ~> x) := {
  invol : f ∘ f ≈ id           (* involution law: f ∘ f ≈ id *)
}.

(* For an involution g, precomposition by g is its own inverse, so it may be
   moved across an equation: f ≈ g ∘ h  iff  g ∘ f ≈ h. *)
Lemma flip_invol {x y} (f h : x ~> y) (g : y ~> y) `{@Involutive _ g} :
  f ≈ g ∘ h ↔ g ∘ f ≈ h.
Proof.
  split; intros.
  - rewrite X, comp_assoc, invol; cat.
  - rewrite <- X, comp_assoc, invol; cat.
Qed.

(* nLab: https://ncatlab.org/nlab/show/split+monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Section f` witnesses that `f : x ~> y` is a split monomorphism: it has a
   left inverse `section : y ~> x` with `section ∘ f ≈ id` (section_comp).
   Equivalently, f is a section of the retraction `section`. Every such f is
   monic (sections_are_monic). Note the naming convention used here: a value
   of `Section f` records that f itself splits, the field `section` being the
   accompanying retraction. *)

Class Section `(f : x ~> y) := {
  section : y ~> x;               (* the retraction (left inverse) of f *)
  section_comp : section ∘ f ≈ id (* left inverse law: section ∘ f ≈ id *)
}.

(* nLab: https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Retraction f` witnesses that `f : x ~> y` is a split epimorphism: it has a
   right inverse `retract : y ~> x` with `f ∘ retract ≈ id` (retract_comp).
   Equivalently, f is a retraction of the section `retract`. Every such f is
   epic (retractions_are_epic). As with `Section`, a value of `Retraction f`
   records that f itself splits, the field `retract` being its section. *)

Class Retraction `(f : x ~> y) := {
  retract : y ~> x;               (* the section (right inverse) of f *)
  retract_comp : f ∘ retract ≈ id (* right inverse law: f ∘ retract ≈ id *)
}.

(* nLab: https://ncatlab.org/nlab/show/split+idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   A split idempotent `split_idem : x ~> x` factors through an object y as a
   retraction `split_idem_r : x ~> y` followed by a section
   `split_idem_s : y ~> x`, with `split_idem_s ∘ split_idem_r ≈ split_idem`
   (split_idem_sr) and `split_idem_r ∘ split_idem_s ≈ id` (split_idem_rs). The
   second law forces `split_idem` to be idempotent. The mediating object y is
   exposed as `split_idem_retract`. *)

Class SplitIdempotent {x y : C} := {
  split_idem_retract := y;                  (* the splitting object y *)

  split_idem    : x ~> x;                   (* the idempotent on x *)
  split_idem_r  : x ~> split_idem_retract;  (* retraction x ~> y *)
  split_idem_s  : split_idem_retract ~> x;  (* section y ~> x *)
  split_idem_sr : split_idem_s ∘ split_idem_r ≈ split_idem;
                                            (* s ∘ r ≈ split_idem *)
  split_idem_rs : split_idem_r ∘ split_idem_s ≈ id
                                            (* r ∘ s ≈ id on y *)
}.

(* nLab: https://ncatlab.org/nlab/show/epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   `Epic f` witnesses that `f : x ~> y` is an epimorphism: f is
   right-cancellable, `g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2` for all parallel
   `g1 g2 : y ~> z` (epic). This is exactly `Monic f` in `C^op`. *)

Class Epic {x y} (f : x ~> y) := {
  epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
                                  (* right cancellation: g1∘f ≈ g2∘f → g1 ≈ g2 *)
}.

(* nLab: https://ncatlab.org/nlab/show/monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Monomorphism

   `Monic f` witnesses that `f : x ~> y` is a monomorphism: f is
   left-cancellable, `f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2` for all parallel
   `g1 g2 : z ~> x` (monic). This is exactly `Epic f` in `C^op`. *)

Class Monic {x y} (f : x ~> y) := {
  monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
                                  (* left cancellation: f∘g1 ≈ f∘g2 → g1 ≈ g2 *)
}.

(* A bimorphism is both epic and monic; a split epi is a retraction and a
   split mono is a section (the converse implications above hold via
   retractions_are_epic and sections_are_monic). *)

Definition Bimorphic `(f : x ~> y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : x ~> y) := Retraction f.
Definition SplitMono `(f : x ~> y) := Section f.

Corollary id_idem : ∀ x, Idempotent (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_invol : ∀ x, Involutive (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_monic : ∀ x, Monic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_left in X.
  assumption.
Qed.

Corollary id_epic : ∀ x, Epic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_right in X.
  assumption.
Qed.

#[local] Hint Unfold Bimorphic : core.
#[local] Hint Unfold SplitEpi : core.
#[local] Hint Unfold SplitMono : core.

Section Lemmas.

Variables x y : C.
Variable f : x ~> y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

(* Every split epimorphism is an epimorphism. *)
Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  transitivity (g2 ∘ (f ∘ retract0));
    [ now apply compose_respects |];
  transitivity (g1 ∘ (f ∘ retract0));
    [| now apply compose_respects ].
  reassociate_right.
Qed.

(* Every split monomorphism is a monomorphism. *)
Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  transitivity ((section0 ∘ f) ∘ g2);
    [ now apply compose_respects |];
  transitivity ((section0 ∘ f) ∘ g1);
    [| now apply compose_respects ].
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

(* Epimorphisms are closed under composition. *)
Definition epi_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic f → Epic g → Epic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply epic0, epic1.
  reassociate_left.
Qed.

(* Monomorphisms are closed under composition. *)
Definition monic_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic f → Monic g → Monic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply monic1, monic0.
  reassociate_right.
Qed.

End Morphisms.

#[export] Hint Unfold Bimorphic : core.
#[export] Hint Unfold SplitEpi : core.
#[export] Hint Unfold SplitMono : core.

(* Section/retraction duality: if `section` is the left inverse witnessing
   that f is a split mono, then f exhibits `section` as a split epi. *)
Definition flip_Section {C : Category} `(f : x ~> y)
           (s : @Section C x y f) : @Retraction C y x section.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

(* Dual of flip_Section: if `retract` is the right inverse witnessing that f
   is a split epi, then f exhibits `retract` as a split mono. *)
Definition flip_Retraction {C : Category} `(f : x ~> y)
           (s : @Retraction C x y f) : @Section C y x retract.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
