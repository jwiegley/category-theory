Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Instance.Fact.

Generalizable All Variables.

(* Orthogonal factorization systems.

   nLab:      https://ncatlab.org/nlab/show/orthogonal+factorization+system
              https://ncatlab.org/nlab/show/factorization+system
   Wikipedia: https://en.wikipedia.org/wiki/Factorization_system

   An (E, M)-factorization of a morphism f : x ~> y, for two classes of
   morphisms E and M on C, is a middle object together with an E-morphism
   followed by an M-morphism composing to f:

        x --e--> mid --m--> y,        m ∘ e ≈ f.

   An orthogonal factorization system (OFS) on C consists of two such
   classes E and M, each respecting the hom-setoid equivalence ≈, such that
   every morphism carries an (E, M)-factorization and every E-morphism is
   orthogonal to every M-morphism in the sense of Theory/Orthogonality.v:
   each commuting square with an E-morphism on the left and an M-morphism
   on the right has a unique diagonal filler.

   The classical consequences developed here:

   - [factorization_unique]: any two (E, M)-factorizations of the same
     morphism are connected by an isomorphism of middle objects commuting
     with both legs, so factorizations are unique up to isomorphism.

   - [ofs_m_char] / [ofs_e_char]: a morphism orthogonal on the appropriate
     side against one whole class belongs to the other class, granted an
     explicit closure hypothesis discussed at the statements.

   - [factorization_fact_iso]: the comparison isomorphism, read inside the
     factorization category Fact f of Instance/Fact.v, connects the two
     factorizations as objects of Fact f. *)

(* An (E, M)-factorization of f : x ~> y: a middle object [fact_mid], a
   left leg [fact_e] belonging to E, and a right leg [fact_m] belonging to
   M, with [fact_m ∘ fact_e ≈ f]. *)
Record Factorization {C : Category} {x y : C} (f : x ~> y)
  (E M : MorphismClass C) := {
  fact_mid  : C;
  fact_e    : x ~> fact_mid;
  fact_e_in : E _ _ fact_e;
  fact_m    : fact_mid ~> y;
  fact_m_in : M _ _ fact_m;
  fact_comm : fact_m ∘ fact_e ≈ f
}.

Arguments fact_mid  {C x y f E M} _.
Arguments fact_e    {C x y f E M} _.
Arguments fact_e_in {C x y f E M} _.
Arguments fact_m    {C x y f E M} _.
Arguments fact_m_in {C x y f E M} _.
Arguments fact_comm {C x y f E M} _.

(* An orthogonal factorization system: two morphism classes closed under ≈,
   a factorization of every morphism, and orthogonality of E against M. *)
Class OFS {C : Category} (E M : MorphismClass C) := {
  ofs_e_respects {x y} (f g : x ~> y) : f ≈ g → E x y f → E x y g;
  ofs_m_respects {x y} (f g : x ~> y) : f ≈ g → M x y f → M x y g;
  ofs_factor {x y} (f : x ~> y) : Factorization f E M;
  ofs_orth {a b x y} (e : a ~> b) (m : x ~> y) :
    E a b e → M x y m → e ⫫ m
}.

Section FactorizationSystem.

Context {C : Category}.
Context {E M : MorphismClass C}.

(* Two factorizations of one morphism bound the same commuting square: the
   two composites are both ≈ f, hence ≈ each other. *)
Lemma factorization_square {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘ fact_e F1.
Proof.
  rewrite (fact_comm F2).
  rewrite (fact_comm F1).
  reflexivity.
Qed.

(* The comparison morphism between two factorizations of f: the unique
   diagonal filler of the square [fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘
   fact_e F1], obtained from (fact_e F1) ⫫ (fact_m F2). *)
Lemma factorization_lift {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ d : fact_mid F1 ~> fact_mid F2,
    (d ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ d ≈ fact_m F1).
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  exact (unique_obj U; unique_property U).
Qed.

(* Any two comparison morphisms between the same pair of factorizations
   agree: both fill the same orthogonality square, whose filler is unique. *)
Lemma factorization_lift_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) (d d' : fact_mid F1 ~> fact_mid F2)
  (de : d ∘ fact_e F1 ≈ fact_e F2) (md : fact_m F2 ∘ d ≈ fact_m F1)
  (d'e : d' ∘ fact_e F1 ≈ fact_e F2) (md' : fact_m F2 ∘ d' ≈ fact_m F1) :
  d ≈ d'.
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  assert (H1 : unique_obj U ≈ d). {
    apply (uniqueness U).
    split.
    - exact de.
    - exact md.
  }
  assert (H2 : unique_obj U ≈ d'). {
    apply (uniqueness U).
    split.
    - exact d'e.
    - exact md'.
  }
  rewrite <- H1.
  exact H2.
Qed.

(* Uniqueness of factorizations: any two (E, M)-factorizations of the same
   morphism have isomorphic middle objects, through a comparison morphism
   commuting with both legs.  The forward comparison and its inverse are the
   two diagonal fillers, and both round trips agree with the identity by
   uniqueness of the filler of each self-square. *)
Theorem factorization_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ i : fact_mid F1 ≅ fact_mid F2,
    (to i ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ to i ≈ fact_m F1).
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  exists {| to := d; from := d'; iso_to_from := dd'; iso_from_to := d'd |}.
  split.
  - exact de.
  - exact md.
Qed.

(* The easy direction of the characterization of M: every M-morphism is
   right orthogonal to every E-morphism.  This is [ofs_orth] restated with
   the arguments in the order matching [ofs_m_char] below. *)
Corollary ofs_m_orth {O : OFS E M} {x y : C} (m : x ~> y) :
  M x y m → ∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m.
Proof.
  intros Hm a b e He.
  exact (ofs_orth e m He Hm).
Qed.

(* Dually, every E-morphism is left orthogonal to every M-morphism. *)
Corollary ofs_e_orth {O : OFS E M} {x y : C} (e : x ~> y) :
  E x y e → ∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m.
Proof.
  intros He a b m Hm.
  exact (ofs_orth e m He Hm).
Qed.

(* Characterization of M, hypothesis form.  Classically, m belongs to M as
   soon as e ⫫ m for every e ∈ E.  The argument factors m as m' ∘ e' and
   shows that e' is an isomorphism, exhibiting m (up to ≈) as an M-morphism
   precomposed with an isomorphism — so it needs M to be closed under
   precomposition with isomorphisms.  Nothing in the four fields of [OFS]
   supplies that closure, so the statement takes it as the explicit
   hypothesis [Mclosed] rather than silently strengthening the class. *)
Theorem ofs_m_char {O : OFS E M}
  (Mclosed : ∀ (x y z : C) (i : x ~> y) (m : y ~> z),
      IsIsomorphism i → M y z m → M x z (m ∘ i))
  {x y : C} (m : x ~> y) :
  (∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m) → M x y m.
Proof.
  intros H.
  destruct (ofs_factor m) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m ∘ id ≈ m' ∘ e' through e' ⫫ m. *)
  assert (comm1 : m ∘ id ≈ m' ∘ e'). {
    rewrite id_right.
    symmetry.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m (H _ _ e' He') id m' comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e' ≈ id,  mD : m ∘ unique_obj U ≈ m'. *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* Both e' ∘ (unique_obj U) and id fill the self-square of (e', m'). *)
  assert (Hu1 : unique_obj Uself ≈ e' ∘ unique_obj U). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite dE.
      cat.
    - rewrite comp_assoc.
      rewrite comm'.
      exact mD.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (ed : e' ∘ unique_obj U ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism e'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := ed;
             is_left_inverse   := dE |}.
  }
  apply (ofs_m_respects (m' ∘ e') m comm').
  exact (Mclosed _ _ _ e' m' Hiso Hm').
Qed.

(* Characterization of E, hypothesis form, dual to [ofs_m_char]: e belongs
   to E as soon as e ⫫ m for every m ∈ M, granted that E is closed under
   postcomposition with isomorphisms ([Eclosed]). *)
Theorem ofs_e_char {O : OFS E M}
  (Eclosed : ∀ (x y z : C) (e : x ~> y) (i : y ~> z),
      IsIsomorphism i → E x y e → E x z (i ∘ e))
  {x y : C} (e : x ~> y) :
  (∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m) → E x y e.
Proof.
  intros H.
  destruct (ofs_factor e) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m' ∘ e' ≈ id ∘ e through e ⫫ m'. *)
  assert (comm1 : m' ∘ e' ≈ id ∘ e). {
    rewrite id_left.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e m' (H _ _ m' Hm') e' id comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e ≈ e',  mD : m' ∘ unique_obj U ≈ id. *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* Both (unique_obj U) ∘ m' and id fill the self-square of (e', m'). *)
  assert (Hu1 : unique_obj Uself ≈ unique_obj U ∘ m'). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite comm'.
      exact dE.
    - rewrite comp_assoc.
      rewrite mD.
      cat.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (dm : unique_obj U ∘ m' ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism m'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := mD;
             is_left_inverse   := dm |}.
  }
  apply (ofs_e_respects (m' ∘ e') e comm').
  exact (Eclosed _ _ _ e' m' Hiso He').
Qed.

(* Every (E, M)-factorization of f is in particular an object of the
   factorization category Fact f of Instance/Fact.v: keep the middle object
   and the two legs, discarding the class memberships. *)
Definition factorization_to_fact {x y : C} (f : x ~> y)
  (F1 : Factorization f E M) : Fact f.
Proof.
  refine (fact_mid F1; (fact_e F1; (fact_m F1; _))).
  symmetry.
  exact (fact_comm F1).
Defined.

(* The comparison morphism of [factorization_unique] is precisely a
   morphism of Fact f — its two triangles are Fact's two commuting
   conditions — and Fact's homs compare underlying C-morphisms only, so the
   two round-trip identities transfer.  Hence two (E, M)-factorizations of
   f are isomorphic as objects of Fact f. *)
Theorem factorization_fact_iso {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  factorization_to_fact f F1 ≅[Fact f] factorization_to_fact f F2.
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  unshelve refine {| to := _; from := _ |}.
  - refine (d; _).
    split.
    + exact de.
    + exact md.
  - refine (d'; _).
    split.
    + exact d'e.
    + exact md'.
  - exact dd'.
  - exact d'd.
Qed.

End FactorizationSystem.
