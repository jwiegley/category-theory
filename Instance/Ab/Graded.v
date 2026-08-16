(** * Graded abelian groups *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.Discrete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §II.4 Exercise 3, printed p. 41 (PDF 51) —
              maclane:II.4:ex3
   nLab:      https://ncatlab.org/nlab/show/graded+object
   Wikipedia: https://en.wikipedia.org/wiki/Graded_(mathematics)

   A graded abelian group is a family of abelian groups, one in each
   degree, and a map of graded abelian groups is a family of
   homomorphisms, one in each degree.  Nothing ties the degrees
   together — no operation carries degree n to degree m — so both the
   objects and the arrows are bare ℕ-indexed families, and every law is
   checked one degree at a time.  Said categorically: the degrees form
   a DISCRETE shape, and the category of graded abelian groups is the
   functor category out of it, Mac Lane's Aᴶ at J discrete and A := Ab.
   That is [Graded_Fun_equiv].

     - [GradedAb]: the direct definition the exercise asks for —
       objects [nat → AbObject], homs the degreewise families of
       [AbHom]s, hom-setoid, identity and composition all componentwise
     - [graded_obj_definitional] … [graded_compose_definitional]: the
       record against [PiCat (fun _ : nat => Ab)] — objects, homs, the
       hom-setoid's RELATION, identity and composition all agree by
       [eq_refl] (the [homset] field itself does not, nor does
       [compose_respects] — see Design note 2)
     - [PiCat_GradedAb_iso]: the two spellings compared in [Cat], by
       functors that are the identity on objects and on arrows
     - [Graded_Fun_equiv]: [([DiscreteCat nat, Ab]) ≅[Cat] GradedAb]
     - [GradedAb_shift]: the degree shift [F ↦ F ∘ S] as an endofunctor,
       with [graded_degree_one] reading a degree-one map as an ordinary
       (degree-preserving) map into the shift
     - witnesses: [Zgroup] and the constant family [ConstZ], the
       degree-dependent endomorphism [graded_deg_mul] (multiplication
       by n in degree n), and [conc0], a group concentrated in degree
       zero, with the shift computing on both

   Design:

   1. THE DISCRETE-SHAPE COLLAPSE IS CONSUMED, NOT REPROVED.  Instance/
      Fun/Discrete.v already proves [Fun_Discrete_PiCat :
      [DiscreteCat A, B] ≅[Cat] PiCat (fun _ : A => B)] for ANY index
      type A — that a transformation over a discrete domain is a bare
      family ([Discrete_Transform], naturality free), and that
      rebuilding a functor from its object function is the identity up
      to identity components ([DiscreteCat_Functor_iso]).  This file
      instantiates it at A := nat, B := Ab and adds only the comparison
      between the indexed product and the hand-written [GradedAb].  No
      transformation over [DiscreteCat nat] is built below; the only
      naturality-shaped goals here are the two coherence conditions of
      the identity-component isomorphisms in [Cat].

   2. WHAT IS DEFINITIONAL, EXACTLY.  [GradedAb] and
      [PiCat (fun _ : nat => Ab)] agree by [eq_refl] on objects
      ([nat → AbObject] against the choice functions
      [∀ _ : nat, obj[Ab]]), on homs, on the hom-setoid's RELATION,
      and on identity and composition — the five Examples below, each
      true by construction, since [GradedAb]'s data were written in
      PiCat's shape; what was MEASURED rather than arranged is the
      divergence: [eq_refl] at the type
      [GradedAb = PiCat (fun _ : nat => Ab)] is rejected, and so are
      the [homset] field itself (only its [equiv] projection agrees),
      [compose_respects], the four category laws and the hom-setoid's
      [Equivalence] witness — separately elaborated proof terms all.
      So the comparison is a genuine pair of functors rather than an
      [eq_refl] — but they are the identity on data, each functor
      obligation closing either by [reflexivity] or by handing back
      the hypothesis, and the natural isomorphisms witnessing both
      round trips have identity components.  Strength note: [≅[Cat]]
      in this tree IS equivalence of categories (Cat's hom-setoid is
      [Functor_Setoid]); the [PiCat] leg of the comparison is in fact
      STRICTER than that — identity on data in both directions —
      while the [Fun_Discrete_PiCat] leg is an equivalence proper
      (its round trip rebuilds a functor from its object function,
      and only one direction is [eq_refl] on objects).

   3. WHY DEGREE-PRESERVING MAPS.  The arrows here are the degree-zero
      maps, which is what makes the category a functor category over a
      discrete shape: a map that raised degrees would have to know how
      to move along ℕ, and a discrete shape supplies no such arrow.
      Maps of higher degree are recovered through [GradedAb_shift]
      rather than lost: a family [∀ n, F n ~> G (S n)] IS a
      [GradedAb]-arrow [F ~> shift G], definitionally
      ([graded_degree_one]).

   4. INDEX-GENERIC MACHINERY, ℕ-SPECIFIC STATEMENT.  Both DONORS are
      generic in the index type; THIS FILE's own definitions are not —
      [GradedAb], both comparison functors and the iso all hardcode
      [nat], as the exercise asks.  A ℤ-graded or multigraded variant
      would reuse the same two donors unchanged but would RESTATE this
      file's definitions at the other index (with their obligations);
      what it would not need to redo is the discrete-shape collapse or
      the indexed-product category, which is where the actual content
      lives.

   5. NAME COLLISION, DISAMBIGUATED.  Monad/Graded.v is about GRADED
      MONADS — a monad indexed by a monoid of effect grades, with
      multiplication [T i ◯ T j ⟹ T (i ⊗ j)].  That is an unrelated
      concept: it grades an endofunctor by a monoid and its grades
      interact, whereas the objects here are families over a discrete
      index whose degrees never interact.  The two share only the
      English word. *)

(** ** The category of graded abelian groups *)

(* Objects are ℕ-indexed families of abelian groups; an arrow is a
   homomorphism in each degree; everything is checked degreewise. *)
Program Definition GradedAb : Category := {|
  obj     := nat → AbObject;
  hom     := fun F G => ∀ n : nat, F n ~{Ab}~> G n;
  homset  := fun F G =>
    {| equiv := fun f g => ∀ n : nat, f n ≈ g n |};
  id      := fun F n => @id Ab (F n);
  compose := fun F G H f g n => f n ∘ g n
|}.
Next Obligation.
  intros F G; constructor.
  - intros f n; reflexivity.
  - intros f g Hfg n; symmetry; exact (Hfg n).
  - intros f g h H1 H2 n.
    transitivity (g n); [ exact (H1 n) | exact (H2 n) ].
Qed.
Next Obligation.
  (* [Ab]'s hom-setoid unfolds to [CMonHom_Setoid], so the ambient
     category of the [Proper] instance has to be named. *)
  intros F G H f f' Hf g g' Hg n.
  exact (@compose_respects Ab (F n) (G n) (H n) _ _ (Hf n) _ _ (Hg n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_left (f n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_right (f n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc (f n) (g n) (h n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc_sym (f n) (g n) (h n)).
Qed.

(** ** The measurement against the indexed product *)

(* The five data fields of [GradedAb] and of the indexed product over
   the constant family agree on the nose.  These are equalities of
   TYPES and of the data carried by the two records — the library's
   convertibility exception to the "never [=] on morphisms" rule — and
   they are what makes the comparison functors below the identity. *)

Example graded_obj_definitional :
  obj[GradedAb] = obj[PiCat (fun _ : nat => Ab)] := eq_refl.

Example graded_hom_definitional (F G : obj[GradedAb]) :
  (F ~{GradedAb}~> G) = (F ~{PiCat (fun _ : nat => Ab)}~> G) := eq_refl.

Example graded_equiv_definitional (F G : obj[GradedAb]) :
  @equiv _ (@homset GradedAb F G)
    = @equiv _ (@homset (PiCat (fun _ : nat => Ab)) F G) := eq_refl.

Example graded_id_definitional (F : obj[GradedAb]) :
  @id GradedAb F = @id (PiCat (fun _ : nat => Ab)) F := eq_refl.

Example graded_compose_definitional (F G H : obj[GradedAb]) :
  @compose GradedAb F G H
    = @compose (PiCat (fun _ : nat => Ab)) F G H := eq_refl.

(** ** The two spellings compared in Cat *)

(* Both directions are the identity on objects and on arrows.  Since
   the data fields coincide, the two functor laws are [reflexivity] and
   respectfulness is the hypothesis handed back degreewise. *)
Program Definition GradedAb_PiCat :
  GradedAb ⟶ PiCat (fun _ : nat => Ab) := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

Program Definition PiCat_GradedAb :
  PiCat (fun _ : nat => Ab) ⟶ GradedAb := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(* Oriented towards [GradedAb], so that it composes on the left of the
   donor isomorphism below. *)
Program Definition PiCat_GradedAb_iso :
  PiCat (fun _ : nat => Ab) ≅[Cat] GradedAb := {|
  to   := PiCat_GradedAb;
  from := GradedAb_PiCat
|}.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.

(** ** Mac Lane §II.4 Exercise 3 *)

(* Graded abelian groups are the diagrams of shape "the discrete
   category on the degrees" in Ab.  The whole content of the discrete
   shape — naturality is free, a functor is its object function — is
   Instance/Fun/Discrete.v's [Fun_Discrete_PiCat], consumed here at
   A := nat and B := Ab; this file contributes the second leg. *)
Definition Graded_Fun_equiv :
  ([DiscreteCat nat, Ab]) ≅[Cat] GradedAb :=
  iso_compose PiCat_GradedAb_iso Fun_Discrete_PiCat.

(** ** The degree shift *)

(* Reindexing along the successor: an endofunctor, since the arrows are
   degreewise and reindexing them needs no more than reindexing the
   objects. *)
Program Definition GradedAb_shift : GradedAb ⟶ GradedAb := {|
  fobj := fun F n => F (S n);
  fmap := fun F G f n => f (S n)
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg (S n)).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(* Maps of degree one are not outside the category: they are ordinary
   arrows into the shift, definitionally. *)
Example graded_degree_one (F G : obj[GradedAb]) :
  (∀ n : nat, F n ~{Ab}~> G (S n))
    = (F ~{GradedAb}~> fobj[GradedAb_shift] G) := eq_refl.

(** ** Witnesses *)

(* ℤ as an abelian group, through the ring layer: Instance/Rng.v's
   [ring_ab] applied to Theory/Algebra/Rig.v's axiom-free [Int_Ring],
   the same donor Instance/Ab/Monoidal.v uses for its unit object. *)
Definition Zgroup : AbObject := ring_ab Int_Ring.

(* Multiplication by a fixed integer, as an endomorphism of ℤ.  The
   [Proper] obligation of the underlying setoid morphism needs no
   proof: ℤ's setoid equivalence is Leibniz equality ([Z_eqT]), so
   elaboration discharges it. *)
Program Definition Zmul_hom (k : Z) : Zgroup ~{Ab}~> Zgroup := {|
  cmon_map := {| morphism := fun m => Z.mul k m |}
|}.
Next Obligation.
  intros k; simpl; exact (Z.mul_0_r k).
Qed.
Next Obligation.
  intros k a b; simpl; exact (Z.mul_add_distr_l k a b).
Qed.

(* The constant graded group ℤ in every degree. *)
Definition ConstZ : obj[GradedAb] := fun _ => Zgroup.

(* A genuinely graded endomorphism: multiplication by n in degree n.
   Its components differ from degree to degree — PROVED below
   ([graded_deg_mul_not_constant]), not asserted: no single
   homomorphism h has [graded_deg_mul] as its constant family. *)
Definition graded_deg_mul : ConstZ ~{GradedAb}~> ConstZ :=
  fun n => Zmul_hom (Z.of_nat n).

Lemma graded_deg_mul_not_constant
      (h : Zgroup ~{Ab}~> Zgroup) :
  (∀ n : nat, graded_deg_mul n ≈ h) → False.
Proof.
  intro Hc.
  pose proof (Hc 0%nat 5%Z) as H0.
  pose proof (Hc 1%nat 5%Z) as H1.
  simpl in H0, H1.
  rewrite <- H0 in H1.
  discriminate H1.
Qed.

Example graded_deg_mul_at_3 :
  cmon_map (graded_deg_mul 3%nat) 5%Z = 15%Z := eq_refl.

Example graded_deg_mul_at_0 :
  cmon_map (graded_deg_mul 0%nat) 5%Z = 0%Z := eq_refl.

(* Shifting relabels the degrees: the component in degree 2 of the
   shifted map is the component in degree 3 of the original. *)
Example shift_deg_mul_at_2 :
  cmon_map (fmap[GradedAb_shift] graded_deg_mul 2%nat) 5%Z = 15%Z := eq_refl.

(* A group concentrated in degree zero — the standard example of a
   graded object that is not constant. *)
Definition conc0 : obj[GradedAb] :=
  fun n => match n with
           | O   => Zgroup
           | S _ => Ab_trivial
           end.

Example conc0_at_0 : conc0 0%nat = Zgroup := eq_refl.

(* Shifting a group concentrated in degree zero leaves nothing behind:
   every degree of the shift is the trivial group. *)
Example shift_conc0_at_0 :
  fobj[GradedAb_shift] conc0 0%nat = Ab_trivial := eq_refl.

Example shift_conc0_at_3 :
  fobj[GradedAb_shift] conc0 3%nat = Ab_trivial := eq_refl.

(* Iterating the shift is reindexing twice, on the nose. *)
Example shift_twice (F : obj[GradedAb]) (n : nat) :
  fobj[GradedAb_shift] (fobj[GradedAb_shift] F) n = F (S (S n)) := eq_refl.
