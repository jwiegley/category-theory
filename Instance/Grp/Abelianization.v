Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The commutator subgroup and the abelianization functor

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.3
    (printed p. 14) and §I.4 (printed pp. 16–17)
    [maclane:I.3:construction3, maclane:I.4:construction2]: the
    commutator subgroup [G, G] is functorial in G — homomorphisms carry
    commutators to commutators — and the factor-commutator group
    G ↦ G/[G, G] is the abelianization functor Grp ⟶ Ab, with the
    projections p_G : G → G/[G, G] a natural transformation from the
    identity functor.
    nLab: https://ncatlab.org/nlab/show/abelianization

    THE SETOID QUOTIENT.  In this library a quotient group needs no new
    carrier: G/[G, G] is G's carrier under the COARSER equivalence
    a ≈' b iff a·b⁻¹ lies in the commutator subgroup ([abel_eq]).  The
    commutator subgroup itself is the inductively generated closure
    [InCommutator]: commutators, the unit, products, inverses, and a
    setoid-respect constructor (generation must be ≈-saturated for the
    quotient relation to be well defined over setoid carriers).  The
    quotient relation is an equivalence by the group laws, the
    operations respect it by NORMALITY — the conjugate of a commutator
    element is again one, an instance of the single induction
    [hom_commutator] (every homomorphism pushes [InCommutator] forward)
    applied to the conjugation homomorphisms [Grp_conj] of
    Instance/Grp/TwoFunctors.v — and commutativity of the quotient is
    the constructor [inc_comm] itself: (a·b)·(b·a)⁻¹ IS a commutator.

    THE TWO FUNCTORS.  [Commutator_Functor : Grp ⟶ Grp] restricts each
    homomorphism to the subgroup (the sigma carrier over
    [InCommutator], compared on elements, as Instance/Grp/Center.v does
    for the center); [Abelianization_Functor : Grp ⟶ Ab] sends G to
    [AbelianizationOb G] — same carrier, coarser setoid, commutative by
    construction — and a homomorphism to itself, [hom_commutator]
    making it respect the quotient relations.  [Ab_to_Grp : Ab ⟶ Grp]
    is the evident inclusion (an abelian group is a group), built here
    since no Ab → Grp bridge existed in tree.

    THE NATURAL PROJECTION ([abel_projection]): the family
    p_G : G → G/[G, G] as a [Transform] from Id[Grp] to
    Ab_to_Grp ◯ Abelianization_Functor.  Because the quotient reuses
    the carrier, every component is the identity function and both
    naturality squares hold by reflexivity of the coarser relation —
    Mac Lane's square p_H ∘ f ≈ f' ∘ p_G with no computation left.

    TOWARD THE ADJUNCTION (the issue's optional stretch, left to a
    future change tying into Construction/Reflective.v): the germ is
    [hom_to_abelian_kills] — a homomorphism from G into (the underlying
    group of) an abelian group sends every commutator element to the
    unit, by a second induction over the same generation — which is
    exactly why such homomorphisms descend along p_G; the adjunction
    Abelianization ⊣ Ab_to_Grp packages that descent and is not built
    here.

    SCOPE OF THE QUOTIENT, disclosed.  The issue hoped the quotient
    infrastructure could be kept reusable over an abstract normal
    subgroup (it would also serve maclane:I.5:ex5 and
    maclane:I.7:prop1).  Here it is SPECIALIZED to [InCommutator]: the
    five congruence proofs below consume only the normal-subgroup
    interface (≈-saturation, unit, closure under product and inverse,
    normality), so a generic [NormalSubgroup]-quotient is extractable
    by abstraction over exactly those five facts — but it is not
    extracted, and the tree currently holds three unshared quotient
    constructions (Instance/Ab.v's [ab_coset_eq], Instance/Grp/Epi.v's
    [Grp_Coset], and this one).  Unifying them is future work.

    NON-DEGENERACY, witnessed: [commutator_GrpTwo_proper] (in an
    abelian group the subgroup omits the nonidentity),
    [commutator_S3_nontrivial] (in S₃ it contains a nonidentity
    element), and [abelianization_S3_nontrivial] (the quotient of the
    nonabelian S₃ does not collapse: the reflection stays apart from
    the unit, seen through the sign character). *)

(** ** Commutators and the generated subgroup *)

Definition gcomm (G : GrpObject) (g h : carrier G) : carrier G :=
  grp_mul G (grp_mul G (grp_mul G g h) (grp_inv G g)) (grp_inv G h).

(* The commutator subgroup, as an ≈-saturated inductive generation. *)
Inductive InCommutator (G : GrpObject) : carrier G → Type :=
  | inc_comm (g h : carrier G) : InCommutator (gcomm G g h)
  | inc_unit : InCommutator (grp_unit G)
  | inc_mul (a b : carrier G) :
      InCommutator a → InCommutator b →
      InCommutator (grp_mul G a b)
  | inc_inv (a : carrier G) :
      InCommutator a → InCommutator (grp_inv G a)
  | inc_resp (a b : carrier G) :
      a ≈ b → InCommutator a → InCommutator b.

Arguments inc_comm {G} g h.
Arguments inc_unit {G}.
Arguments inc_mul {G a b} _ _.
Arguments inc_inv {G a} _.
Arguments inc_resp {G a b} _ _.

(* Every homomorphism pushes the commutator subgroup forward: the one
   induction that serves functoriality, normality (via [Grp_conj]),
   and the descent germ below. *)
Lemma hom_commutator {G H : GrpObject} (f : GrpHom G H)
  (x : carrier G) : InCommutator G x → InCommutator H (grp_map f x).
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - apply (inc_resp (a := gcomm H (grp_map f g) (grp_map f h))).
    + unfold gcomm.
      rewrite <- !(grp_map_inv f).
      rewrite <- !(grp_map_mul f).
      reflexivity.
    + apply inc_comm.
  - exact (inc_resp (symmetry (grp_map_unit f)) inc_unit).
  - exact (inc_resp (symmetry (grp_map_mul f a b)) (inc_mul IHa IHb)).
  - exact (inc_resp (symmetry (grp_map_inv f a)) (inc_inv IHa)).
  - exact (inc_resp (proper_morphism (grp_map f) a b Hab) IHa).
Qed.

(* Normality, as the conjugation instance. *)
Lemma conj_commutator (G : GrpObject) (t x : carrier G) :
  InCommutator G x →
  InCommutator G (grp_mul G (grp_mul G t x) (grp_inv G t)).
Proof. exact (hom_commutator (Grp_conj G t) x). Qed.

(* Homomorphisms into abelian groups kill commutator elements — the
   descent germ for the (future) adjunction. *)
Lemma hom_to_abelian_kills {G H : GrpObject}
  (comm : ∀ a b : carrier H, grp_mul H a b ≈ grp_mul H b a)
  (f : GrpHom G H) (x : carrier G) :
  InCommutator G x → grp_map f x ≈ grp_unit H.
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - unfold gcomm.
    rewrite !(grp_map_mul f), !(grp_map_inv f).
    rewrite (grp_mul_assoc H (grp_map f g) (grp_map f h)
               (grp_inv H (grp_map f g))).
    rewrite (comm (grp_map f h) (grp_inv H (grp_map f g))).
    rewrite <- (grp_mul_assoc H (grp_map f g) (grp_inv H (grp_map f g))
                  (grp_map f h)).
    rewrite (grp_mul_inv_r H (grp_map f g)).
    rewrite (grp_mul_unit_l H (grp_map f h)).
    apply (grp_mul_inv_r H).
  - apply (grp_map_unit f).
  - rewrite (grp_map_mul f a b).
    rewrite IHa, IHb.
    apply (grp_mul_unit_l H).
  - rewrite (grp_map_inv f a).
    rewrite IHa.
    apply (grp_inv_unit H).
  - now rewrite <- (proper_morphism (grp_map f) a b Hab).
Qed.

(** ** The quotient relation *)

Definition abel_eq (G : GrpObject) (a b : carrier G) : Type :=
  InCommutator G (grp_mul G a (grp_inv G b)).

(* The finer relation implies the coarser one. *)
Lemma abel_eq_of_eq (G : GrpObject) (a b : carrier G) :
  a ≈ b → abel_eq G a b.
Proof.
  intro Hab; unfold abel_eq.
  apply (inc_resp (a := grp_unit G)); [| exact inc_unit ].
  rewrite Hab.
  symmetry; apply (grp_mul_inv_r G).
Qed.

Lemma abel_eq_refl (G : GrpObject) (a : carrier G) : abel_eq G a a.
Proof. apply abel_eq_of_eq; reflexivity. Qed.

Lemma abel_eq_sym (G : GrpObject) (a b : carrier G) :
  abel_eq G a b → abel_eq G b a.
Proof.
  unfold abel_eq; intro K.
  apply (inc_resp (a := grp_inv G (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    reflexivity.
  - exact (inc_inv K).
Qed.

Lemma abel_eq_trans (G : GrpObject) (a b c : carrier G) :
  abel_eq G a b → abel_eq G b c → abel_eq G a c.
Proof.
  unfold abel_eq; intros K1 K2.
  apply (inc_resp
           (a := grp_mul G (grp_mul G a (grp_inv G b))
                   (grp_mul G b (grp_inv G c)))).
  - rewrite (grp_mul_assoc G a (grp_inv G b)
               (grp_mul G b (grp_inv G c))).
    rewrite <- (grp_mul_assoc G (grp_inv G b) b (grp_inv G c)).
    rewrite (grp_mul_inv_l G b).
    rewrite (grp_mul_unit_l G (grp_inv G c)).
    reflexivity.
  - exact (inc_mul K1 K2).
Qed.

(* The operations respect the quotient relation; multiplication and
   inversion are where normality earns its keep. *)
Lemma abel_eq_mul (G : GrpObject) (a a' b b' : carrier G) :
  abel_eq G a a' → abel_eq G b b' →
  abel_eq G (grp_mul G a b) (grp_mul G a' b').
Proof.
  unfold abel_eq; intros K1 K2.
  apply (inc_resp
           (a := grp_mul G
                   (grp_mul G (grp_mul G a (grp_mul G b (grp_inv G b')))
                      (grp_inv G a))
                   (grp_mul G a (grp_inv G a')))).
  - rewrite (grp_inv_mul G a' b').
    rewrite (grp_mul_assoc G
               (grp_mul G a (grp_mul G b (grp_inv G b')))
               (grp_inv G a) (grp_mul G a (grp_inv G a'))).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a (grp_inv G a')).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_l G (grp_inv G a')).
    rewrite (grp_mul_assoc G a (grp_mul G b (grp_inv G b'))
               (grp_inv G a')).
    rewrite (grp_mul_assoc G b (grp_inv G b') (grp_inv G a')).
    rewrite (grp_mul_assoc G a b
               (grp_mul G (grp_inv G b') (grp_inv G a'))).
    reflexivity.
  - exact (inc_mul (conj_commutator G a _ K2) K1).
Qed.

Lemma abel_eq_inv (G : GrpObject) (a a' : carrier G) :
  abel_eq G a a' → abel_eq G (grp_inv G a) (grp_inv G a').
Proof.
  unfold abel_eq; intros K.
  apply (inc_resp
           (a := grp_mul G
                   (grp_mul G (grp_inv G a)
                      (grp_inv G (grp_mul G a (grp_inv G a'))))
                   (grp_inv G (grp_inv G a)))).
  - rewrite (grp_inv_mul G a (grp_inv G a')).
    rewrite (grp_inv_inv G a').
    rewrite (grp_inv_inv G a).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a' (grp_inv G a)).
    rewrite (grp_mul_assoc G (grp_mul G (grp_inv G a) a')
               (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_r G (grp_mul G (grp_inv G a) a')).
    reflexivity.
  - exact (conj_commutator G (grp_inv G a) _ (inc_inv K)).
Qed.

(** ** The abelianization of a group *)

Program Definition AbelianizationOb (G : GrpObject) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := carrier G
                    ; is_setoid := {| equiv := abel_eq G |} |};
    cmon_zero := grp_unit G;
    cmon_plus := grp_mul G
  |};
  ab_neg := grp_inv G
|}.
Next Obligation.
  intro G; equivalence.
  - apply abel_eq_refl.
  - now apply abel_eq_sym.
  - now apply (abel_eq_trans G x y).
Qed.
Next Obligation.
  intros G a a' Ha b b' Hb; now apply abel_eq_mul.
Qed.
Next Obligation.
  intros G a b c; apply abel_eq_of_eq, grp_mul_assoc.
Qed.
Next Obligation.
  (* Commutativity IS the generating constructor. *)
  intros G a b; unfold abel_eq.
  apply (inc_resp (a := gcomm G a b)); [| apply inc_comm ].
  unfold gcomm.
  rewrite (grp_inv_mul G b a).
  rewrite (grp_mul_assoc G (grp_mul G a b) (grp_inv G a) (grp_inv G b)).
  reflexivity.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a a' Ha; now apply abel_eq_inv.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_inv_l.
Qed.

(** ** The commutator subgroup, as a functor Grp ⟶ Grp *)

Definition commutator_carrier (G : GrpObject) : Type :=
  { x : carrier G & InCommutator G x }.

Definition mk_comm (G : GrpObject) (x : carrier G)
  (Hx : InCommutator G x) : commutator_carrier G :=
  existT (fun x : carrier G => InCommutator G x) x Hx.

Program Definition CommutatorGrp (G : GrpObject) : GrpObject := {|
  grp_setoid := {| carrier := commutator_carrier G
                 ; is_setoid := {| equiv := fun a b => `1 a ≈ `1 b |} |};
  grp_unit := mk_comm G (grp_unit G) inc_unit;
  grp_mul := fun a b =>
    mk_comm G (grp_mul G (`1 a) (`1 b)) (inc_mul (`2 a) (`2 b));
  grp_inv := fun a => mk_comm G (grp_inv G (`1 a)) (inc_inv (`2 a))
|}.
Next Obligation. intro G; equivalence; now transitivity (`1 y). Qed.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

Program Definition Commutator_Functor : Grp ⟶ Grp := {|
  fobj := CommutatorGrp;
  fmap := fun G H (f : GrpHom G H) =>
    {| grp_map := {| morphism := fun a =>
         mk_comm H (grp_map f (`1 a)) (hom_commutator f (`1 a) (`2 a)) |}
    |}
|}.
Next Obligation.
  intros G H f a b Hab; simpl in *.
  exact (proper_morphism (grp_map f) _ _ Hab).
Qed.
Next Obligation. intros G H f; simpl; apply (grp_map_unit f). Qed.
Next Obligation. intros G H f a b; simpl; apply (grp_map_mul f). Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  exact (Hfg (`1 a)).
Qed.
Next Obligation. intros G a; simpl; reflexivity. Qed.
Next Obligation. intros G H K f g a; simpl; reflexivity. Qed.

(** ** The inclusion Ab ⟶ Grp *)

Program Definition Ab_to_GrpOb (A : AbObject) : GrpObject := {|
  grp_setoid := cmon_setoid A;
  grp_unit := cmon_zero A;
  grp_mul := cmon_plus A;
  grp_inv := ab_neg A
|}.
Next Obligation. intros A a b c; apply cmon_plus_assoc. Qed.
Next Obligation. intros A a; apply cmon_plus_zero_l. Qed.
Next Obligation. intros A a; apply ab_neg_left. Qed.

Program Definition Ab_to_Grp : Ab ⟶ Grp := {|
  fobj := Ab_to_GrpOb;
  fmap := fun A B (f : AbHom A B) =>
    {| grp_map := cmon_map f
     ; grp_map_unit := cmon_map_zero f
     ; grp_map_mul := cmon_map_plus f |}
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** The abelianization functor *)

Program Definition Abelianization_Functor : Grp ⟶ Ab := {|
  fobj := AbelianizationOb;
  fmap := fun G H (f : GrpHom G H) =>
    {| cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
     |}
|}.
Next Obligation.
  (* respect for the coarser relations: push the witness forward *)
  intros G H f a b Hab; simpl in *.
  unfold abel_eq in *.
  apply (inc_resp (a := grp_map f (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_map_mul f a (grp_inv G b)).
    rewrite (grp_map_inv f b).
    reflexivity.
  - exact (hom_commutator f _ Hab).
Qed.
Next Obligation.
  intros G H f; simpl.
  apply abel_eq_of_eq, (grp_map_unit f).
Qed.
Next Obligation.
  intros G H f a b; simpl.
  apply abel_eq_of_eq, (grp_map_mul f).
Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  apply abel_eq_of_eq; exact (Hfg a).
Qed.
Next Obligation. intros G a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G H K f g a; simpl; apply abel_eq_refl. Qed.

(** ** The natural projection *)

(* The component at G: the identity function, read from the fine
   setoid into the coarse one. *)
Program Definition abel_proj (G : GrpObject) :
  G ~{Grp}~> Ab_to_GrpOb (AbelianizationOb G) := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation. intros G a b Hab; apply abel_eq_of_eq, Hab. Qed.
Next Obligation. intros G; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G a b; simpl; apply abel_eq_refl. Qed.

(* Mac Lane's naturality square p_H ∘ f ≈ f' ∘ p_G, with both legs the
   identity on elements: reflexivity of the coarser relation. *)
Program Definition abel_projection :
  @Id Grp ⟹ Ab_to_Grp ◯ Abelianization_Functor := {|
  transform := abel_proj
|}.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.

(** ** Non-degeneracy witnesses *)

(* In an abelian group the commutator subgroup misses the nonidentity:
   [InCommutator] does not collapse to the total predicate. *)
Lemma commutator_GrpTwo_proper :
  InCommutator GrpTwo grp_two_one → False.
Proof.
  intro K.
  pose proof (hom_to_abelian_kills GrpTwo_abelian
                (@grp_hom_id GrpTwo) grp_two_one K) as E.
  exact E.
Qed.

(* In S₃ the subgroup is nontrivial: the commutator of the two
   generators is a member and is not the identity. *)
Lemma commutator_S3_nontrivial :
  InCommutator S3 (gcomm S3 S3_r S3_s) *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - apply inc_comm.
  - intro E; vm_compute in E; discriminate E.
Qed.

(* The abelianization of the nonabelian S₃ does not collapse: the
   reflection stays apart from the unit in the quotient, because the
   sign character kills commutators but not the reflection. *)
Lemma abelianization_S3_nontrivial :
  abel_eq S3 S3_s s3_unit → False.
Proof.
  intro K.
  pose proof (hom_to_abelian_kills GrpTwo_abelian s3_sign _ K) as E.
  vm_compute in E.
  exact E.
Qed.
