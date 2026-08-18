Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Associative K-algebras, and the underlying K-module

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, §III.1, printed p. 59, Exercise 1 — the tensor algebra
          of a vector space and the exterior algebra, each as a universal
          arrow (maclane:III.1:ex1); the roster of free constructions on
          printed p. 56 (maclane:III.1:remark2)
    Book: Mac Lane, ibid., §I.8, printed p. 28 — Ab-categories and the
          hom-rings that make an algebra an algebra
    nLab:      https://ncatlab.org/nlab/show/associative+algebra
    nLab:      https://ncatlab.org/nlab/show/tensor+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

    WHY A SECOND CATEGORY OF ALGEBRAS.  Instance/Rng/Algebras.v already
    carries [KAlg K], and that category is the right home for the
    polynomial ring, for the coslice reading of Mac Lane §II.6 Exercise 1,
    and for everything else whose objects happen to be commutative.  It
    is NOT a possible home for the tensor algebra or the exterior
    algebra, and the obstruction is a field of its record rather than a
    matter of taste: [KAlgObject] carries

      kalg_comm : forall a b, rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a

    so every object of [KAlg K] is commutative.  The tensor algebra T(V)
    is not — Instance/Vect/TensorAlgebra.v's [tensor_not_commutative]
    proves it for a concrete V — and the exterior algebra Λ(V) is
    anticommutative rather than commutative, with
    [ext_anticomm_nontrivial] proving there that the two orders of a
    product of generators genuinely differ.  So a category of algebras
    that does not demand commutativity has to exist before §III.1
    Exercise 1 can be stated at all, and this file supplies it.

    That is the shape Instance/Rng/Algebras.v names and declines: its own
    deferral list says that a non-commutative K-algebra is one in which
    "the structure map is required to land in the CENTRE, a condition
    that is automatic exactly when the target is commutative", and adds
    "No centre-valued variant is built here".  [AAlgObject]'s
    [aalg_central] field IS that condition, so this file is the
    centre-valued variant.  What is NOT claimed is anything about what
    would happen to the universal property of T(V) or Λ(V) if it were
    stated over [KAlg K] instead: no such statement is formed here, and
    the reason for the choice is the two proved non-commutativity results
    above, not a claim about a construction that is not made.

    WHAT REPLACES COMMUTATIVITY.  A K-algebra in the classical sense is a
    K-MODULE with a bilinear associative multiplication.  Presented ring
    first, that is a ring A together with a homomorphism u : K → A whose
    image is CENTRAL in A — centrality is exactly what makes the induced
    action r·a := u(r)·a bilinear, and it is exactly what commutativity
    of A was silently supplying in [KAlgObject].  So [AAlgObject K] and
    [KAlgObject K] have three fields each, and they differ in exactly one:
    the ring and the structure map are shared, and centrality of the
    structure map's image stands where commutativity of the ring stood.
    Morphisms are unchanged — a ring
    homomorphism commuting with the two structure maps — which is what
    lets [KAlg_AAlg] below be full and faithful with no proof obligation
    on the hom side.

    THE TWO CATEGORIES ARE GENUINELY DIFFERENT, and this is proved rather
    than asserted.  [UT2] is the ring of upper-triangular 2×2 integer
    matrices, an object of [AAlg Int_CRng] by way of the scalar diagonal;
    [UT2_not_commutative] exhibits two of its elements whose products
    disagree in both orders, and [AAlg_not_all_commutative] packages the
    consequence.  Without such a witness the reader would have no way to
    tell whether [AAlg K] is a proper generalization of [KAlg K] or a
    re-spelling of it, and the tree contained no non-commutative
    [RingObject] before this file — Instance/Mod/Tensor.v enumerates the
    closed ones ("[Int_Ring], [Q_Ring], [Zero_Ring], [F2_Ring],
    [FracRing] and [CRingOb], all commutative") in the course of deferring
    a result for want of exactly such an object.  That quoted list
    predates Instance/Rng/Polynomial.v and so omits [PolyRing]/[ZPoly];
    the conclusion is unaffected, [PolyRing] being commutative by
    construction (its [pe_mul_comm] constructor).  [UT2] is a closed
    non-commutative [RingObject] and so supplies what that file records as
    missing; whether it makes that file's collapse strict is NOT
    investigated here, and no claim about it is made.

    THE UNDERLYING K-MODULE, and why it is the interesting functor.  An
    associative K-algebra is a K-module for r·a := u(r)·a, and a
    K-algebra map is K-linear.  [AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)]
    packages that, and it is the functor to which the tensor algebra is a
    universal arrow — "T(V) is the free associative K-algebra on the
    K-module V" is precisely the statement that V has a universal arrow to
    [AAlg_Forget_Mod].  Each of the four module laws is one rig law
    conjugated by one preservation law of u, and none of them consumes
    centrality; centrality is consumed downstream, by the algebras that
    are built rather than by the module structure that is read off.

    WHAT IS DELIVERED.

      - [AAlgObject], [AAlgHom], [AAlg K]: associative unital K-algebras
        over a commutative base ring K, with morphisms the ring
        homomorphisms under K;
      - [AAlg_Forget : AAlg K ⟶ Sets] and
        [AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)], the underlying set and
        the underlying K-module;
      - [AAlgLinear], K-linear maps from a K-module into an algebra, with
        the setoid comparing underlying maps, and
        [aalg_linear_of_module_hom] identifying a module homomorphism into
        the underlying module of A with such a map;
      - [KAlg_AAlg : KAlg K ⟶ AAlg K], full and faithful, exhibiting the
        commutative algebras inside the associative ones;
      - [UT2] with [UT2_AAlg], [UT2_not_commutative],
        [AAlg_not_all_commutative] and [UT2_not_in_KAlg]: the inclusion is
        proper, proved;
      - [Base_AAlg]: the base ring is an algebra over itself, so [AAlg K]
        is inhabited for every K with no witness-hunting.

    WHAT IS NOT DELIVERED.  No comparison of [AAlg K] with a category of
    monoid objects in [RMod (`1 K)] — the tree has no monoidal structure
    on module categories (Instance/Mod/Tensor.v builds the tensor product
    of two modules as a universal element but no bifunctor, and says so).
    No opposite-algebra involution, no tensor product of algebras, no
    graded algebras, and in particular no category of graded
    anticommutative algebras — Instance/Vect/TensorAlgebra.v records why
    that last one matters and what it costs.  No claim that [KAlg_AAlg]
    is REPLETE or that its image is closed under any construction. *)

(** ** Objects *)

(* An associative unital K-algebra: a ring, a homomorphism out of the base
   ring, and centrality of the image.  The three fields correspond one for
   one to [KAlgObject]'s, with centrality in place of commutativity. *)
Record AAlgObject (K : CRng) := {
  aalg_ring : RingObject;
  aalg_unit : `1 K ~{Rng}~> aalg_ring;
  aalg_central : ∀ k a,
    rig_mul aalg_ring (rig_map aalg_unit k) a
      ≈ rig_mul aalg_ring a (rig_map aalg_unit k)
}.

Arguments aalg_ring {K} _.
Arguments aalg_unit {K} _.
Arguments aalg_central {K} _ _ _.

(* A morphism of K-algebras is a ring homomorphism commuting with the two
   structure maps.  The orientation of the triangle is [KAlgHom]'s, hence
   [Coslice]'s (Construction/Slice.v:171). *)
Definition AAlgHom {K : CRng} (A B : AAlgObject K) : Type :=
  ∃ f : aalg_ring A ~{Rng}~> aalg_ring B, aalg_unit B ≈ f ∘ aalg_unit A.

(* Two algebra morphisms are equal when their underlying ring
   homomorphisms are; the triangle proof is irrelevant, as in [KAlgHom]. *)
Program Definition AAlgHom_Setoid {K : CRng} (A B : AAlgObject K) :
  Setoid (AAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  intros K A B.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Qed.

Lemma aalg_id_triangle {K : CRng} (A : AAlgObject K) :
  aalg_unit A ≈ id ∘ aalg_unit A.
Proof. now rewrite id_left. Qed.

Lemma aalg_comp_triangle {K : CRng} {A B C : AAlgObject K}
      (f : AAlgHom B C) (g : AAlgHom A B) :
  aalg_unit C ≈ (`1 f ∘ `1 g) ∘ aalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Qed.

Program Definition AAlg (K : CRng) : Category := {|
  obj     := AAlgObject K;
  hom     := @AAlgHom K;
  homset  := @AAlgHom_Setoid K;
  id      := fun A => (id; aalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; aalg_comp_triangle f g)
|}.
Next Obligation.
  intros K A B C f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.

(** ** The underlying set *)

Program Definition AAlg_Forget (K : CRng) : AAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (aalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(** ** The underlying K-module

    Each of the four module laws is one rig law of A conjugated by one
    preservation law of the structure map: distributivity on the left is
    [rig_distr_l] alone, distributivity on the right spends
    [rig_map_add], associativity of the action spends [rig_map_mul], and
    unitality spends [rig_map_one].  Centrality is not consumed. *)

Program Definition AAlg_RMod {K : CRng} (A : AAlgObject K)
  : RModObject (`1 K) := {|
  rm_ab   := ring_ab (aalg_ring A);
  rm_smul := fun r a => rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) a
|}.
Next Obligation.
  intros K A r r' Hr a a' Ha; simpl.
  apply rig_mul_respects; [| exact Ha ].
  now apply (proper_morphism (rig_map (aalg_unit A))).
Qed.
Next Obligation. intros K A r m n; simpl; apply rig_distr_l. Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_add (aalg_unit A) r s).
  apply rig_distr_r.
Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_mul (aalg_unit A) r s).
  apply rig_mul_assoc.
Qed.
Next Obligation.
  intros K A m; simpl.
  rewrite (rig_map_one (aalg_unit A)).
  apply rig_mul_one_l.
Qed.

(* A K-algebra map is K-linear: the triangle turns [f (u_A r · a)] into
   [u_B r · f a]. *)
Program Definition AAlg_RModHom {K : CRng} {A B : AAlgObject K}
  (f : AAlgHom A B) : RModHom (AAlg_RMod A) (AAlg_RMod B) := {|
  rm_hom := {| cmon_map := rig_map (`1 f);
               cmon_map_zero := rig_map_zero (`1 f);
               cmon_map_plus := rig_map_add (`1 f) |}
|}.
Next Obligation.
  intros K A B f r m; simpl.
  rewrite (rig_map_mul (`1 f)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 f r).
Qed.

Program Definition AAlg_Forget_Mod (K : CRng) : AAlg K ⟶ RMod (`1 K) := {|
  fobj := @AAlg_RMod K;
  fmap := fun A B f => AAlg_RModHom f
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(* The two forgetful functors agree on carriers, definitionally: the
   underlying set of the underlying module IS the underlying set.  (This
   is the convertibility exception — an equation between setoids, not
   between morphisms.) *)
Example aalg_forget_agree (K : CRng) (A : AAlg K) :
  fobj[RMod_Forget (`1 K)] (fobj[AAlg_Forget_Mod K] A) = fobj[AAlg_Forget K] A
  := eq_refl.

(** ** K-linear maps into an algebra

    The data a universal property of the tensor algebra consumes: an
    additive map out of a K-module whose interaction with the action is
    multiplication by the image of the scalar.  This is exactly a
    morphism into [AAlg_RMod A] with the packaging removed, and
    [aalg_linear_of_module_hom] and [module_hom_of_aalg_linear] are the
    two passages, mutually inverse on the underlying map by [eq_refl]. *)

Record AAlgLinear {K : CRng} (V : RModObject (`1 K)) (A : AAlgObject K) := {
  alin_map :> SetoidMorphism (cmon_setoid V) (rig_setoid (aalg_ring A));

  alin_add : ∀ v w,
    alin_map (cmon_plus V v w)
      ≈ rig_add (aalg_ring A) (alin_map v) (alin_map w);
  alin_smul : ∀ r v,
    alin_map (rm_smul V r v)
      ≈ rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) (alin_map v)
}.

Arguments alin_map {K V A} _.
Arguments alin_add {K V A} _ _ _.
Arguments alin_smul {K V A} _ _ _.

Program Definition AAlgLinear_Setoid {K : CRng} (V : RModObject (`1 K))
  (A : AAlgObject K) : Setoid (AAlgLinear V A) := {|
  equiv := fun f g => ∀ v, alin_map f v ≈ alin_map g v
|}.
Next Obligation.
  intros K V A.
  constructor.
  - intros f v; reflexivity.
  - intros f g Hfg v; symmetry; apply Hfg.
  - intros f g h Hfg Hgh v; transitivity (alin_map g v);
      [ apply Hfg | apply Hgh ].
Qed.

(* An additive map is zero at zero, by cancellation in the target's
   additive group. *)
Lemma alin_zero {K : CRng} {V : RModObject (`1 K)} {A : AAlgObject K}
  (f : AAlgLinear V A) :
  alin_map f (cmon_zero V) ≈ rig_zero (aalg_ring A).
Proof.
  apply (ab_cancel_l (ring_ab (aalg_ring A)) (alin_map f (cmon_zero V))).
  simpl.
  rewrite <- (alin_add f (cmon_zero V) (cmon_zero V)).
  rewrite (proper_morphism (alin_map f) _ _
             (cmon_plus_zero_l V (cmon_zero V))).
  symmetry; apply rig_add_zero_r.
Qed.

Definition aalg_linear_of_module_hom {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) : AAlgLinear V A := {|
  alin_map   := cmon_map (rm_hom h);
  alin_add   := cmon_map_plus (rm_hom h);
  alin_smul  := rm_map_smul h
|}.

Program Definition module_hom_of_aalg_linear {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) : RModHom V (AAlg_RMod A) := {|
  rm_hom := {| cmon_map := alin_map f;
               cmon_map_zero := alin_zero f;
               cmon_map_plus := alin_add f |};
  rm_map_smul := alin_smul f
|}.

(* Both passages leave the underlying map alone, on the nose. *)
Example aalg_linear_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) :
  alin_map (aalg_linear_of_module_hom (module_hom_of_aalg_linear f))
    = alin_map f := eq_refl.

Example module_hom_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) :
  cmon_map (rm_hom (module_hom_of_aalg_linear (aalg_linear_of_module_hom h)))
    = cmon_map (rm_hom h) := eq_refl.

(* The identity map of an algebra IS K-linear from its own underlying
   module: both laws hold by [reflexivity], the action of [AAlg_RMod]
   being multiplication by the image of the scalar.  This is the cheapest
   non-trivial linear map available, and it is uniform in A. *)
Program Definition alin_id {K : CRng} (A : AAlgObject K)
  : AAlgLinear (AAlg_RMod A) A := {|
  alin_map := setoid_morphism_id
|}.
Next Obligation. intros K A v w; simpl; reflexivity. Qed.
Next Obligation. intros K A r v; simpl; reflexivity. Qed.

Example alin_id_computes {K : CRng} (A : AAlgObject K)
  (a : carrier (rig_setoid (aalg_ring A))) :
  alin_map (alin_id A) a = a := eq_refl.

(* Postcomposition with an algebra map carries a linear map to a linear
   map — the action on which the universal property is stated. *)
Program Definition alin_compose {K : CRng} {V : RModObject (`1 K)}
  {A B : AAlgObject K} (g : AAlgHom A B) (f : AAlgLinear V A)
  : AAlgLinear V B := {|
  alin_map := setoid_morphism_compose (rig_map (`1 g)) (alin_map f)
|}.
Next Obligation.
  intros K V A B g f v w; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_add f v w)).
  apply (rig_map_add (`1 g)).
Qed.
Next Obligation.
  intros K V A B g f r v; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_smul f r v)).
  rewrite (rig_map_mul (`1 g)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 g r).
Qed.

(** ** Commutative algebras sit inside associative ones

    The inclusion needs no data on morphisms: [KAlgHom] and [AAlgHom] are
    the same type once the objects are matched, so fullness and
    faithfulness are the identity implication.  On objects, commutativity
    supplies centrality. *)

Definition AAlg_of_KAlg {K : CRng} (A : KAlgObject K) : AAlgObject K := {|
  aalg_ring := kalg_ring A;
  aalg_unit := kalg_unit A;
  aalg_central := fun k a => kalg_comm A (rig_map (kalg_unit A) k) a
|}.

Program Definition KAlg_AAlg (K : CRng) : KAlg K ⟶ AAlg K := {|
  fobj := @AAlg_of_KAlg K;
  fmap := fun A B f => (`1 f; `2 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

#[export] Instance KAlg_AAlg_Faithful (K : CRng) : Faithful (KAlg_AAlg K).
Proof. constructor; intros A B f g E; exact E. Qed.

#[export] Instance KAlg_AAlg_Full (K : CRng) : Full (KAlg_AAlg K).
Proof.
  unshelve econstructor.
  - intros A B g; exact (`1 g; `2 g).
  - intros A B g a; simpl; reflexivity.
Qed.

(** ** The base ring is an algebra over itself

    So [AAlg K] is inhabited for every K, with no witness-hunting: the
    structure map is the identity and centrality IS K's own
    commutativity. *)
Definition Base_AAlg (K : CRng) : AAlgObject K := {|
  aalg_ring := `1 K;
  aalg_unit := @id Rng (`1 K);
  aalg_central := fun k a => `2 K k a
|}.

Example Base_AAlg_unit (K : CRng) (k : carrier (rig_setoid (`1 K))) :
  rig_map (aalg_unit (Base_AAlg K)) k = k := eq_refl.

(** * A non-commutative witness: upper-triangular 2×2 integer matrices

    The matrix [[a, b], [0, c]] is carried as the triple (a, b, c).  This
    is built by hand rather than read off Instance/Matr.v because that
    file's [Matr] is a CATEGORY of matrices, not a ring: its objects are
    the naturals and there is no [RingObject] anywhere in its output.
    The tree contained no non-commutative [RingObject] at all before this
    file — Instance/Mod/Tensor.v's deferral list says so in terms — so
    the witness is new, not a re-packaging. *)

Definition ut2 : Type := (Z * Z * Z)%type.

Definition ut2_eqT (x y : ut2) : Type := x = y.

Lemma ut2_eqT_Equivalence : Equivalence ut2_eqT.
Proof.
  constructor; unfold ut2_eqT.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition ut2_setoid_object : SetoidObject := {|
  carrier := ut2;
  is_setoid := {| equiv := ut2_eqT; setoid_equiv := ut2_eqT_Equivalence |}
|}.

Definition ut2_zero : ut2 := (0, 0, 0)%Z.
Definition ut2_one : ut2 := (1, 0, 1)%Z.

Definition ut2_add (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') => ((a + a')%Z, (b + b')%Z, (c + c')%Z)
  end.

Definition ut2_neg (x : ut2) : ut2 :=
  match x with (a, b, c) => ((- a)%Z, (- b)%Z, (- c)%Z) end.

(* [[a,b],[0,c]] · [[a',b'],[0,c']] = [[a a', a b' + b c'], [0, c c']] *)
Definition ut2_mul (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') =>
      ((a * a')%Z, (a * b' + b * c')%Z, (c * c')%Z)
  end.

(* The scalar diagonal r ↦ [[r, 0], [0, r]]. *)
Definition ut2_scal (r : Z) : ut2 := (r, 0, r)%Z.

Lemma ut2_eq3 (a b c a' b' c' : Z) :
  a = a' → b = b' → c = c' → ((a, b, c) : ut2) = (a', b', c').
Proof. intros H1 H2 H3; now subst. Qed.

Ltac ut2_crunch :=
  cbv beta iota delta [ut2_eqT ut2_add ut2_neg ut2_mul ut2_zero ut2_one ut2_scal];
  apply ut2_eq3; ring.

Ltac ut2_1 := intros [[? ?] ?]; ut2_crunch.
Ltac ut2_2 := intros [[? ?] ?] [[? ?] ?]; ut2_crunch.
Ltac ut2_3 := intros [[? ?] ?] [[? ?] ?] [[? ?] ?]; ut2_crunch.

Lemma ut2_add_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_add.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Lemma ut2_mul_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_mul.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2_Rig : RigObject := {|
  rig_setoid := ut2_setoid_object;
  rig_zero := ut2_zero;
  rig_add := ut2_add;
  rig_one := ut2_one;
  rig_mul := ut2_mul;
  rig_add_respects := ut2_add_respects;
  rig_mul_respects := ut2_mul_respects
|}.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_2. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.

Lemma ut2_neg_respects : Proper (ut2_eqT ==> ut2_eqT) ut2_neg.
Proof. intros x y Hxy; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2 : RingObject := {|
  ring_rig := UT2_Rig;
  ring_neg := ut2_neg;
  ring_neg_respects := ut2_neg_respects
|}.
Next Obligation. ut2_1. Qed.

(* The scalar diagonal ℤ → UT2, whose image is central because ℤ is
   commutative. *)
(* The respectfulness witness is written out as a pointwise term rather
   than left to instance resolution — the engineering finding recorded in
   Theory/Universal/Element.v, where resolving [Proper] at a concrete
   setoid pinned a carrier universe. *)
Definition ut2_scal_proper
  : Proper (@equiv _ (is_setoid Z_setoid_object)
              ==> @equiv _ (is_setoid ut2_setoid_object)) ut2_scal :=
  fun r s H => f_equal (fun z : Z => ((z, 0, z) : ut2)%Z) H.

Definition ut2_scal_morphism
  : SetoidMorphism (is_setoid Z_setoid_object) (is_setoid ut2_setoid_object) :=
  {| morphism := ut2_scal; proper_morphism := ut2_scal_proper |}.

(* Stated over plain [Z] rather than over [carrier Int_Ring]: the [ring]
   tactic reads the ring structure off the syntactic type of the
   equation, and it does not see through [carrier].  The obligations
   below then close by conversion. *)
Lemma ut2_scal_add (a b : Z) :
  ut2_scal (a + b)%Z = ut2_add (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_add; apply ut2_eq3; ring. Qed.

Lemma ut2_scal_mul (a b : Z) :
  ut2_scal (a * b)%Z = ut2_mul (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_mul; apply ut2_eq3; ring. Qed.

Program Definition ut2_scalar : Int_Ring ~{Rng}~> UT2 := {|
  rig_map := ut2_scal_morphism
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_add a b). Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_mul a b). Qed.

Lemma ut2_scalar_central : ∀ (k : Z) (a : ut2),
  rig_mul UT2 (rig_map ut2_scalar k) a ≈ rig_mul UT2 a (rig_map ut2_scalar k).
Proof. intros k [[x y] z]; ut2_crunch. Qed.

Definition UT2_AAlg : AAlgObject Int_CRng :=
  Build_AAlgObject Int_CRng UT2 ut2_scalar ut2_scalar_central.

(* The two matrix units E11 and E12 do not commute: E11·E12 = E12 while
   E12·E11 = 0. *)
Definition ut2_e11 : ut2 := (1, 0, 0)%Z.
Definition ut2_e12 : ut2 := (0, 1, 0)%Z.

Example ut2_e11_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.
Example ut2_e12_e11 : rig_mul UT2 ut2_e12 ut2_e11 = ut2_zero := eq_refl.

Theorem UT2_not_commutative :
  rig_mul UT2 ut2_e11 ut2_e12 ≈ rig_mul UT2 ut2_e12 ut2_e11 → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

(* Hence [AAlg] does not consist of commutative algebras: the witness is
   an object of [AAlg Int_CRng] whose ring is not commutative. *)
Theorem AAlg_not_all_commutative :
  (∀ (A : AAlgObject Int_CRng) a b,
     rig_mul (aalg_ring A) a b ≈ rig_mul (aalg_ring A) b a) → False.
Proof.
  intro H.
  exact (UT2_not_commutative (H UT2_AAlg ut2_e11 ut2_e12)).
Qed.

(* ...and the same witness is outside the image of [KAlg_AAlg] on the
   nose: no [KAlgObject] has [UT2] for its ring. *)
Theorem UT2_not_in_KAlg (A : KAlgObject Int_CRng) :
  kalg_ring A = UT2 → False.
Proof.
  destruct A as [Ar Acomm Aunit]; simpl; intro HA; subst Ar.
  exact (UT2_not_commutative (Acomm ut2_e11 ut2_e12)).
Qed.

(** The base-ring algebra and the matrix algebra are both objects, so
    [AAlg Int_CRng] has at least two, and a morphism between them: the
    scalar diagonal is itself a map of ℤ-algebras. *)
Lemma ut2_scalar_triangle :
  aalg_unit UT2_AAlg ≈ ut2_scalar ∘ aalg_unit (Base_AAlg Int_CRng).
Proof. intro r; simpl; reflexivity. Qed.

Definition Base_to_UT2 : Base_AAlg Int_CRng ~{AAlg Int_CRng}~> UT2_AAlg :=
  (ut2_scalar; ut2_scalar_triangle).

(* The underlying module of UT2 has the expected action: scalars act
   entrywise, and it computes. *)
Example ut2_module_action :
  rm_smul (AAlg_RMod UT2_AAlg) 3%Z (2, 5, 7)%Z = (6, 15, 21)%Z := eq_refl.
