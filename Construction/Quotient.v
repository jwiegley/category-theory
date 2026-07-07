Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Quotient categories, and transport along object equalities

    nLab: https://ncatlab.org/nlab/show/quotient+category
    Wikipedia: https://en.wikipedia.org/wiki/Quotient_category

    This file is fully general — it never mentions any concrete category —
    and provides two independent kits, reusable by any construction that
    quotients a syntactic category or reasons about Leibniz-strict object
    equalities:

    (a) a transport kit for categories in which certain objects are related
        by Leibniz equality [=] (as happens in strict monoidal categories):
        the transported identities [id_cast]/[hom_cast] and their algebra,
        the [ObjDecEq] class giving axiom-free uniqueness of identity proofs
        on objects, and the [HomEqProp] class reflecting the hom-setoid
        equivalence into [Prop];

    (b) the quotient of an arbitrary category by a [Prop]-valued
        hom-congruence: the quotient [Category] itself, the
        identity-on-objects projection functor, transfer of isomorphisms,
        the lifting universal property, and descent of bifunctors. *)

(** ** The [id_cast]/[hom_cast] transport kit

    [id_cast e] is the identity morphism transported along an object-level
    Leibniz equality [e : x = y].  It is deliberately spelled with the same
    [match e in _ = T return x ~> T with eq_refl => id end] shape as the
    [strict_*_to] fields of [Structure/Monoidal/Strict.v] and the
    [strict_pure_iso_id]/[strict_ap_iso_id] fields of
    [Functor/Structure/Monoidal/Strict.v], so those fields read as
    [to φ ≈ id_cast e] without any unfolding. *)

Section HomCast.

Context {C : Category}.

(** The identity morphism, transported along an object equality. *)
Definition id_cast {x y : C} (e : x = y) : x ~> y :=
  match e in _ = T return x ~> T with eq_refl => id end.

(** At [eq_refl], the cast is the literal identity. *)
Lemma id_cast_refl {x : C} : id_cast (@eq_refl _ x) = id.
Proof. reflexivity. Qed.

(** Composing two casts gives the cast along the composite equality. *)
Lemma id_cast_trans {x y z : C} (e1 : x = y) (e2 : y = z) :
  id_cast e2 ∘ id_cast e1 ≈ id_cast (eq_trans e1 e2).
Proof. destruct e2, e1; cat. Qed.

(** Casting along [e] and back along [eq_sym e] is the identity. *)
Lemma id_cast_inv_l {x y : C} (e : x = y) :
  id_cast (eq_sym e) ∘ id_cast e ≈ id.
Proof. destruct e; cat. Qed.

Lemma id_cast_inv_r {x y : C} (e : x = y) :
  id_cast e ∘ id_cast (eq_sym e) ≈ id.
Proof. destruct e; cat. Qed.

(** Solve [f ≈ g ∘ cast⁻¹] from [f ∘ cast ≈ g]. *)
Lemma comp_cast_shift {x y z : C} (e : x = y) (f : y ~> z) (g : x ~> z) :
  f ∘ id_cast e ≈ g → f ≈ g ∘ id_cast (eq_sym e).
Proof.
  intros Hf.
  rewrite <- Hf.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  now rewrite id_right.
Qed.

(** Nested cast conjugations fuse along [eq_trans]. *)
Lemma id_cast_conj_fuse {x y x' y' x'' y'' : C}
  (e1 : x = x') (e2 : y = y') (d1 : x' = x'') (d2 : y' = y'')
  (f : x ~> y) :
  id_cast d2 ∘ (id_cast e2 ∘ f ∘ id_cast (eq_sym e1)) ∘ id_cast (eq_sym d1)
    ≈ id_cast (eq_trans e2 d2) ∘ f ∘ id_cast (eq_sym (eq_trans e1 d1)).
Proof. destruct e1, e2, d1, d2; cat. Qed.

(** Leibniz-equal objects are in particular isomorphic, via the casts. *)
Definition id_cast_iso {x y : C} (e : x = y) : x ≅ y := {|
  to := id_cast e;
  from := id_cast (eq_sym e);
  iso_to_from := id_cast_inv_r e;
  iso_from_to := id_cast_inv_l e
|}.

(** A whole morphism transported along equalities on both endpoints. *)
Definition hom_cast {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x ~> y) : x' ~> y' :=
  match ey in _ = b return x' ~> b with eq_refl =>
    match ex in _ = a return a ~> y with eq_refl => f end end.

(** At [eq_refl] on both ends, the cast is the morphism itself. *)
Lemma hom_cast_refl {x y : C} (f : x ~> y) :
  hom_cast eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

(** A [hom_cast] is conjugation by the endpoint [id_cast]s. *)
Lemma hom_cast_decompose {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x ~> y) :
  hom_cast ex ey f ≈ id_cast ey ∘ f ∘ id_cast (eq_sym ex).
Proof. destruct ex, ey; cat. Qed.

(** Casting the identity along the same equality twice is the identity. *)
Lemma hom_cast_id {x x' : C} (e : x = x') : hom_cast e e id ≈ id.
Proof. destruct e; cat. Qed.

(** Casts fuse across composition when the middle equalities agree. *)
Lemma hom_cast_comp {x y z x' y' z' : C}
  (ex : x = x') (ey : y = y') (ez : z = z')
  (g : y ~> z) (f : x ~> y) :
  hom_cast ey ez g ∘ hom_cast ex ey f ≈ hom_cast ex ez (g ∘ f).
Proof. destruct ex, ey, ez; cat. Qed.

(** Casting there and back is the identity operation. *)
Lemma hom_cast_roundtrip {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x' ~> y') :
  hom_cast ex ey (hom_cast (eq_sym ex) (eq_sym ey) f) = f.
Proof. destruct ex, ey; reflexivity. Qed.

(** [hom_cast] respects the hom-setoid equivalence. *)
#[export] Instance hom_cast_respects {x y x' y' : C}
  (ex : x = x') (ey : y = y') :
  Proper (equiv ==> equiv) (@hom_cast x y x' y' ex ey).
Proof. destruct ex, ey; repeat intro; assumption. Qed.

End HomCast.

(** Functors take [id_cast e] to [id_cast (f_equal F e)].  This is the
    [id_cast]-phrased sibling of [fmap_match_id] from
    [Functor/Structure/Monoidal/Strict.v]; it is reproved here (one line)
    to keep this root file independent of the monoidal-functor stack. *)
Lemma fmap_id_cast {C D : Category} (F : C ⟶ D) {x y : C} (e : x = y) :
  fmap[F] (id_cast e) ≈ id_cast (f_equal F e).
Proof. destruct e; apply fmap_id. Qed.

(** ** Decidable object equality gives axiom-free UIP

    When the objects of [C] have decidable Leibniz equality, uniqueness of
    identity proofs holds for them without any axiom, by
    [Eqdep_dec.UIP_dec].  This is the target-side mirror of the
    proof-irrelevance results available on syntactic categories with [nat]
    objects, and it makes every [id_cast]/[hom_cast] independent of the
    particular equality proof used. *)

Class ObjDecEq (C : Category) : Type :=
  obj_eq_dec : ∀ x y : obj[C], {x = y} + {x ≠ y}.

(** Uniqueness of identity proofs on objects, with no axioms. *)
Lemma obj_uip {C : Category} `{@ObjDecEq C} {x y : C} (e1 e2 : x = y) :
  e1 = e2.
Proof. exact (UIP_dec obj_eq_dec e1 e2). Qed.

(** [id_cast] does not depend on the choice of equality proof. *)
Lemma id_cast_irr {C : Category} `{@ObjDecEq C} {x y : C} (e1 e2 : x = y) :
  id_cast e1 = id_cast e2.
Proof. rewrite (obj_uip e1 e2); reflexivity. Qed.

(** Any cast along a loop equality [e : x = x] is the identity. *)
Lemma id_cast_loop {C : Category} `{@ObjDecEq C} {x : C} (e : x = x) :
  id_cast e = id.
Proof. rewrite (obj_uip e eq_refl); reflexivity. Qed.

(** Conjugation along different proofs of the same equalities agrees. *)
Lemma id_cast_conj_irr {C : Category} `{@ObjDecEq C} {x y x' y' : C}
  (p1 q1 : x = x') (p2 q2 : y = y') (f : x ~> y) :
  id_cast p2 ∘ f ∘ id_cast (eq_sym p1)
    ≈ id_cast q2 ∘ f ∘ id_cast (eq_sym q1).
Proof. rewrite (obj_uip p1 q1), (obj_uip p2 q2); reflexivity. Qed.

(** [hom_cast] does not depend on the choice of equality proofs. *)
Lemma hom_cast_irr {C : Category} `{@ObjDecEq C} {x y x' y' : C}
  (e1 e1' : x = x') (e2 e2' : y = y') (f : x ~> y) :
  hom_cast e1 e2 f = hom_cast e1' e2' f.
Proof. rewrite (obj_uip e1 e1'), (obj_uip e2 e2'); reflexivity. Qed.

(** Casting a morphism along loop equalities is the morphism itself. *)
Lemma hom_cast_loop {C : Category} `{@ObjDecEq C} {x y : C}
  (e1 : x = x) (e2 : y = y) (f : x ~> y) :
  hom_cast e1 e2 f = f.
Proof. rewrite (obj_uip e1 eq_refl), (obj_uip e2 eq_refl); reflexivity. Qed.

(** ** [Prop]-reflected hom equivalence

    The hom-setoid equivalence [≈] of this library is [Type]-valued (it is
    a [crelation]; see [Lib/Setoid.v]).  A [Prop]-valued inductive with two
    or more constructors — such as the term congruence of a syntactic
    category — cannot be eliminated into that [Type]-valued [≈] of an
    abstract target category: the elimination restriction on [Prop] blocks
    the induction.  Soundness inductions therefore land in a [Prop]-valued
    reflection [heq] of the hom equivalence and round-trip through
    [heq_intro]/[heq_elim].

    No [Equivalence] field is required: reflexivity, symmetry and
    transitivity of [heq] all follow by round-tripping through [≈]. *)

Class HomEqProp (C : Category) : Type := {
  heq : ∀ {x y : C}, (x ~> y) → (x ~> y) → Prop;
  heq_intro : ∀ {x y : C} {f g : x ~> y}, f ≈ g → heq f g;
  heq_elim : ∀ {x y : C} {f g : x ~> y}, heq f g → f ≈ g
}.

(** ** Quotient by a hom-congruence

    A [HomRel] is [Prop]-valued by design: it matches the [Prop]-valued
    term congruences of syntactic categories, and it embeds into the
    [Type]-valued [crelation] demanded by [Setoid] via [Prop ⊆ Type]
    cumulativity, so it can serve directly as the quotient's hom-setoid
    equivalence.  That choice also makes [Quotient_HomEqProp] below
    definitional. *)

Definition HomRel (C : Category) : Type :=
  ∀ x y : C, (x ~> y) → (x ~> y) → Prop.

(** A congruence: an equivalence on each hom containing [≈] (whence
    reflexivity) and compatible with composition. *)
Class HomCongruence {C : Category} (R : HomRel C) : Type := {
  cong_incl {x y : C} {f g : x ~> y} : f ≈ g → R x y f g;
  cong_sym {x y : C} {f g : x ~> y} : R x y f g → R x y g f;
  cong_trans {x y : C} {f g h : x ~> y} :
    R x y f g → R x y g h → R x y f h;
  cong_comp {x y z : C} {f f' : y ~> z} {g g' : x ~> y} :
    R y z f f' → R x y g g' → R x z (f ∘ g) (f' ∘ g')
}.

(** Reflexivity of a congruence, from inclusion of [≈]. *)
Lemma cong_refl {C : Category} {R : HomRel C} `{@HomCongruence C R}
  {x y : C} (f : x ~> y) : R x y f f.
Proof. apply cong_incl; reflexivity. Qed.

(** Each hom-relation of a congruence is an equivalence. *)
Lemma Quotient_equivalence {C : Category} {R : HomRel C}
  `{@HomCongruence C R} (x y : C) : Equivalence (R x y).
Proof.
  constructor.
  - intros f. exact (cong_refl f).
  - intros f g Hfg. exact (cong_sym Hfg).
  - intros f g k Hfg Hgk. exact (cong_trans Hfg Hgk).
Qed.

(** The quotient category [C/R]: same objects and morphisms as [C], with
    the hom-setoid equivalence coarsened from [≈] to [R].  The category
    laws hold because [R] contains [≈] (via [cong_incl]) and [C] already
    satisfies them up to [≈]. *)
Definition Quotient (C : Category) (R : HomRel C)
  `{@HomCongruence C R} : Category := {|
  obj := @obj C;
  hom := @hom C;
  homset := fun x y =>
    {| equiv := R x y; setoid_equiv := Quotient_equivalence x y |};
  id := @id C;
  compose := @compose C;
  compose_respects := fun x y z f f' Hf g g' Hg => cong_comp Hf Hg;
  id_left := fun x y f => cong_incl (id_left f);
  id_right := fun x y f => cong_incl (id_right f);
  comp_assoc := fun x y z w f g h => cong_incl (comp_assoc f g h);
  comp_assoc_sym := fun x y z w f g h => cong_incl (comp_assoc_sym f g h)
|}.

(** The quotient's [≈] IS [R x y] after reduction, so both directions of
    the [Prop] reflection are the identity. *)
#[export] Instance Quotient_HomEqProp (C : Category) (R : HomRel C)
  `{@HomCongruence C R} : HomEqProp (Quotient C R) :=
  Build_HomEqProp (Quotient C R)
    (fun x y f g => R x y f g)
    (fun x y f g Hfg => Hfg)
    (fun x y f g Hfg => Hfg).

(** The quotient has the same objects as [C], so decidability of object
    equality is inherited on the nose. *)
#[export] Instance Quotient_ObjDecEq (C : Category) (R : HomRel C)
  `{@HomCongruence C R} `{OD : @ObjDecEq C} : ObjDecEq (Quotient C R) := OD.

(** *** The universal property of the quotient *)

Section QuotientUMP.

Context {C : Category} {R : HomRel C} `{@HomCongruence C R}.

(** The projection functor: identity on objects and on morphisms; only the
    equivalence coarsens.  (Here and below the record is built with an
    explicit [Build_Functor] so that the codomain category is pinned to the
    quotient; a bare record literal would infer it from the field values,
    which live in [C].) *)
Definition QuotientProj : C ⟶ Quotient C R :=
  Build_Functor C (Quotient C R)
    (fun x => x)
    (fun x y f => f)
    (fun x y f g Hfg => cong_incl Hfg)
    (fun x => cong_refl (@id C x))
    (fun x y z f g => cong_refl (f ∘ g)).

(** Isomorphisms in [C] descend to isomorphisms in the quotient. *)
Definition Quotient_iso {x y : C} (i : x ≅[C] y) : x ≅[Quotient C R] y :=
  @Build_Isomorphism (Quotient C R) x y (to i) (from i)
    (cong_incl (iso_to_from i))
    (cong_incl (iso_from_to i)).

Context {D : Category} (F : C ⟶ D)
  (HF : ∀ x y (f g : x ~> y), R x y f g → fmap[F] f ≈ fmap[F] g).

(** A functor identifying [R]-related morphisms lifts through the
    quotient. *)
Definition QuotientLift : Quotient C R ⟶ D :=
  Build_Functor (Quotient C R) D
    (fun x => F x)
    (fun x y f => fmap[F] f)
    HF
    (fun x => @fmap_id C D F x)
    (fun x y z f g => @fmap_comp C D F x y z f g).

(** The lift factors [F] through the projection — definitionally. *)
Lemma QuotientLift_proj {x y : C} (f : x ~> y) :
  fmap[QuotientLift] (fmap[QuotientProj] f) = fmap[F] f.
Proof. reflexivity. Qed.

(** Uniqueness: [QuotientProj] is the identity on objects and on
    morphisms, so any competitor agreeing with [F] after precomposition
    with the projection is pinned pointwise on every hom.  The competitor's
    object action agrees with [F]'s up to the Leibniz equalities [Hobj],
    and the morphism-level agreement is phrased by conjugating with
    [hom_cast] along them (see the transport kit above); when the object
    agreement is definitional, instantiating [Hobj] with [eq_refl] makes
    both [hom_cast]s disappear definitionally. *)
Lemma QuotientLift_unique (G : Quotient C R ⟶ D)
  (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
  (HG : ∀ x y (f : x ~{C}~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[G] (fmap[QuotientProj] f))
        ≈ fmap[F] f) :
  ∀ x y (f : x ~{Quotient C R}~> y),
    hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[QuotientLift] f.
Proof. exact HG. Qed.

End QuotientUMP.

(** ** Bifunctor descent

    A bifunctor on [C] whose morphism action preserves [R] componentwise
    descends to a bifunctor on the quotient.  The object and morphism
    actions are unchanged; only the respectfulness proof is new (note that
    the product category's hom equivalence is a pair). *)
Definition Quotient_bifunctor {C : Category} {R : HomRel C}
  `{@HomCongruence C R} (F : C ∏ C ⟶ C)
  (HF2 : ∀ (x y : C ∏ C) (f g : x ~{C ∏ C}~> y),
      R (fst x) (fst y) (fst f) (fst g) →
      R (snd x) (snd y) (snd f) (snd g) →
      R (F x) (F y) (fmap[F] f) (fmap[F] g)) :
  Quotient C R ∏ Quotient C R ⟶ Quotient C R :=
  Build_Functor (Quotient C R ∏ Quotient C R) (Quotient C R)
    (fun x => F x)
    (fun x y f => fmap[F] f)
    (fun x y f g Hfg => HF2 x y f g (fst Hfg) (snd Hfg))
    (fun x => cong_incl (@fmap_id _ _ F x))
    (fun x y z f g => cong_incl (@fmap_comp _ _ F x y z f g)).
