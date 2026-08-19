Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Representable functors. *)

(* nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   A functor F : C ⟶ Sets is representable when it is naturally isomorphic to
   a covariant hom-functor Hom(A, ─) for some object A of C, the representing
   object. In library notation this natural isomorphism is

       [Hom A,─] ≅ F     (an iso in the functor category [C, Sets]),

   so [represented] below is precisely Wikipedia's pair (A, Φ): [repr_obj] is
   A and [represented] is the natural iso Φ : Hom(A, ─) ⟹ F. By the Yoneda
   lemma such a Φ is determined by a single universal element of F(A), namely
   Φ_A(id A), and the representing object is unique up to (unique) isomorphism;
   the universal-element half is developed in Structure/UniversalProperty.v,
   and the uniqueness half is [repr_unique_iso] below, the τ = id case of the
   induced-arrow correspondence in the second half of this file. A contravariant
   representable G : C^op ⟶ Sets (a presheaf) is instead naturally isomorphic
   to Hom(─, A); see [Hom ─,A] (Curried_CoHom) in Functor/Hom.v. *)

(* Wikipedia: "Let C be a locally small category and let Set be the category
   of sets. For each object A of C let Hom(A,–) be the hom functor that maps
   object X to the set Hom(A,X).

   A functor F : C → Set is said to be representable if it is naturally
   isomorphic to Hom(A,–) for some object A of C. A representation of F is a
   pair (A, Φ) where

       Φ : Hom(A,–) → F

   is a natural isomorphism.

   A contravariant functor G from C to Set is the same thing as a functor G :
   Cop → Set and is commonly called a presheaf. A presheaf is representable
   when it is naturally isomorphic to the contravariant hom-functor Hom(–,A)
   for some object A of C." *)

Class Representable `(F : C ⟶ Sets) := {
  repr_obj : C;                          (* the representing object A *)
  represented : [Hom repr_obj,─] ≅ F     (* natural iso Φ : Hom(A, ─) ⟹ F *)
}.

Coercion Representable_to_obj `(F : C ⟶ Sets) (R : Representable F) : C :=
  @repr_obj _ _ R.

(** * Representations are functorial in natural transformations

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer 1998, §III.2, Exercise 1, printed p. 62.
    nLab: https://ncatlab.org/nlab/show/representable+functor
    nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

    Mac Lane's exercise reads: given representations ⟨r, ψ⟩ of K and
    ⟨r', ψ'⟩ of K', every natural transformation τ : K ⟹ K' is induced
    by a unique arrow h : r' → r between the representing objects,
    compatibly with the two representations.  The direction of h is the
    exercise's, not a slip: transformations between covariant hom-functors
    run against the arrows, Nat(Hom(r,−), Hom(r',−)) ≅ Hom(r', r), so a
    transformation K ⟹ K' is named by an arrow r' → r.  (When the base
    category is itself an opposite — the presheaf reading, where the objects
    of C are the objects of the ambient C^op — the same statement reads
    covariantly in C; Structure/SubobjectClassifier/Natural.v's
    [Sub_Representable] and Instance/FinSet/Powerset.v's
    [FinPowerset_Representable] are representations of that kind.)

    The exercise is a corollary of the Yoneda lemma in the following exact
    sense.  Conjugating τ by the two representations gives a transformation
    of representable copresheaves,

        σ := ψ'⁻¹ ∘ τ ∘ ψ  :  Hom(r, −) ⟹ Hom(r', −)     ([repr_transport]),

    and the Yoneda embedding, being fully faithful, identifies such σ with
    arrows r' → r.  Fullness produces the arrow — it is σ's value at the
    identity, [repr_induced] — and faithfulness is what makes it unique.
    The two halves are here in elementary form rather than through the
    packaged bijection; see the universe note below for why.

    This is the step at which representability stops being a property of one
    functor and becomes a construction on the category of functors.  The
    correspondence is what makes "the representing object" well defined up
    to a canonical isomorphism (the τ = id case, [repr_unique_iso]), and it
    is why a universal construction is functorial with no extra hypothesis:
    the assignment K ↦ r is the fully faithful functor built in
    Functor/Representable/Functorial.v.

    WHAT IS DELIVERED HERE

    - [repr_transport] and [repr_induced], the conjugated transformation and
      the arrow it names, together with the compatibility predicate
      [ReprCompatible] — Mac Lane's condition stated as an equation in the
      functor category [C, Sets], with [repr_compatible_at] and
      [repr_compatible_of_at] converting it to and from the pointwise form
      (both by [:=], with no tactic: the two are convertible).
    - Existence ([repr_induced_compatible]) and uniqueness
      ([repr_induced_unique]), packaged as
      [repr_induced_universal : ∃! h, ReprCompatible R R' τ h] over
      Lib/Setoid.v's [Unique] at the hom-setoid of C.  [Unique] is what
      Structure/UniversalProperty.v uses for the τ = id case too, though
      there at the setoid of isomorphisms rather than at a hom-setoid.
    - Functoriality: [repr_induced_respects], [repr_induced_id],
      [repr_induced_comp].  Note the composition law's shape,
      h(τ' ∙ τ) ≈ h(τ) ∘ h(τ'): the assignment is contravariant into C, which
      is why the packaged functor in the companion file lands in C^op.
    - [repr_induced_iso], upgrading a natural ISOMORPHISM K ≅ K' to an
      isomorphism of representing objects, and its τ = id specialization
      [repr_unique_iso] with the uniqueness clause
      [repr_unique_iso_universal].
    - [Hom_Representable], the tautological representation of Hom(c, −) by c,
      and [repr_induced_hom], the round trip: the arrow named by
      fmap[Curried_Hom] f is f again.  This is deliberately NOT registered as
      an [Instance]: the tree's [Representable] instances are found by
      resolution (Structure/Cartesian/Closed/Adjunction.v's
      [Curry_Representable_resolves] is solved by resolution alone, and says
      so), so a globally registered tautological instance would add a
      candidate to every such search.  Whether it would in fact divert any
      existing search was not measured; the point is that a [Definition]
      raises the question and an [Instance] would not.

    WHAT IS NOT DELIVERED HERE

    - The cross-link with Structure/UniversalProperty.v's
      [univ_property_unique_up_to_unique_iso], the packaging of K ↦ r as a
      functor, and the concrete witnesses are in
      Functor/Representable/Functorial.v.  They are not here because the
      cross-link needs Structure/UniversalProperty.v, and making the file
      that DECLARES [Representable] depend on it would invert the dependency
      and impose Yoneda plus Construction/Groupoid.v on every consumer of the
      class.  Everything in this section, by contrast, costs no new import at
      all: [Theory.Natural.Transformation], [Construction.Opposite] and
      [Instance.Fun] were already transitive requirements of
      [Category.Functor.Hom].
    - No contravariant restatement.  None is needed and none would be
      separate content: a presheaf is a functor out of C^op, and
      [Curried_CoHom C] IS [Curried_Hom C^op] by definition, so the
      statements below read at C^op are the presheaf statements.
    - No comparison with Theory/Universal/Element.v's [UniversalElement], and
      no claim that τ ↦ h is the ONLY such correspondence; what is proved is
      that h is unique given the compatibility condition.

    A UNIVERSE NOTE, MEASURED

    The issue this development answers suggests routing through
    [Yoneda_Embedding'] (Functor/Hom.v:109), which packages the hom-bijection
    as an [IsIsomorphism] in Sets.  That route was not taken, because
    [Yoneda_Embedding'] — like [Yoneda_Full] and [Yoneda_Faithful], from which
    it is assembled — is stated over [C : Category@{u u u}], with the object,
    hom and proof universes IDENTIFIED, while the [Representable] class itself
    is over [Category@{o h h}] with the object universe FREE.  That
    identification is an artifact of top-level minimization on an unannotated
    [(C : Category)] binder and not inherent: re-running those two proof
    scripts verbatim inside a section whose category is annotated
    [Category@{uo uh uh}] with [uo < uh] declared succeeds.  Nothing here
    repairs the donors — that is a change to a file with wide blast radius and
    is out of this development's scope — but nothing here inherits their pin
    either.  The whole of this section is over an annotated
    [C : Category@{o h h}], and the one thing the Yoneda bijection was needed
    for, that a transformation of representable copresheaves acts by
    precomposition with its value at the identity, is [hom_transform_precomp]
    below: one naturality square, evaluated at the identity.  Measured per
    constant, the result is that [repr_induced], [repr_induced_universal],
    [repr_unique_iso] and [Hom_Representable] leave the object universe [o]
    unconstrained relative to the hom universe [h] — their constraint blocks
    carry no [o = h] and not even [o <= h] — and the
    difference is guarded in Test/ProbeRepresentableInduced.v, where the
    donors are rejected at a category whose objects sit strictly below its
    homs and these constants are accepted.  (The companion file's
    [ReprObjFunctor] does pick up [o <= h], from packaging the assignment as
    a functor into C^op; still no [o = h].)  [Representable]'s own hom = proof
    identification comes from [Instance/Fun.v]'s [Fun], which takes and
    returns categories of the shape [Category@{a b b}], and [represented] is
    an isomorphism in [C, Sets]; nothing here touches it.  Read constraint
    blocks rather than binders: the companion file's
    [repr_pair_iso_from_is_induced] DISPLAYS its binder as
    [Category@{u u0 u0}] and carries [u = u0] in its constraint set. *)

Section ReprInduced.

Universes o h.
Context (C : Category@{o h h}).

(* The computational half of the Yoneda lemma for covariant representables,
   in the only form used below: a transformation between representable
   copresheaves acts by PRECOMPOSITION with its value at the identity.  This
   is naturality at g, evaluated at id, with [id_right] cleaning up.  Up to
   the orientation of [≈] it is the same equation as [Yoneda_Full]'s
   [fmap_sur] obligation (Functor/Hom.v:96-103), with the same proof,
   re-derived here so that this development does not inherit that constant's
   universe pin. *)
Lemma hom_transform_precomp (r r' : C)
  (sigma : [Hom r,─] ~{[C, Sets]}~> [Hom r',─]) (d : C) (g : r ~> d) :
  transform[sigma] d g ≈ g ∘ transform[sigma] r id.
Proof.
  pose proof (@naturality _ _ _ _ sigma r d g id{C}) as N; simpl in N.
  rewrite id_right in N.
  now symmetry.
Qed.

Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(* Mac Lane's ψ'⁻¹ ∘ τ ∘ ψ : the transformation τ carried across the two
   representations, where it becomes a transformation of representable
   copresheaves. *)
Definition repr_transport (tau : K ⟹ K')
  : [Hom (@repr_obj _ _ R),─] ~{[C, Sets]}~> [Hom (@repr_obj _ _ R'),─] :=
  from (@represented _ _ R') ∘[Fun] (tau ∘[Fun] to (@represented _ _ R)).

(* ...and the arrow it names, its value at the identity of the representing
   object.  Unfolded: ψ'⁻¹_r (τ_r (ψ_r id)), so the universal element ψ_r id
   of K is where the construction starts. *)
Definition repr_induced (tau : K ⟹ K') : @repr_obj _ _ R' ~> @repr_obj _ _ R :=
  transform[repr_transport tau] (@repr_obj _ _ R) id.

(* Mac Lane's compatibility condition, as an equation in [C, Sets]:
   ψ' ∘ Hom(h, −) ≈ τ ∘ ψ.  The sides are written in the mirror of the
   issue's display, which is the same statement since [≈] is symmetric.  Note
   that [fmap[Curried_Hom C]] wants a C^op-arrow, so [h : r' ~> r] enters as
   [op h]. *)
Definition ReprCompatible (tau : K ⟹ K')
  (hh : @repr_obj _ _ R' ~> @repr_obj _ _ R) : Type :=
  to (@represented _ _ R') ∘[Fun] fmap[Curried_Hom C] (op hh)
    ≈[Fun] tau ∘[Fun] to (@represented _ _ R).

(* The pointwise reading, in both directions.  Both are supplied by [:=] with
   no tactic: the hom-setoid of [C, Sets] is componentwise and the hom-setoid
   of Sets is pointwise, so the two statements are convertible. *)
Definition repr_compatible_at {tau hh} (compat : ReprCompatible tau hh)
  (d : C) (g : @repr_obj _ _ R ~> d) :
  transform[to (@represented _ _ R')] d (g ∘ hh)
    ≈ transform[tau] d (transform[to (@represented _ _ R)] d g) := compat d g.

Definition repr_compatible_of_at {tau : K ⟹ K'}
  {hh : @repr_obj _ _ R' ~> @repr_obj _ _ R}
  (at_ : ∀ (d : C) (g : @repr_obj _ _ R ~> d),
       transform[to (@represented _ _ R')] d (g ∘ hh)
         ≈ transform[tau] d (transform[to (@represented _ _ R)] d g)) :
  ReprCompatible tau hh := at_.

(* Existence: the arrow named by τ is compatible with the two
   representations.  The proof is [hom_transform_precomp] read backwards —
   turning g ∘ h into σ's value at g — followed by ψ' cancelling ψ'⁻¹. *)
Lemma repr_induced_compatible (tau : K ⟹ K') :
  ReprCompatible tau (repr_induced tau).
Proof.
  apply repr_compatible_of_at; intros d g.
  unfold repr_induced; simpl.
  rewrite <- (hom_transform_precomp _ _ (repr_transport tau) d g).
  pose proof (iso_to_from (@represented _ _ R') d
    (transform[tau] d (transform[to (@represented _ _ R)] d g))) as HH;
    simpl in HH; rewrite HH.
  srewrite (@fmap_id _ _ K' d); reflexivity.
Qed.

(* Uniqueness: a compatible arrow is determined by the condition at the one
   place it can be probed, the identity of the representing object. *)
Lemma repr_induced_unique (tau : K ⟹ K') hh :
  ReprCompatible tau hh → hh ≈ repr_induced tau.
Proof.
  intro compat.
  pose proof (repr_compatible_at compat (@repr_obj _ _ R) id) as E; simpl in E.
  unfold repr_induced; simpl.
  rewrite <- E.
  pose proof (iso_from_to (@represented _ _ R') (@repr_obj _ _ R)
                (id{C} ∘ hh)) as HH; simpl in HH; rewrite HH.
  now rewrite !id_left.
Qed.

(* The exercise as one statement: a unique compatible arrow between the
   representing objects. *)
Program Definition repr_induced_universal (tau : K ⟹ K') :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible tau) := {|
  unique_obj := repr_induced tau;
  unique_property := repr_induced_compatible tau
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

Lemma repr_induced_respects (tau tau' : K ⟹ K') :
  tau ≈ tau' → repr_induced tau ≈ repr_induced tau'.
Proof.
  intro E; unfold repr_induced; simpl.
  apply proper_morphism, (E (@repr_obj _ _ R) _).
Qed.

End ReprInduced.

Arguments repr_transport {C K K'} R R' tau.
Arguments repr_induced {C K K'} R R' tau.
Arguments ReprCompatible {C K K'} R R' tau hh.
Arguments repr_compatible_at {C K K' R R' tau hh} compat d g.
Arguments repr_compatible_of_at {C K K' R R' tau hh} at_.
Arguments repr_induced_compatible {C K K'} R R' tau.
Arguments repr_induced_unique {C K K'} R R' tau hh.
Arguments repr_induced_universal {C K K'} R R' tau.
Arguments repr_induced_respects {C K K'} R R' tau tau'.

(** ** Functoriality *)

Section ReprInducedLaws.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' K'' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K') (R'' : Representable K'').

(* The identity transformation names the identity arrow.  [nat_id]'s component
   is [fmap[K] id] rather than [id] (Theory/Natural/Transformation.v:220), so
   [fmap_id] is spent once here and once in [repr_induced_compatible]. *)
Lemma repr_induced_id : repr_induced R R nat_id ≈ id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  srewrite (@fmap_id _ _ K (@repr_obj _ _ R)).
  pose proof (iso_from_to (@represented _ _ R) (@repr_obj _ _ R) id{C})
    as HH; simpl in HH; rewrite HH.
  now rewrite id_left.
Qed.

(* ...and a composite names the composite, in the opposite order: the
   assignment is contravariant into C.  Proved by uniqueness, not by
   unfolding: the composite arrow is shown compatible, and then it IS the
   induced one. *)
Lemma repr_induced_comp (tau : K ⟹ K') (tau' : K' ⟹ K'') :
  repr_induced R R'' (tau' ∙ tau)
    ≈ repr_induced R R' tau ∘ repr_induced R' R'' tau'.
Proof.
  symmetry; apply repr_induced_unique.
  apply repr_compatible_of_at; intros d g; simpl.
  rewrite comp_assoc.
  rewrite (repr_compatible_at (repr_induced_compatible R' R'' tau') d _).
  now rewrite (repr_compatible_at (repr_induced_compatible R R' tau) d g).
Qed.

End ReprInducedLaws.

Arguments repr_induced_id {C K} R.
Arguments repr_induced_comp {C K K' K''} R R' R'' tau tau'.

(** ** Isomorphisms, and Mac Lane's τ = id case *)

Section ReprInducedIso.

Universes o h.
Context (C : Category@{o h h}).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(* A natural isomorphism of represented functors induces an isomorphism of
   representing objects; both triangle laws are the composition law followed
   by the identity law. *)
Program Definition repr_induced_iso (i : K ≅[Fun] K')
  : @repr_obj _ _ R' ≅ @repr_obj _ _ R := {|
  to   := repr_induced R R' (to i);
  from := repr_induced R' R (from i)
|}.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R R (from i ∙ to i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_from_to i).
Qed.
Next Obligation.
  rewrite <- repr_induced_comp.
  rewrite (repr_induced_respects R' R' (to i ∙ from i) nat_id).
  - now apply repr_induced_id.
  - apply (iso_to_from i).
Qed.

End ReprInducedIso.

Arguments repr_induced_iso {C K K'} R R' i.

Section ReprUnique.

Universes o h.
Context (C : Category@{o h h}).
Context {K : C ⟶ Sets}.
Context (R R' : Representable K).

(* Mac Lane's τ = id case: two representations of ONE functor have
   canonically isomorphic representing objects.  This is [repr_induced_iso]
   at the identity isomorphism; no separate argument. *)
Definition repr_unique_iso : @repr_obj _ _ R' ≅ @repr_obj _ _ R :=
  repr_induced_iso R R' iso_id.

(* ...and the isomorphism's forward leg is the unique compatible arrow, which
   is the clause a bare [≅] does not carry.  Uniqueness is inherited from
   [repr_induced_universal]; it is stated separately because the isomorphism
   is what a consumer names. *)
Program Definition repr_unique_iso_universal :
  @Unique _ (@homset C (@repr_obj _ _ R') (@repr_obj _ _ R))
          (ReprCompatible R R' nat_id) := {|
  unique_obj := to repr_unique_iso;
  unique_property := repr_induced_compatible R R' nat_id
|}.
Next Obligation. symmetry; now apply repr_induced_unique. Qed.

End ReprUnique.

Arguments repr_unique_iso {C K} R R'.
Arguments repr_unique_iso_universal {C K} R R'.

(** ** The tautological representation, and the round trip *)

Section TautologicalRepresentation.

Universes o h.
Context (C : Category@{o h h}).

(* Hom(c, −) represents itself, by the identity isomorphism.  Deliberately a
   plain [Definition] and not an [Instance]: see the header. *)
Definition Hom_Representable (c : C) : Representable ([Hom c,─]) := {|
  repr_obj := c;
  represented := iso_id
|}.

(* Against those representations the correspondence is the identity on
   arrows: the arrow named by Hom(f, −) is f.  Both sides of Mac Lane's
   bijection are visible here, and the residue is three identity laws. *)
Lemma repr_induced_hom (c c' : C) (f : c' ~> c) :
  repr_induced (Hom_Representable c) (Hom_Representable c')
    (fmap[Curried_Hom C] (op f)) ≈ f.
Proof.
  unfold repr_induced, repr_transport; simpl; unfold op.
  now rewrite !id_left.
Qed.

End TautologicalRepresentation.

Arguments Hom_Representable {C} c.
Arguments repr_induced_hom {C} c c' f.
