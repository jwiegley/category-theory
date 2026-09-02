Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Skeleton.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

(** * Left-adjoint-left-inverses, and Mac Lane's Exercise IV.4.4

    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/adjoint+functor
    nLab: https://ncatlab.org/nlab/show/full+subcategory
    nLab: https://ncatlab.org/nlab/show/fully+faithful+functor

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, SS IV.4, printed p. 94 (the definition)
          and p. 95 (Exercise 4).

    Transliterated to ASCII from the page images, p. 94:

      "A functor F : X -> A is said to be a left-adjoint-left-inverse of
       G : A -> X when there is an adjunction <F, G; eta, 1> : X -> A
       with counit the identity.  This means (Exercise 4) that G is an
       isomorphism of A to a reflective subcategory of X.  In the case of
       the Proposition 2 just above, we have shown that the insertion
       A -> C has a left-adjoint-left-inverse."

    and p. 95, Exercise 4:

      "Given a functor G : A -> X, prove the three following conditions
       logically equivalent:
        (a) G has a left-adjoint-left-inverse.
        (b) G has a left adjoint, and is full, faithful, and injective on
            objects.
        (c) There is a full reflective subcategory Y of X and an
            isomorphism H : A ~= Y such that G = KH, where K : Y -> X is
            the insertion."

    Exercise 3 on the same page (S : A -> C full, faithful and SURJECTIVE
    on objects gives an adjoint equivalence with UNIT the identity, and a
    left-adjoint-RIGHT-inverse) and Exercise 5 (the colimit functor over a
    connected shape can be chosen to be a left-adjoint-left-inverse) are
    different catalog items; they are cited here and not delivered.

    ** The design crux: "counit the identity" is not an equation

    In this library the counit of [F ⊣ G] at [a] runs [F (G a) ~> a]
    (Theory/Adjunction.v:218) while [id[a]] runs [a ~> a], so the two
    live in one hom-set only when [F (G a)] and [a] are the same object at
    LEIBNIZ equality.  The equation "counit ~ id", and with it the reading
    "counit ~ nat_id" that suggests itself, is therefore not merely
    unproved: it does not typecheck.  That rejection is a TYPING error
    with no "cannot unify" and no universe clause, pinned in
    Test/ProbeLeftInverse376.v against the [id_cast] form as its control.

    [LeftAdjointLeftInverse G] consequently carries the object equation as
    DATA -- a left adjoint [F], an adjunction, a family
    [lali_obj a : F (G a) = a], and the counit condition stated against the
    identity TRANSPORTED along it, [counit a ~ id_cast (lali_obj a)], over
    Construction/Quotient.v:56's transport kit.  The equivalent phrasing on
    functors ([F ◯ G] strictly equal to [Id[A]], i.e. [~] at
    Theory/Functor.v:606's [Functor_StrictEq_Setoid]) is the same data
    rearranged: its object component is [lali_obj] and its morphism
    coherence is the naturality that [counit] already has.  That
    rearrangement is not performed here.

    ** What is delivered, and at what strength

    Clause (a) is the record [LeftAdjointLeftInverse] just described, with
    accessors [lali_left], [lali_adj], [lali_obj], [lali_counit], together
    with [lali_counit_iso] (the transported identity, as an isomorphism)
    and [lali_counit_IsIsomorphism] (the counit itself is invertible, its
    inverse the reverse cast).

    Clause (b) is the record [LeftAdjointFFInjective] -- a left adjoint,
    [Full G], [Faithful G], and [InjectiveOnObjects G], the last a plain
    [Definition] introduced here because the tree has no such predicate
    (measured below), with its closure properties [InjectiveOnObjects_Id],
    [InjectiveOnObjects_Compose] and the cancellation
    [InjectiveOnObjects_cancel] (an injective composite [G ◯ F] has an
    injective right-hand factor [F], the one applied first; nothing is
    stated about [G]), all three [:=] terms.

    Clause (c) is the record [ReflectiveIsoPresentation]: a subcategory
    [ri_sub], a [Reflective] structure on it (Construction/Reflective.v:60,
    whose [reflective_full] field is the fullness clause), an isomorphism
    [ri_iso : A ≅[StrictCat] Sub X ri_sub], and the factorization
    [ri_factor] stating [G] strictly equal to [Incl ◯ to ri_iso] -- Mac
    Lane's "G = KH", at the strongest equality the library supports for
    functors.  [StrictCat] is forced: an isomorphism in [Cat] is an
    EQUIVALENCE (Instance/Cat.v), which would not pin the object
    assignment that clause (a) is about.

    The three legs, and which are direct:

      [lali_implies_ffi]      (a) => (b), DIRECT and UNCONDITIONAL.
      [ffi_implies_ri]        (b) => (c), DIRECT and UNCONDITIONAL.
      [ri_lali_implies_lali]  (c) => (a), CONDITIONAL: see below.

    packaged as [lali_characterization].  Two further legs are COMPOSED
    rather than proved: [lali_implies_ri] ((a) => (c), the first two) and
    [ri_lali_implies_ffi] ((c) => (b) under the same hypothesis as leg
    three, then leg one).

    ** The third leg is conditional, and the hypothesis is Mac Lane's own
       choice step

    [ri_lali_implies_lali] takes, beyond the presentation, a
    [LeftAdjointLeftInverse (Incl X (ri_sub Pres))]: the insertion's own
    reflector must fix the subcategory ON THE NOSE.  That is clause (a)
    restated for the insertion, and the file says so rather than dressing
    it up.  It is the step Mac Lane performs by hand on p. 94 -- "For
    objects a in A subset of C we can then choose a_0 = a = Ka and
    eta_{Ka} the identity" -- and it is STRONGER than his step: a
    left-adjoint-left-inverse [L] of [Incl X S] forces, for any two
    membership proofs [p q : sobj S x] over one ambient object,
    [(x; p) = (x; q)] as objects of [Sub X S] (the term is
    [eq_trans (eq_sym (lali_obj L (x; p))) (lali_obj L (x; q))], since
    [Incl]'s object action [`1] cannot see the proof), i.e.
    proof-irrelevance of membership on inhabited fibres, which Mac Lane's
    set-theoretic subcategory has for free and this library's
    [Subcategory] does not supply.  What a bare [Reflective] gives is an
    ISOMORPHISM [reflective_counit_iso] (Construction/Reflective.v:92),
    never an identity; the corresponding ill-typed equation is pinned as
    the probe's second TYPING negative.

    The hypothesis is NOT vacuous, and that is proved rather than argued:
    [lali_image_insertion] shows that whenever the presentation comes from
    a left-adjoint-left-inverse, the insertion of the image subcategory has
    one -- which is Mac Lane's own closing sentence on p. 94 -- and
    [lali_ri_insertion]/[lali_cycle] run the cycle (a) => (c) => (a) all
    the way round with the hypothesis discharged.  ([lali_cycle P] is NOT
    [P]: the adjunction is rebuilt through the image subcategory, refuted
    at [eq_refl] and pinned.)

    NOT delivered, and each for a stated reason:

      - No unconditional (c) => (a) and no unconditional (c) => (b) --
        and both are REFUTABLE in this library, not merely unavailable.
        [Subcategory]'s [sobj] is proof-relevant, so [Sub X S] may carry
        two distinct objects over one ambient object, which no functor
        out of [X] can separate: clause (a) for [Incl X S] forces
        membership-proof uniqueness (the term above), and clause (b)'s
        injectivity on objects forces the same.  An audit compiled the
        countermodel out of tree, axiom-free: the subcategory of [_1]
        with [sobj := fun _ => bool] and all morphisms, whose insertion
        is a [ReflectiveIsoPresentation] (a constant reflector at
        [(ttt; true)], [ri_iso] the identity) yet has neither a
        left-adjoint-left-inverse nor an injective-on-objects left
        adjoint, [true = false] following by [discriminate].  It is NOT
        shipped.  Mac Lane's clause (c) is classically true because a
        set-theoretic subcategory has proof-IRRELEVANT membership; the
        formalized clause is strictly weaker, and that gap -- not a
        missing case distinction on membership, which a decider would
        not repair -- is what the third leg's hypothesis pays for.
      - No (b) => (a).  Producing [F' (G a) = a] from injectivity on
        objects is a left inverse of [fobj[G]] on the nose, which
        injectivity alone does not give constructively.  That one is
        argued, not refuted.
      - No [iffT] packaging, no uniqueness of the left-adjoint-left-
        inverse, no dual (Exercise 3), no Exercise 5, and nothing relating
        this to Construction/Subcategory/Dense.v's
        [dense_full_subcategory_reflective] -- that is a (c)-shaped
        witness whose counit is an isomorphism ([dense_counit_iso]) and
        not the identity, so it does not discharge the hypothesis, and no
        bridge is built.

    ** Route, and what it costs

    (a) => (b) is proved DIRECTLY from the transposition corollaries of
    Theory/Adjunction.v: fullness by [prefmap h := ⌈h⌉ ∘ id_cast (eq_sym
    (lali_obj a))] with [fmap_to_adj_counit] and [from_adj_comp_law],
    faithfulness by injectivity of [⌊-⌋] followed by cancelling the
    transported identity.  The one-line alternative -- instantiating
    Adjunction/FullFaithful.v's
    [right_adjoint_fully_faithful_iff_counit_iso] -- was measured and
    declined: requiring that module takes this file's transitive
    in-project closure from 36 modules to 95 (its own closure is 87; all
    three measured on this worktree, each excluding the measured file
    itself).

    (b) => (c) builds the image subcategory ([LaliImageSub], membership
    [{a : A & G a = x}], every ambient morphism retained), the comparison
    [ImageIso : A ≅[StrictCat] Sub X LaliImageSub] whose inverse
    [ImageFrom] is Theory/Skeleton.v's [Finv] pattern ([prefmap] of a
    [hom_cast], functor laws by faithfulness), and the reflection
    [ImageReflective].  The reflection adjunction is assembled, not
    re-derived: [strict_equivalence] reads an isomorphism in [StrictCat]
    as an [EquivalenceOfCategories] whose cells are [id_cast_iso]es,
    Theory/Equivalence/Adjoint.v's [equiv_adjunction] turns that into an
    adjunction, Adjunction/Compose.v's [Adjunction_Compose] pastes it onto
    [F ⊣ G], and [rs_adj] moves the right adjoint along the strict
    equality [G ◯ ImageFrom ~ Incl].

    (c) => (a) is the same three steps in the other order:
    [lali_along_strict_iso] (transport a left-adjoint-left-inverse along
    an isomorphism of categories) then [lali_along_right_strict]
    (transport it along a strict equality of the right adjoint).  The
    counit computation in each is the only place with content, and both
    close through [equiv_adjunction_counit_at]: because the equivalence's
    counit cell is an [id_cast_iso] BY CONSTRUCTION, no half-adjoint
    correction is needed -- Theory/Skeleton.v's [adjointified] is NOT
    used, and the loop it exists to kill never appears.

    Two by-products, both small and both stated for reuse:
    [strict_id_cast_nat] is the missing inverse of Theory/Skeleton.v:229's
    [strict_equiv_of_id_cast_nat] (that file packages only one direction of
    [transport_square]), and [strict_equivalence] is the passage
    [StrictCat]-isomorphism => [EquivalenceOfCategories] with CONTROLLED
    cells, which is what makes the counit computable.

    ** Prior art, measured

    [InjectiveOnObjects] is new: the tree's only prior statements of that
    shape are [GrpAt_Incl_injective_on_objects]
    (Instance/Grp/TwoFunctors.v:363) and [slice_arrow_reflect]/
    [coslice_arrow_reflect] (Instance/Cat/Pullback.v:716, :885, each
    under that section's [ObjUIP C]; its comment at :708 names the
    property), each for one concrete functor, with no general predicate
    anywhere -- an audit found the two slice ones after a first draft
    named only the first.  The
    nearest relatives to clause (a) are Adjunction/Compose.v:71's
    [Adjunction_Id_counit] (the counit of [Id ⊣ Id] is the identity -- the
    degenerate case, recovered here as [Id_LALI]),
    Construction/Reflective.v:92's [reflective_counit_iso] (an
    isomorphism, strictly weaker) and
    Construction/Localization/Universal.v:126's [reflection_retract]
    ([Refl ◯ Iota ≈ Id] at [Cat] level, i.e. up to natural isomorphism
    rather than on the nose).  Theory/Skeleton.v:336's
    [skeletal_equivalence_is_isomorphism] is the precedent for building a
    [≅[StrictCat]] out of fullness, faithfulness and object data, and its
    [Finv] is the pattern [ImageFrom] follows.

    Two constants are rebuilt rather than consumed, each for a measurement:

      - [PointAt], the functor [1 ⟶ C] picking an object, duplicates
        Theory/Shapes.v:205's [Point], whose source is pinned at
        [_1@{_ Set Set}]: over a category whose homs are declared strictly
        above [Set], [Point x : _1@{o h h} ⟶ C] is rejected with "Cannot
        enforce Set = h" while [PointAt] is accepted (both pinned in the
        probe).  Consuming [Point] would have confined the terminal example
        to [Set]-homed categories.  The pin is the donor's minimization,
        not a property of [_1] (whose three levels are free), and is not
        claimed unavoidable.
      - [TwoY_Terminal] duplicates Instance/Two/Monoidal.v:95's
        [Two_Terminal] (renamed here to avoid the collision).  That module
        costs 16 modules on this file's closure (36 -> 52, measured) for a
        twelve-line witness, so it is not required.

    ** Examples

    [Id_LALI] is the identity adjunction, degenerate by design.
    [terminal_LALI] is general: for ANY category with a terminal object,
    the functor [1 ⟶ C] picking it has a left-adjoint-left-inverse, namely
    [Erase C] -- the object equation is one case analysis on the single
    object of [1] (it reads [ttt = a], not [a = a]) and the counit
    condition is discharged because [1]'s hom-setoid is Leibniz equality
    on [poly_unit], so any two of its morphisms agree.  It is
    instantiated at the walking arrow, where
    [two_lali_moves_TwoX] proves the composite [G ◯ F] is not the identity
    (it carries [TwoX] to [TwoY]), so the example is not an isomorphism of
    categories in disguise.

    ** Universes, measured off both binder and block

    [InjectiveOnObjects@{ao ah ap xo xh xp}] is FREE: six binders, an empty
    equation set, and only the bounds [Functor] itself imposes.  Its three
    closure constants are not: [InjectiveOnObjects_Id] carries [ch = cp],
    which is [Id]'s own ([Id] takes two levels, its category being
    [Category@{o h h}]), and [InjectiveOnObjects_Compose] and
    [InjectiveOnObjects_cancel] put all three categories' hom-and-proof
    levels at ONE level, which is [Compose]'s (declared over three
    categories sharing one such level) -- both inherited, neither
    introduced here.  Everything
    that mentions an adjunction or a strict functor equality identifies the
    two categories' hom-and-proof universes, and the identification sits in
    the BINDER, not the block: [LeftAdjointLeftInverse@{u u0 u1 u2 u3}] is
    over [A : Category@{u2 u3 u3}] and [X : Category@{u u3 u3}] -- one
    level [u3] for four slots -- while its block carries no equation at
    all.  THREE donors would each do it, and none is tested in isolation
    by the record: [Functor] in the REVERSE direction suffices ALONE -- at
    hom levels declared apart [Au ⟶ Xu] is accepted while [Xu ⟶ Au] is
    REJECTED (both in the probe), and [lali_left : X ⟶ A] is a field, so
    with the parameter [G : A ⟶ X] the identification is forced before
    either of the other two is consulted; [Adjunction]
    (Theory/Adjunction.v:133) carries [h1 = p1], [h1 = h2], [h1 = p2] in
    its own block, and [Functor_StrictEq_Setoid] (Theory/Functor.v:606)
    is declared over [Category@{u1 u4 u4}] and [Category@{u2 u4 u4}] --
    only the last is probed in isolation, its command naming no reverse
    functor.  The probe's [Au ⟶ Xu] control shows only that [Functor]
    bounds source-hom by target-hom in ONE direction; it does not
    discriminate among the three, and an earlier draft called two of
    them independent on that control's strength.  None of the three is
    introduced here and none is claimed unavoidable.

    At the PACKAGED [lali_characterization] one more level pair is
    identified: its binder reads [A X : Category@{u6 u13 u13}], so the two
    OBJECT universes coincide as well.  That is clause (c)'s doing, not
    clause (a)'s -- [ri_iso] compares [A] with [Sub X ri_sub] inside
    [StrictCat], whose objects are [Category] at ONE universe instance --
    and the contrast is exhibited in the probe: at object levels declared
    apart, [LeftAdjointLeftInverse G] and [LeftAdjointFFInjective G] are
    still formable while [@Isomorphism StrictCat] and [ffi_implies_ri] are
    not.

    Two constants keep the two categories' OBJECT universes apart:
    [lali_along_strict_iso] and [lali_image_insertion] (measured: binders
    [A : Category@{u u0 u0}], [X : Category@{u1 u2 u2}], the block
    carrying [u0 = u2] -- the hom identification every adjunction
    constant here has -- and no equation between [u] and [u1]), because
    they only PROJECT the object families out of strict equalities
    instead of building one between [A] and [X].

    Exactly five of the 118 constants carry [Set] -- [TwoY_Terminal],
    [two_LALI] and the three [two_lali_*] readbacks -- inherited from
    Instance/Two.v's [TwoHom : TwoObj -> TwoObj -> Set].  The general
    theory, all 113 others, is [Set]-free.

    ** Registration

    Nothing here is registered for instance resolution: every record is
    data (a chosen left adjoint, a chosen subcategory, a chosen
    isomorphism), passed explicitly at use sites, following the rule
    Theory/Equivalence.v states for quasi-inverses.

    ** Engineering notes

    [image_to_from_strict] and [image_incl_strict] MUST be [Defined], not
    [Qed]: [ii_counit] reads their object families back through [`1], and
    with [Qed] the projection is stuck and the transitivity step does not
    close -- which is how the need was found, and which an audit
    re-measured by flipping each to [Qed] in a scratch copy (each alone
    breaks [ii_counit]).  [image_from_to_strict] and [image_factor] are
    [Defined] for uniformity, not necessity: measured, either or both
    compile as [Qed]. *)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

Definition InjectiveOnObjects@{ao ah ap xo xh xp}
  {A : Category@{ao ah ap}} {X : Category@{xo xh xp}} (G : A ⟶ X) :=
  ∀ a a' : A, G a = G a' → a = a'.

Definition InjectiveOnObjects_Id@{co ch cp} {C : Category@{co ch cp}} :
  InjectiveOnObjects Id[C] :=
  fun a a' H => H.

Definition InjectiveOnObjects_Compose {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C}
  (HG : InjectiveOnObjects G) (HF : InjectiveOnObjects F) :
  InjectiveOnObjects (G ◯ F) :=
  fun a a' H => HF a a' (HG (F a) (F a') H).

Definition InjectiveOnObjects_cancel {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C} (HGF : InjectiveOnObjects (G ◯ F)) :
  InjectiveOnObjects F :=
  fun a a' H => HGF a a' (f_equal (fobj[G]) H).

Record LeftAdjointLeftInverse {A X : Category} (G : A ⟶ X) : Type := {
  lali_left : X ⟶ A;
  lali_adj : lali_left ⊣ G;
  lali_obj (a : A) : lali_left (G a) = a;
  lali_counit (a : A) :
    @counit A X lali_left G lali_adj a ≈ id_cast (lali_obj a)
}.

Arguments lali_left {A X G} _.
Arguments lali_adj {A X G} _.
Arguments lali_obj {A X G} _ _.
Arguments lali_counit {A X G} _ _.

Section Consequences.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Local Notation F := (lali_left P).
Local Notation e := (lali_obj P).

Definition lali_counit_iso (a : A) : F (G a) ≅ a := id_cast_iso (e a).

(* The counit itself is invertible, its inverse the reverse cast. *)
Program Definition lali_counit_IsIsomorphism (a : A) :
  IsIsomorphism (@counit A X F G (lali_adj P) a) := {|
  two_sided_inverse := id_cast (eq_sym (e a))
|}.
Next Obligation.
  intros a; rewrite (lali_counit P a); apply id_cast_inv_r.
Qed.
Next Obligation.
  intros a; rewrite (lali_counit P a); apply id_cast_inv_l.
Qed.

Program Definition lali_Full : Category.Theory.Functor.Full G := {|
  prefmap := fun a a' h =>
    from (@adj A X F G (lali_adj P) (G a) a') h ∘ id_cast (eq_sym (e a))
|}.
Next Obligation.
  intros a a' g.
  rewrite (@fmap_to_adj_counit A X F G (lali_adj P)).
  rewrite (lali_counit P a).
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l, id_right.
  exact (@from_adj_comp_law A X F G (lali_adj P) (G a) a' g).
Qed.

Program Definition lali_Faithful : Faithful G := {| fmap_inj := _ |}.
Next Obligation.
  intros x y f g Hfg.
  rewrite !(@fmap_to_adj_counit A X F G (lali_adj P)) in Hfg.
  assert (f ∘ @counit A X F G (lali_adj P) x
            ≈ g ∘ @counit A X F G (lali_adj P) x) as Hc.
  { rewrite <- (@to_adj_comp_law A X F G (lali_adj P) _ _
                  (f ∘ @counit A X F G (lali_adj P) x)).
    rewrite <- (@to_adj_comp_law A X F G (lali_adj P) _ _
                  (g ∘ @counit A X F G (lali_adj P) x)).
    now rewrite Hfg. }
  rewrite (lali_counit P x) in Hc.
  rewrite <- (id_right f), <- (id_right g).
  rewrite <- (id_cast_inv_r (e x)).
  rewrite !comp_assoc.
  now rewrite Hc.
Qed.

Definition lali_injective_on_objects : InjectiveOnObjects G :=
  fun a a' H =>
    eq_trans (eq_sym (e a)) (eq_trans (f_equal (fobj[F]) H) (e a')).

End Consequences.

(** ** Strict functor equality, in [id_cast] form *)

Definition strict_id_cast_nat {C D : Category} {F H : C ⟶ D}
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F H)
  (x y : C) (f : x ~> y) :
  id_cast (`1 E y) ∘ fmap[F] f ≈ fmap[H] f ∘ id_cast (`1 E x) :=
  fst (transport_square (`1 E x) (`1 E y) (fmap[F] f) (fmap[H] f))
      (`2 E x y f).

(** ** The inverse of an [id_cast] isomorphism, without [eq_sym_involutive] *)

Program Definition id_cast_iso_sym {C : Category} {x y : C} (e : x = y) :
  y ≅ x := {|
  to   := id_cast (eq_sym e);
  from := id_cast e
|}.
Next Obligation. intros; destruct e; cat. Qed.
Next Obligation. intros; destruct e; cat. Qed.

(** ** An isomorphism of categories is an equivalence of categories *)

Section StrictEquivalence.

Context {A B : Category}.
Context (P : A ⟶ B).
Context (Q : B ⟶ A).
Context (E1 : @equiv _ (@Functor_StrictEq_Setoid B B) (P ◯ Q) Id[B]).
Context (E2 : @equiv _ (@Functor_StrictEq_Setoid A A) (Q ◯ P) Id[A]).

Program Definition strict_equivalence : @EquivalenceOfCategories A B P := {|
  quasi_inverse := Q;
  equivalence_counit := (fun b => id_cast_iso (`1 E1 b); _);
  equivalence_unit := (fun a => id_cast_iso_sym (`1 E2 a); _)
|}.
Next Obligation.
  intros b b' u; simpl.
  rewrite <- comp_assoc.
  rewrite <- (strict_id_cast_nat E1 b b' u).
  rewrite comp_assoc, id_cast_inv_l.
  now rewrite id_left.
Qed.
Next Obligation.
  intros a a' u; simpl.
  rewrite (strict_id_cast_nat E2 a a' u).
  rewrite <- comp_assoc, id_cast_inv_r.
  now rewrite id_right.
Qed.

End StrictEquivalence.

(** ** Transporting along a strict equality of the right adjoint *)

Section RightStrict.

Context {A X : Category}.
Context {F : X ⟶ A}.
Context {G G' : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G').

Definition rs_to (x : X) (a : A) (f : F x ~> a) : x ~> G' a :=
  id_cast (`1 E a) ∘ to (@adj A X F G Adj x a) f.

Definition rs_from (x : X) (a : A) (g : x ~> G' a) : F x ~> a :=
  from (@adj A X F G Adj x a) (id_cast (eq_sym (`1 E a)) ∘ g).

Program Definition rs_iso (x : X) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (F x) a  ; is_setoid := @homset A (F x) a |}
    {| carrier := @hom X x (G' a) ; is_setoid := @homset X x (G' a) |} := {|
  to   := {| morphism := rs_to x a |};
  from := {| morphism := rs_from x a |}
|}.
Next Obligation.
  intros x a f g Hfg; unfold rs_to; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x a f g Hfg; unfold rs_from; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x a g; unfold rs_to, rs_from; simpl.
  rewrite (@from_adj_comp_law A X F G Adj).
  rewrite comp_assoc, id_cast_inv_r.
  now rewrite id_left.
Qed.
Next Obligation.
  intros x a f; unfold rs_to, rs_from; simpl.
  rewrite comp_assoc, id_cast_inv_l, id_left.
  exact (@to_adj_comp_law A X F G Adj x a f).
Qed.

Lemma rs_to_nat_l (x y : X) (a : A) (f : F y ~> a) (g : x ~> y) :
  rs_to x a (f ∘ fmap[F] g) ≈ rs_to y a f ∘ g.
Proof.
  unfold rs_to.
  rewrite (@to_adj_nat_l A X F G Adj).
  now rewrite comp_assoc.
Qed.

Lemma rs_to_nat_r (x : X) (a b : A) (f : a ~> b) (g : F x ~> a) :
  rs_to x b (f ∘ g) ≈ fmap[G'] f ∘ rs_to x a g.
Proof.
  unfold rs_to.
  rewrite (@to_adj_nat_r A X F G Adj).
  rewrite comp_assoc.
  rewrite (strict_id_cast_nat E a b f).
  now rewrite <- comp_assoc.
Qed.

Definition rs_adj : F ⊣ G' :=
  @Build_Adjunction' A X F G' rs_iso rs_to_nat_l rs_to_nat_r.

Lemma rs_counit (a : A) :
  @counit A X F G' rs_adj a
    ≈ @counit A X F G Adj a ∘ fmap[F] (id_cast (eq_sym (`1 E a))).
Proof.
  unfold counit.
  transitivity (rs_from (G' a) a id).
  - reflexivity.
  - unfold rs_from.
    rewrite id_right.
    exact (@from_adj_counit A X F G Adj (G' a) a (id_cast (eq_sym (`1 E a)))).
Qed.

End RightStrict.

Definition lali_along_right_strict {A X : Category} {G G' : A ⟶ X}
  (P : LeftAdjointLeftInverse G)
  (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G') :
  LeftAdjointLeftInverse G'.
Proof.
  unshelve refine {|
    lali_left := lali_left P;
    lali_adj := rs_adj (lali_adj P) E;
    lali_obj := fun a =>
      eq_trans (f_equal (fobj[lali_left P]) (eq_sym (`1 E a))) (lali_obj P a)
  |}.
  intros a.
  rewrite (rs_counit (lali_adj P) E a).
  rewrite (lali_counit P a).
  rewrite fmap_id_cast.
  now rewrite id_cast_trans.
Defined.

(** ** Clause (b): a left adjoint, full, faithful, injective on objects *)

Record LeftAdjointFFInjective {A X : Category} (G : A ⟶ X) : Type := {
  ffi_left : X ⟶ A;
  ffi_adj : ffi_left ⊣ G;
  ffi_full : Category.Theory.Functor.Full G;
  ffi_faithful : Faithful G;
  ffi_injective : InjectiveOnObjects G
}.

Arguments ffi_left {A X G} _.
Arguments ffi_adj {A X G} _.
Arguments ffi_full {A X G} _.
Arguments ffi_faithful {A X G} _.
Arguments ffi_injective {A X G} _.

Definition lali_implies_ffi {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : LeftAdjointFFInjective G := {|
  ffi_left := lali_left P;
  ffi_adj := lali_adj P;
  ffi_full := lali_Full P;
  ffi_faithful := lali_Faithful P;
  ffi_injective := lali_injective_on_objects P
|}.

(** ** The image subcategory *)

Section Image.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (B : LeftAdjointFFInjective G).

Program Definition LaliImageSub : Subcategory X := {|
  sobj := fun x => { a : A & G a = x };
  shom := fun x y ox oy f => True
|}.
Next Obligation. intros; exact I. Defined.
Next Obligation. intros; exact I. Defined.

Program Definition ImageTo : A ⟶ Sub X LaliImageSub := {|
  fobj := fun a => (G a; (a; eq_refl));
  fmap := fun a a' f => (fmap[G] f; I)
|}.
Next Obligation. intros a a' f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros a; simpl; apply fmap_id. Qed.
Next Obligation. intros a a' a'' f g; simpl; apply fmap_comp. Qed.

Program Definition ImageFrom : Sub X LaliImageSub ⟶ A := {|
  fobj := fun y => `1 (`2 y);
  fmap := fun y y' f =>
    prefmap (Full := ffi_full B)
      (hom_cast (eq_sym (`2 (`2 y))) (eq_sym (`2 (`2 y'))) (`1 f))
|}.
Next Obligation.
  intros y y' f g Hfg.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite !(fmap_sur (Full := ffi_full B)).
  now apply hom_cast_respects.
Qed.
Next Obligation.
  intros y.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite (fmap_sur (Full := ffi_full B)), fmap_id.
  now rewrite hom_cast_id.
Qed.
Next Obligation.
  intros y y' y'' f g.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite fmap_comp, !(fmap_sur (Full := ffi_full B)).
  now rewrite hom_cast_comp.
Qed.


(** The two round trips, at strict functor equality. *)

Definition image_from_to_obj (a : A) : ImageFrom (ImageTo a) = a := eq_refl.

Definition image_to_from_obj (y : Sub X LaliImageSub) :
  ImageTo (ImageFrom y) = y.
Proof. destruct y as [u [b e]]; destruct e; reflexivity. Defined.

Lemma image_from_to_strict :
  @equiv _ (@Functor_StrictEq_Setoid A A) (ImageFrom ◯ ImageTo) Id[A].
Proof.
  apply (strict_equiv_of_id_cast_nat (ImageFrom ◯ ImageTo) Id[A]
           image_from_to_obj).
  intros a a' f; unfold image_from_to_obj; simpl.
  rewrite id_left, id_right.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Lemma image_to_from_strict :
  @equiv _ (@Functor_StrictEq_Setoid (Sub X LaliImageSub) (Sub X LaliImageSub))
    (ImageTo ◯ ImageFrom) Id[Sub X LaliImageSub].
Proof.
  apply (strict_equiv_of_id_cast_nat (ImageTo ◯ ImageFrom)
           Id[Sub X LaliImageSub] image_to_from_obj).
  intros y y' f.
  destruct y as [u [b e]], y' as [u' [b' e']].
  destruct e, e'; simpl.
  rewrite id_left, id_right.
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Definition ImageIso : @Isomorphism StrictCat A (Sub X LaliImageSub) :=
  @Build_Isomorphism StrictCat A (Sub X LaliImageSub) ImageTo ImageFrom
    image_to_from_strict image_from_to_strict.


(** The image subcategory is full and reflective, and [G] factors through
    its insertion. *)

Definition image_equivalence : @EquivalenceOfCategories A (Sub X LaliImageSub)
    ImageTo :=
  strict_equivalence ImageTo ImageFrom image_to_from_strict
    image_from_to_strict.

Definition image_incl_obj (y : Sub X LaliImageSub) :
  G (ImageFrom y) = Incl X LaliImageSub y := `2 (`2 y).

Lemma image_incl_strict :
  @equiv _ (@Functor_StrictEq_Setoid (Sub X LaliImageSub) X)
    (G ◯ ImageFrom) (Incl X LaliImageSub).
Proof.
  apply (strict_equiv_of_id_cast_nat (G ◯ ImageFrom) (Incl X LaliImageSub)
           image_incl_obj).
  intros y y' f.
  destruct y as [u [b e]], y' as [u' [b' e']].
  destruct e, e'; simpl.
  rewrite id_left, id_right.
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Definition image_reflective_adj :
  (ImageTo ◯ ffi_left B) ⊣ Incl X LaliImageSub :=
  rs_adj (Adjunction_Compose (ffi_adj B) (equiv_adjunction image_equivalence))
    image_incl_strict.

Definition image_full : Construction.Subcategory.Full X LaliImageSub :=
  fun x y ox oy f => I.

Definition ImageReflective : Reflective LaliImageSub := {|
  reflective_full := image_full;
  reflector := ImageTo ◯ ffi_left B;
  reflective_adj := image_reflective_adj
|}.

Lemma image_factor :
  @equiv _ (@Functor_StrictEq_Setoid A X) G (Incl X LaliImageSub ◯ ImageTo).
Proof.
  apply (strict_equiv_of_id_cast_nat G (Incl X LaliImageSub ◯ ImageTo)
           (fun a => eq_refl)).
  intros a a' f; simpl.
  now rewrite id_left, id_right.
Defined.

End Image.

(** ** Clause (c): a full reflective subcategory and an isomorphism *)

Record ReflectiveIsoPresentation {A X : Category} (G : A ⟶ X) : Type := {
  ri_sub : Subcategory X;
  ri_reflective : Reflective ri_sub;
  ri_iso : @Isomorphism StrictCat A (Sub X ri_sub);
  ri_factor : @equiv _ (@Functor_StrictEq_Setoid A X) G
                (Incl X ri_sub ◯ to ri_iso)
}.

Arguments ri_sub {A X G} _.
Arguments ri_reflective {A X G} _.
Arguments ri_iso {A X G} _.
Arguments ri_factor {A X G} _.

Definition ffi_implies_ri {A X : Category} {G : A ⟶ X}
  (B : LeftAdjointFFInjective G) : ReflectiveIsoPresentation G := {|
  ri_sub := @LaliImageSub A X G;
  ri_reflective := ImageReflective B;
  ri_iso := ImageIso B;
  ri_factor := @image_factor A X G
|}.

(** ** Transporting a left-adjoint-left-inverse along an isomorphism *)

Section StrictIsoTransport.

Context {A X Y : Category}.
Context {K : Y ⟶ X}.
Context (P : LeftAdjointLeftInverse K).
Context (H : @Isomorphism StrictCat A Y).

Definition si_equivalence : @EquivalenceOfCategories Y A (from H) :=
  strict_equivalence (from H) (to H) (iso_from_to H) (iso_to_from H).

Definition si_adj : (from H ◯ lali_left P) ⊣ (K ◯ to H) :=
  Adjunction_Compose (lali_adj P) (equiv_adjunction si_equivalence).

Definition si_obj (a : A) : (from H ◯ lali_left P) ((K ◯ to H) a) = a :=
  eq_trans (f_equal (fobj[from H]) (lali_obj P (to H a)))
           (`1 (iso_from_to H) a).

Lemma si_counit (a : A) :
  @counit A X (from H ◯ lali_left P) (K ◯ to H) si_adj a ≈ id_cast (si_obj a).
Proof.
  transitivity
    (from (@adj A Y (from H) (to H) (equiv_adjunction si_equivalence)
             (lali_left P (K (to H a))) a)
       (@counit Y X (lali_left P) K (lali_adj P) (to H a))).
  { reflexivity. }
  rewrite (lali_counit P (to H a)).
  rewrite (@from_adj_counit A Y (from H) (to H)
             (equiv_adjunction si_equivalence)).
  rewrite (equiv_adjunction_counit_at si_equivalence a).
  rewrite fmap_id_cast.
  unfold si_obj.
  rewrite <- id_cast_trans.
  reflexivity.
Qed.

Definition lali_along_strict_iso : LeftAdjointLeftInverse (K ◯ to H) := {|
  lali_left := from H ◯ lali_left P;
  lali_adj := si_adj;
  lali_obj := si_obj;
  lali_counit := si_counit
|}.

End StrictIsoTransport.

(** ** The characterization *)

Definition strict_sym {C D : Category} {F H : C ⟶ D}
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F H) :
  @equiv _ (@Functor_StrictEq_Setoid C D) H F :=
  @Equivalence_Symmetric _ _
    (@setoid_equiv _ (@Functor_StrictEq_Setoid C D)) F H E.

Definition ri_lali_implies_lali {A X : Category} {G : A ⟶ X}
  (Pres : ReflectiveIsoPresentation G)
  (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))) :
  LeftAdjointLeftInverse G :=
  lali_along_right_strict
    (lali_along_strict_iso L (ri_iso Pres))
    (strict_sym (ri_factor Pres)).

Theorem lali_characterization {A X : Category} (G : A ⟶ X) :
  (LeftAdjointLeftInverse G → LeftAdjointFFInjective G)
    * (LeftAdjointFFInjective G → ReflectiveIsoPresentation G)
    * (∀ Pres : ReflectiveIsoPresentation G,
         LeftAdjointLeftInverse (Incl X (ri_sub Pres))
           → LeftAdjointLeftInverse G).
Proof.
  split; [ split | ].
  - exact (@lali_implies_ffi A X G).
  - exact (@ffi_implies_ri A X G).
  - exact (@ri_lali_implies_lali A X G).
Defined.

Definition ri_lali_implies_ffi {A X : Category} {G : A ⟶ X}
  (Pres : ReflectiveIsoPresentation G)
  (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))) :
  LeftAdjointFFInjective G :=
  lali_implies_ffi (ri_lali_implies_lali Pres L).

Definition lali_implies_ri {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : ReflectiveIsoPresentation G :=
  ffi_implies_ri (lali_implies_ffi P).

(** ** The insertion of the image subcategory has a left-adjoint-left-inverse *)

Section ImageInsertion.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Local Notation B := (lali_implies_ffi P).

Definition ii_obj (y : Sub X (@LaliImageSub A X G)) :
  (ImageTo ◯ lali_left P) (Incl X (@LaliImageSub A X G) y) = y :=
  eq_trans
    (f_equal (fobj[ImageTo ◯ lali_left P]) (eq_sym (image_incl_obj B y)))
    (eq_trans (f_equal (fobj[@ImageTo A X G])
                 (lali_obj P (ImageFrom B y)))
              (image_to_from_obj B y)).

Lemma ii_counit (y : Sub X (@LaliImageSub A X G)) :
  @counit (Sub X (@LaliImageSub A X G)) X (ImageTo ◯ lali_left P)
    (Incl X (@LaliImageSub A X G)) (image_reflective_adj B) y
    ≈ id_cast (ii_obj y).
Proof.
  unfold image_reflective_adj.
  rewrite (rs_counit
             (Adjunction_Compose (ffi_adj B)
                (equiv_adjunction (image_equivalence B)))
             (image_incl_strict B) y).
  transitivity
    (from (@adj (Sub X (@LaliImageSub A X G)) A ImageTo (ImageFrom B)
             (equiv_adjunction (image_equivalence B))
             (lali_left P (G (ImageFrom B y))) y)
       (@counit A X (lali_left P) G (lali_adj P) (ImageFrom B y))
       ∘ fmap[ImageTo ◯ lali_left P]
           (id_cast (eq_sym (image_incl_obj B y)))).
  { reflexivity. }
  rewrite (lali_counit P (ImageFrom B y)).
  rewrite (@from_adj_counit (Sub X (@LaliImageSub A X G)) A ImageTo
             (ImageFrom B) (equiv_adjunction (image_equivalence B))).
  rewrite (equiv_adjunction_counit_at (image_equivalence B) y).
  rewrite !fmap_id_cast.
  unfold ii_obj.
  rewrite <- !id_cast_trans.
  reflexivity.
Qed.

Definition lali_image_insertion :
  LeftAdjointLeftInverse (Incl X (@LaliImageSub A X G)) := {|
  lali_left := ImageTo ◯ lali_left P;
  lali_adj := image_reflective_adj B;
  lali_obj := ii_obj;
  lali_counit := ii_counit
|}.

End ImageInsertion.

(** ** The cycle closes on presentations that come from a left-adjoint-
       left-inverse *)

Definition lali_ri_insertion {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) :
  LeftAdjointLeftInverse (Incl X (ri_sub (lali_implies_ri P))) :=
  lali_image_insertion P.

Definition lali_cycle {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali (lali_implies_ri P) (lali_ri_insertion P).

(** ** Examples *)

Definition Id_LALI {C : Category} : LeftAdjointLeftInverse (Id[C]) := {|
  lali_left := Id[C];
  lali_adj := Adjunction_Id;
  lali_obj := fun a => eq_refl;
  lali_counit := fun a => Adjunction_Id_counit
|}.

Section TerminalPoint.

Universes o h.

Context {C : Category@{o h h}}.
Context (T : @Terminal C).

Local Notation One := (_1@{o h h}).
Local Notation t := (@terminal_obj C T).

(* The functor 1 ⟶ C picking out an object.  [Theory/Shapes.v:205]'s
   [Point] is this functor, but its source is pinned at [_1@{_ Set Set}]
   (measured: [Point x : _1@{o h h} ⟶ C] is rejected with "Cannot enforce
   Set = h"), which would confine the example below to categories whose
   homs live in [Set]; the six lines are rebuilt here with the universe
   binders that keep C arbitrary. *)

Program Definition PointAt (c : C) : One ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ _ => id
|}.
Next Obligation. proper. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; now rewrite id_left. Qed.

Lemma one_cat_thin {x y : @obj One} (f g : @hom One x y) : f ≈ g.
Proof. destruct f, g; reflexivity. Qed.

Definition point_adj : Erase C ⊣ PointAt t.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros x a.
    unshelve eapply Build_Isomorphism.
    + unshelve eapply Build_SetoidMorphism.
      * exact (fun _ => @one C T x).
      * proper.
    + unshelve eapply Build_SetoidMorphism.
      * exact (fun _ => ttt).
      * proper.
    + intros g; simpl; apply one_unique.
    + intros f; simpl; now destruct f.
  - intros x y a f g; simpl; apply one_unique.
  - intros x a b f g; simpl; apply one_unique.
Defined.

Definition terminal_LALI : LeftAdjointLeftInverse (PointAt t).
Proof.
  unshelve refine {| lali_left := Erase C; lali_adj := point_adj |}.
  - intros a; now destruct a.
  - intros a; apply one_cat_thin.
Defined.

End TerminalPoint.

(** A non-degenerate instance: the walking arrow. *)

Program Definition TwoY_Terminal : @Terminal _2 := {|
  terminal_obj := TwoY;
  one := fun x => match x with
                  | TwoX => TwoXY
                  | TwoY => TwoIdY
                  end
|}.
Next Obligation.
  intros x f g; destruct x; simpl in *.
  - pose proof (TwoHom_inv TwoX TwoY f) as Hf.
    pose proof (TwoHom_inv TwoX TwoY g) as Hg.
    simpl in Hf, Hg; now subst.
  - pose proof (TwoHom_inv TwoY TwoY f) as Hf.
    pose proof (TwoHom_inv TwoY TwoY g) as Hg.
    simpl in Hf, Hg; now subst.
Qed.

Definition two_LALI : LeftAdjointLeftInverse (PointAt (C:=_2) TwoY) :=
  terminal_LALI TwoY_Terminal.

Example two_lali_left_is_Erase :
  lali_left two_LALI = Erase _2 := eq_refl.

Example two_lali_obj_TwoY :
  PointAt (C:=_2) TwoY (lali_left two_LALI TwoX) = TwoY := eq_refl.

Lemma two_lali_moves_TwoX :
  PointAt (C:=_2) TwoY (lali_left two_LALI TwoX) = TwoX → False.
Proof. simpl; discriminate. Qed.

(** ** Strict readbacks

    Every identification below holds at Leibniz equality, by [eq_refl];
    the two that do NOT are pinned in Test/ProbeLeftInverse376.v (the
    round trip [lali_cycle P = P], and the object equality of
    [ImageTo ◯ ImageFrom] at a variable object of the subcategory). *)

Section Readbacks.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).
Context (B : LeftAdjointFFInjective G).

Example ffi_left_is_lali_left :
  ffi_left (lali_implies_ffi P) = lali_left P := eq_refl.

Example ffi_adj_is_lali_adj :
  ffi_adj (lali_implies_ffi P) = lali_adj P := eq_refl.

Example ri_sub_is_image :
  ri_sub (lali_implies_ri P) = @LaliImageSub A X G := eq_refl.

Example ri_iso_to_is_ImageTo :
  to (ri_iso (ffi_implies_ri B)) = @ImageTo A X G := eq_refl.

Example ri_iso_from_is_ImageFrom :
  from (ri_iso (ffi_implies_ri B)) = ImageFrom B := eq_refl.

Example image_reflector_is_composite :
  reflector (ImageReflective B) = ImageTo ◯ ffi_left B := eq_refl.

Example image_incl_obj_is_membership (y : Sub X (@LaliImageSub A X G)) :
  image_incl_obj B y = `2 (`2 y) := eq_refl.

Example image_from_to_obj_is_refl (a : A) :
  image_from_to_obj B a = eq_refl := eq_refl.

Example lali_Full_prefmap (a a' : A) (h : G a ~> G a') :
  prefmap (Full := lali_Full P) h
    = from (@adj A X (lali_left P) G (lali_adj P) (G a) a') h
        ∘ id_cast (eq_sym (lali_obj P a)) := eq_refl.

Example lali_left_along_right_strict {G' : A ⟶ X}
  (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G') :
  lali_left (lali_along_right_strict P E) = lali_left P := eq_refl.

Example lali_image_insertion_left :
  lali_left (lali_image_insertion P) = ImageTo ◯ lali_left P := eq_refl.

End Readbacks.

Example lali_left_along_strict_iso {A X Y : Category} {K : Y ⟶ X}
  (L : LeftAdjointLeftInverse K) (H : @Isomorphism StrictCat A Y) :
  lali_left (lali_along_strict_iso L H) = from H ◯ lali_left L := eq_refl.

Example terminal_lali_left {C : Category} (T : @Terminal C) :
  lali_left (terminal_LALI T) = Erase C := eq_refl.
