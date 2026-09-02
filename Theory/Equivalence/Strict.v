Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Quotient.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.

(** * Left-adjoint-right-inverses, and Mac Lane's Exercise IV.4.3

    nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
    nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
    nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
    nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
    nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, SS IV.4, printed p. 95, Exercise 3.

    Transliterated to ASCII from the page image:

      "3.  If S : A -> C is full, faithful, and surjective on objects
       (each c in C is c = Sa for some a in A), prove that there is an
       adjoint equivalence <T, S; 1, epsilon> : C -> A with unit the
       identity (and thence that T is a left-adjoint-right-inverse
       of S)."

    Under the SS IV.1 convention the first-listed functor of a triple
    C -> A is the LEFT adjoint, so T : C ⟶ A is left adjoint to S, the
    unit 1 : Id[C] ⟹ S ◯ T is the identity, and the counit
    epsilon : T ◯ S ⟹ Id[A] is an isomorphism -- NOT an identity; see
    below.  Exercise 4 on the same page (the left-adjoint-LEFT-inverse
    characterization) is Adjunction/LeftInverse.v, which is CONSUMED here
    and not rebuilt; Exercises 1, 2 and 5 are separate catalog items and
    are cited rather than delivered.

    ** The design crux: "unit the identity" is not an equation

    In this library the unit of [T ⊣ S] at [c] runs [c ~> S (T c)]
    (Theory/Adjunction.v:217) while [id[c]] runs [c ~> c], so the two live
    in one hom-set only when [S (T c)] and [c] are the same object at
    LEIBNIZ equality.  So surjectivity on objects must carry that equation
    as DATA, and "the unit is the identity" must be stated against the
    identity TRANSPORTED along it.  This is Adjunction/LeftInverse.v's
    situation one variance over, and the same [id_cast] transport kit
    (Construction/Quotient.v:56, :69, :73, :97) does the work.

    [SurjectiveOnObjects S := ∀ c, { a & S a = c }] is therefore a chosen
    preimage together with its object equation, the exact mirror of
    Adjunction/LeftInverse.v:352's [InjectiveOnObjects], with the same
    three closure constants -- but note the ASYMMETRY in the cancellation
    lemma: [InjectiveOnObjects_cancel] recovers the INNER factor [F] of an
    injective [G ◯ F], while [SurjectiveOnObjects_cancel] recovers the
    OUTER factor [G] of a surjective one.  No choice principle is
    consumed anywhere: the tree's [∃] is [sigT], so the witness is data.

    [surjective_ESO] repackages it as Theory/Equivalence.v:154's
    [EssentiallySurjective], the generic form of
    Construction/Grothendieck/RoundTrip.v:1579's [RT_EssSurj]; at an
    [eq_refl] witness -- the shape [RT_EssSurj] is in -- both legs of the
    witnessing isomorphism are [id] on the nose
    ([surjective_ESO_refl_to], [surjective_ESO_refl_from]).

    ** What is delivered, and at what strength

    [LeftAdjointRightInverse S] is the record: a left adjoint
    [lari_left], an adjunction [lari_adj], a family
    [lari_obj c : S (lari_left c) = c], and
    [lari_unit c : unit c ≈ id_cast (eq_sym (lari_obj c))].

    Mac Lane's Exercise 3 is [ff_surjective_adjoint_equivalence], an
    [AdjointEquivalence ff_surjective_left S] (Adjoint.v:69), with
    [ff_surjective_LARI] the left-adjoint-right-inverse it carries.  The
    left adjoint [T := ff_surjective_left] has object action the chosen
    preimage and arrow action [prefmap] of the conjugate
    [id_cast⁻¹ ∘ f ∘ id_cast]; every functor law is [fmap_inj] followed by
    [fmap_sur], the [ImageFrom] pattern of Adjunction/LeftInverse.v.  The
    adjunction is built DIRECTLY from the hom-set isomorphism through
    [Build_Adjunction'] (Theory/Adjunction.v:159), which is why the unit
    computes; see the route note below.

    Strengths, measured strict first.  Holding at [eq_refl]:
    [ff_surj_left_obj], [ff_surj_left_map], [ff_surj_to], [ff_surj_from],
    [ff_surj_lari_left], [ff_surj_lari_adj], [ff_surj_equiv_adj],
    [ff_surj_counit_unfold] (the counit IS the [prefmap] of the
    transported identity), and the two comparisons with the alternative
    route below.  Reaching [≈] only: [ff_surj_unit_is], whose residue is
    exhibited at Leibniz equality by [ff_surj_unit_residue] -- the unit is
    [⌊id⌋], so it carries an [fmap[S] id] that no choice of transpose can
    remove, and the strict form is refuted and pinned in
    Test/ProbeStrict377.v.

    ** The two routes, and which one computes

    The alternative route is the one Construction/Subcategory/Dense.v
    takes: [surjective_ESO], then Theory/Equivalence/FullFaithful.v:160's
    [FF_ESO_Equivalence], then Adjoint.v:333's
    [Equivalence_to_AdjointEquivalence], then Adjoint.v:407's
    [AdjointEquivalence_swap] to put the correct functor on the left.  It
    is built here as [ff_surj_eso_adjoint_equivalence] and MEASURED
    against the direct one.

    The two left adjoints agree on BOTH actions at [eq_refl]
    ([ff_surj_eso_inverse_obj], [ff_surj_eso_inverse_map]), hence at
    Theory/Functor.v:606's [Functor_StrictEq_Setoid] with every object
    component [eq_refl] ([ff_surj_eso_inverse_strict]); the whole functor
    RECORDS are not Leibniz-equal, the three law fields being rebuilt.
    But the ADJUNCTIONS are not the same, and the difference is exactly
    what the exercise is about: the alternative route's unit does not
    reduce to the transported identity, and it does not reduce at all --
    it is stuck at [equiv_adj_to EquivalenceOfCategories_sym id], i.e. at
    the [symmetry] taken on Theory/Functor.v:149's [Functor_Setoid], whose
    [Equivalence] obligation is closed opaquely at Theory/Functor.v:193 --
    a chain confirmed constant by constant (every route constant prints a
    body; [equiv_adj_to] is [equivalence_prefmap], which projects
    [`1 equivalence_unit], and the symmetric equivalence's unit field IS
    that [symmetry]), though no experiment removes that one step and shows
    the term then reducing, so it is not claimed to be the only blocker.
    So the direct route is shipped, and both stuck points are pinned in
    the probe.

    ** What a left-adjoint-right-inverse does NOT give

    Read Exercise 3 in the direction it is stated.  The converse that
    suggests itself -- that [S] having a left-adjoint-right-inverse makes
    [S] full, faithful and surjective on objects -- is TRUE only in its
    third clause, and the other two are refuted here.

    What IS delivered is [lari_left_ff_surjective]: the LEFT adjoint is
    full and faithful ([lari_left_Full], [lari_left_Faithful]) and [S] is
    surjective on objects ([lari_surjective]).  That is the correct
    reading: for [T ⊣ S] an invertible unit makes T fully faithful, and it
    is an invertible COUNIT that would make S fully faithful.  The record
    demands nothing of the counit.  Both halves of that statement are
    already theorems in tree, cited rather than consumed:
    Adjunction/FullFaithful.v:656's [left_adjoint_fully_faithful_iff_unit_iso]
    and :475's [right_adjoint_fully_faithful_iff_counit_iso].
    [lari_left_Full] and [lari_left_Faithful] ARE derivable from the first
    in one line ([snd left_adjoint_fully_faithful_iff_unit_iso] at
    [lari_unit_IsIsomorphism], compiled out of tree), so the five lemmas
    here are a deliberate re-derivation on a measurement: requiring that
    file raises this file's closure from 38 modules to 97, where
    [Instance/Coq] was declined for 23.

    The two refutations share one construction: for any [A] with an
    initial object, the erasing functor [erase_pt A : A ⟶ 1] has a
    left-adjoint-right-inverse [erase_LARI], the left adjoint being
    constant at the initial object.  Instantiated at the walking arrow it
    gives [lari_does_not_imply_Full] -- there is no arrow TwoY ~> TwoX
    (Instance/Two.v:128) while there is one between their images -- and at
    [Sets] it gives [lari_does_not_imply_Faithful], the identity and the
    constant [true] on the two-element setoid being distinct arrows with
    equal images.  The same [Sets] witness gives
    [lari_does_not_imply_AdjointEquivalence]: the counit at that setoid
    is the unique arrow out of the empty setoid ([Sets_Initial],
    Instance/Sets.v:270), whose inverse would carry [true] into [False].
    [Sets] is chosen over [Coq] on a measurement: both refutations go
    through verbatim over either, and [Instance/Sets] is already in this
    file's closure through [Theory/Adjunction], where [Instance/Coq]
    would add twenty-three modules for two witnesses.  All three are packaged
    over a sigma binding the functor ONCE, since two occurrences of one
    universe-polymorphic constant in a single statement are two instances
    and would relate two categories rather than one.

    So the honest statement of the equivalence is one-directional: full +
    faithful + surjective-on-objects gives a left-adjoint-right-inverse
    ([ff_surjective_LARI]), and the hypothesis "S has a left adjoint" that
    the naive converse would add is REDUNDANT -- the left adjoint is
    constructed, not assumed.

    ** Non-vacuity

    [indiscrete_LARI] and [indiscrete_adjoint_equivalence] instantiate the
    headline at [Erase (Indiscrete bool)] (Reconstruct.v:416), which is
    full, faithful and surjective on objects without being injective on
    objects: [IndT ttt] is [true] on the nose, so at the other point the
    counit connects [true] to [false], two objects proved distinct by
    [indiscrete_counit_endpoints_differ].  That is why Mac Lane's epsilon
    is an isomorphism and not an identity, and why
    [counit a ≈ id[a]] is not even well-typed in general; it is pinned in
    the probe as a typing negative.

    ** Universes

    [SurjectiveOnObjects@{ao ah ap co ch cp}] is FREE: six binders, and
    its constraint block carries only the bounds [Functor] itself imposes,
    with no equation -- character for character the same five bounds
    [InjectiveOnObjects] carries.  The one difference between the two is
    the SORT: injectivity lands in [Prop], surjectivity in
    [Type@{max(Set,ao,co)}], because the chosen preimage is data.  Its
    three closure constants are not free, exactly as their mirrors are
    not: [SurjectiveOnObjects_Id] carries [cp = ch], which is [Id]'s own,
    and [SurjectiveOnObjects_Compose] and [SurjectiveOnObjects_cancel]
    bind all three categories at ONE hom-and-proof level in the BINDER,
    which is [Compose]'s, with no equation in either block.
    [surjective_ESO], by contrast, identifies both categories' hom and
    proof universes with one another, which is [EssentiallySurjective]'s
    doing.  [LeftAdjointRightInverse@{u u0 u1 u2 u3}] reads
    [A : Category@{u u3 u3}] and [C : Category@{u2 u3 u3}] in the BINDER,
    so hom is identified with proof in both and the two hom universes with
    each other; its block carries no such equation, so reading the block
    alone would report none.  [ff_surjective_left], [ff_surj_adj],
    [ff_surjective_LARI] and [ff_surjective_adjoint_equivalence] carry
    [u0 = u2] in the block (the two categories' hom levels) with both
    OBJECT universes free, and no [Set] anywhere.

    The witness block is a different matter and the restriction is
    disclosed rather than worked around: [erase_LARI] and everything below
    it read [A : Category@{_ Set Set}].  The cause is [_1]'s hom type
    [poly_unit@{h}], pinned at [Set] inside [erase_left], after which both
    hom-setoids of the adjunction's isomorphism must sit in a [Sets] whose
    carrier universe is [Set].  Two repairs were tried and neither works.
    Turning minimization to [Set] off is INERT here -- measured, by
    compiling the file with and without the flag and comparing the printed
    universe instances, which are identical -- so no such flag is set.
    Annotating [erase_left] with explicit universe binders is rejected
    outright, its [Program] obligations then needing universes outside the
    declared list, with or without the flexible-binder marker.  The pin is
    NOT claimed unavoidable, and it costs the three witnesses nothing:
    each is a concrete category, and an existential witness is not
    weakened by a restriction on the class it is drawn from.

    ** Prior art, measured at f16f04e9

    No constant named for surjectivity on objects existed anywhere:
    [rg -n 'surjective on objects|SurjectiveOnObjects'] over [*.v] returns
    prose only (Theory/Lawvere/Sets.v:39, Theory/Connected/Components.v:687,
    Construction/Grothendieck/RoundTrip.v:55,
    Construction/Coproduct/Indexed.v:253).  Neither was there any
    left-adjoint-right-inverse packaging.  The issue's own line reference
    for [EssentiallySurjective] is stale -- it is Theory/Equivalence.v:154,
    not :141; its references to [FF_ESO_Equivalence] (:160) and
    [Equivalence_to_AdjointEquivalence] (:333) are right.

    [poly_unit_all_eq] is deliberately NOT called [poly_unit_eq]:
    Instance/StrictCat/Terminal.v:28 has that name for the identical
    statement.

    ** Registration

    Nothing here is registered for instance resolution, following
    Theory/Equivalence.v: a chosen preimage is data, and a
    left-adjoint-right-inverse is a choice of adjoint, always passed
    explicitly at use sites.

    ** NOT delivered

    No dual (a right-adjoint-left-inverse, or the coreflective reading of
    the image of [T]); no comparison of [LeftAdjointRightInverse] with
    Adjunction/LeftInverse.v's [LeftAdjointLeftInverse] beyond naming the
    pair; no uniqueness statement for the left adjoint; no statement in
    [StrictCat] and no equality of functors [S ◯ T = Id[C]]; no
    identification of the two routes' ADJUNCTIONS at any strength (only
    their left adjoints are compared); no characterization of when a
    left-adjoint-right-inverse upgrades to an adjoint equivalence; and no
    [Reflective]- or [Coreflective]-style subcategory packaging. *)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Surjectivity on objects, as data *)

Definition SurjectiveOnObjects@{ao ah ap co ch cp}
  {A : Category@{ao ah ap}} {C : Category@{co ch cp}} (S : A ⟶ C) :=
  ∀ c : C, { a : A & S a = c }.

Definition SurjectiveOnObjects_Id@{co ch cp} {C : Category@{co ch cp}} :
  SurjectiveOnObjects Id[C] :=
  fun c => (c; eq_refl).

Definition SurjectiveOnObjects_Compose {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C}
  (HG : SurjectiveOnObjects G) (HF : SurjectiveOnObjects F) :
  SurjectiveOnObjects (G ◯ F) :=
  fun c => (`1 (HF (`1 (HG c)));
            eq_trans (f_equal (fobj[G]) (`2 (HF (`1 (HG c)))))
                     (`2 (HG c))).

Definition SurjectiveOnObjects_cancel {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C} (HGF : SurjectiveOnObjects (G ◯ F)) :
  SurjectiveOnObjects G :=
  fun c => (F (`1 (HGF c)); `2 (HGF c)).

Definition surjective_ESO {A C : Category} {S : A ⟶ C}
  (surj : SurjectiveOnObjects S) : EssentiallySurjective S :=
  @Build_EssentiallySurjective A C S
    (fun c => `1 (surj c))
    (fun c => id_cast_iso (`2 (surj c))).

(* The chosen preimage survives the repackaging on the nose, and at an
   [eq_refl] witness -- the shape [Construction/Grothendieck/RoundTrip.v]'s
   [RT_EssSurj] is in -- the witnessing isomorphism has [id] for both
   legs. *)
Example surjective_ESO_obj {A C : Category} {S : A ⟶ C}
  (surj : SurjectiveOnObjects S) (c : C) :
  @eso_obj A C S (surjective_ESO surj) c = `1 (surj c) := eq_refl.

Example surjective_ESO_refl_to {C : Category} (c : C) :
  to (@eso_iso C C Id[C] (surjective_ESO SurjectiveOnObjects_Id) c) = id
  := eq_refl.

Example surjective_ESO_refl_from {C : Category} (c : C) :
  from (@eso_iso C C Id[C] (surjective_ESO SurjectiveOnObjects_Id) c) = id
  := eq_refl.

(** ** Left-adjoint-right-inverses *)

Record LeftAdjointRightInverse {A C : Category} (S : A ⟶ C) : Type := {
  lari_left : C ⟶ A;
  lari_adj : lari_left ⊣ S;
  lari_obj (c : C) : S (lari_left c) = c;
  lari_unit (c : C) :
    @unit A C lari_left S lari_adj c ≈ id_cast (eq_sym (lari_obj c))
}.

Arguments lari_left {A C S} _.
Arguments lari_adj {A C S} _.
Arguments lari_obj {A C S} _ _.
Arguments lari_unit {A C S} _ _.

(** ** Consequences of having a left-adjoint-right-inverse *)

Section Consequences.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context (P : LeftAdjointRightInverse S).

Local Notation T := (lari_left P).
Local Notation e := (lari_obj P).
Local Notation D := (lari_adj P).

Definition lari_unit_iso (c : C) : c ≅ S (T c) := id_cast_iso_sym (e c).

Program Definition lari_unit_IsIsomorphism (c : C) :
  IsIsomorphism (@unit A C T S D c) := {|
  two_sided_inverse := id_cast (e c)
|}.
Next Obligation.
  intros c; rewrite (lari_unit P c); apply id_cast_inv_l.
Qed.
Next Obligation.
  intros c; rewrite (lari_unit P c); apply id_cast_inv_r.
Qed.

Definition lari_surjective : SurjectiveOnObjects S :=
  fun c => (T c; e c).

(* The forward transpose of an image arrow is the unit followed by the
   arrow itself: [to_adj_nat_l] at the identity. *)
Lemma lari_to_fmap {x y : C} (f : x ~> y) :
  to (@adj A C T S D x (T y)) (fmap[T] f) ≈ @unit A C T S D y ∘ f.
Proof.
  rewrite <- (id_left (fmap[T] f)).
  rewrite (@to_adj_nat_l A C T S D).
  reflexivity.
Qed.

(* The unit is componentwise monic, being a transported identity. *)
Lemma lari_unit_monic {x y : C} (f g : x ~> y) :
  @unit A C T S D y ∘ f ≈ @unit A C T S D y ∘ g → f ≈ g.
Proof.
  intros Hfg.
  rewrite (lari_unit P y) in Hfg.
  rewrite <- (id_left f), <- (id_left g).
  rewrite <- (id_cast_inv_r (e y)).
  rewrite <- !comp_assoc.
  now rewrite Hfg.
Qed.

(* The forward transpose is injective, being one leg of an isomorphism. *)
Lemma lari_adj_to_inj {x : C} {a : A} (u v : T x ~> a) :
  to (@adj A C T S D x a) u ≈ to (@adj A C T S D x a) v → u ≈ v.
Proof.
  intros Huv.
  rewrite <- (@to_adj_comp_law A C T S D x a u).
  rewrite <- (@to_adj_comp_law A C T S D x a v).
  now rewrite Huv.
Qed.

Program Definition lari_left_Full : Category.Theory.Functor.Full T := {|
  prefmap := fun x y g =>
    id_cast (e y) ∘ to (@adj A C T S D x (T y)) g
|}.
Next Obligation.
  intros x y g.
  apply lari_adj_to_inj.
  rewrite lari_to_fmap.
  rewrite (lari_unit P y).
  rewrite comp_assoc, id_cast_inv_l, id_left.
  reflexivity.
Qed.

Program Definition lari_left_Faithful : Faithful T := {| fmap_inj := _ |}.
Next Obligation.
  intros x y f g Hfg.
  apply lari_unit_monic.
  rewrite <- !lari_to_fmap.
  now rewrite Hfg.
Qed.

(* What a left-adjoint-right-inverse of [S] yields: the LEFT adjoint is
   full and faithful, and [S] is surjective on objects.  Nothing here
   asserts that [S] is full or faithful; both are refuted below. *)
Definition lari_left_ff_surjective :
  (Category.Theory.Functor.Full T * Faithful T) * SurjectiveOnObjects S :=
  ((lari_left_Full, lari_left_Faithful), lari_surjective).

End Consequences.

Arguments lari_unit_iso {A C S} _ _.
Arguments lari_surjective {A C S} _ _.

(** ** A conjugation lemma for the two casts *)

Lemma cast_conj_comp {D : Category} {x y z x' y' z' : D}
  (ex : x' = x) (ey : y' = y) (ez : z' = z) (f : y ~> z) (g : x ~> y) :
  (id_cast (eq_sym ez) ∘ f ∘ id_cast ey)
    ∘ (id_cast (eq_sym ey) ∘ g ∘ id_cast ex)
    ≈ id_cast (eq_sym ez) ∘ (f ∘ g) ∘ id_cast ex.
Proof. destruct ex, ey, ez; cat. Qed.

(** ** Mac Lane's Exercise IV.4.3 *)

Section FFSurjective.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).

Definition ff_surj_obj (c : C) : A := `1 (surj c).

Definition ff_surj_eq (c : C) : S (ff_surj_obj c) = c := `2 (surj c).

Definition ff_surj_conj {c c' : C} (f : c ~> c') :
  S (ff_surj_obj c) ~> S (ff_surj_obj c') :=
  id_cast (eq_sym (ff_surj_eq c')) ∘ f ∘ id_cast (ff_surj_eq c).

Program Definition ff_surjective_left : C ⟶ A := {|
  fobj := ff_surj_obj;
  fmap := fun c c' f => prefmap (ff_surj_conj f)
|}.
Next Obligation.
  intros c c' f g Hfg.
  apply fmap_inj.
  rewrite !fmap_sur.
  unfold ff_surj_conj.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c.
  apply fmap_inj.
  rewrite fmap_sur, fmap_id.
  unfold ff_surj_conj.
  rewrite id_right.
  apply id_cast_inv_l.
Qed.
Next Obligation.
  intros c c' c'' f g.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur.
  unfold ff_surj_conj.
  symmetry.
  apply cast_conj_comp.
Qed.

Program Definition ff_surj_hom_iso (c : C) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (ff_surjective_left c) a;
       is_setoid := @homset A (ff_surjective_left c) a |}
    {| carrier := @hom C c (S a);
       is_setoid := @homset C c (S a) |} := {|
  to := {| morphism := fun f => fmap[S] f ∘ id_cast (eq_sym (ff_surj_eq c)) |};
  from := {| morphism := fun g => prefmap (g ∘ id_cast (ff_surj_eq c)) |}
|}.
Next Obligation.
  intros c a f g Hfg; simpl in *.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c a f g Hfg; simpl in *.
  apply fmap_inj.
  rewrite !fmap_sur.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c a g; simpl in *.
  rewrite fmap_sur.
  rewrite <- comp_assoc, id_cast_inv_r.
  apply id_right.
Qed.
Next Obligation.
  intros c a f; simpl in *.
  apply fmap_inj.
  rewrite fmap_sur.
  rewrite <- comp_assoc, id_cast_inv_l.
  apply id_right.
Qed.

Definition ff_surj_adj : ff_surjective_left ⊣ S.
Proof.
  unshelve eapply (@Build_Adjunction' A C ff_surjective_left S
                     ff_surj_hom_iso).
  - intros x y z f g; simpl.
    rewrite fmap_comp, fmap_sur.
    unfold ff_surj_conj.
    rewrite <- !comp_assoc.
    rewrite id_cast_inv_r, id_right.
    reflexivity.
  - intros x y z f g; simpl.
    rewrite fmap_comp.
    rewrite <- comp_assoc.
    reflexivity.
Defined.

Program Definition ff_surjective_LARI : LeftAdjointRightInverse S := {|
  lari_left := ff_surjective_left;
  lari_adj := ff_surj_adj;
  lari_obj := ff_surj_eq
|}.
Next Obligation.
  intros c.
  unfold unit; simpl.
  rewrite fmap_id, id_left.
  reflexivity.
Qed.

Definition ff_surjective_unit_iso (c : C) :
  IsIsomorphism (@unit A C ff_surjective_left S ff_surj_adj c) :=
  lari_unit_IsIsomorphism ff_surjective_LARI c.

Lemma ff_surj_counit_unfold (a : A) :
  @counit A C ff_surjective_left S ff_surj_adj a
    = prefmap (id[S a] ∘ id_cast (ff_surj_eq (S a))).
Proof. reflexivity. Qed.

Program Definition ff_surjective_counit_iso (a : A) :
  IsIsomorphism (@counit A C ff_surjective_left S ff_surj_adj a) := {|
  two_sided_inverse := prefmap (id_cast (eq_sym (ff_surj_eq (S a))))
|}.
Next Obligation.
  intros a.
  rewrite ff_surj_counit_unfold.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  rewrite id_left.
  apply id_cast_inv_r.
Qed.
Next Obligation.
  intros a.
  rewrite ff_surj_counit_unfold.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  rewrite id_left.
  apply id_cast_inv_l.
Qed.

Definition ff_surjective_adjoint_equivalence :
  AdjointEquivalence ff_surjective_left S :=
  @Build_AdjointEquivalence C A ff_surjective_left S ff_surj_adj
    ff_surjective_unit_iso ff_surjective_counit_iso.

(** *** Strict readbacks and the one residue *)

Example ff_surj_left_obj (c : C) : ff_surjective_left c = ff_surj_obj c :=
  eq_refl.

Example ff_surj_left_map (c c' : C) (f : c ~> c') :
  fmap[ff_surjective_left] f = prefmap (ff_surj_conj f) := eq_refl.

Example ff_surj_to (c : C) (a : A) (f : ff_surjective_left c ~> a) :
  to (@adj A C ff_surjective_left S ff_surj_adj c a) f
    = fmap[S] f ∘ id_cast (eq_sym (ff_surj_eq c)) := eq_refl.

Example ff_surj_from (c : C) (a : A) (g : c ~> S a) :
  from (@adj A C ff_surjective_left S ff_surj_adj c a) g
    = prefmap (g ∘ id_cast (ff_surj_eq c)) := eq_refl.

(* The unit is the transported identity only up to [≈]: the residue is a
   [fmap[S] id], exhibited here at Leibniz equality. *)
Example ff_surj_unit_residue (c : C) :
  @unit A C ff_surjective_left S ff_surj_adj c
    = fmap[S] (id[ff_surjective_left c]) ∘ id_cast (eq_sym (ff_surj_eq c))
  := eq_refl.

Definition ff_surj_unit_is (c : C) :
  @unit A C ff_surjective_left S ff_surj_adj c
    ≈ id_cast (eq_sym (ff_surj_eq c)) :=
  lari_unit ff_surjective_LARI c.

Example ff_surj_lari_left : lari_left ff_surjective_LARI = ff_surjective_left
  := eq_refl.

Example ff_surj_lari_adj : lari_adj ff_surjective_LARI = ff_surj_adj
  := eq_refl.

Example ff_surj_equiv_adj :
  @adj_equivalence C A ff_surjective_left S ff_surjective_adjoint_equivalence
    = ff_surj_adj := eq_refl.

(** *** The route through [FF_ESO_Equivalence], measured *)

Definition ff_surj_eso : EssentiallySurjective S := surjective_ESO surj.

Definition ff_surj_eso_equivalence : EquivalenceOfCategories S :=
  @FF_ESO_Equivalence A C S _ _ ff_surj_eso.

Definition ff_surj_eso_adjoint_equivalence :
  AdjointEquivalence (@ff_eso_inverse A C S _ _ ff_surj_eso) S :=
  AdjointEquivalence_swap
    (Equivalence_to_AdjointEquivalence ff_surj_eso_equivalence).

(* Both actions of the two left adjoints agree on the nose. *)
Example ff_surj_eso_inverse_obj (c : C) :
  @ff_eso_inverse A C S _ _ ff_surj_eso c = ff_surjective_left c := eq_refl.

Example ff_surj_eso_inverse_map (c c' : C) (f : c ~> c') :
  fmap[@ff_eso_inverse A C S _ _ ff_surj_eso] f
    = fmap[ff_surjective_left] f := eq_refl.

(* Hence the two left adjoints are equal at [Functor_StrictEq_Setoid], with
   every object component [eq_refl]; the whole functor RECORDS are not
   Leibniz-equal, the three law fields being rebuilt. *)
Program Definition ff_surj_eso_inverse_strict :
  @equiv _ (@Functor_StrictEq_Setoid C A)
    (@ff_eso_inverse A C S _ _ ff_surj_eso) ff_surjective_left :=
  (fun _ => eq_refl; _).
Next Obligation. intros x y f; reflexivity. Qed.


End FFSurjective.

(** ** Witnesses *)

(* Any two parallel arrows of the point are equal: its hom is [poly_unit]. *)
Lemma one_hom_unique {x y : @obj _1} (f g : x ~{_1}~> y) : f ≈ g.
Proof. destruct f, g; reflexivity. Qed.

(* [_1]'s hom-setoid is [Morphism_equality], i.e. Leibniz equality, and a
   tactic that unfolds [≈] leaves goals in that shape.  [apply] cannot use
   the lemma just above on such a goal: [hom _1] ignores its endpoints, so
   the implicit [y] is not determined by unification.  The endpoint-free
   spelling below is what those goals need.  It is NOT called
   [poly_unit_eq]: that name is taken by Instance/StrictCat/Terminal.v:28
   for the identical statement, and the print-assumptions target loads many
   modules into one scope, where a shared name audits the wrong constant. *)
Lemma poly_unit_all_eq (f g : poly_unit) : f = g.
Proof. destruct f, g; reflexivity. Qed.

(** *** The erasing functor of a category with an initial object *)

Program Definition erase_left {A : Category}
  (I : @Initial A) : _1 ⟶ A := {|
  fobj := fun _ => @initial_obj A I;
  fmap := fun _ _ _ => id
|}.
Next Obligation. proper. Qed.
Next Obligation. intros; simpl; rewrite ?id_left; reflexivity. Qed.

Definition erase_pt (A : Category) : A ⟶ _1 := Erase A.

Program Definition erase_hom_iso {A : Category}
  (I : @Initial A) (x : @obj _1) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (erase_left I x) a;
       is_setoid := @homset A (erase_left I x) a |}
    {| carrier := @hom _1 x (erase_pt A a);
       is_setoid := @homset _1 x (erase_pt A a) |} := {|
  to := {| morphism := fun _ => ttt |};
  from := {| morphism := fun _ => @zero A I a |}
|}.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.

Definition erase_adj {A : Category} (I : @Initial A) :
  erase_left I ⊣ erase_pt A.
Proof.
  unshelve eapply (@Build_Adjunction' A _ (erase_left I) (erase_pt A)
                     (erase_hom_iso I)).
  - intros x y z f g; apply one_hom_unique.
  - intros x y z f g; apply one_hom_unique.
Defined.

Definition erase_obj_eq {A : Category} (I : @Initial A) :
  ∀ c, erase_pt A (erase_left I c) = c :=
  fun c => match c with ttt => eq_refl end.

Program Definition erase_LARI {A : Category} (I : @Initial A) :
  LeftAdjointRightInverse (erase_pt A) := {|
  lari_left := erase_left I;
  lari_adj := erase_adj I;
  lari_obj := erase_obj_eq I
|}.
Next Obligation. intros A I c; apply one_hom_unique. Qed.

Example erase_pt_is_Erase (A : Category) : erase_pt A = Erase A := eq_refl.

(** *** The walking arrow: a left-adjoint-right-inverse without fullness *)

Program Definition Two_Initial : @Initial _2 := {|
  terminal_obj := TwoX;
  one := fun x => match x return TwoX ~{_2}~> x with
                  | TwoX => TwoIdX
                  | TwoY => TwoXY
                  end
|}.
Next Obligation. intros x f g; apply Two_thin. Qed.

Definition two_erase_LARI : LeftAdjointRightInverse (erase_pt _2) :=
  erase_LARI Two_Initial.

Example two_erase_left_TwoY :
  lari_left two_erase_LARI (erase_pt _2 TwoY) = TwoX := eq_refl.

Lemma two_erase_object_moved :
  lari_left two_erase_LARI (erase_pt _2 TwoY) = TwoY → False.
Proof. discriminate. Qed.

Theorem two_erase_not_Full :
  Category.Theory.Functor.Full (Erase _2) → False.
Proof.
  intros F.
  exact (TwoHom_Y_X_absurd (@prefmap _2 _1 (Erase _2) F TwoY TwoX ttt)).
Qed.

(* Packaged so that BOTH halves speak of one and the same functor: two
   separate occurrences of [erase_pt _2] in one statement would be two
   universe instances, and the pair would then relate two categories
   rather than one. *)
Definition lari_does_not_imply_Full :
  { X : Category & { S : X ⟶ _1 &
      LeftAdjointRightInverse S
        * (Category.Theory.Functor.Full S → False) } } :=
  (_2; (erase_pt _2; (two_erase_LARI, two_erase_not_Full))).

(** *** Sets: a left-adjoint-right-inverse without faithfulness *)

Definition sets_erase_LARI : LeftAdjointRightInverse (erase_pt Sets) :=
  erase_LARI Sets_Initial.

(* The two-element setoid under Leibniz equality, and two distinct parallel
   arrows on it.  The lambda domains are annotated and the respectfulness
   certificates written by hand: left to instance search, an unannotated
   record literal resolves its source setoid before meeting the expected
   type (the Theory/Universal/Element.v hazard). *)
Definition sets_bool_obj : SetoidObject :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition sets_bool_id : sets_bool_obj ~{Sets}~> sets_bool_obj :=
  {| morphism := fun b : bool => b;
     proper_morphism := ltac:(intros a b H; exact H) |}.

Definition sets_bool_const_true : sets_bool_obj ~{Sets}~> sets_bool_obj :=
  {| morphism := fun _ : bool => true;
     proper_morphism := ltac:(intros a b H; reflexivity) |}.

Theorem sets_erase_not_Faithful : Faithful (Erase Sets) → False.
Proof.
  intros FF.
  assert (@fmap Sets _1 (Erase Sets) sets_bool_obj sets_bool_obj sets_bool_id
            ≈ @fmap Sets _1 (Erase Sets) sets_bool_obj sets_bool_obj
                sets_bool_const_true)
    as Hf by reflexivity.
  pose proof (@fmap_inj Sets _1 (Erase Sets) FF sets_bool_obj sets_bool_obj
                sets_bool_id sets_bool_const_true Hf false) as Hx.
  simpl in Hx.
  discriminate.
Qed.

Definition lari_does_not_imply_Faithful :
  { X : Category & { S : X ⟶ _1 &
      LeftAdjointRightInverse S * (Faithful S → False) } } :=
  (Sets; (erase_pt Sets; (sets_erase_LARI, sets_erase_not_Faithful))).

Theorem sets_erase_counit_not_iso :
  IsIsomorphism (@counit Sets _ (lari_left sets_erase_LARI) (erase_pt Sets)
                   (lari_adj sets_erase_LARI) sets_bool_obj) → False.
Proof. intros [g _ _]; destruct (g true). Qed.

Definition lari_does_not_imply_AdjointEquivalence :
  { X : Category & { S : X ⟶ _1 & { P : LeftAdjointRightInverse S &
      { a : X & IsIsomorphism
                  (@counit X _1 (lari_left P) S (lari_adj P) a) → False } } } }
  := (Sets; (erase_pt Sets; (sets_erase_LARI;
       (sets_bool_obj; sets_erase_counit_not_iso)))).

(** *** A non-degenerate instance of the exercise *)

Program Definition indiscrete_erase_Full :
  Category.Theory.Functor.Full (Erase (Indiscrete bool)) := {|
  prefmap := fun x y g => tt
|}.
Next Obligation. intros x y g; apply one_hom_unique. Qed.

Program Definition indiscrete_erase_Faithful :
  Faithful (Erase (Indiscrete bool)) := {| fmap_inj := _ |}.
Next Obligation. intros x y f g Hfg; destruct f, g; reflexivity. Qed.

Definition indiscrete_erase_surjective :
  SurjectiveOnObjects (Erase (Indiscrete bool)) :=
  fun c => (true; match c with ttt => eq_refl end).

Definition IndT : _1 ⟶ Indiscrete bool :=
  @ff_surjective_left (Indiscrete bool) _1 (Erase (Indiscrete bool))
    indiscrete_erase_Full indiscrete_erase_Faithful
    indiscrete_erase_surjective.

Definition indiscrete_LARI :
  LeftAdjointRightInverse (Erase (Indiscrete bool)) :=
  @ff_surjective_LARI (Indiscrete bool) _1 (Erase (Indiscrete bool))
    indiscrete_erase_Full indiscrete_erase_Faithful
    indiscrete_erase_surjective.

Definition indiscrete_adjoint_equivalence :
  AdjointEquivalence IndT (Erase (Indiscrete bool)) :=
  @ff_surjective_adjoint_equivalence (Indiscrete bool) _1
    (Erase (Indiscrete bool)) indiscrete_erase_Full
    indiscrete_erase_Faithful indiscrete_erase_surjective.

Example indiscrete_left_obj : IndT ttt = true := eq_refl.

Lemma indiscrete_counit_endpoints_differ :
  IndT (Erase (Indiscrete bool) false) = false → False.
Proof. discriminate. Qed.

