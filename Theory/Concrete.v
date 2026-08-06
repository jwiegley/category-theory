Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(** * Concrete categories *)

(* nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.7 ("Large Categories"), printed p. 26
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Definition 1.6.18 and Example 1.6.19, printed pp. 45-46
   Book:      Awodey, "Category Theory", 2nd ed., OUP 2010, §1.5, Remark 1.7,
              printed p. 15
   Paper:     Freyd, "Homotopy is not concrete", in "The Steenrod Algebra and
              Its Applications", Lecture Notes in Mathematics 168, Springer
              1970, pp. 25-34

   A concrete category, in Mac Lane's §I.7 sense, is a PAIR `⟨C, U⟩`: a
   category together with a chosen faithful functor `U : C ⟶ Sets`.  The
   pairing is the whole point.  Concreteness is not a property a category has
   on its own; it is structure one equips a category with, and different
   choices of `U` on the same `C` give different concrete categories.  The
   class below therefore carries the functor as a field rather than
   existentially quantifying it.

   The intended reading — every object has an underlying set, and every arrow
   is an actual function between those sets — is recorded here as a
   definitional unfolding rather than as a separate axiom, since it IS what
   the two fields say once they are unfolded:

     - the object part `underlying x` is the underlying set of `x`;
     - the arrow part `fmap[underlying] f` is the actual function
       carried by `f`, and `fmap_respects` says an arrow determines its
       function;
     - `underlying_faithful` says the function determines the arrow.

   [concrete_arrow_eq] below is the second bullet's converse spelled out at
   the level of elements: two parallel arrows agreeing pointwise on the
   underlying sets are already equal in `C`.  This is Riehl's gloss
   (Definition 1.6.18): being a morphism is a PROPERTY of the underlying
   function — continuity, say — rather than extra data, and a forgetful
   functor is not faithful exactly when morphisms carry structure invisible
   on the underlying sets.

   Note the setoid discipline of this library.  `Sets` (Instance/Sets.v) is
   the category of setoids, so "the underlying set" is a carrier type plus an
   equivalence relation, and "actual function" means a setoid map.  Equality
   of arrows in THIS FILE and its two companions is `≈` throughout, never
   `=` — a claim about these three files only, not about the library, which
   does state a few deliberate arrow equalities elsewhere (for instance
   Construction/Quotient.v's cast-irrelevance lemmas).  Concretely, faithfulness reads
   `fmap f ≈ fmap g → f ≈ g` with `≈` at both ends: the `Sets`-side `≈` is
   pointwise equivalence of setoid maps, the `C`-side `≈` is `C`'s hom-setoid.

   Awodey's refinement (§1.5, Remark 1.7) is developed in the second half of
   this file.  He observes that the naive notion is defective and proposes
   testing arrows against GENERALIZED ELEMENTS: arrows `f, g : x ~> y` should
   be determined by their composites `f ∘ e`, `g ∘ e` with maps `e : t ~> x`
   out of a test object `t`.  An object with that property is a separator (a
   generator): [Separator] below.  A separator is exactly what makes the
   representable `Hom(t, −) : C ⟶ Sets` faithful, so every separator
   concretizes its category — [Concrete_of_Separator].  Awodey's own case is
   `t` terminal, i.e. testing by global elements; that is
   [WellPointedCategory], and it yields [Concrete_of_WellPointed].

   Naming caution: [WellPointedCategory] here is unrelated to the
   [WellPointed] class of Instance/Fun.v:240, which is a condition on a
   POINTED ENDOFUNCTOR (`F ⊳ point` and `point ⊲ F` agreeing), not on a
   category.  The two notions share only the English adjective; hence the
   distinct name.

   Disclosed deferrals (the two negative halves of Mac Lane's §I.7 remark)
   ---------------------------------------------------------------------

   (1) Toph, the pointed homotopy category, has NO faithful functor to
       sets whatsoever (Freyd 1970).  That theorem is out of scope here and
       is not proved, weakened, or assumed anywhere in this development.  It
       is not even stateable in-tree yet: the library has no homotopy
       category.  Riehl records the same result as a footnote to Definition
       1.6.18.

   (2) Rel, the category of sets and relations (Instance/Rel.v), is often
       quoted alongside Toph as "not concrete".  That quotation is too
       strong, and this development does not repeat it.  What is true, and
       what Instance/Concrete.v proves, is a statement about the EVIDENT
       candidate functor: no functor `U : Rel ⟶ Sets` whose value at the
       one-element set is a subsingleton can be faithful, because Rel already
       has two distinct endorelations of the one-element set.  The evident
       "underlying set" candidate has exactly that property, so it is not
       faithful.  Rel is nevertheless concretizable — Instance/Concrete.v
       exhibits `Rel_Concrete` via the direct-image (powerset) functor, whose
       value at the one-element set is a two-element setoid, precisely
       escaping the obstruction.  So the honest reading of Mac Lane's remark
       is "not concrete via its evident forgetful functor", and that is what
       is proved.  Non-concretizability of Rel is not claimed and would in
       fact be false. *)

Section Concrete.

(* A concrete category: a category `C` paired with a chosen faithful functor
   to `Sets`.  Mac Lane §I.7's `⟨C, U⟩`; Riehl §1.6, Definition 1.6.18. *)
Class Concrete (C : Category) := {
  underlying : C ⟶ Sets;             (* the chosen underlying-set functor U *)
  underlying_faithful : Faithful underlying   (* arrows ARE actual functions *)
}.

#[export] Existing Instance underlying_faithful.

Context {C : Category}.
Context `{Con : @Concrete C}.

(* The actual function carried by an arrow: the object part of [underlying]
   supplies the underlying set of each object, and [concrete_fun f] is `f`
   read as a setoid map between those sets.  (`SetoidMorphism` coerces to its
   carrier function, so `concrete_fun f a` is literally an application.) *)
Definition concrete_fun {x y : C} (f : x ~> y) :
  underlying x ~{Sets}~> underlying y := fmap[underlying] f.

(* An arrow determines its function.  This half is just functoriality
   ([fmap_respects]); it is recorded so the two halves sit together. *)
Lemma concrete_fun_respects {x y : C} (f g : x ~> y) :
  f ≈ g → ∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a.
Proof.
  intros Hfg a.
  exact (fmap_respects (Functor:=underlying) x y f g Hfg a).
Qed.

(* The function determines the arrow: "arrows ARE actual functions", as the
   definitional unfolding of [underlying_faithful] at the level of elements.
   Note that the conclusion is `≈` in `C`'s hom-setoid and the hypothesis is
   `≈` in the codomain setoid — no `=` occurs on either side. *)
Lemma concrete_arrow_eq {x y : C} (f g : x ~> y) :
  (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a) → f ≈ g.
Proof.
  intros Hfg.
  apply (fmap_inj (F:=underlying)).
  exact Hfg.
Qed.

(* The two halves packaged as the biconditional Riehl states: parallel arrows
   are equal exactly when the functions they carry agree pointwise. *)
Corollary concrete_arrow_iff {x y : C} (f g : x ~> y) :
  f ≈ g ↔ (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a).
Proof.
  split.
  - apply concrete_fun_respects.
  - apply concrete_arrow_eq.
Qed.

End Concrete.

Arguments concrete_fun {C Con x y} f.

(** ** Awodey's refinement: separators and well-pointedness *)

Section Separator.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/separator

   A separator (generator) is a test object `t` whose generalized elements
   `e : t ~> x` jointly detect equality of arrows out of `x`.  Awodey §1.5,
   Remark 1.7 introduces exactly this condition, as the repair of the naive
   notion of concreteness.  Compare Adjunction/SAFT.v:99's `Cogenerator`,
   which is the dual notion (arrows INTO a test object) packaged there for
   the special adjoint functor theorem. *)
Class Separator (t : C) := {
  separates {x y : C} (f g : x ~> y) :
    (∀ e : t ~> x, f ∘ e ≈ g ∘ e) → f ≈ g   (* generalized elements detect ≈ *)
}.

(* A separator concretizes: `Hom(t, −)` is faithful precisely when `t`
   separates, since `fmap[Hom(t,−)] f ≈ fmap[Hom(t,−)] g` unfolds to
   `∀ e : t ~> x, f ∘ e ≈ g ∘ e`.  This is the exact sense in which Awodey's
   refinement implies (his version of) concreteness. *)
Program Definition Concrete_of_Separator (t : C) `{@Separator t} :
  Concrete C := {|
  underlying := fobj[Curried_Hom C] t
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  apply (separates (t:=t)).
  intro e.
  exact (Hfg e).
Qed.

(* The converse reading: whenever `Hom(t, −)` is faithful, `t` separates.  So
   [Separator t] and faithfulness of the representable are interderivable, and
   neither direction is an extra assumption. *)
Definition Separator_of_Faithful (t : C)
  (H : Faithful (fobj[Curried_Hom C] t)) : Separator t.
Proof.
  constructor; intros x y f g Hfg.
  apply (fmap_inj (F:=fobj[Curried_Hom C] t)).
  simpl; intro e.
  exact (Hfg e).
Qed.

End Separator.

Arguments separates {C} t {Separator x y} f g _.

(* Awodey's own case: the test object is terminal, so generalized elements are
   GLOBAL elements `1 ~> x` — the points of `x`.  A category in which the
   terminal object separates is well-pointed.

   This is a property of a CATEGORY equipped with a terminal object.  It has
   nothing to do with the [WellPointed] class of Instance/Fun.v:240, which is
   a coherence condition on a pointed endofunctor; the names are kept apart
   deliberately. *)
Definition WellPointedCategory (C : Category) `{T : @Terminal C} : Type :=
  Separator (@terminal_obj C T).

(* A well-pointed category is concrete, via its global-elements functor
   `Hom(1, −)`.  This is Awodey's refined notion of concreteness. *)
Definition Concrete_of_WellPointed {C : Category} `{T : @Terminal C}
  (W : WellPointedCategory C) : Concrete C :=
  @Concrete_of_Separator C (@terminal_obj C T) W.

(** ** The category of setoids is concrete, and well-pointed *)

(* `Sets` is concrete by way of its identity functor: an object IS its
   underlying set and an arrow IS its function.  Faithfulness is then the
   identity implication.  This instance is the degenerate one, and it is NOT
   vacuous: `Sets` has parallel arrows that differ, as [Sets_two_arrows]
   below witnesses. *)
#[export] Program Instance Sets_Concrete@{o so+} : Concrete Sets@{o so} := {|
  underlying := Id[Sets@{o so}]
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  exact Hfg.
Qed.

(* The two-element setoid, used below to show the `Sets` instance has
   content. *)
Definition bool_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := @eq bool ; setoid_equiv := eq_equivalence |} |}.

(* Non-vacuity of [Sets_Concrete]: faithfulness is not free, because the
   hom-setoid it is injective on is not trivial.  The identity and negation
   maps on the two-element setoid are parallel arrows that are DISTINCT in
   the hom-setoid `bool_setoid_object ~{Sets}~> bool_setoid_object`, whose
   `≈` is pointwise equality of the underlying functions. *)
Program Definition Sets_negb@{o so+} :
  bool_setoid_object@{o o} ~{Sets@{o so}}~> bool_setoid_object@{o o} :=
  {| morphism := negb |}.

(* Stated with an explicit `→ False` rather than `¬`: hom-equivalence in this
   library is a `crelation`, i.e. `Type`-valued, and `¬` is `Prop`-valued. *)
Lemma Sets_two_arrows@{o so+} :
  @id Sets@{o so} bool_setoid_object@{o o} ≈ Sets_negb@{o so} → False.
Proof.
  intro Heq.
  (* `≈` in this hom-setoid is pointwise `=` on `bool`; instantiate at
     `true`. *)
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(* The point of a setoid `x` at an element `a`: the constant map out of the
   singleton terminal object.  This is the same probe Instance/Sets.v uses to
   characterize monos as injections. *)
Program Definition Sets_point@{o so+} {x : Sets@{o so}} (a : carrier x) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> x := {| morphism := fun _ => a |}.

(* `Sets` is well-pointed: a point of `x` is a map out of the singleton
   setoid, and the constant map at `a` is such a point picking out `a`.  So
   global elements detect equality of setoid maps. *)
#[export] Instance Sets_Separator@{o so+} :
  @Separator Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  constructor.
  intros x y f g Hfg a.
  exact (Hfg (Sets_point a) ttt).
Qed.

Definition Sets_WellPointed@{o so+} : WellPointedCategory Sets@{o so} :=
  Sets_Separator@{o so}.

(* [Separator] is a genuine condition on an object, not one every object
   satisfies: the EMPTY setoid is not a separator of `Sets`, because there is
   nothing to probe with — every hypothesis of the separator condition holds
   vacuously, so it would identify the two distinct arrows of
   [Sets_two_arrows].  Recording this keeps the class from being read as
   content-free. *)
Definition empty_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier := False ; is_setoid := False_Setoid@{u} |}.

Lemma Sets_empty_not_Separator@{o so+} :
  @Separator Sets@{o so} empty_setoid_object@{o o} → False.
Proof.
  intro Hsep.
  destruct Hsep as [sep].
  apply Sets_two_arrows@{o so}.
  apply sep.
  intros e a.
  destruct a.
Qed.

(* The global-elements concretization of `Sets` obtained from
   well-pointedness.  It is a SECOND concrete structure on the same category:
   its underlying-set functor is `Hom(1, −)` where [Sets_Concrete]'s is the
   identity.  The two are different data — which is why Mac Lane's definition
   pairs the functor with the category — and no claim is made here about how
   the two functors compare up to natural isomorphism. *)
Definition Sets_Concrete_Points@{o so+} : Concrete Sets@{o so} :=
  Concrete_of_WellPointed Sets_WellPointed@{o so}.
