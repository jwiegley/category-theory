Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The currying adjunction (- × S) ⊣ (-)^S, and evaluation as its counit *)

(* nLab: https://ncatlab.org/nlab/show/exponential+object
   nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/representable+functor
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer 1998; §I.4 (Natural Transformations) and Chapter IV
         (Adjoints), §6 (Cartesian Closed Categories)
   Book: Riehl, "Category Theory in Context", Dover 2016; §2.1
         (Representable functors), Example 2.1.6(iv)

   Structure/Cartesian/Closed.v already carries the currying bijection: the
   field [exp_iso] of [Closed] is the setoid isomorphism

       (x × S ~> z)  ≊  (x ~> z^S),

   with [curry] its forward direction, [uncurry] its inverse, and
   [eval := uncurry id]. What that class does NOT do is exhibit the two sides
   as functors and the bijection as natural in x and z; the [Closed] class
   states the bijection objectwise and recovers the substitution laws
   ([curry_comp_l], [curry_comp], [uncurry_comp], [uncurry_comp_r]) as
   corollaries. This file assembles those corollaries into the structure they
   are the naturality squares of.

   Fixing an object S of a cartesian closed C, this file builds:

     - [Prod_Functor S] : C ⟶ C, the endofunctor (- × S), acting on arrows by
       [first];
     - [Exp_Functor S] : C ⟶ C, the endofunctor (-)^S, acting on arrows by
       f ↦ curry (f ∘ eval) — the internal-hom bifunctor of
       Functor/Hom/Internal.v with its contravariant argument held at S, as
       [Exp_Functor_InternalHom] records;
     - [eval_natural], the naturality of evaluation in its target (base)
       variable: f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id[S]);
     - [eval_Transform] : Prod_Functor S ◯ Exp_Functor S ⟹ Id[C], that same
       square bundled as a natural transformation with components [eval];
     - [Curry_Adjunction] : Prod_Functor S ⊣ Exp_Functor S, the adjunction in
       the hom-set form of Theory/Adjunction.v, whose transposes are [curry]
       and [uncurry] and whose counit is [eval] and unit [curry id] — both
       recorded below and both holding by [reflexivity], not merely up to ≈;
     - [Curry_Representable], an instance of [Representable] for the presheaf
       X ↦ C(X × S, B), with representing object B^S — the first inhabitant
       of that class in the tree, found by typeclass resolution
       ([Curry_Representable_resolves]) and read back through the class's
       own coercion ([Curry_repr_obj]).

   Note on the exponential's argument order: [exponent_obj x y] is displayed
   y ^ x, so the endofunctor (-)^S is [fun x => x ^ S], i.e.
   [fun x => exponent_obj S x], and [eval] at x is the arrow x^S × S ~> x.

   The header of Theory/Adjunction.v (lines 93-94, in the paragraph beginning
   "For the functional programmer") says in prose that "the function type
   arises from − × a ⊣ (−)^a with eval as counit". [Curry_Adjunction] and
   [curry_adj_counit] are that sentence as a theorem. The Sets model — where
   the counit computes to e(h, s) = h s — is
   Instance/Sets/Cartesian/Closed/Adjunction.v. *)

(* Currying, naturality, and representability

   nLab: https://ncatlab.org/nlab/show/exponential+object
   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer 1998
   Book: Riehl, "Category Theory in Context", Dover 2016
   Paper: Lawvere, "Adjointness in Foundations", Dialectica 23(3/4), 1969;
          reprinted as TAC Reprints 16, 2006

   Mac Lane's Chapter I fixes the vocabulary this file is written in: §I.4
   defines a natural transformation as a family of arrows whose square
   commutes for every morphism of the source category, and the entire content
   of [eval_natural] is that [eval] is such a family once the two sides are
   read as functors of the base object. His Chapter IV, "Adjoints", is where
   the exponential becomes one: its §6 is titled "Cartesian Closed
   Categories", and the adjunction − × S ⊣ (−)^S with evaluation as counit is
   the shape this file instantiates.

   The nLab's page on exponential objects states the same content in two
   registers and both are realized here. Universally: the exponential is "an
   object X^Y equipped with an evaluation map ev : X^Y × Y → X" through which
   every e : Z × Y → X factors uniquely — this is [ump_exponents] in
   Structure/Cartesian/Closed.v. Representably: X^Y is "a representing object
   for the functor hom(− × Y, X)", the currying isomorphism
   hom(Z, X^Y) ≅ hom(Z × Y, X) being "a natural isomorphism of sets". The
   second reading is the one [Curry_Representable] formalizes.

   Riehl's Example 2.1.6(iv) is that reading verbatim: "The functor
   Hom(− × A, B) : Set^op → Set that sends a set X to the set of functions
   X × A → B is represented by the set B^A of functions from A to B. That is,
   there is a natural bijection between functions X × A → B and functions
   X → B^A. This natural isomorphism is referred to as currying in computer
   science". Two adjustments are made in passing to that example here. First,
   the ambient category is a general cartesian closed C rather than Set, so
   the presheaf is the hom-functor C(− × S, B) : C^op ⟶ Sets and the
   representing object is B^S; Riehl's own statement is recovered by taking C
   to be [Sets], which Instance/Sets/Cartesian/Closed/Adjunction.v does.
   Second, "natural bijection" is here a genuine isomorphism in the functor
   category [C^op, Sets] of setoid-valued functors, since hom-sets in this
   library are setoids and equality of their elements is ≈, never =.

   Lawvere's "Adjointness in Foundations" is the source of the slogan that
   cartesian closed structure IS an adjunction — currying is − × a ⊣ (−)^a —
   quoted already in the essay that heads Theory/Adjunction.v; the [Adjunction]
   packaging below is what lets the general theory of that file apply, so
   that the triangle identities ([curry_adj_triangle_left] and
   [curry_adj_triangle_right]) arrive as instances of [counit_fmap_unit] and
   [fmap_counit_unit] rather than being re-proved.

   In-tree, this file sits between three neighbours. Structure/Cartesian/
   Closed.v supplies every exponential equation used below, so no new lemma
   about exponentials is needed: the four naturality fields of [Adjunction] are
   exactly [curry_comp_l], [curry_comp], [uncurry_comp] and [uncurry_comp_r].
   Functor/Hom/Internal.v supplies the internal-hom bifunctor
   [-,-] : C^op ∏ C ⟶ C, of which [Exp_Functor] is the partial application at
   a fixed exponent; the two agree up to ≈ ([Exp_Functor_InternalHom]) but not
   definitionally, because the bifunctor inserts a [second id] that the
   endofunctor does not. Adjunction/Diagonal/Product.v is the companion
   result one level down: the same hom-set packaging applied to the product's
   universal property, Δ ⊣ ×.

   Theory/Naturality.v is deliberately NOT used. That file is naturality
   infrastructure — a [Naturality] class computing, from the type of a family
   of arrows, the naturality statement appropriate to it, plus the [Mapping]
   class recording a morphism action without the functor laws. Its commented-
   out [PartialApply_Product_Left] / [PartialApply_Curried_Right] block is the
   only part that would bear on the present file, and it partially applies a
   bifunctor already presented as C ∏ C ⟶ C or C ⟶ [C, C]. The exponential in
   [Closed] is neither: it is a bare object operation [exponent_obj] plus the
   iso [exp_iso], with functoriality nowhere assumed, so there is no bifunctor
   to partially apply until one is built. Building [Exp_Functor] directly also
   keeps [fmap] definitionally equal to curry (f ∘ eval), which is what lets
   the adjunction's naturality fields discharge by the existing [Closed]
   corollaries and lets the counit be [eval] on the nose. The [Mapping]-based
   [ArityOne] instances would give a naturality *statement* but no functor,
   and [Adjunction] needs functors. *)

Section CurryAdjunction.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S : C).

(* The left adjoint (- × S) : C ⟶ C. On arrows it is [first f] = f × id[S],
   so the functor laws are [first_id] and [first_comp]. *)
Program Definition Prod_Functor : C ⟶ C := {|
  fobj := fun x => x × S;
  fmap := fun _ _ f => first f
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(* The right adjoint (-)^S : C ⟶ C, the endofunctor the issue calls (−)^S.
   On arrows it is post-composition inside the exponential, f ↦ curry (f ∘
   eval); [fmap] is this term definitionally, not merely up to ≈. Preservation
   of identities is [curry_eval] and of composition is [curry_comp]. *)
Program Definition Exp_Functor : C ⟶ C := {|
  fobj := fun x => x ^ S;
  fmap := fun _ _ f => curry (f ∘ eval)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite <- comp_assoc; apply curry_comp. Qed.

(* Naturality of [eval] in its target (base) variable: transporting along
   f : x ~> y after evaluating agrees with evaluating after transporting the
   function part along f. Reading [fmap[Prod_Functor] (fmap[Exp_Functor] f)]
   as curry (f ∘ eval) × id[S], the square is

       f ∘ eval ≈ eval ∘ (curry (f ∘ eval) × id[S]) : x^S × S ~> y,

   which is [ump_exponents] applied to f ∘ eval. Both sides are arrows of C
   compared with ≈; nothing here is an equality of morphisms. On vacuity:
   neither [Category] nor [Closed] forces hom-setoids to be trivial, so this
   is a genuine constraint — Instance/Sets/Cartesian/Closed/Adjunction.v
   exhibits a model in which the two sides are visibly non-trivial maps and
   the ambient hom-setoid separates arrows — and the proof consumes the
   exponential's universal property rather than a general categorical law. *)
Lemma eval_natural {x y : C} (f : x ~> y) :
  f ∘ eval ≈ eval ∘ fmap[Prod_Functor] (fmap[Exp_Functor] f).
Proof. simpl; now rewrite ump_exponents. Qed.

(* The same square bundled: evaluation is a natural transformation from
   (-)^S × S to the identity functor. This is the counit of the adjunction
   below, exhibited before the adjunction so that the naturality content is
   visible on its own. *)
Program Definition eval_Transform : Prod_Functor ◯ Exp_Functor ⟹ Id[C] := {|
  transform := fun _ => eval
|}.

(* The currying adjunction, in the hom-set form of Theory/Adjunction.v: the
   family of setoid isomorphisms (x × S ~> y) ≊ (x ~> y^S) is [exp_iso], with
   [curry] forward and [uncurry] back, and the four naturality fields are the
   substitution laws already proved in Structure/Cartesian/Closed.v. *)
#[export] Program Instance Curry_Adjunction : Prod_Functor ⊣ Exp_Functor := {|
  adj := fun _ _ =>
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
|}.
(* to_adj_nat_l: curry (f ∘ first g) ≈ curry f ∘ g *)
Next Obligation. symmetry; apply curry_comp_l. Qed.
(* to_adj_nat_r: curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g *)
Next Obligation. apply curry_comp. Qed.
(* from_adj_nat_l: uncurry (f ∘ g) ≈ uncurry f ∘ first g *)
Next Obligation. apply uncurry_comp. Qed.
(* from_adj_nat_r: uncurry (curry (f ∘ eval) ∘ g) ≈ f ∘ uncurry g *)
Next Obligation. symmetry; apply uncurry_comp_r. Qed.

(* The counit of the adjunction is evaluation. Both sides are arrows
   x^S × S ~> x and the comparison is ≈, as everywhere in this library; the
   [reflexivity] proof records the stronger fact that the two are convertible
   (the counit ⌈id⌉ unfolds to [uncurry id], which is the definition of
   [eval] in Structure/Cartesian/Closed.v). *)
Corollary curry_adj_counit {x : C} :
  @counit _ _ _ _ Curry_Adjunction x ≈ eval.
Proof. reflexivity. Qed.

(* Dually the unit is [curry id] : x ~> (x × S)^S, again convertible, not
   merely ≈-equal. *)
Corollary curry_adj_unit {x : C} :
  @unit _ _ _ _ Curry_Adjunction x ≈ curry id.
Proof. reflexivity. Qed.

(* The transposes of the adjunction are [curry] and [uncurry] on the nose:
   ⌊-⌋ = to adj is currying and ⌈-⌉ = from adj is uncurrying. Stated with ≈
   between arrows of C, as required; both hold by [reflexivity] because
   [Curry_Adjunction]'s [adj] field is [exp_iso] itself. *)
Corollary curry_adj_to {x y : C} (f : x × S ~> y) :
  to (@adj _ _ _ _ Curry_Adjunction x y) f ≈ curry f.
Proof. reflexivity. Qed.

Corollary curry_adj_from {x y : C} (g : x ~> y ^ S) :
  from (@adj _ _ _ _ Curry_Adjunction x y) g ≈ uncurry g.
Proof. reflexivity. Qed.

(* The two triangle identities, obtained from the general theory of
   Theory/Adjunction.v rather than re-proved. The first, ε ∘ F η ≈ id, reads
   eval ∘ (curry id × id[S]) ≈ id on x × S. *)
Corollary curry_adj_triangle_left {x : C} :
  eval ∘ first (curry (id[x × S])) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Curry_Adjunction x). Qed.

(* The second, U ε ∘ η ≈ id, on x^S; here [curry (eval ∘ eval)] is
   [fmap[Exp_Functor]] applied to the counit [eval]. *)
Corollary curry_adj_triangle_right {x : C} :
  curry (eval ∘ eval) ∘ curry (id[x^S × S]) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ Curry_Adjunction x). Qed.

(* [Exp_Functor] is the internal-hom bifunctor of Functor/Hom/Internal.v held
   fixed in its contravariant argument. The agreement is up to ≈ and not
   definitional: the bifunctor's action inserts [second (op id)], which is
   [second id] and only ≈-equal to [id]. *)
Lemma Exp_Functor_InternalHom {x y : C} (f : x ~> y) :
  fmap[Exp_Functor] f
    ≈ @fmap _ _ (InternalHomFunctor C) (S, x) (S, y) (id[S], f).
Proof. simpl; rewrite second_id, id_right; reflexivity. Qed.

End CurryAdjunction.

Arguments Prod_Functor {C _} S.
Arguments Exp_Functor {C _ _} S.

Section CurryRepresentable.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S B : C).

(* The presheaf of Riehl's Example 2.1.6(iv), for a general cartesian closed
   C: X ↦ C(X × S, B), contravariant in X. It is assembled from pieces
   already in the tree — the contravariant hom [Hom ─, B] of Functor/Hom.v
   composed with the opposite of the left adjoint — so its functor laws are
   inherited and no new obligation arises. Unfolded, [Curry_Presheaf x] is the
   hom-setoid (x × S ~> B) and [fmap] sends g to g ∘ first f. *)
Definition Curry_Presheaf : C^op ⟶ Sets := [Hom ─, B] ◯ (Prod_Functor S)^op.

(* The representation itself: the currying bijection, natural in X. The
   forward direction of a [Representable] is a transformation OUT of the
   represented functor, so [to] is [uncurry] : (x ~> B^S) → (x × S ~> B) and
   [from] is [curry]; naturality in x is [uncurry_comp] and [curry_comp_l],
   and the two round trips are [uncurry_curry] and [curry_uncurry]. Note that
   [Hom ─, B^S] is the covariant hom-functor of C^op at B^S, which is what
   the [Representable] class asks for when the base category is C^op. *)
Program Definition Curry_Representation : [Hom ─, B^S] ≅ Curry_Presheaf := {|
  to   := {| transform := fun _ => {| morphism := uncurry |} |};
  from := {| transform := fun _ => {| morphism := curry |} |}
|}.
Next Obligation. symmetry; apply uncurry_comp. Qed.
Next Obligation. apply uncurry_comp. Qed.
Next Obligation. apply curry_comp_l. Qed.
Next Obligation. symmetry; apply curry_comp_l. Qed.
Next Obligation. rewrite first_id, id_right; apply uncurry_curry. Qed.

(* The [Representable] witness. Before this instance the class of
   Functor/Representable.v had no inhabitants anywhere in the tree; this is
   the first, and it says exactly what Riehl's Example 2.1.6(iv) says: the
   functor C(− × S, B) is represented by B^S. The base category of the
   instance is C^op, since the functor is contravariant in C. *)
#[export] Program Instance Curry_Representable : Representable Curry_Presheaf := {|
  repr_obj := B ^ S;
  represented := Curry_Representation
|}.

(* Identification of the universal element. The Yoneda lemma — in-tree as
   [Yoneda_Lemma] in Functor/Hom/Yoneda.v, not re-proved here — says a
   representation Φ : C(A, −) ≅ F is determined by the single element
   Φ_A(id[A]) of F A. For this representation A is B^S and that element is
   [eval] : B^S × S ~> B, so what is being represented is the exponential's
   own evaluation and not some unrelated family. The comparison is ≈ between
   arrows of C; the [reflexivity] proof shows the two sides convertible. *)
Lemma Curry_repr_universal :
  to Curry_Representation (B ^ S) id ≈ eval.
Proof. reflexivity. Qed.

(* What the presheaf's action is, spelled out: restricting a map along
   f : y ~> x re-indexes by f in the first factor. This is a definitional
   unfolding — [reflexivity] closes it, and it carries no content beyond
   naming what [Curry_Presheaf]'s [fmap] computes to — but it is what makes
   the naturality obligations of [Curry_Representation] above legible. Stated
   as ≈ of arrows of C, as everywhere. *)
Lemma Curry_Presheaf_fmap {x y : C} (f : y ~> x) (g : x × S ~> B) :
  fmap[Curry_Presheaf] f g ≈ g ∘ first f.
Proof. reflexivity. Qed.

End CurryRepresentable.

Arguments Curry_Presheaf {C _} S B.
Arguments Curry_Representation {C _ _} S B.

(* The instance is usable, not merely declared: typeclass resolution finds it
   for the goal [Representable (Curry_Presheaf S B)] (the [_] below is solved
   by resolution alone), and the class's [Representable_to_obj] coercion —
   which had no callers in the tree either — reads the representing object
   back off it as B^S. The second statement is a Leibniz equality between two
   OBJECTS of C, which is the only sense available: this library has no ≈ on
   objects, only isomorphism, and objects are not morphisms. *)
Definition Curry_Representable_resolves
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable (Curry_Presheaf S B) := _.

Example Curry_repr_obj
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable_to_obj _ (Curry_Representable S B) = (B ^ S)%object.
Proof. reflexivity. Qed.
