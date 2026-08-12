Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

Import EqNotations.

(** * Small products and coproducts in [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/product
   nLab:      https://ncatlab.org/nlab/show/coproduct
   nLab:      https://ncatlab.org/nlab/show/complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   Sources transposed here, all cited BY LOCATION; the printed text of none of
   the three books was consulted while writing this file.  The one-line
   descriptions below are transcribed from the catalog entries of issue #254,
   not from the books:

     - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
       (Springer GTM 5), section I.6, printed p. 24, exercises 1 and 2.  The
       exercises are the set-theoretic statement that a universe is closed
       under small cartesian products and small unions.  Their categorical
       transposition is this file: [Sets] at level [o] has products and
       coproducts of families indexed by any type at level [o] -- [o] being
       the universe of the carriers of [Sets]' objects, per the universe
       discipline recorded below.
     - Mac Lane, same book, section III.4, printed p. 72, exercise 2: the
       J-indexed cartesian product with its projections is the categorical
       product in Set.  That is [Sets_HasIndexedProducts] below.  (The same
       exercise also asks for the description in Top; see SCOPE, below.)
     - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
       September 2005), section 2.9 exercise 7, printed p. 56, parts (a) and
       (b).  Part (a) -- the universal property of an I-indexed product -- is
       already in the tree as [IsIndexedProduct], Structure/Limit/Product.v:51.
       Part (b) -- the function set X^I satisfies it for the constant family
       -- is [Sets_exponent_IsIndexedProduct] and
       [Sets_constant_iprod_exponent] below.
     - Riehl, "Category Theory in Context", 2nd ed., section 3.2, printed
       p. 94, example 5: the product of a J-indexed family of sets is the set
       of J-tuples.  Here an element of [Sets_iprod_obj F] literally IS a
       J-tuple, the dependent function [∀ i : A, F i].

   WHAT IS CONSTRUCTED

     [Sets_iprod_obj F]    carrier [∀ i : A, F i], with [g ≈ h] pointwise;
     [Sets_icoprod_obj F]  carrier [{ i : A & F i }], with [(i; x) ≈ (j; y)]
                           iff some [e : i = j] carries [x] to a value
                           equivalent to [y].

   [Sets_HasIndexedProducts] and [Sets_HasIndexedCoproducts] package these
   with their projections/injections and universal properties.  Before this
   file the tree had no [HasIndexedProducts] instance at any category, and no
   [HasIndexedCoproducts] vocabulary at all.

   WHAT THIS DOES NOT SETTLE ELSEWHERE

   Theory/WeaklyInitial.v:43-50 takes its two products as explicit hypotheses
   "rather than harvested from a [Complete] / [HasIndexedProducts] instance",
   and that note is NOT a record of the absence just described: its reason is
   a universe one, and it survives an instance existing.  The second of its
   two products ranges over a hom-type, so "routing it through a class that
   quantifies over every index [Type] would over-commit the ambient
   universes", whereas the explicit form "leaves the smallness of the index
   (hence the relevant universe constraints) in the caller's hands".  Nothing
   below changes that, and the note stands as written.

   At [Sets], though, the obstacle it guards against is absent, and
   [Sets_endo_iprod] / [Sets_endo_iprod_ump] below record the fact: the
   endomorphism-indexed product of [P] with itself is supplied by
   [Sets_HasIndexedProducts], with its universal property, at the very same
   [Sets] --

     Sets_endo_iprod@{u u0} : obj[Sets@{u0 u}] → obj[Sets@{u0 u}]
                                              (* with u0 < u *)

   -- no second [Sets] and no universe growth, because [Sets]' hom-type sits
   at exactly the index universe the instance accepts.  That is an observation
   about [Sets] alone; for an arbitrary category the hom universe need not sit
   where the class puts the index, which is the case the explicit hypotheses
   of Theory/WeaklyInitial.v exist to cover.

   THE UNIVERSE DISCIPLINE, WHICH IS THE POINT OF THE EXERCISE

   [Sets@{o so} : Category@{so o o}] (Instance/Sets.v:188): its objects are
   [SetoidObject@{o o}], whose carriers live at [Type@{o}], and its homs also
   live at [Type@{o}].  A dependent function type [∀ i : A, F i] over
   [A : Type@{u}] lands at [Type@{max(u,o)}], so it is a carrier of an object
   of [Sets@{o so}] exactly when [u <= o]; likewise [{ i : A & F i }].  The
   smallness side condition of Mac Lane I.6 is therefore, in this
   development, the universe level of the index type, and it is not imposed by
   hand -- it is what universe inference records.

   [HasIndexedProducts] of Structure/Limit/Product.v:128 quantifies its index
   as [{A : Type}], and under the library's [Set Universe Polymorphism]
   (Lib.v) that [Type] is a universe PARAMETER of the class, not a quantifier
   over all universes.  Printing the class shows the three parameters, one per
   field:

     HasIndexedProducts@{u u0 u1 u2 u3 u4} (C : Category@{u3 u4 u4})
       { indexed_product      : ∀ A : Type@{u},  ...
         indexed_product_proj : ∀ A : Type@{u0}, ...
         indexed_product_ump  : ∀ A : Type@{u1}, ... }

   so the class as literally stated CAN be instantiated at [Sets], with those
   three universes taken to be [o].  That is what happens here;
   [About Sets_HasIndexedProducts] prints

     Sets_HasIndexedProducts@{u u0} : HasIndexedProducts@{u0 u0 u0 u0 u u0}
                                        Sets@{u0 u}     (* with u0 < u *)

   -- [u0] is [o] and [u] is [so], the three index universes are all [u0], and
   the ambient [Category@{u3 u4 u4}] is [Category@{u u0 u0}], which is
   [Sets@{u0 u}].  There is no separate index universe variable to
   instantiate: the index universe is [o], the universe of the CARRIERS of
   [Sets]' objects -- the level at which the small sets themselves live.  It
   is NOT [so], the universe of [obj[Sets]], which is where [Sets] qua
   [Category@{so o o}] keeps its objects and which sits strictly above [o];
   indexing by [obj[Sets]] is exactly what the next paragraph shows to be
   rejected.  The coproduct instance is the same story through
   [Structure/Limit/Coproduct.v]'s definitional dual:

     Sets_HasIndexedCoproducts@{u u0} : HasIndexedCoproducts@{u u0 u0 u u0}
                                          Sets@{u0 u}   (* with u0 < u *)

   where [Print HasIndexedCoproducts] shows [u0] in the second position to be
   the index universe and [Category@{u2 u3 u3}] with [u2 := u], [u3 := u0] to
   be [Sets].

   No universe-constrained VARIANT of the class was introduced: the instances
   above inhabit [Structure/Limit/Product.v]'s [HasIndexedProducts] itself.

   The condition bites in the expected direction.  Applying [indexed_product]
   at an index type one universe up -- [SetoidObject@{o o}] itself, which is
   [Type@{o+1}] -- is rejected by the elaborator with a universe
   inconsistency.  This was checked outside the tree rather than recorded as a
   command here, so that the [make todo] scan stays clean; a reader can
   reproduce it with

     Definition big@{o so}
       (F : SetoidObject@{o o} -> SetoidObject@{o o}) : SetoidObject@{o o} :=
       @indexed_product Sets@{o so} Sets_HasIndexedProducts@{so o}
                        (SetoidObject@{o o}) F.

   which reports that [SetoidObject@{o o}] "has type Type@{o+1} while it is
   expected to have type Type@{o}".  Why a bound of this kind must exist at
   all is not argued here; Structure/Complete.v:64-72 records Freyd's theorem
   that a category with products of families as large as its own morphism set
   is a preorder.

   NO FUNCTION EXTENSIONALITY

   Two elements of [Sets_iprod_obj F] are identified when they agree at every
   index up to the codomain's own [≈].  That is extensional equality of
   dependent functions realised as the object's chosen equivalence rather than
   as an axiom, exactly the move Instance/Sets.v:26 makes for the hom-setoid.
   Nothing here appeals to [funext], choice, or [UIP]: the coproduct
   equivalence transports along an equality of indices and every proof about
   it proceeds by destructing that equality.  [Print Assumptions] reports
   "Closed under the global context" for every constant in this file; the
   Makefile's [print-assumptions] target audits the headline ones.

   WHICH EXISTING CONSTANTS DO THE WORK

   Reused unchanged: [IsIndexedProduct] and [HasIndexedProducts]
   (Structure/Limit/Product.v:51, :128); [Sets], [SetoidObject],
   [SetoidMorphism] (Instance/Sets.v); [eq_Setoid] (Lib/Setoid.v:65) for the
   discrete setoid on an index type; and, for the Awodey comparison and the
   witnesses only,
   [Sets_Cartesian] (Instance/Sets/Cartesian.v:32), [Sets_Cocartesian]
   (Instance/Sets/Cocartesian.v:28), [Sets_Closed]
   (Instance/Sets/Cartesian/Closed.v:38), [Sets_Terminal] and [Sets_Initial]
   (Instance/Sets.v).  Genuinely new: every [Sets_*] constant below, together
   with the [HasIndexedCoproducts] vocabulary of Structure/Limit/Coproduct.v.

   NON-DEGENERACY OF THE WITNESSES

   An indexed product over an empty index is the terminal object and one over
   a singleton index is the family's only member -- [Sets_iprod_empty] and
   [Sets_iprod_unit] prove exactly that, and neither exercises the
   construction.  The witnesses that do are [Sets_iprod_bool] (two distinct
   indices: the product is the binary product of Instance/Sets/Cartesian.v --
   a statement whose right-hand side names two distinct members of the family,
   which the empty and singleton statements cannot do) and [Sets_iprod_nat]
   (an infinite index: the product satisfies the stream equation
   P ≅ F 0 × P', peeling a factor off and finding a product of the same shape
   underneath).  [Sets_icoprod_empty], [Sets_icoprod_unit],
   [Sets_icoprod_bool] and [Sets_icoprod_nat] are the four coproduct
   counterparts.

   Neither of those is by itself a SEPARATION: neither exhibits a property
   that holds at a degenerate index and is lost at a genuine one.  That is
   supplied by [Sets_iprod_unit_pigeonhole] together with
   [Sets_iprod_nat_no_pigeonhole].  The first proves, of the product of
   two-element setoids over a SINGLETON index, that no three elements are
   pairwise apart -- given [x y z], from [(x ≈ y) → False] and
   [(y ≈ z) → False] it concludes [x ≈ z].  The second refutes that same
   implication over [nat], by exhibiting three pairwise-apart elements.
   Together they are what makes the [nat] INDEX load-bearing rather than
   decorative; note that both statements are about
   [indexed_product (fun _ : nat => Sets_bool)] directly and neither mentions
   [Sets_iprod_nat], so what they separate is the index, not the stream
   decomposition.  [Sets_icoprod_unit_pigeonhole] and
   [Sets_icoprod_nat_no_pigeonhole] are the coproduct counterparts.

   SCOPE: WHAT IS DEFERRED

   Mac Lane section III.4 exercise 2 also asks for the analogous description
   of the J-indexed product in Top -- the product topology, its projections
   and its tupling universal property.  That is NOT delivered, here or
   anywhere in this development, and is deferred: the library has no category
   of topological spaces (tracked as issue #259).  It is an optional
   extension, not a prerequisite; every [Sets] result in this file stands
   without it.

   Two further limits of scope, stated so they are not mistaken for claims.
   First, [Sets_constant_iprod_exponent] compares the indexed product over an
   index TYPE [I] with the exponential at the DISCRETE setoid on [I], because
   [HasIndexedProducts] indexes by a bare [Type] while an exponential in
   [Sets] has a setoid for its base; no claim is made here about the
   exponential at a coarser setoid.  Second, this file supplies products and
   coproducts only; completeness of [Sets] is Instance/Sets/Complete.v, and
   cocompleteness is not addressed at all, here or anywhere else in the
   tree. *)

(* The default obligation tactic is switched off for this file, as
   Instance/Sets/End.v does: where [Program] raises an obligation it is
   discharged by an explicit script below rather than by the library's [cat] /
   [cat_simpl] automation, and no script below invokes a proof-search tactic:
   none of them calls [auto], [eauto], [intuition], [firstorder] or [tauto].
   A few scripts do use the tacticals [now] (at the obligations of
   [Sets_iprod_tuple], [Sets_icoprod_obj] and [Sets_icoprod_case]) and
   [first [...]] (in the two singleton pigeonhole lemmas), which sequence and
   choose among explicit steps rather than search.  Note also that some
   [proper_morphism] fields never become obligations at all -- instance
   resolution closes them during elaboration -- which is why several tactic
   scripts further down use an [all:] selector, a no-op when no goal is
   left. *)
#[local] Obligation Tactic := idtac.

(** ** Indexed products: the dependent-function setoid *)

Definition Sets_iprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (∀ i : A, F i) :=
  fun g h => ∀ i : A, g i ≈ h i.

Program Definition Sets_iprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := ∀ i : A, F i;
  is_setoid := {| equiv := Sets_iprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros g i; reflexivity.
  - intros g h Hgh i; symmetry; exact (Hgh i).
  - intros g h k Hgh Hhk i; transitivity (h i); [exact (Hgh i)|exact (Hhk i)].
Qed.

Program Definition Sets_iprod_proj {A : Type}
  (F : A → SetoidObject) (i : A) : Sets_iprod_obj F ~{Sets}~> F i := {|
  morphism := fun g => g i
|}.
Next Obligation. intros A F i g h Hgh; exact (Hgh i). Qed.

Program Definition Sets_iprod_tuple {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (pi : ∀ i : A, c ~{Sets}~> F i) : c ~{Sets}~> Sets_iprod_obj F := {|
  morphism := fun x i => pi i x
|}.
Next Obligation. intros A F c pi x y Hxy i; now rewrite Hxy. Qed.

Program Definition Sets_iprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (pi : ∀ i : A, c ~{Sets}~> F i) :
  ∃! u : c ~{Sets}~> Sets_iprod_obj F,
    ∀ i : A, Sets_iprod_proj F i ∘ u ≈ pi i := {|
  unique_obj := Sets_iprod_tuple F c pi
|}.
Next Obligation. intros A F c pi i x; reflexivity. Qed.
Next Obligation. intros A F c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_IsIndexedProduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  @Build_IsIndexedProduct Sets A F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (fun c pi => Sets_iprod_ump F c pi).

#[export]
Instance Sets_HasIndexedProducts : @HasIndexedProducts Sets :=
  @Build_HasIndexedProducts Sets
    (@Sets_iprod_obj) (@Sets_iprod_proj) (@Sets_IsIndexedProduct).

(** ** The endomorphism-indexed product

    The index that Theory/WeaklyInitial.v declines to draw from a class,
    because for a general category it need not sit where the class puts the
    index: the endomorphisms of an object.  At [Sets] it does sit there.  The
    two constants below are the whole of the observation -- their existence,
    and the universe context they elaborate at, ARE the content, so both are
    stated as instances of what [Sets_HasIndexedProducts] already supplies
    rather than reproved.  See the header for what this does and does not say
    about the general note. *)

Definition Sets_endo_iprod (P : obj[Sets]) : obj[Sets] :=
  indexed_product (fun _ : P ~{Sets}~> P => P).

Definition Sets_endo_iprod_ump (P : obj[Sets]) :
  IsIndexedProduct (fun _ : P ~{Sets}~> P => P) (Sets_endo_iprod P)
                   (indexed_product_proj (fun _ : P ~{Sets}~> P => P)) :=
  indexed_product_ump (fun _ : P ~{Sets}~> P => P).

(** ** Indexed coproducts: the sigma setoid *)

Definition Sets_icoprod_carrier {A : Type}
  (F : A → SetoidObject) : Type := { i : A & F i }.

Definition Sets_icoprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (Sets_icoprod_carrier F) :=
  fun p q =>
    { e : projT1 p = projT1 q
    & rew [fun i : A => carrier (F i)] e in projT2 p ≈ projT2 q }.

Program Definition Sets_icoprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := Sets_icoprod_carrier F;
  is_setoid := {| equiv := Sets_icoprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros [i x]; exists eq_refl; reflexivity.
  - intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [i x] [j y] [k z] [e Hxy] [e' Hyz]; simpl in *.
    destruct e; destruct e'; simpl in *.
    exists eq_refl; simpl; now transitivity y.
Qed.

Program Definition Sets_icoprod_inj {A : Type}
  (F : A → SetoidObject) (i : A) : F i ~{Sets}~> Sets_icoprod_obj F := {|
  morphism := fun x => existT _ i x
|}.
Next Obligation. intros A F i x y Hxy; exists eq_refl; exact Hxy. Qed.

Program Definition Sets_icoprod_case {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (iota : ∀ i : A, F i ~{Sets}~> c) : Sets_icoprod_obj F ~{Sets}~> c := {|
  morphism := fun p => iota (projT1 p) (projT2 p)
|}.
Next Obligation.
  intros A F c iota [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  now rewrite Hxy.
Qed.

Program Definition Sets_icoprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (iota : ∀ i : A, F i ~{Sets}~> c) :
  ∃! u : Sets_icoprod_obj F ~{Sets}~> c,
    ∀ i : A, u ∘ Sets_icoprod_inj F i ≈ iota i := {|
  unique_obj := Sets_icoprod_case F c iota
|}.
Next Obligation. intros A F c iota i x; reflexivity. Qed.
Next Obligation.
  intros A F c iota v Hv [i x]; simpl; symmetry; exact (Hv i x).
Qed.

Definition Sets_IsIndexedCoproduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedCoproduct F (Sets_icoprod_obj F) (Sets_icoprod_inj F) :=
  @Build_IsIndexedCoproduct Sets A F
    (Sets_icoprod_obj F) (Sets_icoprod_inj F)
    (fun c iota => Sets_icoprod_ump F c iota).

#[export]
Instance Sets_HasIndexedCoproducts : @HasIndexedCoproducts Sets :=
  @Build_HasIndexedCoproducts Sets
    (@Sets_icoprod_obj) (@Sets_icoprod_inj)
    (@Sets_IsIndexedCoproduct).

(** ** Awodey 2.9 Exercise 7(b): the function set as a constant-family product *)

Definition Sets_discrete (I : Type) : obj[Sets] :=
  {| carrier := I; is_setoid := eq_Setoid I |}.

(* The exponential X^I of Instance/Sets/Cartesian/Closed.v, taken at the
   discrete setoid on the index type I.  Written as a definition rather than
   inline so that the ambient category is pinned to [Sets] for elaboration. *)
Definition Sets_pow (I : Type) (X : obj[Sets]) : obj[Sets] :=
  (X ^ Sets_discrete I)%object.

Program Definition Sets_exponent_eval (I : Type) (X : obj[Sets]) (i : I) :
  Sets_pow I X ~{Sets}~> X := {|
  morphism := fun f => f i
|}.
Next Obligation. intros I X i f g Hfg; exact (Hfg i). Qed.

(* The element of X^I named by a family [pi] at a point [x].  Built with
   [unshelve refine] rather than [Program] so that the [proper_morphism]
   certificate is supplied by hand.  This is not a matter of taste: with the
   [Program] form, instance resolution closes that field during elaboration
   -- the definition raises no obligation at all -- and the constant comes out
   pinned to [Set]:

     ∀ (I : Type@{u}) (X c : obj[Sets@{Set u0}]), ...
       (* with  Set < u0  and  Set = u *)

   The index universe [u] is [Set] by a universe EQUALITY, not merely bounded
   by it, and the ambient [Sets] is pinned along with it.  The [unshelve
   refine] form below instead prints
   [∀ (I : Type@{u}) (X c : obj[Sets@{u u0}])] with only [u < u0].  (Observed
   while writing this file; the mechanism behind the pinning was not
   investigated.) *)
Definition Sets_exponent_elt (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) (x : c) : Sets_discrete I ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun i => pi i x |}.
  intros i j Hij; destruct Hij; reflexivity.
Defined.

Program Definition Sets_exponent_tuple (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) : c ~{Sets}~> Sets_pow I X := {|
  morphism := Sets_exponent_elt I X c pi
|}.
Next Obligation.
  intros I X c pi x y Hxy i; exact (proper_morphism (pi i) x y Hxy).
Qed.

Program Definition Sets_exponent_ump (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) :
  ∃! u : c ~{Sets}~> Sets_pow I X,
    ∀ i : I, Sets_exponent_eval I X i ∘ u ≈ pi i := {|
  unique_obj := Sets_exponent_tuple I X c pi
|}.
Next Obligation. intros I X c pi i x; reflexivity. Qed.
Next Obligation. intros I X c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_exponent_IsIndexedProduct (I : Type) (X : obj[Sets]) :
  IsIndexedProduct (fun _ : I => X) (Sets_pow I X)
                   (Sets_exponent_eval I X) :=
  @Build_IsIndexedProduct Sets I (fun _ : I => X) (Sets_pow I X)
    (Sets_exponent_eval I X) (fun c pi => Sets_exponent_ump I X c pi).

(* Each isomorphism below is assembled from two named setoid maps rather than
   through [Program] at the isomorphism itself: the isomorphism is a [refine]
   over two concrete morphisms, leaving exactly the two inverse laws.

   The maps themselves are built two ways.  Most are [unshelve refine], with
   the [proper_morphism] certificate discharged under an [all:] selector: for
   some of them instance resolution already closes that goal during
   elaboration, and [all:] is a no-op when no goal remains, so the script does
   not depend on which of the two happens.  The exception is the pair making
   up [Sets_constant_iprod_exponent] -- [Sets_exponent_tuple] above and
   [Sets_exponent_untuple] just below -- both of which are [Program].  For
   [Sets_exponent_untuple], whose SOURCE is the exponential [Sets_pow I X],
   this was measured: refining a record literal against a goal whose type has
   to be unfolded through [Sets_Closed] did not return within sixty seconds,
   where the [Program] form elaborates in well under a second.
   [Sets_exponent_tuple] was written as [Program] from the start and no such
   measurement was taken for it. *)
Program Definition Sets_exponent_untuple (I : Type) (X : obj[Sets]) :
  Sets_pow I X ~{Sets}~> indexed_product (fun _ : I => X) := {|
  morphism := fun f => fun i => f i
|}.
Next Obligation. intros I X f g Hfg i; exact (Hfg i). Qed.

Definition Sets_constant_iprod_exponent (I : Type) (X : obj[Sets]) :
  indexed_product (fun _ : I => X) ≅[Sets] Sets_pow I X.
Proof.
  refine {| to := Sets_exponent_tuple I X (indexed_product (fun _ : I => X))
                    (fun i => Sets_iprod_proj (fun _ : I => X) i)
          ; from := Sets_exponent_untuple I X |}.
  - intros f i; reflexivity.
  - intros g i; reflexivity.
Defined.

(** ** Degenerate indices

    An indexed product over an empty index is the terminal object, and one
    over a singleton index is the family's only member; dually for
    coproducts.  Neither exercises the construction.  They are recorded here
    so that the contrast drawn with the non-degenerate cases of the next
    section is proved rather than asserted. *)

Definition Sets_iprod_empty_to (F : False → obj[Sets]) :
  indexed_product F ~{Sets}~> 1%object.
Proof.
  unshelve refine {| morphism := fun _ => ttt |}.
  all: intros g h Hgh; reflexivity.
Defined.

Definition Sets_iprod_empty_from (F : False → obj[Sets]) :
  1%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun _ => fun i : False => match i with end |}.
  all: intros x y Hxy i; destruct i.
Defined.

Definition Sets_iprod_empty (F : False → obj[Sets]) :
  indexed_product F ≅[Sets] 1%object.
Proof.
  refine {| to := Sets_iprod_empty_to F; from := Sets_iprod_empty_from F |}.
  - intros u; destruct u; reflexivity.
  - intros g i; destruct i.
Defined.

Definition Sets_iprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_product F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun g => g ttt |}.
  all: intros g h Hgh; exact (Hgh ttt).
Defined.

Definition Sets_iprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun x =>
      fun i => match i return carrier (F i) with ttt => x end |}.
  all: intros x y Hxy i; destruct i; exact Hxy.
Defined.

Definition Sets_iprod_unit (F : poly_unit → obj[Sets]) :
  indexed_product F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_iprod_unit_to F; from := Sets_iprod_unit_from F |}.
  - intros x; reflexivity.
  - intros g i; destruct i; reflexivity.
Defined.

Definition Sets_icoprod_empty_to (F : False → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> 0%object.
Proof.
  unshelve refine {| morphism := fun p => projT1 p |}.
  all: intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_empty_from (F : False → obj[Sets]) :
  0%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x : False => match x with end |}.
  all: intros x; destruct x.
Defined.

Definition Sets_icoprod_empty (F : False → obj[Sets]) :
  indexed_coproduct F ≅[Sets] 0%object.
Proof.
  refine {| to := Sets_icoprod_empty_to F; from := Sets_icoprod_empty_from F |}.
  - intros x; destruct x.
  - intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ i x =>
          match i return carrier (F i) → carrier (F ttt) with
          | ttt => fun x => x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x => existT _ ttt x |}.
  all: intros x y Hxy; exists eq_refl; exact Hxy.
Defined.

Definition Sets_icoprod_unit (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_icoprod_unit_to F; from := Sets_icoprod_unit_from F |}.
  - intros x; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(** ** Non-degenerate indices: two distinct indices, and an infinite index *)

(* [bool] is the smallest non-degenerate index.  The product over it is the
   binary product of Instance/Sets/Cartesian.v -- a statement whose right-hand
   side names two distinct members of the family, which the empty and
   singleton statements cannot do.  ([Sets_iprod_empty] and [Sets_iprod_unit]
   above are their counterparts, and neither mentions two members.) *)

Definition Sets_iprod_bool_to (F : bool → obj[Sets]) :
  indexed_product F ~{Sets}~> (F true × F false)%object.
Proof.
  unshelve refine {| morphism := fun g => (g true, g false) |}.
  all: intros g h Hgh; split; [exact (Hgh true)|exact (Hgh false)].
Defined.

Definition Sets_iprod_bool_from (F : bool → obj[Sets]) :
  (F true × F false)%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun b => match b return carrier (F b) with
               | true  => fst p
               | false => snd p
               end |}.
  all: intros p q [Hl Hr] b; destruct b; assumption.
Defined.

Definition Sets_iprod_bool (F : bool → obj[Sets]) :
  indexed_product F ≅[Sets] (F true × F false)%object.
Proof.
  refine {| to := Sets_iprod_bool_to F; from := Sets_iprod_bool_from F |}.
  - intros p; split; reflexivity.
  - intros g b; destruct b; reflexivity.
Defined.

(* [nat] is an infinite index.  The product over it satisfies the stream
   equation P ≅ F 0 × P': peel one factor off and a product of the same shape
   is underneath.  This exhibits the infinite case; it is not by itself a
   separation from the degenerate ones, which is what
   [Sets_iprod_unit_pigeonhole] and [Sets_iprod_nat_no_pigeonhole] at the end
   of this file are for. *)

Definition Sets_iprod_nat_to (F : nat → obj[Sets]) :
  indexed_product F
    ~{Sets}~> (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun g => (g 0%nat, fun m => g (S m)) |}.
  all: intros g h Hgh; split; [exact (Hgh 0%nat)|intros m; exact (Hgh (S m))].
Defined.

Definition Sets_iprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat × indexed_product (fun n => F (S n)))%object
    ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun n => match n return carrier (F n) with
               | O   => fst p
               | S m => snd p m
               end |}.
  all: intros p q [Hl Hr] n; destruct n; [exact Hl|exact (Hr n)].
Defined.

Definition Sets_iprod_nat (F : nat → obj[Sets]) :
  indexed_product F
    ≅[Sets] (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_iprod_nat_to F; from := Sets_iprod_nat_from F |}.
  - intros p; split; [reflexivity|intros m; reflexivity].
  - intros g n; destruct n; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_bool]: the sigma setoid over
   [bool] is the binary coproduct of Instance/Sets/Cocartesian.v. *)

Definition Sets_icoprod_bool_to (F : bool → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> (F true + F false)%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ b x =>
          match b return carrier (F b) →
                         carrier (F true) + carrier (F false) with
          | true  => fun x => Datatypes.inl x
          | false => fun x => Datatypes.inr x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_bool_from (F : bool → obj[Sets]) :
  (F true + F false)%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT _ true x
      | Datatypes.inr y => existT _ false y
      end |}.
  all: intros s t Hst; destruct s, t; try contradiction;
       exists eq_refl; exact Hst.
Defined.

Definition Sets_icoprod_bool (F : bool → obj[Sets]) :
  indexed_coproduct F ≅[Sets] (F true + F false)%object.
Proof.
  refine {| to := Sets_icoprod_bool_to F; from := Sets_icoprod_bool_from F |}.
  - intros s; destruct s; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_nat]: the sigma setoid over [nat]
   splits off its zeroth summand and reproduces itself underneath. *)

Definition Sets_icoprod_nat_to (F : nat → obj[Sets]) :
  indexed_coproduct F
    ~{Sets}~> (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ n x =>
          match n return carrier (F n) →
                         carrier (F 0%nat)
                         + Sets_icoprod_carrier (fun m => F (S m)) with
          | O   => fun x => Datatypes.inl x
          | S m => fun x => Datatypes.inr (existT _ m x)
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i;
       [ exact Hxy | exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat + indexed_coproduct (fun n => F (S n)))%object
    ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT (fun i : nat => carrier (F i)) 0%nat x
      | Datatypes.inr q =>
          match q with
          | existT _ m x => existT (fun i : nat => carrier (F i)) (S m) x
          end
      end |}.
  all: intros s t Hst; destruct s as [x|[m x]], t as [y|[n y]];
       try contradiction; simpl in *;
       [ exists eq_refl; exact Hst
       | destruct Hst as [e Hxy]; simpl in *; destruct e; simpl in *;
         exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat (F : nat → obj[Sets]) :
  indexed_coproduct F
    ≅[Sets] (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_icoprod_nat_to F; from := Sets_icoprod_nat_from F |}.
  - intros s; destruct s as [x|[m x]]; reflexivity.
  - intros [i x]; destruct i; simpl; exists eq_refl; reflexivity.
Defined.

(** ** A separating property: pigeonhole at a singleton index, refuted at [nat]

    The isomorphisms above exhibit the construction at non-degenerate
    indices, but none of them is by itself a separation: none exhibits a
    property that holds at a degenerate index and is lost at a genuine one.
    The four results here do.  What is proved is the implication

      ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z,

    read over the product -- and, separately, over the coproduct -- of
    two-element setoids: no three elements are pairwise apart.  It holds over
    a SINGLETON index and is refutable over [nat].  A property of the
    construction at a degenerate index is therefore provably lost at a
    genuine one.

    Two cautions on reading that implication.  It is NOT the disjunctive
    pigeonhole "of any three elements, two coincide"; no disjunction is
    proved anywhere below.  The two forms are interderivable for these
    particular objects only because [Sets_bool] carries decidable equality,
    and that decidability is used inside the proofs (the [destruct ... eqn:]
    on [bool]) rather than stated as a hypothesis.  Separately, the informal
    reason the singleton case holds -- the object there has only two elements
    up to [≈] -- is not itself proved; the implication is. *)

(* The two-element setoid, [bool] under Coq's equality. *)
Definition Sets_bool : obj[Sets] :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Lemma Sets_iprod_unit_pigeonhole
  (x y z : carrier (indexed_product (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_product (fun _ : poly_unit => Sets_bool)),
                 a ttt = b ttt → a ≈ b)
    by (intros a b H i; destruct i; exact H).
  destruct (x ttt) eqn:Hx, (y ttt) eqn:Hy, (z ttt) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* Three elements of the [nat]-indexed product of two-element setoids: the
   constantly-[false] tuple, and the tuples true at index 0 and at index 1. *)
Definition Sets_iprod_pt0 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) := fun _ => false.

Definition Sets_iprod_pt1 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with O => true | S _ => false end.

Definition Sets_iprod_pt2 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with S O => true | _ => false end.

Lemma Sets_iprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_product (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_iprod_pt0 ≈ Sets_iprod_pt1) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  assert (H12 : (Sets_iprod_pt1 ≈ Sets_iprod_pt2) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  specialize (H _ _ _ H01 H12 1%nat); simpl in H; discriminate.
Qed.

Lemma Sets_icoprod_unit_pigeonhole
  (x y z : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool)),
                 projT2 a = projT2 b → a ≈ b)
    by (intros [i a] [j b] Hab; simpl in *; destruct i, j;
        exists eq_refl; exact Hab).
  destruct (projT2 x) eqn:Hx, (projT2 y) eqn:Hy, (projT2 z) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* The [k]-th summand's [true].  Identifying two of these calls for an
   equality of the two indices, which is what the refutation below turns
   on. *)
Definition Sets_icoprod_pt (k : nat) :
  carrier (indexed_coproduct (fun _ : nat => Sets_bool)) :=
  existT (fun _ : nat => carrier Sets_bool) k true.

Lemma Sets_icoprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_coproduct (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_icoprod_pt 0 ≈ Sets_icoprod_pt 1) → False)
    by (intros [e _]; simpl in e; discriminate).
  assert (H12 : (Sets_icoprod_pt 1 ≈ Sets_icoprod_pt 2) → False)
    by (intros [e _]; simpl in e; discriminate).
  destruct (H _ _ _ H01 H12) as [e _]; simpl in e; discriminate.
Qed.
