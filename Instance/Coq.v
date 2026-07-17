Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Constant.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category COQ of types and functions. *)

(* nLab: https://ncatlab.org/nlab/show/Set
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   This is the strict-function model of the "category of sets" built from
   Coq's universe Type: objects are types `A : Type`, morphisms `A ~> B` are
   functions `A → B`, identity is `λ x, x` and composition is `λ x, g (f x)`.
   Morphism equivalence is pointwise (extensional) equality of functions,
   `f ≈ g  :=  ∀ x, f x = g x`; unlike Instance/Sets.v (the setoid model),
   the underlying `=` here is Coq's Leibniz equality on the codomain.

   The category laws and the cartesian/cocartesian/terminal/initial structure
   below hold with no axioms (pointwise `=` needs none). The closed structure
   (exponentials) does invoke functional_extensionality, which is the expected,
   pre-existing funext axiom of this layer and lies outside the core
   zero-axiom guarantee. *)

(* Types and functions as the category of sets: history and applications

   nLab:  https://ncatlab.org/nlab/show/ETCS
   nLab (type theory and category theory):
   https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
   Blog:  https://math.andrej.com/2016/08/06/hask-is-not-a-category/

   Reading types and functions as a category enacts the structural stance
   that Lawvere took when he axiomatized the category of sets directly —
   objects and composites first, membership a derived notion (Lawvere, "An
   elementary theory of the category of sets", PNAS 52, 1964, the origin
   of ETCS).  On that view a set is whatever composes, and [Coq] is the
   stance implemented over the universe Type, machine-checked rather than
   postulated.

   The instance is one half of Curry–Howard–Lambek.  Lambek's "Deductive
   systems and categories" series (II, LNM 86, 1969; III, LNM 274, 1972)
   recast deductive systems as categories, Part III pairing cartesian
   closed categories with intuitionist propositional calculus and
   combinatory logic; the polished equivalence between typed λ-calculi
   and cartesian closed categories is Part I of Lambek and Scott,
   "Introduction to Higher Order Categorical Logic", CUP 1986.  In-tree
   the correspondence runs in both directions: Instance/Lambda.v builds
   the simply typed λ-calculus as a syntactic cartesian closed category,
   and Instance/Lambda/Sem.v interprets that syntax into this category —
   the standard model meeting its own internal language.  What is
   folklore in Haskell is a theorem here: Bauer observed that no rigorous
   morphism equality was ever fixed for the supposed category of Haskell
   types and functions, and that under the natural candidates the
   identity law does not survive seq (Bauer, "Hask is not a category",
   2016).  Coq functions are total, and the header above fixes the
   morphism equivalence exactly.

   The division of labour with Instance/Sets.v follows a known fault line
   in intensional type theory.  Hofmann showed that the intensional
   identity type does not identify pointwise-equal functions and yields
   no quotient types, and that setoid models restore both (Hofmann,
   "Extensional concepts in intensional type theory", Edinburgh thesis,
   1995); the Rocq standard library accordingly states
   functional_extensionality_dep as an Axiom rather than a theorem.  The
   two instances occupy the two sides of that line: Instance/Sets.v pays
   with respectfulness bookkeeping on every morphism yet obtains
   exponentials without axioms (Instance/Sets/Cartesian/Closed.v), while
   here the category laws and the structure of [Coq_Terminal],
   [Coq_Initial], [Coq_Cartesian] and [Coq_Cocartesian] hold by Leibniz
   rewriting alone, and exactly one axiom is spent, in [Coq_Closed],
   where currying must respect the pointwise equivalence before
   [exp_iso] can be an isomorphism of hom-setoids.  The setoid side has
   its own boundary: the canonical truth-value object for Instance/Sets.v
   cannot fit at a single universe level — its carrier is the universe
   itself, which the predicative Type hierarchy places one level up, the
   universe-constraint graph staying acyclic (Rocq reference manual,
   sorts) — so Instance/Sets/Classifier.v develops the classifier
   theorems cross-universe instead.

   The payoff here is computational: composition is literally
   λ x, g (f x), so a categorical equation over [Coq] is a runnable
   program equivalence, and developments that stay out of the
   exponentials stay axiom-free.  Instance/Coq/Lists.v proves list A the
   initial algebra of its base functor with pointwise equality and list
   induction alone; Theory/Coq/Monad/Proofs.v defines lawfulness of the
   Haskell-style Monad class as arising from a monad on this category.
   The boundary is itself machine-checked: Instance/Coq/Comonad/Store.v
   shows that the respectfulness field a store functor hosted here would
   require already entails functional extensionality, and hosts Store
   over Instance/Sets.v instead — a live marker of where the Leibniz
   model stops and the setoid model takes over.

   The applications run through the cartesian closed structure.  Because
   the simply typed λ-calculus is modeled by any cartesian closed
   category, a typed program written against this category can be
   reinterpreted in others — the method of Elliott, "Compiling to
   categories" (PACMPL 1, ICFP 2017), practised in-tree by
   Tools/Abstraction.v.  The programmer-facing picture of types as
   objects and functions as morphisms (Milewski, "Category: The Essence
   of Composition", 2014) is this file made rigorous, and
   [Coq_StrongFunctor] packages, once and for every endofunctor, the
   canonical strength that Set-based accounts of effects leave implicit
   (Kock, "Strong functors and monoidal monads", Arch. Math. 23, 1972). *)

#[export]
Program Instance Coq : Category := {
  obj     := Type;                                   (* objects are types *)
  hom     := λ A B : Type, A → B;                    (* morphisms are functions *)
  homset  := λ _ _, {| equiv := λ f g, ∀ x, f x = g x |};  (* pointwise equality *)
  id      := λ _ x, x;                               (* identity function *)
  compose := λ _ _ _ g f x, g (f x)                  (* function composition *)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* Terminal object: the singleton `unit`, with the unique map `λ _, tt`. *)
#[export]
Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;       (* the terminal object 1 := unit *)
  one := λ _ a, tt                    (* the unique map x ~> unit *)
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

(* Products: the cartesian product of types `x * y`, with projections fst/snd
   and pairing ⟨f, g⟩ := λ x, (f x, g x). *)
#[export]
Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := λ x y, x * y : Type;          (* product object x × y *)
  fork := λ _ _ _ f g x, (f x, g x);           (* pairing ⟨f, g⟩ *)
  exl  := λ _ _ p, fst p;                       (* first projection *)
  exr  := λ _ _ p, snd p                        (* second projection *)
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - intros; simplify.
    rewrite <- H, <- H0.
    rewrite <- surjective_pairing; reflexivity.
Qed.

(* The cartesian monoidal structure: tensor := × with unit I := 1 (unit). *)
#[export]
Program Instance Coq_Monoidal : @Monoidal Coq :=
  @CC_Monoidal Coq Coq_Cartesian Coq_Terminal.

(* Exponentials: the function type `y^x := x → y` (Basics.arrow), making COQ
   cartesian closed. The defining isomorphism is curry/uncurry, exhibiting the
   adjunction `(- × x) ⊣ (x → -)` (hom(z × x, y) ≅ hom(z, x → y)). Establishing
   that to/from are mutually inverse invokes functional_extensionality. *)
#[export]
Program Instance Coq_Closed : @Closed Coq _ := {
  exponent_obj := Basics.arrow;                         (* exponential y^x := x → y *)
  exp_iso := λ _ _ _,
    {| to   := {| morphism := λ f a b, f (a, b) |}      (* curry *)
     ; from := {| morphism := λ f p, f (fst p) (snd p) |} |}  (* uncurry *)
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* The cartesian-closed structure read as a closed monoidal structure: the
   internal hom of the cartesian monoidal product is the exponential above. *)
#[export]
Program Instance Coq_ClosedMonoidal : @ClosedMonoidal Coq :=
  @CCC_ClosedMonoidal Coq Coq_Cartesian Coq_Terminal Coq_Closed.

(* Initial object: the empty type `False`, with the unique map out of it given
   by False_rect (the empty function). Because `Initial Coq` unfolds to
   `Terminal (Coq^op)` (initiality is terminality in the opposite category),
   the fields are spelled with the Terminal names `terminal_obj` and `one`. *)
#[export]
Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False;             (* the initial object 0 := False *)
  one := λ _ _, False_rect _ _       (* the unique map False ~> x *)
}.
Next Obligation. contradiction. Qed.

(* Coproducts: the disjoint union (sum type) `x + y`, with injections inl/inr
   and copairing [f, g] by case analysis. Being cocartesian is being cartesian
   in Coq^op, so the fields reuse the Cartesian names: `product_obj` is the
   coproduct object, `fork` is the copairing, and `exl`/`exr` are the
   injections (the projections read in the opposite category). *)
#[export]
Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  product_obj := sum;                          (* coproduct object x + y *)
  fork := λ _ _ _ f g x,                        (* copairing [f, g] *)
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Datatypes.inl p;            (* left injection inl *)
  exr  := λ _ _ p, Datatypes.inr p             (* right injection inr *)
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - destruct x0; firstorder.
Qed.

(* nLab: https://ncatlab.org/nlab/show/tensorial+strength

   Every endofunctor on COQ carries a (unique) tensorial strength. This is the
   familiar fact that every Set-endofunctor is canonically strong, since over a
   cartesian closed category strength is equivalent to enrichment and every
   ordinary functor is automatically Set-enriched (Kock). The strength
   `x × F y ~> F (x × y)` is built by mapping the partial pairing `λ y, (x, y)`
   through F. *)

#[export]
Program Instance Coq_StrongFunctor (F : Coq ⟶ Coq) : StrongFunctor F := {|
  strength := λ _ _ p, fmap[F] (λ y, (fst p, y)) (snd p)  (* x × F y ~> F (x × y) *)
|}.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  now srewrite (@fmap_id _ _ F).
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
