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
