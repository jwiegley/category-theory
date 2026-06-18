Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The free bicartesian closed category, presented syntactically. *)

(* nLab: https://ncatlab.org/nlab/show/free+cartesian+category
   nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   A bicartesian closed category is a cartesian closed category that also has
   finite coproducts (an initial object and binary coproducts); its internal
   language is the simply-typed lambda calculus with sums. This file builds the
   free such category on no generators as a term model: objects [Obj] are the
   syntax of types and morphisms [Hom a b] are the syntax of arrows (abstract
   syntax trees) built from the bicartesian-closed combinators.

   Following the term-model construction (nLab: free cartesian category),
   composition is the syntactic constructor [Compose] and the product/coproduct
   structure is given by the pairing/copairing constructors. Rather than quotient
   the terms by βη-equality directly, two arrows are deemed equivalent when they
   agree under *every* interpretation into a concrete bicartesian closed category:

       f ≈ g  :=  ∀ C (bicartesian closed), interp f ≈ interp g     ([AST] homset)

   This makes [interp] sound by construction and, because the free category is
   initial among bicartesian closed categories, the relation coincides with
   equality of arrows in the free BiCCC. The result is the canonical setting for
   normalising/deciding equations of bicartesian-closed combinators (a solver:
   prove an equation once in [AST] and it holds in every model). *)

#[local] Obligation Tactic := cat_simpl.

(* The syntax of objects: the closed type formers of a bicartesian closed
   category (1, ×, ^, 0, +). [denote] reads each former off in a model C. *)
Inductive Obj : Set :=
  | One_    : Obj                       (* terminal object 1 *)
  | Prod_   : Obj → Obj → Obj           (* product x × y *)
  | Exp_    : Obj → Obj → Obj           (* exponential, [Exp_ x y] = y ^ x *)
  | Zero_   : Obj                       (* initial object 0 *)
  | Coprod_ : Obj → Obj → Obj.          (* coproduct x + y *)

(* Interpretation of object syntax into a bicartesian closed category C:
   each type former is read off using the corresponding structure of C. *)
Fixpoint denote `(o : Obj) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_        => 1
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => 0
  | Coprod_ x y => denote x + denote y
  end.

(* The syntax of arrows: one constructor per bicartesian-closed combinator.
   This is a typed term language (a GADT indexed by source and target object),
   so every well-formed AST denotes a morphism via [interp] below. *)
Inductive Hom : Obj → Obj → Set :=
  | Id      : ∀ {a}, Hom a a                                     (* identity id *)
  | Compose : ∀ {a b c}, Hom b c → Hom a b → Hom a c             (* composition g ∘ f *)

  | One'    : ∀ {a}, Hom a One_                                  (* terminal map ! : a ~> 1 *)

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a                         (* projection exl *)
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b                         (* projection exr *)
  | Fork    : ∀ {a c d}, Hom a c → Hom a d → Hom a (Prod_ c d)   (* pairing ⟨f, g⟩ *)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c → Hom a (Exp_ b c)    (* transpose curry *)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) → Hom (Prod_ a b) c    (* inverse transpose uncurry *)

  | Zero'   : ∀ {a}, Hom Zero_ a                                 (* initial map ¡ : 0 ~> a *)

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)                       (* injection inl *)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)                       (* injection inr *)
  | Merge   : ∀ {a c d}, Hom c a → Hom d a → Hom (Coprod_ c d) a. (* copairing [f, g] *)

(* Interpretation of arrow syntax into a bicartesian closed category C: each
   combinator is sent to the corresponding operation of C, so [interp] is the
   unique structure-preserving functor out of the free category into any model. *)
Program Fixpoint interp `(c : Hom a b) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
  match c with
  | Id          => id
  | Compose f g => interp f ∘ interp g

  | One'        => one

  | Exl         => exl
  | Exr         => exr
  | Fork f g    => fork (interp f) (interp g)

  | Curry f     => curry (interp f)
  | Uncurry f   => uncurry (interp f)

  | Zero'       => zero

  | Inl         => inl
  | Inr         => inr
  | Merge f g   => merge (interp f) (interp g)
  end.

(* The free bicartesian closed category: objects are [Obj], arrows are [Hom],
   identity and composition are the syntactic constructors, and two arrows are
   equivalent when they agree under every interpretation (see the file header).
   That equivalence is an equivalence relation [Next Obligation] and is a
   congruence for composition (proven for [Hom_Cartesian] etc. below). *)
#[export]
Program Instance AST : Category := {
  obj     := Obj;
  hom     := Hom;
  id      := @Id;
  compose := @Compose;
  homset  := fun _ _ =>
    {| equiv := fun f g =>
         ∀ (C : Category)
                (A : @Cartesian C)
                `(@Closed C A)
                `(@Cocartesian C)
                `(@Terminal C)
                `(@Initial C),
           interp f ≈ interp g |}
}.
Next Obligation.
  equivalence.
  transitivity (interp y); auto.
Qed.

(* Terminal object 1 = [One_], with the unique arrow into it given by [One']. *)
#[export]
Program Instance Hom_Terminal : @Terminal AST := {
  terminal_obj := One_;
  one := @One'
}.
Next Obligation. apply one_unique. Qed.

(* Binary products x × y = [Prod_], with pairing [Fork] and projections
   [Exl]/[Exr]; the universal property holds under every interpretation. *)
#[export]
Program Instance Hom_Cartesian : @Cartesian AST := {
  product_obj := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
  - split; intros; rewrite HA; cat.
  - intros.
    destruct HA as [? ?].
    rewrite <- e, <- e0.
    rewrite fork_comp; cat.
Qed.

(* Exponentials z ^ y = [Exp_], with the currying isomorphism realised by the
   mutually-inverse syntactic transposes [Curry] and [Uncurry]. *)
#[export]
Program Instance Hom_Closed : @Closed AST _ := {
  exponent_obj := Exp_;
  exp_iso := fun x y z =>
    {| to   := {| morphism := @Curry x y z |}
     ; from := {| morphism := @Uncurry x y z |} |}
}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.

(* Initial object 0 = [Zero_], with the unique arrow [Zero'] out of it. Since
   [Initial AST] unfolds to [Terminal (AST^op)] (duality idiom), this fills the
   dual fields [terminal_obj]/[one], which on the C-side read as initial_obj/zero. *)
#[export]
Program Instance Hom_Initial : @Initial AST := {
  terminal_obj := Zero_;
  one := @Zero'
}.
Next Obligation. apply zero_unique. Qed.

(* Binary coproducts x + y = [Coprod_], with copairing [Merge] and injections
   [Inl]/[Inr]. As [Cocartesian AST] unfolds to [Cartesian (AST^op)] (duality
   idiom), the cartesian fields [fork]/[exl]/[exr] are filled by the dual
   combinators, recovering merge/inl/inr on the C-side. *)
#[export]
Program Instance Hom_Cocartesian : @Cocartesian AST := {
  product_obj := Coprod_;
  fork := @Merge;
  exl  := @Inl;
  exr  := @Inr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
  - split; intros; rewrite HA; cat.
  - intros.
    destruct HA as [? ?].
    rewrite <- e, <- e0.
    rewrite merge_comp; cat.
Qed.

(* [interp] respects arrow equivalence: equivalent ASTs interpret to equivalent
   morphisms in C. This is immediate, since the homset equivalence of [AST] is
   precisely agreement under every interpretation, instantiated here at C. *)
#[export]
Program Instance interp_proper {x y : Obj}
        {C : Category} {A : @Cartesian C}
        `{@Closed C A} `{@Cocartesian C}
        `{@Terminal C} `{@Initial C} :
  Proper (@equiv _ (@homset AST x y) ==>
                     @equiv _ (@homset C _ _))
         (fun f => @interp x y f C A _ _ _ _).
