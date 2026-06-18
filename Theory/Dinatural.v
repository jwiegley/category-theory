Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Dinatural.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.
Context {G : C^op ∏ C ⟶ D}.

(* `prod_split f g` packages a contravariant component `f` (a morphism of
   `C^op`) and a covariant component `g` (a morphism of `C`) into a single
   morphism of the product category `C^op ∏ C`, on which `F` and `G` act.
   The notation `f ⋆⋆⋆ g` (section-local) just abbreviates `(f, g)`, making
   the mixed variance of each functor argument explicit at the use sites in
   `dinaturality`. *)
Definition prod_split {x y z w} (f : x ~{C^op}~> z) (g : y ~{C}~> w) :
  (x, y) ~{ (C ^op) ∏ C }~> (z, w) := (f, g).
Arguments prod_split {_ _ _ _} _ _ /.

Infix "⋆⋆⋆" := prod_split (at level 100) : category_scope.

(* nLab: https://ncatlab.org/nlab/show/dinatural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Dinatural_transformation

   A dinatural transformation `α : F ⇏ G` between functors of mixed variance
   `F G : C^op ∏ C ⟶ D` is a family of morphisms `α_x : F (x, x) ~> G (x, x)`,
   one per object `x : C` (its components, the diagonal F(x,x) → G(x,x)). In
   place of a naturality square it satisfies, for every `f : x ~> y`, the
   dinaturality hexagon — a six-edge diagram in which both composites run from
   `F (y, x)` to `G (x, y)`:

     G f x ∘ α_x ∘ F f x  ≈  G x f ∘ α_y ∘ F x f

   In the library's variance-explicit notation this reads:

     fmap[G] (id ⋆⋆⋆ f) ∘ α_x ∘ fmap[F] (op f ⋆⋆⋆ id)
       ≈ fmap[G] (op f ⋆⋆⋆ id) ∘ α_y ∘ fmap[F] (id ⋆⋆⋆ f)

   The hexagon is weaker than naturality: it only constrains the diagonal
   components, and applies to functors contravariant in their first argument
   and covariant in their second. Dinatural transformations do NOT compose in
   general (the composite of two dinaturals need not be dinatural), which is
   why no identity/composition structure is provided here — only the data and
   its setoid of components. *)
Class Dinatural := {
  ditransform {x} : F (x, x) ~> G (x, x);  (* component α_x on the diagonal *)

  (* dinaturality hexagon, for `f : x ~> y`, both sides `F (y,x) ~> G (x,y)`:
     `G f x ∘ α_x ∘ F f x ≈ G x f ∘ α_y ∘ F x f` *)
  dinaturality {x y} (f : x ~{C}~> y) :
    fmap[G] (op f ⋆⋆⋆ id) ∘ @ditransform y ∘ fmap[F] (id ⋆⋆⋆ f)
        ≈ fmap[G] (id ⋆⋆⋆ f) ∘ @ditransform x ∘ fmap[F] (op f ⋆⋆⋆ id)
}.

#[export] Program Instance Dinatural_Setoid : Setoid Dinatural := {|
  equiv := fun X Y => forall x, (@ditransform X x) ≈ (@ditransform Y x)
|}.
Next Obligation.
  equivalence.
  transitivity (@ditransform y x0); auto.
Qed.

End Dinatural.

Notation "ditransform[ F ]" := (@ditransform _ _ _ _ F)
  (at level 9, format "ditransform[ F ]") : category_scope.

(* Dinatural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion ditransform : Dinatural >-> Funclass.
