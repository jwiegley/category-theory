Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The slice (over) category C/c and coslice (under) category c/C. *)

(* nLab: https://ncatlab.org/nlab/show/over+category
   nLab: https://ncatlab.org/nlab/show/under+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Fix a category C and an object c : C. The slice category C/c has as objects
   the morphisms a ~> c into c (encoded as the dependent pair (∃ a : C, a ~> c),
   so `1 x is the domain a and `2 x is the structure morphism a ~> c). A
   morphism from x = (a, g : a ~> c) to y = (a', g' : a' ~> c) is a morphism
   f : a ~> a' in C making the triangle commute, `2 y ∘ f ≈ `2 x, i.e.
   g' ∘ f ≈ g:

       a  --f-->  a'
        \         /
       g \       / g'      commute, i.e.  g' ∘ f ≈ g.
          v     v
            c

   Identity is id (g ∘ id ≈ g) and composition is composition in C (the
   triangle for f ∘ f' follows by associativity); two slice morphisms are
   equivalent when their underlying C-morphisms are ≈, the triangle proof being
   irrelevant. Dually, the coslice c/C has objects the morphisms c ~> a out of
   c and morphisms f : a ~> a' with `2 y ≈ f ∘ `2 x, i.e. ι' ≈ f ∘ ι.

   Both are special cases of the comma category (Construction/Comma.v). Taking
   the constant functor =(c) := Δ(c) : 1 ⟶ C selecting c, the slice is the
   comma (Id[C] ↓ =(c)) and the coslice is (=(c) ↓ Id[C]); these isomorphisms
   are proven below as Comma_Slice and Comma_Coslice. The forgetful functor
   C/c ⟶ C sending (a, g) to a is the comma projection comma_proj1 transported
   across Comma_Slice; the post-composition functor C/a ⟶ C/b induced by a
   morphism a ~> b (making C/(-) functorial) lives in Construction/Slice/
   Pullback.v as Bang_Functor. *)

Program Definition Slice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, a ~> c;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite comp_assoc; rewrites; reflexivity. Defined.

Notation "C  ̸ c" := (@Slice C c) (at level 90) : category_scope.

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Id[C] ↓ Δ(c)). *)

#[local] Set Transparent Obligations.

#[export]
Program Instance Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ =(c)) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct H0, H1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct H, H0; simpl; cat.
  - destruct H, H0; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.

Program Definition Coslice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, c ~> a;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ≈ f ∘ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite <- comp_assoc; rewrites; reflexivity. Defined.

Notation "c  ̸co C" := (@Coslice C c) (at level 90) : category_scope.

#[export]
Program Instance Comma_Coslice `(C : Category) `(c : C) :
  c ̸co C ≅[Cat] (=(c) ↓ Id) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct x0, x1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct x0, x1; simpl; cat.
  - destruct x0, x1; simpl; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.
