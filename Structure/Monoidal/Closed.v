Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Closed.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   nLab: https://ncatlab.org/nlab/show/internal+hom
   Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

   A closed monoidal category is a monoidal category in which every functor
   - ⨂ y has a right adjoint y ⇒ -, the internal hom. Equivalently, for all
   objects y, z there is an internal hom object y ⇒ z equipped with an
   evaluation map

       eval : (y ⇒ z) ⨂ y ~> z

   that is universal: for every f : x ⨂ y ~> z there is a unique transpose
   (the curry) curry f : x ~> y ⇒ z with eval ∘ (curry f ⨂ id) ≈ f.

   Packaged as an adjunction, the universal property is the tensor-hom
   bijection

       Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z)         ([exp_iso])

   natural in x, y and z, expressing (- ⨂ y) ⊣ (y ⇒ -). Currying is the
   left-to-right direction, uncurrying its inverse, and eval is the image of
   the identity on y ⇒ z (the counit of the adjunction). Because the right
   tensor factor - ⨂ y is the one given the right adjoint, this is the
   right-closed structure; when C is braided the two tensorings agree and
   [flip] transports the transpose across the braiding.

   This file requires the cartesian (in fact biproduct-style) monoidal
   structure of [CartesianMonoidal] rather than bare [Monoidal], so that the
   pairing used by the substitution lemmas below is available. *)

Reserved Infix "⇒" (at level 30, right associativity).

Class ClosedMonoidal := {
  closed_is_cartesian : @CartesianMonoidal C;   (* the underlying ⨂-structure *)

  exponent_obj : obj → obj → obj    (* internal hom; x ⇒ y = exponent_obj x y *)
    where "x ⇒ y" := (exponent_obj x y);

  (* The tensor-hom adjunction (- ⨂ y) ⊣ (y ⇒ -), as the natural isomorphism
     Hom(x ⨂ y, z) ≅ Hom(x, y ⇒ z).  This is the closed UMP in packaged form:
     the iso bundles existence and uniqueness of the transpose, and naturality
     recovers the substitution laws below. *)
  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);    (* transpose: x⨂y~>z to x~>y⇒z *)
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);  (* inverse transpose *)

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;   (* evaluation; counit, = uncurry id *)

  (* UMP existence-and-uniqueness: the unique transpose h = curry f satisfies
     the beta law f ≈ eval ∘ (h ⨂ id).  Uniqueness is also guaranteed by
     [exp_iso] being an isomorphism (see [uncurry_curry]). *)
  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance closed_is_cartesian.

Coercion closed_is_cartesian : ClosedMonoidal >-> CartesianMonoidal.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{ClosedMonoidal}.

Definition curry   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := @curry' _ x y z.
Definition uncurry {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := @uncurry' _ x y z.
Arguments curry' {_ _ _ _} /.
Arguments uncurry' {_ _ _ _} /.

Definition eval {x y} : (x ⇒ y) ⨂ x ~> y := uncurry id.
Arguments eval' {_ _ _} /.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

#[export] Program Instance curry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@curry a b c).
Next Obligation.
  proper.
  unfold curry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct to; simpl in *.
  rewrites; reflexivity.
Qed.

#[export] Program Instance uncurry_respects (a b c : C) :
  Proper (equiv ==> equiv) (@uncurry a b c).
Next Obligation.
  proper.
  unfold uncurry; simpl in *.
  destruct exp_iso; simpl in *.
  destruct from; simpl in *.
  rewrites; reflexivity.
Qed.

Corollary curry_uncurry {x y z} (f : x ~> y ⇒ z) :
  curry (uncurry f) ≈ f.
Proof.
  sapply (iso_to_from (@exp_iso _ x y z)).
Qed.

Corollary uncurry_curry {x y z} (f : x ⨂ y ~> z) :
  uncurry (curry f) ≈ f.
Proof.
  sapply (iso_from_to (@exp_iso _ x y z)).
Qed.

#[local] Hint Rewrite @curry_uncurry : categories.
#[local] Hint Rewrite @uncurry_curry : categories.
#[local] Hint Rewrite @ump_exponents : categories.

(* Swap the two transposed arguments through the braiding: given a transpose
   of an x⨂y map, produce the transpose of the corresponding y⨂x map. *)
Definition flip `{@BraidedMonoidal C} {x y z : C} `(f : x ~> y ⇒ z) :
  y ~> x ⇒ z := curry (uncurry f ∘ braid).

Corollary curry_eval {x y : C} :
  curry eval ≈ @id _ (x ⇒ y).
Proof.
  intros; unfold eval; simpl; cat.
Qed.

#[local] Hint Rewrite @curry_eval : categories.

Corollary curry_inj {x y z : C} (f g : x ⨂ y ~> z) :
  curry f ≈ curry g → f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrites; reflexivity.
Qed.

Corollary uncurry_inj {x y z : C} (f g : x ~> y ⇒ z) :
  uncurry f ≈ uncurry g → f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrites; reflexivity.
Qed.

End Closed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

#[export] Hint Rewrite @curry_uncurry : categories.
#[export] Hint Rewrite @uncurry_curry : categories.
#[export] Hint Rewrite @ump_exponents : categories.
#[export] Hint Rewrite @curry_eval : categories.
