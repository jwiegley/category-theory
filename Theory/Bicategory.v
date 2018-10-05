Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "~~>" (at level 90, right associativity).
Reserved Infix "~~~>" (at level 90, right associativity).
Reserved Infix "∘∘" (at level 40, left associativity).
Reserved Infix "∘∘∘" (at level 40, left associativity).

Class Bicategory := {
  bi0cell : Type;

  bi1uhom := Type : Type;
  bi1cell : bi0cell -> bi0cell -> bi1uhom
    where "a ~~> b" := (bi1cell a b);

  bi2uhom := Type : Type;
  bi2cell {x y : bi0cell} : bi1cell x y -> bi1cell x y -> bi2uhom
    where "a ~~~> b" := (bi2cell a b);

  bi2homset {x y : bi0cell} :> ∀ X Y : bi1cell x y, Setoid (@bi2cell x y X Y);

  bi2id {x y : bi0cell} {a : bi1cell x y} : a ~~~> a;

  vcompose {x y : bi0cell} {a b c : bi1cell x y}
           (f : b ~~~> c) (g : a ~~~> b) : a ~~~> c
    where "f ∘∘ g" := (vcompose f g);

  vcompose_respects x y a b c :>
    Proper (equiv ==> equiv ==> equiv) (@vcompose x y a b c);

  bi2id_left  {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : bi2id ∘∘ f ≈ f;
  bi2id_right {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : f ∘∘ bi2id ≈ f;

  vcompose_assoc {x y : bi0cell} {a b c d : bi1cell x y}
                 (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    f ∘∘ (g ∘∘ h) ≈ (f ∘∘ g) ∘∘ h;
  vcompose_assoc_sym {x y : bi0cell} {a b c d : bi1cell x y}
                     (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    (f ∘∘ g) ∘∘ h ≈ f ∘∘ (g ∘∘ h);

  bicat (x y : bi0cell) : Category := {|
    obj              := @bi1cell x y;
    hom              := @bi2cell x y;
    homset           := @bi2homset x y;
    id               := @bi2id x y;
    compose          := @vcompose x y;
    compose_respects := @vcompose_respects x y;
    id_left          := @bi2id_left x y;
    id_right         := @bi2id_right x y;
    comp_assoc       := @vcompose_assoc x y;
    comp_assoc_sym   := @vcompose_assoc_sym x y;
  |};

  hcompose {x y z : bi0cell} : bicat y z ∏ bicat x y ⟶ bicat x z
    where "f ∘∘∘ g" := (hcompose (f, g));

  (* jww (2018-06-16): The horizontal composition is required to be
     associative up to a natural isomorphism α between morphisms. *)

  (* hcompose_assoc {x y z w : bi0cell} *)
  (*                (f : bicat z w) (g : bicat y z) (h : bicat x y) : *)
  (*   f ∘∘ (g ∘∘ h) ≅ (f ∘∘ g) ∘∘ h *)

  (* jww (2018-06-16): Some more coherence axioms, similar to those needed for
     monoidal categories, are moreover required to hold. *)
}.
