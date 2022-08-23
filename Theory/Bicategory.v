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

(** Bicategory *)

(* From [ncatlab](https://ncatlab.org/nlab/show/bicategory#detailedDefn):

{In the following text, → matches ~> in this library, and ⇒ matches ~~>}

A bicategory B consists of

- a collection Ob[B] of objects or 0-cells,
- for each object a and object b,
  a collection B(a,b) or Hom[B](a,b)
  of morphisms or 1-cells a → b, and
- for each object a, object b, morphism f:a → b, and morphism g:a → b,
  a collection B(f,g) or 2Hom[B](f,g)
  of 2-morphisms or 2-cells f ⇒ g or f ⇒ g:a → b,

equipped with

- for each object a,
  an identity 1[a]:a → a or id[a]:a → a,
- for each a,b,c, f:a → b, and g:b → c,
  a composite f;g: a → c or g ∘ f:a → c,
- for each f:a → b,
  an identity or 2-identity 1[f]:f ⇒ f or Id[f]:f → f,
- for each f,g,h:a → b, η:f ⇒ g, and θ:g ⇒ h,
  a vertical composite θ ∙ η:f ⇒ h,
- for each a,b,c, f,g:a → b, h:b → c, and η:f ⇒ g,
  a left whiskering h ⊲ η:h ∘ f ⇒ h ∘ g,
- for each a,b,c, f:a → b, g,h:b → c, and η:g ⇒ h,
  a right whiskering η ⊳ f:g ∘ f ⇒ h ∘ f,
- for each f:a → b,
  a left unitor λ[f]:id[b] ∘ f ⇒ f,
  and an inverse left unitor λ⁻¹[f]:f ⇒ id[b] ∘ f,
- for each f:a → b,
  a right unitor ρ[f]:f ∘ id[a] ⇒ f
  and an inverse right unitor ρ⁻¹[f]:f ⇒ f ∘ id[a], and
- for each a →[f] b →[g] c →[h] d,
  an associator α[h,g,f]:(h ∘ g) ∘ f ⇒ h ∘ (g ∘ f)
  and an inverse associator α⁻¹[h,g,f]: h ∘ (g ∘ f) ⇒ (h ∘ g) ∘ f,

such that

- for each η:f ⇒ g:a → b,
  the vertical composites η ∙ Id[f] and Id[g] ∙ η both equal η,
- for each f ⇒[η] g ⇒[θ] h ⇒[ι] i:a → b,
  the vertical composites ι ∙ (θ ∙ η) and (ι ∙ θ) ∙ η are equal,
- for each a →[f] b →[g] c,
  the whiskerings Id[g] ⊳ f and g ⊲ Id[f]; both equal Id[g ∘ f],
- for each f ⇒[η] g ⇒[θ] h:a → b and i:b → c,
  the vertical composite (i ⊲ θ) ∙ (i ⊲ η) equals the whiskering i ⊲ (θ ∙ η),
- for each f:a → b and g ⇒[η] h ⇒[θ] i:b → c,
  the vertical composite (θ ⊳ f) ∙ (η ⊲ f) equals the whiskering (θ ∙ η) ⊳ f,
- for each η:f ⇒ g:a → b,
  the vertical composites λ[g] ∙ (id[b] ⊲ η) and η ∙ λ[f] are equal,
- for each η:f ⇒ g:a → b,
  the vertical composites ρ[g] ∙ (η ⊳ id[a]) and η ∙ ρ[f] are equal,
- for each a →[f] b →[g] c and η:h ⇒ i:c → d,
  the vertical composites α⁻¹[i,g,f] ∙ (η ⊳ (g ∘ f))
  and ((η ⊳ g) ⊳ f) ∙ α⁻¹[h,g,f] are equal,
- for each f:a → b, η:g ⇒ h:b → c, and i:c → d,
  the vertical composites α⁻¹[i,h,f] ∙ (i ⊲ (η ⊳ f))
  and ((i ⊲ η) ⊳ f) ∙ α⁻¹[i,g,f] are equal,
- for each η:f ⇒ g:a → b and b →[h] c →[i] d,
  the vertical composites α⁻¹[i,h,g] ∙ (i ⊲ (h ⊲ η))
  and ((i ∘ h) ⊲ η) ∙ α⁻¹[i,h,f] are equal,
- for each η:f ⇒ g:a → b and θ:h ⇒ i:b → c,
  the vertical composites (i ⊲ η) ∙ (θ ⊳ f) and (θ ⊳ g) ∙ (h ⊲ η) are equal,
- for each f:a → b,
  the vertical composites λ[f] ∙ λ⁻¹[f]:f ⇒ f
  and λ⁻¹[f] ∙ λ[f]:id[b] ∘ f ⇒ id[b] ∘ f
  equal the appropriate identity 2-morphisms,
- for each f:a → b,
  the vertical composites ρ[f] ∙ ρ⁻¹[f]:f ⇒ f
  and ρ⁻¹[f] ∙ ρ[f]:f ∘ id[a] ⇒ f ∘ id[a]
  equal the appropriate identity 2-morphisms,
- for each a →[f] b →[g] c →[h] d,
  the vertical composites α⁻¹[h,g,f] ∙ α[h,g,f]:(h ∘ g) ∘ f ⇒ (h ∘ g) ∘ f
  and α[h,g,f] ∙ α⁻¹[h,g,f]:h ∘ (g ∘ f) ⇒ h ∘ (g ∘ f)
  equal the appropriate identity 2-morphisms,
- for each a →[f] b →[g] c,
  the vertical composite (ρ[g] ⊳ f) ∙ α⁻¹[g,id[b],f]
  equals the whiskering g ⊲ λ[f], and
- for each a →[f] b →[g] c →[h] d →[i] e,
  the vertical composites ((α⁻¹[i,h,g] ⊳ f) ∙ α⁻¹[i,h∘g,f]) ∙ (i ⊲ α⁻¹[h,g,f])
  and α⁻¹[i∘h,g,f] ∙ α⁻¹[i,h,g∘f] are equal.

*)

Class Bicategory := {
  bi0cell : Type;

  bi1uhom := Type : Type;
  bi1cell : bi0cell -> bi0cell -> bi1uhom
    where "a ~~> b" := (bi1cell a b);

  bi2uhom := Type : Type;
  bi2cell {x y : bi0cell} (f g : bi1cell x y) : bi2uhom
    where "f ~~~> g" := (bi2cell f g);

  bi1id {x : bi0cell} : x ~~> x;

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
