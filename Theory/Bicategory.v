Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Reserved Infix "~~>" (at level 90, right associativity).
Reserved Infix "~~~>" (at level 90, right associativity).
Reserved Infix "∘∘" (at level 40, left associativity).
Reserved Infix "∘∘∘" (at level 40, left associativity).

(** Bicategory *)

(* nLab: https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory

   A bicategory (a weak 2-category) has 0-cells (objects), 1-cells between
   0-cells, and 2-cells between parallel 1-cells. For each pair of 0-cells the
   1-cells and 2-cells form a hom-category `bicat x y` (objects are 1-cells,
   morphisms are 2-cells, `∘∘` is vertical composition). Horizontal
   composition `hcompose` is a functor of these hom-categories, associative
   and unital only up to coherent 2-isomorphism: an associator α and left/right
   unitors λ, ρ, subject to the pentagon and triangle coherence laws.

   Notation map: in the verbatim nLab definition below, → is `~>` (a 1-cell)
   and ⇒ is `~~>` (a 2-cell); here `~~~>` is also a 2-cell, `∘∘` is vertical
   2-cell composition and `∘∘∘` is horizontal 1-cell composition.

   STATUS: this development supplies the bicategory data through the hom-
   categories `bicat x y` and the horizontal-composition functor `hcompose`.
   The associator, left/right unitors, and the pentagon and triangle coherence
   laws are not yet formalised; they are described in the TODOs after the
   `hcompose` field. The class as written is therefore an incomplete (data-
   only) bicategory, retained as scaffolding. *)

(* From https://ncatlab.org/nlab/show/bicategory#detailedDefn :

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
  bi0cell : Type;                       (* collection of 0-cells (objects) *)

  bi1uhom := Type : Type;               (* universe of 1-cell collections *)
  bi1cell : bi0cell → bi0cell → bi1uhom (* 1-cells a ~~> b *)
    where "a ~~> b" := (bi1cell a b);

  bi2uhom := Type : Type;               (* universe of 2-cell collections *)
  bi2cell {x y : bi0cell} (f g : bi1cell x y) : bi2uhom  (* 2-cells f ~~~> g *)
    where "f ~~~> g" := (bi2cell f g);

  bi1id {x : bi0cell} : x ~~> x;        (* identity 1-cell on a 0-cell *)

  bi2homset {x y : bi0cell} : ∀ X Y : bi1cell x y, Setoid (@bi2cell x y X Y);
                                        (* 2-cells form a hom-setoid (≈) *)

  bi2id {x y : bi0cell} {a : bi1cell x y} : a ~~~> a;  (* identity 2-cell on a 1-cell *)

  vcompose {x y : bi0cell} {a b c : bi1cell x y}      (* vertical 2-cell composition *)
           (f : b ~~~> c) (g : a ~~~> b) : a ~~~> c
    where "f ∘∘ g" := (vcompose f g);

  vcompose_respects x y a b c :         (* vertical composition respects ≈ *)
    Proper (equiv ==> equiv ==> equiv) (@vcompose x y a b c);

  bi2id_left  {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : bi2id ∘∘ f ≈ f;
                                        (* left unit law for vertical composition *)
  bi2id_right {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : f ∘∘ bi2id ≈ f;
                                        (* right unit law for vertical composition *)

  vcompose_assoc {x y : bi0cell} {a b c d : bi1cell x y}  (* associativity of vertical comp. *)
                 (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    f ∘∘ (g ∘∘ h) ≈ (f ∘∘ g) ∘∘ h;
  vcompose_assoc_sym {x y : bi0cell} {a b c d : bi1cell x y}  (* dual form (built-in duality) *)
                     (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    (f ∘∘ g) ∘∘ h ≈ f ∘∘ (g ∘∘ h);

  bicat (x y : bi0cell) : Category := {|  (* hom-category B(x,y): 1-cells / 2-cells *)
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
    where "f ∘∘∘ g" := (hcompose (f, g));  (* horizontal composition functor *)

  (* The following coherence data and laws of a bicategory are not yet
     formalised (cf. the STATUS note in the header); each would be added as a
     field above. Using the library isomorphism `≅` (in the hom-category
     `bicat _ _`) for the coherence 2-isomorphisms:

       - associator α[h,g,f] : (h ∘∘∘ g) ∘∘∘ f ≅ h ∘∘∘ (g ∘∘∘ f), natural in
         f, g, h (jww 2018-06-16: associativity holds up to this natural iso);
       - left  unitor λ[f] : bi1id ∘∘∘ f ≅ f, natural in f;
       - right unitor ρ[f] : f ∘∘∘ bi1id ≅ f, natural in f;
       - triangle identity relating ρ, λ and α on a ~> b ~> c;
       - pentagon identity relating the four reassociations on a ~> .. ~> e.

     jww (2018-06-16): these coherence axioms, analogous to those of a
     monoidal category, remain to be added. *)

  (* hcompose_assoc {x y z w : bi0cell} *)
  (*                (f : bicat z w) (g : bicat y z) (h : bicat x y) : *)
  (*   f ∘∘∘ (g ∘∘∘ h) ≅ (f ∘∘∘ g) ∘∘∘ h *)
}.
#[export] Existing Instance bi2homset.
#[export] Existing Instance vcompose_respects.
