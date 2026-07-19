Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
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

   STATUS: this development supplies a complete bicategory. Beyond the hom-
   categories `bicat x y` and the horizontal-composition functor `hcompose`, the
   class now carries the associator `hassoc`, the left/right unitors
   `hunit_left`/`hunit_right` (as 2-isomorphisms in the hom-categories), their
   naturality squares, and the triangle and pentagon coherence laws — exactly
   the fields mirroring `Structure/Monoidal.v` under the dictionary
   tensor ↔ hcompose, I ↔ bi1id, λ ↔ hunit_left, ρ ↔ hunit_right,
   α ↔ hassoc. The derived horizontal 2-cell operation `hcomp2` (Godement
   whiskering) is the functorial action of `hcompose` on a pair of 2-cells, and
   is what the coherence laws are stated through. *)

(* Why weaken a 2-category: examples, coherence, and the monad slogan

   nLab:      https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory
   Paper: Bénabou, J., "Introduction to bicategories", Reports of the
          Midwest Category Seminar, LNM 47, Springer 1967, pp. 1-77
   Paper: Kelly, G.M., Street, R., "Review of the elements of
          2-categories", LNM 420, Springer 1974, pp. 75-103
   Paper: Mac Lane, S., Paré, R., "Coherence for bicategories and indexed
          categories", J. Pure Appl. Algebra 37, 1985, pp. 59-80

   The notion is due to Bénabou (1967).  A strict 2-category demands that
   horizontal composition of 1-cells be associative and unital on the
   nose, and almost none of the naturally occurring 2-dimensional
   structures meet that demand.  When composition is given by a universal
   construction — pullback of spans, tensor of bimodules, coend of
   profunctors — the result is determined only up to canonical
   isomorphism, so [hcompose] is associative and unital up to a coherent
   invertible 2-cell rather than on the nose.  A [Bicategory] keeps such
   examples honest by recording the associator [hassoc] and the unitors
   [hunit_left], [hunit_right] as data, and constraining them by the two
   coherence laws [hcoherence_pentagon] and [hcoherence_triangle], so that
   every reasonable diagram of associators and unitors commutes.  This
   was, per nLab, the earliest such notion and remains the one in most
   common use.

   The one-object case is exactly a monoidal category.  Read at a single
   [bi0cell], with [bi1id] as the unit and [hcompose] as the tensor, the
   bicategory axioms are the monoidal coherence axioms; this delooping is
   why the [Bicategory] class was shaped to mirror Structure/Monoidal.v
   field for field (the dictionary in the header above), and
   Theory/Bicategory/OneObject.v realizes the correspondence by projecting
   the monoidal data into a one-object bicategory (nLab; Wikipedia).

   Cat is the archetypal strict example — categories, functors, natural
   transformations — realized in Instance/Cat/Bicategory.v, where the
   hom-category [bicat] C D is definitionally the functor category on C
   and D.  The motivating weak examples lie elsewhere.  Span(C) over a
   category with pullbacks is, as the header of Construction/Span/Category.v
   notes, literally a bicategory, and quotienting by apex-iso recovers a
   strict 1-category (with Span(Set) subsuming Rel); its pushout mirror
   Cospan(C) is in Construction/Cospan/Category.v; bimodules over rings are
   what nLab calls the prototype for many similar examples; and profunctors
   compose by a coend, whose unit and associator laws are developed in
   Construction/Profunctor/Laws.v.

   The headline payoff, observed in the same 1967 paper, is a slogan: a
   small category is a monad in the bicategory of spans of sets.  A monad
   on a set A₀ in Span(Set) is a span A₀ ← A₁ → A₀ (objects, morphisms,
   source and target) with a multiplication A₁ ×_{A₀} A₁ → A₁
   (composition) and a unit A₀ → A₁ (identities), and its monad axioms are
   the category axioms.  Varying the ambient bicategory specializes the
   slogan: a monad in Prof is a promonad, the categorical content of
   Hughes's arrows and the setting for profunctor optics (Milewski,
   "Promonads, Arrows, and Einstein Notation for Profunctors", 2019;
   Clarke et al., "Profunctor Optics, a Categorical Update", arXiv 2020).
   More broadly, a bicategory is where composition given by a universal
   construction is modeled without asserting a strict equality it does not
   have.

   Adjunctions internal to a bicategory, and the mates correspondence —
   the bijection of 2-cells they induce — are the 2-categorical toolkit
   for lifts, transports, and Beck-Chevalley squares (Kelly, Street
   1974); the in-tree development gives internal adjunctions in
   Theory/Bicategory/Adjunction.v, the Kelly-Street mates calculus in
   Theory/Bicategory/Mates.v, pseudofunctors (the weak 2-functors) in
   Theory/Bicategory/Pseudofunctor.v, and lax transformations and
   modifications in Theory/Bicategory/Lax.v and
   Theory/Bicategory/Modification.v, with a bicategorical adjunction in
   Cat shown to coincide with F ⊣ U in
   Instance/Cat/Bicategory/Adjunction.v.  The coherence theorem (Mac Lane,
   Paré 1985) shows every bicategory biequivalent to a strict 2-category,
   even though the naturally occurring examples are presented weakly;
   Theory/DoubleCategory.v cross-refers to the [hassoc] orientation used
   here. *)

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

  (* The horizontal composite of two 2-cells (Godement whiskering), obtained as
     the functorial action of `hcompose` on the pair. This is a manifest field:
     it is a definition, not new data, so it computes to the underlying
     bifunctor's `fmap`. All the coherence laws below are phrased through it. *)
  hcomp2 {x y z : bi0cell} {g g' : bicat y z} {f f' : bicat x y}
         (θ : g ~{bicat y z}~> g') (η : f ~{bicat x y}~> f') :
    (g ∘∘∘ f) ~{bicat x z}~> (g' ∘∘∘ f')
    := @fmap _ _ (@hcompose x y z) (g, f) (g', f') (θ, η);

  (* The coherence 2-isomorphisms of a bicategory, living in the hom-categories
     `bicat _ _` and mirroring the unitors and associator of a monoidal
     category (`Structure/Monoidal.v`), with tensor ↔ hcompose, I ↔ bi1id. *)

  hunit_left  {x y : bi0cell} (f : bicat x y) :   (* left  unitor λ[f] *)
    (bi1id ∘∘∘ f) ≅[bicat x y] f;
  hunit_right {x y : bi0cell} (f : bicat x y) :   (* right unitor ρ[f] *)
    (f ∘∘∘ bi1id) ≅[bicat x y] f;
  hassoc {w x y z : bi0cell}                      (* associator α[h,g,f] *)
         (h : bicat y z) (g : bicat x y) (f : bicat w x) :
    ((h ∘∘∘ g) ∘∘∘ f) ≅[bicat w z] (h ∘∘∘ (g ∘∘∘ f));

  (* The unitors and the associator are natural in their 1-cell arguments; each
     square is the horizontal-composition analogue of the monoidal naturality
     of λ, ρ and α (the `to`-direction; the `from`-direction follows since these
     are isomorphisms). *)

  hunit_left_natural {x y : bi0cell} {f f' : bicat x y}
                     (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_left f) ≈ to (hunit_left f') ∘∘ hcomp2 (bi2id (a:=bi1id)) η;
  hunit_right_natural {x y : bi0cell} {f f' : bicat x y}
                      (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_right f) ≈ to (hunit_right f') ∘∘ hcomp2 η (bi2id (a:=bi1id));
  hassoc_natural {w x y z : bi0cell}
      {h h' : bicat y z} {g g' : bicat x y} {f f' : bicat w x}
      (θ : h ~{bicat y z}~> h') (γ : g ~{bicat x y}~> g') (η : f ~{bicat w x}~> f') :
    hcomp2 θ (hcomp2 γ η) ∘∘ to (hassoc h g f)
      ≈ to (hassoc h' g' f') ∘∘ hcomp2 (hcomp2 θ γ) η;

  (* The two coherence laws: the triangle relates the unitors to the associator
     across `bi1id`, and the pentagon makes the two reassociations of a fourfold
     horizontal composite agree. Endpoints mirror `Monoidal.triangle_identity`
     and `Monoidal.pentagon_identity` exactly. *)

  hcoherence_triangle {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
    hcomp2 (to (hunit_right g)) (bi2id (a:=f))
      ≈ hcomp2 (bi2id (a:=g)) (to (hunit_left f)) ∘∘ to (hassoc g bi1id f);
  hcoherence_pentagon {v w x y z : bi0cell}
      (k : bicat y z) (h : bicat x y) (g : bicat w x) (f : bicat v w) :
    hcomp2 (bi2id (a:=k)) (to (hassoc h g f))
      ∘∘ to (hassoc k (h ∘∘∘ g) f)
      ∘∘ hcomp2 (to (hassoc k h g)) (bi2id (a:=f))
      ≈ to (hassoc k h (g ∘∘∘ f)) ∘∘ to (hassoc (k ∘∘∘ h) g f)
}.
#[export] Existing Instance bi2homset.
#[export] Existing Instance vcompose_respects.

(* Smart constructor for [Bicategory], mirroring [Build_Category']: it takes
   every field except `vcompose_assoc_sym` and supplies that symmetric form
   automatically as `symmetry (vcompose_assoc …)`. This is "what symmetry
   permits" — the dual orientation of vertical associativity carries no extra
   content — and keeps duality definitional exactly as in [Category]. Intended
   for use with `unshelve refine`, leaving the coherence obligations as goals. *)
Definition Build_Bicategory'
    bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon :=
  @Build_Bicategory bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    (fun x y a b c d f g h => symmetry (vcompose_assoc x y a b c d f g h))
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon.
