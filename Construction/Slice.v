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

(* The relative point of view

   nLab: https://ncatlab.org/nlab/show/locally+cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/codomain+fibration
   nLab: https://ncatlab.org/nlab/show/fundamental+theorem+of+topos+theory
   nLab: https://ncatlab.org/nlab/show/coreader+comonad
   Wikipedia:
   https://en.wikipedia.org/wiki/Grothendieck%27s_relative_point_of_view

   The slice category is the formal home of the relative point of view:
   it makes "an object over a base" a first-class object, turning
   morphisms into c into objects and commuting triangles into morphisms.
   Comma categories, and with them the slice as their leading special
   case, enter the literature in Lawvere's doctoral dissertation
   (Lawvere, "Functorial Semantics of Algebraic Theories", Columbia
   1963); Wikipedia records that the technique "did not become generally
   known until many years later", and that the name — after the comma in
   Lawvere's original notation — displeased even its author.  Yet the
   viewpoint is older.  Grothendieck's relative point of view, dating
   from the Grothendieck–Riemann–Roch period around 1956, replaces the
   study of a single object X by the study of a morphism f : X ~> S
   over a base S: a property of the map becomes a property of an object
   of C/S, a whole family is handled as one thing, and since C/1 is
   isomorphic to C, a theorem proved over an arbitrary base specializes
   to the absolute theorem over the terminal object (nLab, "over
   category").

   The construction is a dictionary of familiar mathematics.  In Set, an
   object of Set/I is the same data as an I-indexed family of sets: a
   map p : F ~> I carries its fibres, and a family reassembles as the
   disjoint union with its projection — an equivalence Set/I ≃ Set^I
   (Leinster, "Higher Operads, Higher Categories", CUP 2004; nLab,
   "family of sets").  A bundle over a base B in any category is simply
   an object equipped with a morphism to B, so bundles over B form the
   slice C/B (nLab, "bundle"), and covering spaces of X form a full
   subcategory of Top/X.  For a poset P, the slice P/p is the principal
   down-set of p (nLab, "over category").  The dual [Coslice] captures
   pointed structures: pointed sets are the coslice of Set under the
   one-point set (Wikipedia, "Comma category").

   The slice is the fibre-level piece of a larger apparatus.  A morphism
   f : a ~> b induces the post-composition functor Σ_f : C/a ⟶ C/b —
   here [Bang_Functor] in Construction/Slice/Pullback.v — and, when C
   has pullbacks, the base change functor f^* in the other direction
   ([Star_Functor], same file), with the adjunction Σ_f ⊣ f^* recorded
   in that file's header (nLab, "dependent sum").  When every f^* has a
   further right adjoint Π_f, C is locally cartesian closed.  The triple
   Σ_f ⊣ f^* ⊣ Π_f descends from Lawvere's identification of the
   quantifiers as adjoints to substitution (Lawvere, "Adjointness in
   Foundations", Dialectica 1969), and it interprets dependent type
   theory: slice objects are dependent types over their base, base
   change is substitution, and Σ and Π are the dependent sum and product
   (Seely, "Locally cartesian closed categories and type theory", Math.
   Proc. Camb. Phil. Soc. 1984).  Assembling every slice at once yields
   the self-indexing C/(-), whose Grothendieck construction is the
   codomain functor on the arrow category — always an opfibration, and a
   fibration precisely when C has pullbacks, the cartesian lifts being
   the pullback squares (nLab, "codomain fibration").  In-tree,
   Construction/Displayed/Codomain.v presents that fibration
   displayed-style: its fibre over x uses literally this file's object
   encoding, and [codomain_cleaving] / [codomain_cleaving_pullbacks]
   exchange cartesian lifts for pullbacks.

   Two further readings mark where the theory continues.  The
   fundamental theorem of topos theory states that every slice of a
   topos is again a topos; the construction appears as the "topos
   induit" of SGA4 (Artin, Grothendieck, Verdier, SGA4 1972, exposés
   III.5 and IV.5), while the name is due to McLarty (McLarty,
   "Elementary Categories, Elementary Toposes", OUP 1992).  Relative to
   Structure/Topos.v's [ElementaryTopos], it remains the headline
   theorem about this construction not yet formalized here.  And
   comonadically, a coalgebra of the environment comonad e × − is the
   same thing as a single morphism into e, so the category of its
   coalgebras is isomorphic to the slice over e (nLab, "coreader
   comonad"); Instance/Coq/Comonad/Env.v and Comonad/Coalgebra.v supply
   the comonad and its coalgebra categories, the identification with
   [Slice] being a natural corollary still to be stated. *)

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
