Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The product of two categories. *)

(* nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   The product category C ∏ D has as objects the pairs (c, d) with c : C and
   d : D, and as morphisms (c, d) ~> (c', d') the pairs (f, g) of a morphism
   f : c ~> c' in C and a morphism g : d ~> d' in D. Identity and composition
   are componentwise: id := (id, id) and (f, g) ∘ (f', g') := (f ∘ f', g ∘ g').
   Equivalence of morphisms is the componentwise conjunction of ≈ in C and ≈
   in D, and the unit and associativity laws hold componentwise because they
   hold in each factor.

   This is the cartesian product in Cat, the category of categories: the
   projection functors Fst and Snd (π₁, π₂ below) exhibit C ∏ D as the
   categorical product of C and D, so a functor E ⟶ C ∏ D is the same as a
   pair of functors E ⟶ C and E ⟶ D. This is the product *of categories*, and
   is distinct from a product *object* inside a single category, formed via a
   universal cone in Structure/Cartesian.v.

   All of the methods are spelled out here to ease simplification. *)

(* Bifunctors, interchange, and the product's place in Cat

   nLab (the rival tensor): https://ncatlab.org/nlab/show/funny+tensor+product

   The product category exists so that a functor of several variables
   requires no theory of its own.  In the founding paper of the subject
   (Eilenberg and Mac Lane, "General Theory of Natural Equivalences",
   Transactions of the AMS 1945), functors in two arguments are axiomatized
   directly: its §3 posits an object-function and a mapping-function subject
   to an identity condition and to an interchange condition equating the
   image of a pair of composites with the interleaved composite of images —
   stated with no product category in sight, for the paper never constructs
   one.  The packaging is the textbook consolidation of Mac Lane,
   Categories for the Working Mathematician, §II.3 (1971), which defines
   C × D, redefines a bifunctor as an ordinary functor out of it, and
   characterizes such functors by two families of partial functors agreeing
   on objects and satisfying interchange.  Riehl introduces the product for
   the same reason, so that the covariant and contravariant represented
   functors "assemble into a single bifunctor, which is the name for a
   functor of two variables" (Riehl, Category Theory in Context, Dover
   2016, Definition 1.3.12).  Once [Product] is in hand, every general
   theorem about functors — naturality, composition, adjunctions, limits —
   applies verbatim to multivariable ones.

   The definition packages the interchange law once and for all.
   Functoriality of F : C ∏ D ⟶ E at a composable pair of pair-morphisms IS
   middle-four exchange: Functor/Bifunctor.v reads it off as [bimap_comp],
   where [bimap] applied to f and g is literally fmap at the pair (f, g)
   ([bimap_fmap] holds at Leibniz equality), and factoring (f, g) through
   (f, id) and (id, g) in either order recovers Mac Lane's two partial
   functors ([bimap_comp_id_left], [bimap_comp_id_right]) together with
   their commutation ([bimap_id_right_left], [bimap_id_left_right]).
   Haskell's Data.Bifunctor class is the same content in type-class form,
   where the default bimap composes the two one-sided actions and is lawful
   precisely because they commute; separate functoriality does not in
   general yield joint functoriality, and the categories where the two
   notions come apart are the premonoidal categories of
   Structure/Premonoidal.v (Milewski, "Functoriality", 2015).  The
   companion construction classifying separately-functorial maps with no
   interchange at all is the funny tensor product of Construction/Funny.v;
   indeed Cat carries exactly two symmetric closed monoidal structures —
   this cartesian product and the funny tensor — and no others (Foltz,
   Lair and Kelly, "Algebraic categories with few monoidal biclosed
   structures or none", Journal of Pure and Applied Algebra 1980).

   Mixed variance is handled through opposites: contravariance in one slot
   is covariance from the opposite category in that slot, and
   [Product_Opposite] makes the bookkeeping free of transport.  The leading
   example is the hom bifunctor [Hom] : C^op ∏ C ⟶ Sets of Functor/Hom.v,
   whose curried form [Curried_Hom] underlies the Yoneda development;
   further consumers include the tensor ⊗ : C ∏ C ⟶ C of
   Structure/Monoidal.v, horizontal composition [hcompose] in
   Theory/Bicategory.v, profunctors C ⇸ D as functors C^op ∏ D ⟶ Sets in
   Theory/Profunctor.v, and the dinatural transformations of
   Theory/Dinatural.v.  The tensor bifunctor also carries the physical
   reading of monoidal categories, modelling composite systems in quantum
   foundations and quantum informatics (Coecke and Paquette, "Categories
   for the practising physicist", 2009); the ZX-calculus instance
   Instance/ZX.v imports this file for exactly that tensor.  Double
   diagrams are functors from a product of index categories, and [Swap] is
   the symmetry through which limits over them are interchanged (Riehl
   2016, Theorem 3.8.1).  Within Cat itself, Instance/Cat/Cartesian.v
   takes this construction as the product object,
   Functor/Construction/Product.v supplies its action on functors F ∏⟶ G,
   and Instance/Cat/Cartesian/Closed.v adds the currying isomorphism,
   exhibiting Cat as cartesian closed. *)

Definition Product (C D : Category) : Category := {|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g);

  compose_respects := fun x y z f g fg h i hi =>
    (compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun x y f =>
    (@id_left C (fst x) (fst y) (fst f),
     @id_left D (snd x) (snd y) (snd f));
  id_right := fun x y f =>
    (@id_right C (fst x) (fst y) (fst f),
     @id_right D (snd x) (snd y) (snd f));

  comp_assoc := fun x y z w f g h =>
    (@comp_assoc C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun x y z w f g h =>
    (@comp_assoc_sym C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h))
|}.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

(* First projection functor π₁ : C ∏ D ⟶ C, taking (c, d) to c on objects and
   (f, g) to f on morphisms. *)
#[export]
Program Instance Fst {C D : Category} : C ∏ D ⟶ C := {
  fobj := fst;                          (* (c, d) ↦ c *)
  fmap := fun _ _ => fst                (* (f, g) ↦ f *)
}.

(* Second projection functor π₂ : C ∏ D ⟶ D, taking (c, d) to d on objects and
   (f, g) to g on morphisms. *)
#[export]
Program Instance Snd {C D : Category} : C ∏ D ⟶ D := {
  fobj := snd;                          (* (c, d) ↦ d *)
  fmap := fun _ _ => snd                (* (f, g) ↦ g *)
}.

(* The symmetry functor C ∏ D ⟶ D ∏ C exchanging the two factors, witnessing
   that the product of categories is commutative up to isomorphism. *)
Program Definition Swap
        {C : Category} {D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);      (* (c, d) ↦ (d, c) *)
  fmap := fun _ _ f => (snd f, fst f);  (* (f, g) ↦ (g, f) *)
|}.

Corollary fst_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.

Require Import Category.Construction.Opposite.

(* The opposite of a product is the product of the opposites, on the nose:
   both Opposite and Product act componentwise, so the two categories are
   definitionally equal (hence the proof by reflexivity, using =). *)
Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
