Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/closed+category
   nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

   This file is an in-progress stub for a "closed category" in the sense of
   Eilenberg and Kelly: a category C equipped with an internal hom bifunctor

       [-, -] : C^op ∏ C ⟶ C,

   a unit object I, a natural isomorphism x ≅ [I, x], an identity element
   I ~> [x, x], and a composition morphism [y, z] ~> [[x, y], [x, z]],
   subject to coherence axioms. Unlike a closed *monoidal* category, a closed
   category need not carry a tensor product; the internal hom is primitive and
   the tensor-hom adjunction Hom(x ⊗ y, z) ≅ Hom(x, [y, z]) is not assumed.

   The [Closed] class capturing this structure is sketched but commented out
   below (see the jww TODO); only the two helper functors [Curry] and [Flip]
   are live. The fully worked closed *monoidal* category, with tensor, an
   evaluation morphism eval[a, b] : (a ⇒ b) ⊗ a ~> b, and the currying
   universal property, lives instead in [Structure.Monoidal.Closed]. *)

(* Where closed categories come from, and why the hom is primitive

   nLab (La Jolla proceedings):
   https://ncatlab.org/nlab/show/Proceedings+of+the+Conference+on+Categorical+Algebra+-+La+Jolla+1965
   Wikipedia:
   https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
   Wikipedia: https://en.wikipedia.org/wiki/Currying
   Paper: Eilenberg, Kelly, "Closed Categories", in Proceedings of the
          Conference on Categorical Algebra — La Jolla 1965, Springer 1966,
          421–562
   Paper: Kelly, "Basic Concepts of Enriched Category Theory", LMS Lecture
          Note Series 64, Cambridge University Press 1982

   The definition sketched above opens Eilenberg and Kelly's La Jolla
   paper, a 142-page work that also treated monoidal categories — the
   very name "monoidal category" is, Mac Lane later wrote, due to
   Eilenberg, and it is used there — and introduced strict 2-categories
   under the name "hypercategories".  Their original axioms differ from
   the modern nLab presentation in one respect: rather than asking that
   the map from morphisms x ~> y to global elements I ~> [x, y] be a
   bijection, the paper carried an underlying-set functor sending the
   internal hom strictly to the external hom-set.  Closed categories
   serve as a base for enrichment — the nLab observes that a closed
   structure on V is already an enrichment context in which V is
   self-enriched — a subject given its textbook consolidation in Kelly's
   1982 book; enrichment over a monoidal base is realized in-tree in
   Construction/Enriched.v.

   The point of declining the tensor is that in many categories the hom is
   the obvious datum and the tensor is not.  Abelian groups internalize
   their homs by pointwise addition; so do the algebras of any commutative
   algebraic theory, and strict 2-categories with lax transformations.  In
   each case, the nLab notes, there is a corresponding tensor product,
   "but its construction is much less intuitive, being essentially defined
   by a sort of adjoint functor theorem" — the Gray tensor product and the
   projective tensor product of Banach spaces were originally defined as
   left adjoints to their homs.  The asymmetry is genuine: a closed
   monoidal category yields a closed category by forgetting the tensor,
   yet recovering a monoidal structure demands C-natural representability
   of [a, [b, ─]], stronger than the Set-natural isomorphisms needed in
   the other direction (for symmetric closed categories ordinary
   naturality suffices; Day–LaPlaza, Prop. 2.3, per the nLab).  LaPlaza's
   embedding theorem (1977) nevertheless places every closed category
   fully and faithfully inside a closed monoidal one.

   Lambek carried closed structure into logic in his deductive-systems
   trilogy (Lambek, "Deductive Systems and Categories I–III", Mathematical
   Systems Theory 2 1968; Springer LNM 86 1969; LNM 274 1972), whose third
   part exhibits cartesian closed categories as the equational theory
   shared by intuitionistic propositional proofs and typed combinators —
   the categorical leg of Curry–Howard, "abstracting away from dynamics of
   computation such as beta reduction" (Wikipedia, "Curry–Howard
   correspondence"; book form in Lambek and Scott, "Introduction to Higher
   Order Categorical Logic", Cambridge University Press 1986).
   Theory/Category.v cites that reading as the bridge behind this file and
   Instance/Lambda/: Instance/Lambda.v builds the syntactic cartesian
   closed category of the simply typed lambda calculus, and [Coq_Closed]
   in Instance/Coq.v interprets exponentials as Coq's own arrow types.

   The live content of this file is itself a currying statement one level
   up.  [Curry] transposes a bifunctor C^op ∏ D ⟶ E into a functor-valued
   functor C^op ⟶ [D, E] — the cartesian closure of Cat, used to present
   the partial applications of an internal hom — and [Curry] after [Flip]
   yields the contravariant section; the transposition device itself
   predates category theory (Frege 1893, Schönfinkel 1924; Curry wrote in
   1980 that "Schönfinkel had the idea some 6 years before I did" —
   Wikipedia, "Currying").  The library's operative closed interfaces are
   Structure/Cartesian/Closed.v (exponentials via [exp_iso], with curry,
   uncurry and eval) and Structure/Monoidal/Closed.v ([ClosedMonoidal],
   the tensor-hom adjunction); Functor/Hom/Internal.v derives the internal
   hom bifunctor [InternalHomFunctor] from cartesian closure;
   Structure/Monoidal/StarAutonomous.v declines this file as a base, a
   placeholder carrying no tensor-hom adjunction, and works over its own
   [SymMonClosed]; and Construction/Funny/Closed.v presents the only other
   monoidal biclosed structure on Cat (Foltz, Lair, Kelly, JPAA 17(2),
   1980). *)

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

#[local] Set Transparent Obligations.

(* [Curry] partially applies a bifunctor in its first argument: it sends a
   functor of two variables F : C^op ∏ D ⟶ E to the functor-valued functor
   x ↦ (y ↦ F (x, y)), of type C^op ⟶ [D, E]. On objects the inner functor
   acts by F (x, -); the outer fmap of f : x ~> y yields the natural
   transformation z ↦ fmap[F] (f, id[z]). This is the section [F x, ─] of a
   bifunctor, and is what makes the [ X , ─ ] / [ ─ , X ] notations below
   denote genuine functors. *)
Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

(* [Flip] swaps the two arguments of a bifunctor, sending
   F : C^op ∏ D ⟶ E to (x, y) ↦ F (y, x) of type D ∏ C^op ⟶ E. Composing
   [Curry] with [Flip] partially applies the *second* argument, giving the
   contravariant section [ ─ , X ]. *)
Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

(* jww (2018-10-05): TODO

   The class below sketches the Eilenberg-Kelly data: the internal hom
   bifunctor, the unit object I (= unit_object), the unit isomorphism
   i : x ≅ [I, x] (hom_id_iso), the identity element j : I ~> [x, x]
   (hom_id), and the composition morphism L : [y, z] ~> [[x, y], [x, z]]
   (hom_compose). The two coherence fields are still incomplete: hom_id_right
   and the unnamed hom_ field both contain underscores standing for morphisms
   that have not yet been pinned down, so the class does not yet typecheck.
   Completing it means stating the five Eilenberg-Kelly axioms relating i, j
   and L; until then the whole block is left commented out.

Class Closed := {
  internal_hom_functor : C^op ∏ C ⟶ C       (* [-, -] internal hom *)
    where "[ X , Y ]" := (@internal_hom_functor (X, Y));
  unit_object : C;                          (* the unit object I *)

  (* hom_id_iso  : Id[C] ≅[Fun] Curry internal_hom_functor unit_object; *)
  hom_id_iso {x} : x ≅ [unit_object, x];    (* unit iso i : x ≅ [I, x] *)

  hom_id {x} : unit_object ~> [x, x];                 (* identity j : I ~> [x, x] *)
  hom_compose {x y z} : [y, z] ~> [[x, y], [x, z]];   (* composition L *)

  hom_id_right {x y} :
    @hom_compose x y y ∘ hom_id << unit_object ~~> [[x, y], [x, y]] >> hom_id;

  hom_ {x y} :
    _ ∘ @hom_compose x x y
      << [x, y] ~~> [unit_object, [x, y]] >>
    to (hom_id_iso ([x, y]))
}.

Notation "[ X , Y ]" := (internal_hom_functor (X, Y))
  (at level 90, right associativity, format "[ X ,  Y ]") : object_scope.

Notation "[ X , ─ ]" := (Curry internal_hom_functor X)
  (at level 90, right associativity, format "[ X ,  ─ ]") : object_scope.

Notation "[ ─ , X ]" := (Curry (Flip internal_hom_functor) X)
  (at level 90, right associativity, format "[ ─ ,  X ]") : object_scope.

*)

End Closed.
