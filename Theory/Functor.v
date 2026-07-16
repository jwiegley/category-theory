Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   A functor F : C ⟶ D assigns to each object x : C an object F x : D and to
   each morphism f : x ~> y a morphism fmap f : F x ~> F y, subject to the two
   functoriality laws fmap id ≈ id (fmap_id) and fmap (f ∘ g) ≈ fmap f ∘ fmap g
   (fmap_comp). Because hom-sets here are setoids, the morphism mapping must
   also respect ≈ (fmap_respects); the equational laws above use ≈ rather than
   = throughout. Functoriality forces functors to preserve isomorphisms (see
   [fobj_iso] below).

   Note that there are many species of functor, one each for the various
   categorical structures (included below), for example, the `CartesianFunctor`
   that maps products to products and preserves all its structural properties
   and laws. *)

(* Where functors come from, and what they are for

   SEP:  https://plato.stanford.edu/entries/category-theory/
   nLab: https://ncatlab.org/nlab/show/General+Theory+of+Natural+Equivalences

   Functors are the founding notion of category theory, not a derived one.
   Categories, functors, and natural transformations entered mathematics
   together in (Eilenberg, Mac Lane, "General theory of natural
   equivalences", Transactions of the American Mathematical Society 58,
   1945) — the paper the nLab page above calls the foundational document of
   category theory — distilled from the group-level computations of their
   "Group Extensions and Homology" (Annals of Mathematics, 1942).  The
   authors were explicit about the order of ideas: "the whole concept of a
   category is essentially an auxiliary one" (quoted in the SEP entry
   above), the basic concepts being those of functor and natural
   transformation.  Categories exist so that functors have domains and
   codomains, and functors exist so that naturality can be stated.  The
   word itself was borrowed from Rudolf Carnap, who had used it for a
   linguistic notion in The Logical Syntax of Language (1937), as recorded
   in Mac Lane, Categories for the Working Mathematician (Springer, 1971),
   p. 30.

   A functor is the homomorphism notion for categories — the nLab frames it
   as a horizontal categorification of the homomorphism concept — and its
   purpose is double-sided.  Read outward, a functor transports whole
   situations from one mathematical world to another, homology carrying
   spaces to groups being the founding example; it follows from the iso
   preservation recorded in [fobj_iso] that an invariant packaged as a
   functor can never distinguish isomorphic objects.  Read inward, a
   functor INTO a category is a diagram: a diagram of type J in C is a
   covariant functor from J to C (Wikipedia, "Functor"), and
   Structure/Limit.v takes exactly such an F : J ⟶ C as the shape over
   which limits are formed.  Because [Compose] is associative with [Id] as
   unit up to the natural isomorphisms of [Functor_Setoid]
   ([fun_equiv_id_left], [fun_equiv_id_right], [fun_equiv_comp_assoc]),
   categories themselves assemble into the category Cat of Instance/Cat.v,
   whose morphisms are this file's functors; the same functors are the
   objects of the functor categories of Instance/Fun.v, whose morphisms —
   natural transformations, Theory/Natural/Transformation.v — form the next
   rung of the ladder.

   The applications track both readings.  Contravariant functors to Sets
   are presheaves (nLab), of which the hom-functors of Functor/Hom.v and
   the Yoneda embedding built from them are the canonical examples; a
   functor from a one-object category BG to vector spaces is precisely a
   linear representation of the group G (nLab); and Lawvere's functorial
   semantics recast universal algebra by taking a theory to be a category
   with finite products and a model to be a product-preserving functor out
   of it (Lawvere, "Functorial Semantics of Algebraic Theories", PhD
   thesis, Columbia University 1963; reprinted as TAC Reprints No. 5,
   2004), the perspective implemented over this file in
   Theory/Lawvere/Model.v.  The structure-preserving species the header
   advertises live under Functor/Structure/.

   The computational reading is genuine.  In typed functional programming
   the type constructor is the object map and fmap the morphism map, with
   the two laws left as the programmer's proof obligation, verified by
   equational reasoning (Milewski, "Functors", 2015); this file
   accordingly ships the Haskell spellings <$>, <$ and <&> as parsing-only
   notations, and Theory/Coq/Functor.v carries the fmap-only class of that
   tradition, its laws discharged per instance.  In Haskell the second law
   is redundant, derivable from the first together with the free theorem of
   the type of fmap, up to the usual caveat about bottom and seq
   (Luposchainsky, "The second functor law is redundant").  No such
   parametricity is available over arbitrary categories with setoid
   hom-sets, so here [fmap_comp] is a genuine obligation of the class, and
   a third law, [fmap_respects], appears that Haskell renders invisible.
   The same setoid design decides what functor equality means: not
   pointwise identity of objects but a natural isomorphism
   ([Functor_Setoid]), with a stricter transport-based alternative deferred
   to [Functor_StrictEq_Setoid] at the end of this file. *)

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;                                (* action on objects *)
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;  (* action on morphisms *)

  fmap_respects : ∀ x y,                       (* fmap respects ≈ (setoid law) *)
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;       (* functor law: preserves identities *)
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :  (* functor law: preserves composition *)
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
#[export] Existing Instance fmap_respects.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(* Functors used as functions map objects of categories, similar to the way
   type constructors behave in Haskell. We cannot, unfortunately, have a
   similar coercion for morphisms, because coercions cannot be bound to
   scopes. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%_category D%_category Functor%_functor x%_object y%_object} f%_morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 0, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 0, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

#[export]
Program Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D) := {
  (* Note that it doesn't make much sense (with our definition of [Category])
     to ask that [∀ x : C, F x = G x] and
     [∀ (x y :C) (f : x ~> y), fmap[F] f ≈ fmap[G] f] because the second
     condition is hard to work with in the type-system since it needs lots of
     equality proofs. *)
  equiv := fun F G =>
    (* Equality of objects in a category is taken to be a natural
       isomorphism *)
    { iso : ∀ x : C, F x ≅ G x
    & ∀ (x y : C) (f : x ~> y),
        fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x) }
}.
Next Obligation.
  equivalence.
  - isomorphism.
    + exact (from (x0 x1)).
    + exact (to (x0 x1)).
    + apply iso_from_to.
    + apply iso_to_from.
  - simpl.
    rewrite e.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - isomorphism.
    + apply (to (x0 x2) ∘ to (x1 x2)).
    + apply (from (x1 x2) ∘ from (x0 x2)).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x1 x2)).
      rewrite iso_to_from, id_left.
      apply iso_to_from.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x0 x2)⁻¹).
      rewrite iso_from_to, id_left.
      apply iso_from_to.
  - simpl.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _ (x0 y0)⁻¹).
    rewrite <- (comp_assoc _ ((x0 y0)⁻¹ ∘ _)).
    rewrite <- e.
    apply e0.
Qed.

Lemma fun_equiv_to_fmap {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    to (``eqv y) ∘ fmap[F] f ≈ fmap[G] f ∘ to (``eqv x).
Proof.
  intros.
  rewrite <- id_right.
  rewrite ((`2 eqv) _ _).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Lemma fun_equiv_fmap_from {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    fmap[F] f ∘ from (``eqv x) ≈ from (``eqv y) ∘ fmap[G] f.
Proof.
  intros.
  rewrite <- id_left.
  rewrite ((`2 eqv) _ _).
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Ltac constructive :=
  simpl;
  match goal with
    [ |- { iso : ?I & ?F } ] =>
    given (iso : I); [ intros; isomorphism; simpl; intros
                     | exists iso; intros ]
  end.

#[export]
Program Instance fobj_iso `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) (fobj[F]).
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
  - rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  - rewrite <- fmap_comp.
    rewrite iso_from_to; cat.
Defined.

#[export]
Instance fobj_respects `(F : C ⟶ D) :
  Proper (equiv ==> equiv) (@fobj C D F) := @fobj_iso C D F.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

(* The identity functor Id[C] maps every object and morphism to itself; it is
   the unit for functor composition (see fun_equiv_id_left/right below). *)
Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 0, format "Id[ C ]") : functor_scope.

(* Composition of functors F ◯ G applies G then F on both objects and
   morphisms. It is associative with Id as unit, making Cat a category. *)
Program Definition Compose {C D E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. intros; rewrite !fmap_comp; reflexivity. Qed.

#[export] Hint Unfold Compose : categories.

Notation "F ◯ G" := (Compose F%functor G%functor)
  (at level 40, left associativity) : category_scope.

#[export]
Program Instance Compose_respects {C D E : Category} :
  Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
Next Obligation.
  proper.
  - isomorphism; simpl; intros.
    + exact (fmap (to (x1 x3)) ∘ to (x2 (x0 x3))).
    + exact (from (x2 (x0 x3)) ∘ fmap (from (x1 x3))).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x2 (x0 x3))).
      rewrite iso_to_from, id_left.
      rewrite <- fmap_comp.
      rewrite iso_to_from; cat.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap _)).
      rewrite <- fmap_comp.
      rewrite iso_from_to, fmap_id, id_left.
      rewrite iso_from_to; cat.
  - simpl.
    rewrite e0, e.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
Qed.

Corollary fobj_Compose `(F : D ⟶ E) `(G : C ⟶ D) {x} :
  fobj[F ◯ G] x = fobj[F] (fobj[G] x).
Proof. reflexivity. Defined.

Lemma fun_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_right {A B} F.

Lemma fun_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_left {A B} F.

Lemma fun_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
  F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
Proof. construct; cat. Qed.

Arguments fun_equiv_comp_assoc {A B C D} F G H.

(* nLab: https://ncatlab.org/nlab/show/full+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_functor

   F is full when each hom-map fmap[F] : (x ~> y) → (F x ~> F y) is surjective.
   Constructively this is witnessed by a section [prefmap] of [fmap[F]]: a
   choice of preimage with fmap[F] (prefmap g) ≈ g ([fmap_sur]), rather than by
   a bare surjectivity proposition. No functoriality is demanded of [prefmap]
   itself — it need not respect ≈ nor preserve identities/composition; only that
   it lands in a genuine preimage. This matches the standard meaning of fullness
   (cf. issue #118); the previous definition's [prefmap_respects], [prefmap_id]
   and [prefmap_comp] fields were extraneous. *)
Class Full `(F : C ⟶ D) := {
  prefmap {x y} (g : F x ~> F y) : x ~> y;     (* chosen preimage of g under fmap *)

  fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g  (* prefmap is a section of fmap *)
}.

(* nLab: https://ncatlab.org/nlab/show/faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Faithful_functor

   F is faithful when each hom-map fmap[F] : (x ~> y) → (F x ~> F y) is
   injective. *)
Class Faithful `(F : C ⟶ D) := {
  fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g → f ≈ g  (* injectivity of fmap[F] *)
}.

(* nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_and_faithful_functors

   A fully faithful functor (both Full and Faithful) reflects isomorphisms: if
   F x ≅ F y then x ≅ y. The witnesses are [prefmap] applied to the given iso;
   the inverse laws are discharged by faithfulness ([fmap_inj]), which reduces
   each to the corresponding law of the image iso after pushing [fmap] through
   composition ([fmap_comp]) and cancelling the sections ([fmap_sur]). Fullness
   alone no longer needs to be functorial. *)
Lemma FullyFaithful `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y.
Proof.
  intros.
  construct.
  + apply prefmap, X.
  + apply prefmap, X.
  + abstract
      (apply fmap_inj;
       rewrite fmap_comp, !fmap_sur, fmap_id;
       apply iso_to_from).
  + abstract
      (apply fmap_inj;
       rewrite fmap_comp, !fmap_sur, fmap_id;
       apply iso_from_to).
Defined.

(* nLab: https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/F-algebra

   For an endofunctor F : C ⟶ C, an F-algebra on a carrier object a is a
   structure morphism F a ~> a; the dual F-coalgebra is a ~> F a. The
   (F, G)-dialgebra generalizes both to a morphism F a ~> G a between the
   images of two endofunctors. Here these definitions name only the carrying
   morphism type, not the full category of algebras. *)
Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

Definition FCoalgebra `(F : C ⟶ C) (a : C) := a ~> F a.

Definition FGDialgebra `(F : C ⟶ C) `(G : C ⟶ C) (a : C) := F a ~> G a.

Section AFunctor.

Context {C D : Category}.

(* [AFunctor] allows the object mapping to be stated explicitly. *)
Class AFunctor (F : C → D) : Type := {
  a_fmap {x y : C} (f : x ~> y) : F x ~> F y;

  a_fmap_respects {x y : C} : Proper (equiv ==> equiv) (@a_fmap x y);

  a_fmap_id {x : C} : a_fmap (@id C x) ≈ id;
  a_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    a_fmap (f ∘ g) ≈ a_fmap f ∘ a_fmap g;
}.
#[export] Existing Instance a_fmap_respects.

Definition FromAFunctor `(AFunctor F) : C ⟶ D := {|
  fobj          := λ x, F x;
  fmap          := @a_fmap F _;
  fmap_respects := @a_fmap_respects F _;
  fmap_id       := @a_fmap_id F _;
  fmap_comp     := @a_fmap_comp F _;
|}.

Coercion FromAFunctor : AFunctor >-> Functor.

Definition ToAFunctor (F : C ⟶ D) : AFunctor F := {|
  a_fmap          := @fmap _ _ F;
  a_fmap_respects := @fmap_respects _ _ F;
  a_fmap_id       := @fmap_id _ _ F;
  a_fmap_comp     := @fmap_comp _ _ F;
|}.

Corollary FromAFunctor_ToAFunctor {F} :
  FromAFunctor (ToAFunctor F) = F.
Proof. reflexivity. Qed.

Corollary ToAFunctor_FromAFunctor `{H : AFunctor F} :
  ToAFunctor (FromAFunctor H) = H.
Proof. reflexivity. Qed.

End AFunctor.

(* An alternative setoid of functors that uses strict (propositional) equality
   of objects, F x = G x, rather than the natural isomorphism F x ≅ G x of
   [Functor_Setoid]. Because objects equal only up to = require transporting
   morphisms along those equalities, this section first develops the transport
   lemmas needed to state and prove the morphism-coherence condition
   ([Functor_StrictEq_Setoid]). This notion is stricter than [Functor_Setoid]
   and is provided for settings where object equality is available. *)
Section StrictEq.
 Lemma transport_adjunction (A : Type) (B : A -> Type) (R: forall a :A, crelation (B a)) :
   forall (a a' : A) (p : a = a') (x : B a) (y : B a'),
    ((R _ x (transport_r B p y) -> R _ (transport B p x) y)) *
      (R _ (transport B p x) y -> (R _ x (transport_r B p y))).
  intros a a' p x y. split.
  - destruct p. now unfold transport_r.
  - destruct p. now unfold transport_r.
Defined.

Lemma transport_relation_exchange (A : Type) (R : crelation A) :
  forall (a a' b b': A) (p : a = b) (q : a' = b') (t : R a a'),
    transport (fun z => R b z) q
      (transport (fun k => R k a') p t) =
      transport (fun k => R k b') p
        (transport (fun z => R a z) q t).
Proof.
  intros a a' b b' p q t; destruct p, q; reflexivity.
Defined.

Lemma transport_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a0) (p : a0 = a1) (q : a1 = a2),
    transport B q (transport B p x) = transport B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Lemma transport_r_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a2) (p : a0 = a1) (q : a1 = a2),
    transport_r B p (transport_r B q x) = transport_r B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Global Instance proper_transport (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport B p).
Proof.
  intros a b p. destruct p. now unfold transport.
Defined.

Global Instance proper_transport_r (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport_r B p).
Proof.
  intros a b p. destruct p. now (unfold transport_r).
Defined.

(* Global Instance proper_transport_hom_cod (C : Category) (c d d': C) (p : d = d')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom c z) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

(* Global Instance proper_transport_hom_dom (C : Category) (c c' d: C) (p : c = c')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom z d) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

#[export] Instance proper_transport_dom (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c c' d : A) (p : c = c') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B z d) p).
Proof.
  destruct p. now trivial.
Defined.

#[export] Instance proper_transport_cod (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c d d' : A) (p : d = d') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B c z) p).
Proof.
  destruct p. now trivial.
Defined.

Program Instance Functor_StrictEq_Setoid {C D : Category} : Setoid (C ⟶ D) := {
    equiv := fun F G =>
      { eq_on_obj : ∀ x : C, F x = G x
                  & ∀ (x y : C) (f : x ~> y),
            transport (fun z => hom (fobj[ F ] x) z) (eq_on_obj y) (fmap[F] f) ≈
                   (transport_r (fun z => hom z (fobj[G] y)) (eq_on_obj x) (fmap[G] f)) }
}.
Next Obligation.
  equivalence.
  - unfold transport_r. rewrite eq_sym_involutive.
    fold (transport_r (λ z : obj[D], fobj[y] x1 ~{ D }~> z) (x0 y0)).
    symmetry.
    rename x into F, y into G, x0 into eq_ob, x1 into x, y0 into y.
    refine ((snd
               (transport_adjunction D (hom (fobj[G] x))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    rewrite transport_relation_exchange.
    refine ((fst
               (transport_adjunction D (fun d' => hom d' (fobj[G] y))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    exact (e _ _ _).
  - exact(eq_trans (x1 x2) (x0 x2)).
  - rename x into F, y into G, z into H, x1 into F_eq_ob_G,
      e0 into F_eq_ob_G_resp_mor, x0 into G_eq_ob_H,
      e into G_eq_ob_H_resp_mor, x2 into domf, y0 into codf.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite F_eq_ob_G_resp_mor.
    unfold transport_r at 1 2. rewrite transport_relation_exchange.
    apply proper_transport_dom.
    apply G_eq_ob_H_resp_mor.
Defined.

Lemma transport_f_equal (A B : Type) (C : B -> Type) (f : A -> B)
  (x y : A) (p : x = y) (t : C (f x))
  : transport (fun a => C (f a)) p t = transport (fun b => C b) (f_equal f p) t.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_dom (C D: Category) (F : @Functor C D) (c c' d : C)
  (p : c = c') (f : hom c d)
  : fmap[F] (transport (fun z => hom z d) p f) =
      transport (fun z => hom z (fobj[F] d)) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_cod (C D: Category) (F : @Functor C D) (c d d': C)
  (p : d = d') (f : hom c d)
  : fmap[F] (transport (fun z => hom c z) p f) =
      transport (fun z => hom (fobj[F] c) z) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

#[export]
 Program Instance Compose_respects_stricteq {C D E : Category} :
   Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
 Next Obligation.
  intros F G [FG_eq_on_obj FG_morphismcoherence] H K [HK_eq_on_obj HK_morphismcoherence].
  unshelve eapply (_ ; _).
  - intro c; simpl.
      exact(eq_trans (f_equal (fobj[F]) (HK_eq_on_obj c)) (FG_eq_on_obj (fobj[K] c))).
  - intros c c' f.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite <- transport_functorial_cod.
    rewrite HK_morphismcoherence.
    unfold transport_r at 1 2.
    rewrite transport_functorial_dom.
    rewrite transport_relation_exchange.
    rewrite <- eq_sym_map_distr.
    apply proper_transport_dom.
    now trivial.
 Defined.

 Lemma fun_strict_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_id_right {A B} F.

 Lemma fun_strict_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_id_left {A B} F.

 Lemma fun_strict_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
   F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_comp_assoc {A B C D} F G H.

End StrictEq.

