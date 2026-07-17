Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Universal arrows *)

(* nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   A universal arrow from an object c : C to a functor F : D ⟶ C is a pair
   (a, u) consisting of an object a : D and a morphism u : c ~> F a, such that
   for every object d : D and every morphism h : c ~> F d there exists a
   unique g : a ~> d satisfying h ≈ fmap[F] g ∘ u. Equivalently, (a, u) is an
   initial object of the comma category =(c) ↓ F (objects are pairs (d, f)
   with f : c ~> F d). The dual notion, a universal arrow from F to c, is a
   terminal object of F ↓ =(c). Universal arrows are the unifying notion
   behind limits, representables, and adjunctions: when every c : C has a
   universal arrow to U : D ⟶ C, the assignment c ↦ a extends to a left
   adjoint of U, with the arrows u serving as the components of the unit. *)

(* From universal mappings to adjoint functors

   nLab:  https://ncatlab.org/nlab/show/universal+construction
   Paper: Samuel, "On universal mappings and free topological groups",
          Bull. Amer. Math. Soc. 54(6), 1948
   Paper: Porst, "The history of the General Adjoint Functor Theorem",
          arXiv:2310.19528, 2024

   The universal arrow is the common shape of the universal mapping
   problems of classical algebra and topology, isolated before category
   theory had vocabulary to state it.  Free groups were current in the
   1920s, the Stone–Čech compactification in the 1930s, and Markov's free
   topological groups in the 1940s, each with its own bespoke existence
   proof (Porst 2024).  The general problem was first posed by Pierre
   Samuel, whose 1948 paper opens by observing that "constructions so
   apparently different as Kronecker products, ... field of quotients of
   an integral domain, free groups, free topological groups, completion
   of a uniform space, Čech compactification enter in the same frame".
   Samuel worked without functors — his axiomatized "kinds of structure"
   derive from Bourbaki's theory of structures, cited from unpublished
   manuscripts and the 1939 Résultats — yet his problem of universal
   mappings asks exactly for a universal arrow to a forgetful functor,
   unique up to isomorphism.  Mac Lane's chapter notes credit Samuel with
   "the bold step of really formulating the general notion", suggest that
   uniqueness only up to isomorphism is why the notion was slow to
   develop, and record that Bourbaki then popularized it lavishly; the
   notes to the adjunctions chapter add that Bourbaki's one-sided
   formulation "lacks the symmetry of the adjunction problem" and so
   just missed adjoint functors, whose discovery was left to Kan in
   1958 (Mac Lane, "Categories for the Working Mathematician", Springer
   1998, notes to Chapters III and IV).  Products described by the
   universal property of their projections date from about the same
   time (Mac Lane, 1948/1950); Functor/Diagonal.v plays out that dual
   story in-tree.

   The purpose of the notion is codified by Theorem IV.1.2 of the same
   book: a functor has a left adjoint precisely when every object of its
   codomain has a universal arrow to it, and those arrows are then the
   components of the unit.  A universal arrow is thus the local,
   pointwise form of an adjunction, and this file implements the
   local-to-global direction: [LeftAdjointFunctorFromUniversalArrows]
   assembles the functor, and [AdjunctionFromUniversalArrows] the
   adjunction, from a family of [UniversalArrow] witnesses.  The
   comma-category packaging does real work here: because [arrow_initial]
   is an initial object, uniqueness up to unique isomorphism is the
   generic initial-object argument rather than a lemma re-proved per
   construction — in Riehl's phrasing, "universal" is "a synonym for
   either 'initial' or 'terminal'" (Riehl, "Category Theory in Context",
   Dover 2016).  Structure/UniversalProperty/Universal/Arrow.v keeps the
   representability face: [UniversalArrowIsUniversalProperty] identifies
   an [AUniversalArrow] with a hom-set isomorphism via Yoneda.

   The adjoint functor theorems are machines for manufacturing these
   witnesses.  Samuel's own existence proof — form the product of all
   mappings into structures of bounded cardinal, then cut down by
   closure — is the skeleton of Freyd's proof of the General Adjoint
   Functor Theorem (1960 thesis, printed 1964), which Porst accordingly
   proposes to rename the Samuel–Freyd theorem.  In-tree the route is
   Mac Lane's: Adjunction/GAFT.v produces an initial object of each comma
   category, and its [GAFT_from_initials] concludes with the two
   constructors of this file; Monad/Lifting.v proves the Dubuc
   adjoint-triangle theorem the same way, one universal arrow per object;
   and Construction/Free/Quiver.v instantiates the oldest pattern, a free
   construction as a universal arrow to a forgetful functor
   ([UniversalArrowQuiverCat]).

   The rendering throughout is proof-relevant.  [ump_universal_arrows]
   returns the mediating morphism as data together with its uniqueness
   certificate, and [LeftAdjointFunctorFromUniversalArrows] computes the
   action of the induced functor on a morphism f as the unique g with
   arrow ∘ f ≈ fmap[U] g ∘ arrow: a free functor acts on arrows by
   factorization rather than by choice.  The setoid discipline surfaces
   in the direct encoding: uniqueness in [universal_arrow_universal] is
   uniqueness up to ≈, and [AUniversalArrowEquiv] declares two universal
   arrows at the same object equivalent precisely when their underlying
   morphisms are ≈, the uniqueness half carrying no further data.  The
   method remains in use well outside foundations (Pestov, "Universal
   arrows to forgetful functors from categories of topological algebra",
   1992), and Milewski teaches it to programmers as the "universal
   construction": pick a shape, enumerate its occurrences, rank
   candidates by unique factorization (Milewski, "Products and
   Coproducts", 2015). *)

(* Two encodings of this notion are given below. UniversalArrow packages the
   property as an initial object of the comma category =(c) ↓ F, which makes
   the universal mapping property [ump_universal_arrows] an immediate
   consequence; AUniversalArrow records the same data directly as a morphism
   together with its [Unique] factorization, without naming the object a as a
   projection out of the comma category. *)

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(* A universal arrow from c to F is an initial object of the comma category
   =(c) ↓ F.  Its underlying object [arrow_obj] and morphism [arrow] are read
   off as the two projections of that initial object. *)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);   (* the universal property, as initiality *)

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));     (* the universal object a : D *)
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)  (* the universal morphism u : c ~> F a *)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(* The universal mapping property: any h : c ~> F d factors as h ≈ fmap[F] g ∘
   arrow through a unique g : arrow_obj ~> d.  This follows directly from the
   initiality of arrow_obj in the comma category =(c) ↓ F. *)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((ttt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
  - assumption.
  - intros.
    rewrite <- id_right in e.
    rewrite <- id_right in X.
    exact (snd (@zero_unique _ arrow_initial ((ttt, d); h)
                             ((ttt, h1); e) ((ttt, v); X))).
Qed.

(* Conversely, the universal mapping property reconstructs the initial object,
   hence a UniversalArrow: given η : c ~> F d that factors every f : c ~> F d'
   uniquely, (d, η) is initial in =(c) ↓ F. *)
Definition universal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D) (η : c ~> fobj[F] d)
  (u : ∀ (d' : D) (f : c ~> fobj[F] d'), ∃! g : d ~> d', f ≈ fmap[F] g ∘ η)
  : UniversalArrow c F.
Proof.
  unshelve eapply Build_UniversalArrow. simpl. unshelve esplit.
  - simpl. unshelve esplit; [ split; [ exact ttt | exact d ] | exact η ].
  - simpl. intros [ [unit d'] f]; simpl in *.
    unshelve esplit; [ split ; [ exact ttt | exact (unique_obj (u d' f))] | ].
    rewrite id_right; simpl. exact (unique_property (u d' f)).
  - simpl. intros [[unit d']  f]; simpl in *.
    intros [[unit2 g] g_eq]. simpl in g_eq.
    intros [[unit3 h] h_eq]. split.
    + simpl. destruct unit2, unit3; reflexivity.
    + simpl. rewrite id_right in g_eq, h_eq. simpl in h_eq.
      rewrite <- (uniqueness (u d' f) _ g_eq).
      exact (uniqueness (u d' f) _ h_eq).
Defined.

Context (U : @Functor D C).

Arguments arrow : clear implicits.
Arguments arrow_obj : clear implicits.

(* A universal arrow to U from every object c : C assembles into a left adjoint
   of U.  The object map sends c to its universal object arrow_obj, and the
   morphism map sends f : x ~> y to the unique factorization of arrow ∘ f
   through arrow_obj x. *)
Definition LeftAdjointFunctorFromUniversalArrows (H : forall c : C, UniversalArrow c U)
  : @Functor C D.
Proof.
  refine
    ({|
        fobj := (fun c => arrow_obj _ _ (H c));
        fmap := (fun x y f => unique_obj (ump_universal_arrows (H x)
                                            ((arrow _ _ (H y) ∘ f))))

      |}).
  - abstract(intros x y f g f_eq_g;
             apply uniqueness;
             rewrite <- (unique_property
                  (ump_universal_arrows (H x) (arrow y U (H y) ∘ g)));
             now rewrite f_eq_g).
  - abstract(intros ?; apply uniqueness; cat_simpl).
  - abstract(intros c1 c2 c3 g f; apply uniqueness;
      rewrite fmap_comp,
      <- comp_assoc,
      <- (unique_property (ump_universal_arrows (H c1) _)),
      2! comp_assoc;
      exact (compose_respects _ _
             (unique_property (ump_universal_arrows (H c2) _))
             f f (Equivalence_Reflexive _))).
Defined.

(* The induced functor is genuinely left adjoint to U: the hom-set isomorphism
   (LeftAdjoint c ~> d) ≊ (c ~> U d) is exactly the universal factorization,
   with the universal arrows u serving as the unit of the adjunction. *)
Definition AdjunctionFromUniversalArrows (H: forall c : C, UniversalArrow c U) :
  @Adjunction _ _ (LeftAdjointFunctorFromUniversalArrows H) U.
Proof.
  unshelve eapply Build_Adjunction'.
  + intros c d; unshelve eapply Isomorphism.Build_Isomorphism.
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact (fun g => (fmap[U] g) ∘ (arrow _ _ (H c))).
    * abstract(intros ? ? g1_eq_g2; rewrite g1_eq_g2; reflexivity).
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact(fun f => unique_obj (ump_universal_arrows (H c) f)).
    * abstract(intros f1 f2 f1_eq_f2; apply uniqueness; rewrite f1_eq_f2;
               apply (unique_property (ump_universal_arrows (H c) f2))).
  - abstract(intro f; symmetry; exact (unique_property (ump_universal_arrows (H c) f))).
  - abstract(simpl; intro g; apply uniqueness; reflexivity).
  + abstract(intros c1 c2 d f g;
             simpl; rewrite fmap_comp, <- 2! comp_assoc;
             apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _) _ _);
             symmetry;
             apply (unique_property (ump_universal_arrows (H c1) _))).
  + abstract(intros ? ? ? ? ?; simpl; rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.


(* The same notion stated directly, with the universal object a : D given as a
   parameter rather than projected from a comma category.  The data is the
   universal morphism together with its uniqueness-of-factorization property. *)
Class AUniversalArrow (c : C) (F : D ⟶ C) (a : D) := {
    universal_arrow : c ~> fobj[F] a ;                 (* the universal morphism u : c ~> F a *)
    universal_arrow_universal {d} {f : c ~> (fobj[F] d)} :  (* the universal property: f factors uniquely as fmap[F] g ∘ u *)
    Unique (fun g : hom a d => fmap[F] g ∘ universal_arrow ≈ f)
  }.

(* Two universal arrows at the same object are equivalent when their underlying
   morphisms agree; the uniqueness property carries no further data. *)
#[export] Program Instance AUniversalArrowEquiv (c : C) (F : D ⟶ C) (a : D) :
  Setoid (AUniversalArrow c F a) :=
  {| equiv := fun X Y => (@universal_arrow _ _ _ X) ≈ (@universal_arrow _ _ _ Y) |}.

End UniversalArrow.
