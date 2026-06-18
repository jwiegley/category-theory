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
