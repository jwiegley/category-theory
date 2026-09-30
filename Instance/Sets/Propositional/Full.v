Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(** * The full subcategory of propositional setoids, reflective in [Sets] *)

(* nLab:    https://ncatlab.org/nlab/show/full+subcategory
   nLab:    https://ncatlab.org/nlab/show/reflective+subcategory
   nLab:    https://ncatlab.org/nlab/show/Bishop+set
   nLab:    https://ncatlab.org/nlab/show/propositional+truncation
   Book:    The Univalent Foundations Program, "Homotopy Type Theory", IAS
            2013, Definition 3.1.1 (a SET) and Definition 3.3.1 (a MERE
            PROPOSITION), as cited in Lib/Setoid/Propositional.v
   Book:    Awodey, "Category Theory", Carnegie Mellon pre-print of the 1st
            ed. (September 2005), §10.3, printed p. 278 (PDF p. 287), read
            from the page image: "Its left adjoint F is the discrete poset
            functor.  For any set X, therefore, one has as the unit the
            identity function X = UF(X)."

   BACKGROUND.  The sets of the textbooks have a propositional equality:
   two elements are equal or they are not, and a proof that they are equal
   carries no information.  The objects of this library's [Sets]
   (Instance/Sets.v) are Bishop sets, setoids whose `≈` is [Type]-valued,
   and Lib/Setoid/Propositional.v explains why that stays so and names the
   property [PropEquiv] that a particular setoid's `≈` is logically a
   proposition.  Instance/Sets/Propositional.v carries the property along
   the constructions of [Sets], and its header records that no instance
   of the shape "every object of [Sets] is propositional" is available.
   This file takes the other route: it cuts out the full subcategory
   [PropSets] of [Sets] on the setoids that CARRY a [PropEquiv], so that
   inside it every object is propositional by construction.  It is the
   category in which a textbook argument that uses the equality of sets
   can be read without truncating anything.

   The subcategory is reflective, and the reflector is the truncation of
   the equality.  [trunc_setoid S] keeps the carrier of S and compares by
   [inhabited (x ≈ y)], a [Prop]; a map out of it into a propositional
   setoid is a map out of S, because [inhabited (x ≈ y)] can be
   eliminated into the [Prop] mirror of the target's `≈` (Lib/Setoid/
   Propositional.v's [pequiv_elim_inhabited], the one elimination
   [PropEquiv] buys).  The unit of the reflection is the identity
   function S → trunc S, and so is the counit trunc X → X.  Over the
   propositional setoids the counit is an isomorphism, as for every full
   reflective subcategory (Construction/Reflective.v's
   [reflective_counit_iso]).

   IN-TREE CONNECTIONS.
     - Construction/Subcategory.v supplies the record, the category
       [Sub], the inclusion [Incl] and its faithfulness; the sibling
       precedent for a full subcategory of [Sets] cut out by a property of
       objects is Construction/Subcategory/Finite.v's [FinSets].
     - Construction/Reflective.v's record [Reflective] packages the
       reflection ([PropSets_Reflective]); Construction/Reflective/
       Monadic.v's [Reflective_Monadic] then makes [PropSets_Incl] monadic,
       which Instance/Pos/Monadicity.v states ([PropSets_Incl_Monadic]).
     - Instance/Pos/Monadicity.v is the first consumer.  Every poset's
       setoid is propositional there ([pos_PropEquiv]), so Instance/Pos.v's
       [Pos_Forget] factors through [PropSets] by [PropSets_lift]; the
       discrete poset on a propositional setoid needs no truncation, and
       the monad it induces on [PropSets] is isomorphic to the identity
       monad with identity components, which is Awodey's p. 278 unit
       "the identity function X = UF(X)" read over [PropSets].  Over the
       whole of [Sets] the discrete poset is the reflector [PropSets_trunc]
       followed by that one, on objects and on arrows at [eq_refl] (as
       functors the equation is refused, structurally past the standard
       library: R19 of Test/ProbeMonadicity469.v), and its monad is the
       truncation.
     - The concrete algebraic object records carry a [PropEquiv] field
       since PR #1320 ("Algebraic carriers are sets", merged 2026-09-17),
       so their forgetful functors factor through [PropSets] by
       [PropSets_lift] as well; none of those factorizations is built
       here.
     - Instance/Top/Components.v (#462, PR #1338, merged 2026-09-30)
       built the same category first: its [PSetsSub] and [PSets] are
       [PropSets_sub] and [PropSets] at [eq_refl] (a control of
       Test/ProbeComponents462.v).  This file keeps its own copy as the
       reusable home under Instance/Sets/, with a [Require] closure of 39
       modules against Components.v's 118 (by [Print Libraries]);
       unifying the two is left to the maintainer.

   WHAT IS HERE.
     - [PropSets_sub], [PropSets] and [PropSets_Incl]: the subcategory
       record ([sobj] is Instance/Sets/Propositional.v's [PropEquivObj],
       [shom] is [True]), the category and the inclusion, with the
       readbacks [PropSets_Incl_fobj] and [PropSets_Incl_fmap].
     - [PropSets_Full] (full as data), [PropSets_Incl_Full] (full as a
       functor, with the chosen preimage (g; I) readable) and
       [PropSets_Incl_Faithful].
     - [PropSets_LocallyPropositional]: its hom-setoids are propositional,
       pointwise in the target's [pequiv], by Instance/Sets/
       Propositional.v's [LocallyPropositional_of_relation] with the
       relation of its [hom_PropEquiv] read on first projections.  That
       file declares no such instance for [Sets].
     - [PropSets_lift F P]: a functor into [Sets] whose values carry a
       [PropEquiv] factors through [PropSets]; after [PropSets_Incl] it is
       F on objects and arrows ([PropSets_lift_obj], [PropSets_lift_map])
       and ≈ F ([PropSets_lift_Incl]).
     - The truncation: [trunc_equivalence], [trunc_setoid],
       [trunc_PropEquiv], the reflector [PropSets_trunc] with its object
       part [PropSets_trunc_obj], the two transposes [trunc_transpose] and
       [trunc_extend], the hom-set isomorphism [PropSets_trunc_iso] and the
       reflection [PropSets_trunc_Incl : PropSets_trunc ⊣ PropSets_Incl];
       its unit and counit are the identity functions ([PropSets_trunc_unit],
       [PropSets_trunc_counit]); [PropSets_Reflective] is the bundle.

   STRENGTHS.  By [eq_refl]: [PropSets_Incl_fobj], [PropSets_Incl_fmap],
   [PropSets_lift_obj], [PropSets_lift_map], [PropSets_trunc_unit] and
   [PropSets_trunc_counit].  Up to ≈: [PropSets_lift_Incl], in
   Theory/Functor.v's [Functor_Setoid], with identity isomorphisms.  An
   object of [PropSets] is a setoid PAIRED WITH a chosen [PropEquiv], as in
   Construction/Subcategory/Finite.v: two witnesses on one setoid give two
   objects, isomorphic by Construction/Subcategory.v's
   [Full_membership_iso] and not equal in general.  That is why
   Instance/Pos/Monadicity.v's monad on [PropSets] is isomorphic to the
   identity monad and not equal to it, for two reasons: its functor
   recomputes the witness from the order (R7 and R12 of
   Test/ProbeMonadicity469.v), and Coq's [sigT] has no η, so a variable
   object does not convert with its rebuilt pair (R20, R21).  Eight
   proofs end [Defined] (counted by token).  Closing each alone [Qed] in
   a copy of this file followed by Instance/Pos/Monadicity.v and the
   commands of an earlier version of that probe, five stop something:
   [PropSets_lift], [PropSets_trunc], [trunc_transpose], [trunc_extend]
   and [PropSets_trunc_Incl] (the readbacks and the transposition read
   through them).  [PropSets_Incl_Full], [PropSets_lift_Incl] and
   [trunc_equivalence] are [Defined] by the data convention only;
   [PropSets_LocallyPropositional], which was a ninth when that was
   measured, is now a plain term.  The chosen preimage of
   [PropSets_Incl_Full] computes for the use of later files: no constant
   of the tree, and no command of the probe, reads through it.

   UNIVERSES, read off [About]; [o] the carriers and homs, [so] the
   objects, as in [Sets@{o so}], and the bounds o <= Projections.*,
   so <= Projections.* of the sigma types, the compose/ID caps of [Sets]
   and the Logic_lemmas.equality, prod_rect and projections caps of the
   [Adjunction] record (first carried here by [PropSets_trunc_Incl]) are
   the [+].  [PropSets@{o so} : Category@{so o o}], the shape of
   [Sets@{o so}]: the membership [PropEquivObj@{so o o}] sits at the object
   level so, and [Sub]'s own strict level (above the hom level, used only
   in its [id_left] and [id_right] obligations) is instantiated at so,
   which o < so allows.  [trunc_equivalence] and [trunc_setoid] bind the
   single level o, with an empty block on Rocq 9.1.1; their [+] allows
   o <= inhabited.u0, the global level that [inhabited] carries on Coq
   8.19.2 and 8.20.1 (measured there: without it [trunc_equivalence] is
   refused), and [trunc_PropEquiv] has one for the same reason.
   [PropSets_lift@{co ch o so}] adds ch <= o from its functor argument;
   its readbacks pass through [Compose], which forces ch = o by typing
   and adds its strict level s (o < s); [PropSets_lift_Incl] adds a and
   b, the levels of [Functor_Setoid] (o < b its own strict bound).
   [PropSets_trunc_Incl] adds a, the free level of the [Adjunction]
   record that [Build_Adjunction'] leaves.  No block has an equation, and
   [Set] occurs only as [Set < so], which o < so implies.

   NOT DELIVERED.  The forgetful functors of the algebraic categories are
   not factored through [PropSets].  No equivalence between [PropSets] and
   a category of types with [Prop]-valued equivalence relations is built.
   Limits and colimits of [PropSets] are not constructed (the limits would
   come from Instance/Sets/Propositional.v's [limit_PropEquiv]). *)

(** ** The subcategory *)

Definition PropSets_sub@{o so | o < so +} :
  Subcategory@{so o so o} Sets@{o so} :=
  @Build_Subcategory Sets@{o so} PropEquivObj@{so o o}
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition PropSets@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o so o so o so} Sets@{o so} PropSets_sub@{o so}.

Definition PropSets_Incl@{o so | o < so +} :
  PropSets@{o so} ⟶ Sets@{o so} :=
  Incl@{so o so o so so} Sets@{o so} PropSets_sub@{o so}.

Example PropSets_Incl_fobj@{o so | o < so +} (X : PropSets@{o so}) :
  fobj[PropSets_Incl@{o so}] X = projT1 X := eq_refl.

Example PropSets_Incl_fmap@{o so | o < so +} (X Y : PropSets@{o so})
  (f : X ~{PropSets@{o so}}~> Y) :
  fmap[PropSets_Incl@{o so}] f = projT1 f := eq_refl.

(** ** Full and faithful *)

Definition PropSets_Full@{o so | o < so +} :
  Full Sets@{o so} PropSets_sub@{o so} :=
  fun _ _ _ _ _ => I.

(* Built directly rather than by [Full_Implies_Full_Functor], which is
   [Qed]: the chosen preimage of g is (g; I), and it computes, for later
   files; nothing in the tree reads through it yet. *)
Definition PropSets_Incl_Full@{o so | o < so +} :
  Functor.Full PropSets_Incl@{o so}.
Proof.
  unshelve refine {| prefmap := fun X Y g => _ |}.
  - exists g. exact I.
  - intros X Y g x. simpl. reflexivity.
Defined.

Definition PropSets_Incl_Faithful@{o so | o < so +} :
  Functor.Faithful PropSets_Incl@{o so} :=
  Incl_Faithful Sets@{o so} PropSets_sub@{o so}.

(** ** Locally propositional *)

(* Two arrows are ≈ when their functions agree pointwise up to the
   target's `≈`, so the target's [pequiv] mirrors it pointwise: the
   relation of Instance/Sets/Propositional.v's [hom_PropEquiv], read on
   first projections, since a hom-setoid of [PropSets] is a [sigT] over
   [Sets]'s and not [Sets]'s own. *)
#[export] Instance PropSets_LocallyPropositional@{o so | o < so +} :
  LocallyPropositional PropSets@{o so} :=
  LocallyPropositional_of_relation PropSets@{o so}
    (fun X Y (f g : X ~{PropSets@{o so}}~> Y) =>
       ∀ a : carrier (projT1 X),
         @pequiv _ _ (projT2 Y) (projT1 f a) (projT1 g a))
    (fun X Y f g H a => pequiv_to _ _ (H a))
    (fun X Y f g H a => pequiv_from _ _ (H a)).

(** ** Functors into [Sets] with propositional values *)

Definition PropSets_lift@{co ch o so | o < so, ch <= o +}
  {C : Category@{co ch ch}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) : C ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor C PropSets@{o so}
                     (fun c => existT _ (F c) (P c)) (fun x y f => _)
                     _ _ _).
  - exists (fmap[F] f). exact I.
  - intros x y f g H. simpl. exact (@fmap_respects _ _ F x y f g H).
  - intros x. simpl. exact (@fmap_id _ _ F x).
  - intros x y z f g. simpl. exact (@fmap_comp _ _ F x y z f g).
Defined.

Example PropSets_lift_obj@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (c : C) :
  fobj[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] c
    = fobj[F] c := eq_refl.

Example PropSets_lift_map@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (x y : C) (f : x ~> y) :
  fmap[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] f
    = fmap[F] f := eq_refl.

Definition PropSets_lift_Incl@{co o so s a b |
  o < so, o < s, o < b, co <= a, co <= b, o <= a, so <= a +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) :
  @equiv _ (@Functor_Setoid@{a b co s so o} C Sets@{o so})
    (PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P) F.
Proof.
  exists (fun c => iso_id). intros x y f a. simpl. reflexivity.
Defined.

(** ** The truncation *)

Definition trunc_equivalence@{o | +} (S : SetoidObject@{o o}) :
  @Equivalence@{o o} (carrier S)
    (fun x y : carrier S => inhabited (x ≈ y)).
Proof.
  constructor.
  - intros x. exact (inhabits (reflexivity x)).
  - intros x y [H]. exact (inhabits (symmetry H)).
  - intros x y z [H] [K]. exact (inhabits (transitivity H K)).
Defined.

Definition trunc_setoid@{o | +} (S : SetoidObject@{o o}) :
  SetoidObject@{o o} :=
  {| carrier := carrier S;
     is_setoid := {| equiv := fun x y : carrier S => inhabited (x ≈ y);
                     setoid_equiv := trunc_equivalence@{o} S |} |}.

Definition trunc_PropEquiv@{o so | o < so +} (S : SetoidObject@{o o}) :
  PropEquivObj@{so o o} (trunc_setoid@{o} S) :=
  @PropEquiv_of_relation (carrier S) (is_setoid (trunc_setoid@{o} S))
    (fun x y : carrier S => inhabited (x ≈ y))
    (fun x y H => H) (fun x y H => H).

Definition PropSets_trunc_obj@{o so | o < so +} (S : Sets@{o so}) :
  PropSets@{o so} :=
  existT _ (trunc_setoid@{o} S) (trunc_PropEquiv@{o so} S).

Definition PropSets_trunc@{o so | o < so +} :
  Sets@{o so} ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor Sets@{o so} PropSets@{o so}
                     PropSets_trunc_obj@{o so} (fun S T f => _) _ _ _).
  - unshelve eexists; [ | exact I ].
    unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => f x) _).
    intros x y H. simpl in *. destruct H as [H].
    exact (inhabits (proper_morphism f x y H)).
  - intros S T f g H x. simpl. exact (inhabits (H x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

(** ** The reflection *)

Definition trunc_transpose@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (k : PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X) :
  S ~{Sets@{o so}}~> PropSets_Incl@{o so} X.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => projT1 k x) _).
  intros x y H. exact (proper_morphism (projT1 k) x y (inhabits H)).
Defined.

Definition trunc_extend@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (g : S ~{Sets@{o so}}~> PropSets_Incl@{o so} X) :
  PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X.
Proof.
  unshelve eexists; [ | exact I ].
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _).
  intros x y H. apply (@pequiv_elim_inhabited _ _ (projT2 X)).
  simpl in H. destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
Defined.

#[local] Obligation Tactic := idtac.

Program Definition PropSets_trunc_iso@{o so | o < so +}
  (S : Sets@{o so}) (X : PropSets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom PropSets@{o so} (PropSets_trunc@{o so} S) X ;
       is_setoid := @homset PropSets@{o so} (PropSets_trunc@{o so} S) X |}
    {| carrier := @hom Sets@{o so} S (PropSets_Incl@{o so} X) ;
       is_setoid := @homset Sets@{o so} S (PropSets_Incl@{o so} X) |} := {|
  to   := {| morphism := fun k => trunc_transpose@{o so} k |};
  from := {| morphism := fun g => trunc_extend@{o so} g |}
|}.
Next Obligation. intros S X k k' H x; exact (H x). Qed.
Next Obligation. intros S X g g' H x; exact (H x). Qed.
Next Obligation. intros S X g x; reflexivity. Qed.
Next Obligation. intros S X k x; reflexivity. Qed.

Definition PropSets_trunc_Incl@{o so a | o < so +} :
  @Adjunction@{so o o so o o o o so o a} PropSets@{o so} Sets@{o so}
    PropSets_trunc@{o so} PropSets_Incl@{o so}.
Proof.
  unshelve refine (@Build_Adjunction'@{so o o so o o a so} _ _
                     PropSets_trunc@{o so} PropSets_Incl@{o so}
                     PropSets_trunc_iso@{o so} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Example PropSets_trunc_unit@{o so a | o < so +} (S : Sets@{o so}) :
  @Sets.morphism _ _ _ _
    (@Category.Theory.Adjunction.unit _ _ _ _
       PropSets_trunc_Incl@{o so a} S) = (fun x : carrier S => x)
  := eq_refl.

Example PropSets_trunc_counit@{o so a | o < so +} (X : PropSets@{o so}) :
  @Sets.morphism _ _ _ _
    (projT1 (@Category.Theory.Adjunction.counit _ _ _ _
               PropSets_trunc_Incl@{o so a} X))
    = (fun x : carrier (projT1 X) => x)
  := eq_refl.

Definition PropSets_Reflective@{o so a | o < so +} :
  Reflective PropSets_sub@{o so} :=
  {| reflective_full := PropSets_Full@{o so};
     reflector := PropSets_trunc@{o so};
     reflective_adj := PropSets_trunc_Incl@{o so a} |}.
