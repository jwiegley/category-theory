Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * The finite setoids inside [Sets]: a worked full-subcategory example *)

(* nLab:      https://ncatlab.org/nlab/show/FinSet
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_finite_sets
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.3, printed pp. 14-15
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
              Remark 1.5.8, printed p. 33

   Mac Lane's §I.3 example of a full subcategory is the finite sets inside
   Set, with all functions between them.  This file is that example over
   Instance/Sets.v's setoids, assembled from Construction/Subcategory.v:
   [FinSets] selects objects by a finiteness witness and retains EVERY
   morphism of [Sets] between selected objects, so its inclusion is full
   ([FinSets_Full_Functor]) as well as faithful ([FinSets_Faithful]).

   Finiteness, over setoids.  A setoid counts as finite here when some list of
   its carrier exhausts it UP TO `≈` ([FiniteSetoid] via [mem_upto]).  The
   list need not be duplicate-free and the carrier needs no decidable
   equality.  This is the reading forced by the setoid discipline: the ambient
   `≈` is what "the same element" means, so exhaustion must be stated with
   respect to it, not with respect to Coq's `=` on the carrier.

   This is deliberately the cheap witness, sufficient for a full-subcategory
   example and nothing more.  Mac Lane's §I.4 skeleton construction — the
   equivalence between finite sets and finite ordinals, catalog item
   `maclane:I.4:construction4`, filed as issue #238 — is the place where a
   canonical choice of representative for each finite cardinality belongs;
   Instance/FinSet.v already carries the skeletal side of that story.  Nothing
   here depends on either, and no skeleton is constructed below.

   What is exhibited, and what is not
   ----------------------------------

   [FinSets_Incl] is a FULLY FAITHFUL functor into [Sets] whose objects are
   finite setoids.  It is NOT claimed to be injective on objects.  An object
   of [Sub] is a setoid PAIRED WITH a chosen witness, so one setoid can be
   presented with two different enumerations and yield two objects with the
   same image under the inclusion; [FinSets_bool] and [FinSets_bool_dup]
   below do exactly that, and [FinSets_bool_same_image] records that their
   images agree on the nose.  Whether those two objects are themselves
   distinct is not decided here — deciding it would need proof irrelevance for
   the [sobj] component, which this library does not assume — and in any case
   they are isomorphic in the subcategory ([FinSets_bool_iso]).  Nothing in
   the [Subcategory] record of Construction/Subcategory.v forces [sobj] to be
   subsingleton-valued, so this is a feature of the apparatus rather than of
   finiteness.

   Terminology, accordingly: "subcategory" in this file always names the
   [Subcategory] RECORD of Construction/Subcategory.v — the selection data —
   and never asserts that [FinSets_Incl] is injective on objects.  The functor
   is described as fully faithful, which is what is proved of it.

   Non-vacuity.  Statements about an inclusion are content-free if the
   hom-setoids involved are trivial, and faithfulness in particular is an
   injectivity claim that would then say nothing.  [FinSets_two_arrows] below
   exhibits two parallel morphisms of the subcategory — the identity and the
   negation of the two-element setoid — and shows them DISTINCT in the
   subcategory's own hom-setoid.  [FinSets_negb_Monic] then puts
   Theory/Functor.v's [faithful_reflects_monic] to work on that morphism. *)

(** ** Finiteness of a setoid *)

(* Membership up to the ambient `≈` rather than up to `=`; `∨` is
   Category.Lib's `sum`, so this is `Type`-valued and can be eliminated into
   `Type`. *)
Fixpoint mem_upto {X : SetoidObject} (a : carrier X)
         (l : list (carrier X)) : Type :=
  match l with
  | nil       => False
  | cons b l' => (a ≈ b) ∨ mem_upto a l'
  end.

(* A setoid is finite when some list of its carrier exhausts it up to `≈`. *)
Definition FiniteSetoid (X : SetoidObject) : Type :=
  { l : list (carrier X) & ∀ a : carrier X, mem_upto a l }.

(** ** The subcategory of finite setoids *)

(* [shom] ignores its morphism argument: every [Sets]-morphism between finite
   setoids is retained.  That is what makes the subcategory full, and it also
   makes the two closure conditions immediate. *)
Definition FinSets : Subcategory Sets :=
  @Build_Subcategory Sets FiniteSetoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition FinSetsCat : Category := Sub Sets FinSets.

Definition FinSets_Incl : FinSetsCat ⟶ Sets := Incl Sets FinSets.

(* Full as data, hence full as a functor. *)
Definition FinSets_Full : Subcategory.Full Sets FinSets :=
  fun _ _ _ _ _ => I.

Definition FinSets_Full_Functor : Functor.Full FinSets_Incl :=
  Full_Implies_Full_Functor Sets FinSets FinSets_Full.

(* Faithful by the generic argument of Construction/Subcategory.v, which is
   where the observation that it holds for every subcategory now lives. *)
Definition FinSets_Faithful : Functor.Faithful FinSets_Incl :=
  Incl_Faithful Sets FinSets.

(* [shom] here does not inspect its morphism argument, so it is trivially
   closed under `≈`, and the converse bridge applies: fullness of the
   inclusion returns fullness of the data.  This instantiates the hypothesis
   that Construction/Subcategory.v has to assume, showing it is a real
   condition met by the standard shape of full subcategory and not an
   unreachable one. *)
Definition FinSets_ShomRespects : ShomRespects Sets FinSets :=
  fun _ _ _ _ _ _ _ _ => I.

Definition FinSets_Full_roundtrip : Subcategory.Full Sets FinSets :=
  Full_Functor_Implies_Full Sets FinSets
    FinSets_ShomRespects FinSets_Full_Functor.

(** ** Two objects over the same setoid, and two distinct parallel arrows *)

(* The two-element setoid of Theory/Concrete.v is finite: `true` and `false`
   exhaust it. *)
Definition bool_finite : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false nil)).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

(* A second, deliberately redundant enumeration of the very same setoid. *)
Definition bool_finite_dup : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false (cons true nil))).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

Definition FinSets_bool : FinSetsCat := (bool_setoid_object; bool_finite).

Definition FinSets_bool_dup : FinSetsCat :=
  (bool_setoid_object; bool_finite_dup).

(* The two objects have the same image under the inclusion.  This statement is
   deliberately `=` and not `≈`: it compares OBJECTS of [Sets], for which the
   library supplies no hom-setoid to weaken to, and the two images are the same
   object literally, so [reflexivity] closes it.  The setoid discipline applies
   to morphisms, and every morphism-level claim in this file uses `≈`. *)
Lemma FinSets_bool_same_image :
  FinSets_Incl FinSets_bool = FinSets_Incl FinSets_bool_dup.
Proof. reflexivity. Qed.

(* They are isomorphic in the subcategory, by the identity of [Sets] in both
   directions: the two enumerations differ, the underlying setoid does not. *)
Program Definition FinSets_bool_iso :
  FinSets_bool ≅[FinSetsCat] FinSets_bool_dup := {|
  to   := (id; I);
  from := (id; I)
|}.

(* Negation, as a morphism of the subcategory: the underlying [Sets]-morphism
   paired with the trivial [shom] witness. *)
Definition FinSets_negb : FinSets_bool ~{FinSetsCat}~> FinSets_bool :=
  (Sets_negb; I).

(* Non-vacuity.  [Sub]'s `≈` is `≈` of first projections, so distinctness of
   these two parallel morphisms of the subcategory reduces to distinctness of
   `id` and `negb` in [Sets] — Theory/Concrete.v's [Sets_two_arrows].  Stated
   with `→ False` because hom-equivalence here is `Type`-valued, so `¬`, which
   forces `Prop`, does not apply. *)
Lemma FinSets_two_arrows :
  @id FinSetsCat FinSets_bool ≈ FinSets_negb → False.
Proof.
  intro Heq.
  exact (Sets_two_arrows Heq).
Qed.

(* [faithful_reflects_monic] on this example.  Negation is injective, hence
   monic in [Sets] by Instance/Sets.v's [injectivity_is_monic]; the inclusion
   is faithful; so negation is monic in the subcategory as well.  The
   conclusion is not content-free: monicity cancels over every hom-setoid into
   [FinSets_bool], and at least one of them — the endo-hom-setoid, taking the
   source to be [FinSets_bool] itself — has the two distinct elements exhibited
   by [FinSets_two_arrows]. *)
Lemma FinSets_negb_Monic : Monic FinSets_negb.
Proof.
  apply (faithful_reflects_monic FinSets_Incl).
  apply (fst (injectivity_is_monic Sets_negb)).
  intros a b Hab; destruct a, b; simpl in *;
    solve [ reflexivity | discriminate ].
Qed.
