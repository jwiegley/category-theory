Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Monads are monoids in the category of endofunctors *)

(* nLab:      https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   The endofunctor category [[C, C]] is monoidal with functor composition [∘]
   as tensor and the identity functor [Id] as unit (this monoidal structure is
   [Compose_Monoidal]). A monad on [C] is exactly a monoid object in this
   monoidal category: the carrier is the endofunctor [M], the monoid unit
   [mempty : Id ⟹ M] is the monad unit [ret] (η), and the monoid
   multiplication [mappend : M ∘ M ⟹ M] is the monad multiplication [join]
   (μ). Because the tensor here is strict composition, the unitors and
   associator are identities, so the monoid unit/associativity laws collapse to
   the bare monad laws [join_ret], [join_fmap_ret] and [join_fmap_join]; the
   naturality squares of [mempty]/[mappend] become [fmap_ret] and
   [join_fmap_fmap]. This is the precise content of the slogan "a monad is a
   monoid in the category of endofunctors".

   [Monoid_Monad] proves the correspondence as a genuine logical equivalence
   ([↔]), constructing a monad from any such monoid object and vice versa. *)

Definition Endofunctors `(C : Category) := ([C, C]).

(* The two directions are written without setoid rewriting and with every
   universe named (issue #1348), so that [Monoid_Monad] has the same four
   universes on Coq 8.19.2, Coq 8.20.1 and Rocq 9.1.1 ([About] on each).
   Its earlier proof, by [autorewrite] and [rewrite], left a universe list
   whose length depended on the version: four levels on Rocq 9.1.1 and
   twenty-six on Coq 8.19.2, measured by [About] in #468 and recorded with
   control C40 of Test/ProbeMonadMorphism468.v, so that no statement with
   fixed universe binders could use it on all three versions.  Its binder
   lists the four in the order [About] printed on Rocq 9.1.1 before the
   rewrite, and [About] there prints the same constraints as before, up to
   the names of the universes.  The two directions bind them as the
   bridges of Monad/Morphism/Monoid.v do, whose rewrite-free proofs
   (#468) they are; those bridges are now read off this equivalence.
   Outside the former [Section], [Endofunctors] has the four universes of
   its body where it had six: the two dropped were the section's, and
   occurred in no constraint and nowhere in its type ([About], before and
   after, on Rocq 9.1.1). *)
Definition monoidobject_monad@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C}
  (m : @MonoidObject (@Fun@{o h o h f f s} C C)
         (@Compose_Monoidal@{s f o h} C) M) :
  @Monad C M.
Proof.
  unshelve refine (@Build_Monad C M
     (fun x => transform[@mempty _ _ _ m] x)
     (fun x => transform[@mappend _ _ _ m] x) _ _ _ _ _).
  - intros x y g. symmetry. exact (naturality[@mempty _ _ _ m] _ _ g).
  - intros x.
    pose proof (@mappend_assoc _ _ _ m x) as E; simpl in E.
    symmetry.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id.
    + etransitivity;
        [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
      etransitivity; [ apply id_right | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left.
  - intros x.
    pose proof (@mempty_right _ _ _ m x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
  - intros x.
    pose proof (@mempty_left _ _ _ m x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x y g. symmetry. exact (naturality[@mappend _ _ _ m] _ _ g).
Defined.

Definition monad_monoidobject@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C} (T : @Monad C M) :
  @MonoidObject (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) M.
Proof.
  unshelve refine (@Build_MonoidObject (@Fun@{o h o h f f s} C C)
     (@Compose_Monoidal@{s f o h} C) M _ _ _ _ _).
  - exact (Build_Transform'@{o h h o h h} (F := Id) (G := M)
             (fun x => @ret C M T x)
             (fun x y g => symmetry (fmap_ret g))).
  - exact (Build_Transform'@{o h h o h h} (F := M ◯ M) (G := M)
             (fun x => @join C M T x)
             (fun x y g => symmetry (join_fmap_fmap g))).
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_fmap_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
  - intros x; simpl.
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id. }
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    etransitivity; [ apply id_right | ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left. }
    apply join_fmap_join.
Defined.

Definition Monoid_Monad@{o h s f | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C} :
  @MonoidObject (Endofunctors C) (@Compose_Monoidal@{s f o h} C) M
    ↔ @Monad C M :=
  (@monoidobject_monad@{o h f s} C M, @monad_monoidobject@{o h f s} C M).
