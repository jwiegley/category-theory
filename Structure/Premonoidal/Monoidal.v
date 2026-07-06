Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(** * Monoidal categories versus premonoidal categories

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    Wikipedia: https://en.wikipedia.org/wiki/Premonoidal_category

    Power–Robinson ("Premonoidal categories and notions of computation",
    Math. Structures Comput. Sci. 7(5), 1997) observe that a monoidal
    category is precisely a premonoidal category in which every morphism
    is central.  This file delivers both directions of that comparison.

    Direction 1 ([Monoidal_Premonoidal]).  A monoidal structure on [C]
    restricts to a binoidal one, [Monoidal_Binoidal]: the two one-sided
    tensoring functors are the partial applications [- ⨂ w] and [w ⨂ -]
    of the tensor bifunctor, packaged as [AFunctor]s so that the object
    maps stay definitionally the monoidal tensor.  The middle-four
    interchange laws of a bifunctor ([bimap_id_right_left] /
    [bimap_id_left_right]) say exactly that the two orders of tensoring
    a pair of morphisms agree, so EVERY morphism is central
    ([Monoidal_all_central]).  The monoidal unitors and associator then
    populate a premonoidal structure field-for-field: the one-variable
    naturality squares are instances of the joint ones with identities
    in the untouched positions, and triangle/pentagon carry over
    verbatim.

    Direction 2 ([Premonoidal_Monoidal], the all-central engine).  In a
    premonoidal category together with a witness that every morphism is
    central, the interleaved tensor [composite_ff'] becomes a genuine
    bifunctor [Premonoidal_Tensor] on [C ∏ C]: interchange in the middle
    of [fmap_comp] is discharged by [composite_ff'_comp_l], the single
    point where the centrality witness is consumed.  All remaining
    [Build_Monoidal] fields are the [composite_ff']-phrased corollaries
    already derived in Structure/Premonoidal.v — in particular the joint
    associator naturality [premon_joint_assoc_natural], which needs no
    centrality at all.

    Downstream, Direction 2 is the funnel that makes the Kleisli
    category of a commutative strong monad monoidal
    (Monad/Kleisli/Commutative.v), and Direction 1 supplies the
    premonoidal reading of a monoidal base category used by Freyd
    categories (Structure/Premonoidal/Freyd.v). *)

(** ** Direction 1: a monoidal category is premonoidal *)

Section MonoidalPremonoidal.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** *** The one-sided tensoring functors

    [Monoidal_Tensor_Left w] is [- ⨂ w] and [Monoidal_Tensor_Right w]
    is [w ⨂ -], each an [AFunctor] over the stated object map so that
    the binoidal tensor below is definitionally the monoidal one.  The
    functor laws are the one-variable specializations of bifunctor
    functoriality ([bimap_id_id], [bimap_comp_id_right] /
    [bimap_comp_id_left]). *)

Lemma Monoidal_Tensor_Left_respects (w x y : C) :
  Proper (equiv ==> equiv) (fun f : x ~> y => f ⨂ id[w]).
Proof.
  intros f g E.
  apply bimap_respects; [assumption|reflexivity].
Qed.

Lemma Monoidal_Tensor_Left_id (w x : C) :
  id[x] ⨂ id[w] ≈ id[(x ⨂ w)%object].
Proof. apply bimap_id_id. Qed.

Lemma Monoidal_Tensor_Left_comp (w : C) {x y z : C}
      (f : y ~> z) (g : x ~> y) :
  (f ∘ g) ⨂ id[w] ≈ (f ⨂ id[w]) ∘ (g ⨂ id[w]).
Proof. apply bimap_comp_id_right. Qed.

Definition Monoidal_Tensor_Left (w : C) :
  @AFunctor C C (fun x : C => (x ⨂ w)%object) :=
  @Build_AFunctor C C (fun x : C => (x ⨂ w)%object)
    (fun x y (f : x ~> y) => f ⨂ id[w])
    (fun x y => Monoidal_Tensor_Left_respects w x y)
    (fun x => Monoidal_Tensor_Left_id w x)
    (fun x y z f g => Monoidal_Tensor_Left_comp w f g).

Lemma Monoidal_Tensor_Right_respects (w y z : C) :
  Proper (equiv ==> equiv) (fun f : y ~> z => id[w] ⨂ f).
Proof.
  intros f g E.
  apply bimap_respects; [reflexivity|assumption].
Qed.

Lemma Monoidal_Tensor_Right_id (w y : C) :
  id[w] ⨂ id[y] ≈ id[(w ⨂ y)%object].
Proof. apply bimap_id_id. Qed.

Lemma Monoidal_Tensor_Right_comp (w : C) {x y z : C}
      (f : y ~> z) (g : x ~> y) :
  id[w] ⨂ (f ∘ g) ≈ (id[w] ⨂ f) ∘ (id[w] ⨂ g).
Proof. apply bimap_comp_id_left. Qed.

Definition Monoidal_Tensor_Right (w : C) :
  @AFunctor C C (fun y : C => (w ⨂ y)%object) :=
  @Build_AFunctor C C (fun y : C => (w ⨂ y)%object)
    (fun y z (f : y ~> z) => id[w] ⨂ f)
    (fun y z => Monoidal_Tensor_Right_respects w y z)
    (fun y => Monoidal_Tensor_Right_id w y)
    (fun x y z f g => Monoidal_Tensor_Right_comp w f g).

Definition Monoidal_Binoidal : @Binoidal C :=
  @Build_Binoidal C
    (fun x y : C => (x ⨂ y)%object)
    Monoidal_Tensor_Left
    Monoidal_Tensor_Right.

(** *** Every morphism of a monoidal category is central

    Under [Monoidal_Binoidal] the tensorings of [f] and [f'] in the two
    orders are [bimap f id ∘ bimap id f'] and [bimap id f' ∘ bimap f id];
    both reduce to [bimap f f'] by the middle-four interchange, so the
    two defining squares of [central] are a single lemma applied twice
    with the roles of [f] and [f'] exchanged. *)

Lemma Monoidal_central_square {x y x' y' : C} (f : x ~> y) (f' : x' ~> y') :
  (f ⨂ id[y']) ∘ (id[x] ⨂ f') ≈ (id[y] ⨂ f') ∘ (f ⨂ id[x']).
Proof.
  rewrite bimap_id_right_left.
  rewrite bimap_id_left_right.
  reflexivity.
Qed.

Lemma Monoidal_all_central {x y : C} (f : x ~> y) :
  @central C Monoidal_Binoidal x y f.
Proof.
  intros x' y' f'; split.
  - exact (Monoidal_central_square f f').
  - exact (Monoidal_central_square f' f).
Qed.

(* The interleaved binoidal tensor over [Monoidal_Binoidal] agrees with
   the monoidal [bimap]; recorded here because downstream instances
   (e.g. Structure/Premonoidal/Freyd.v's identity example) rewrite
   between the two spellings. *)
Lemma Monoidal_composite_ff' {x x' y y' : C} (f : x ~> y) (f' : x' ~> y') :
  @composite_ff' C Monoidal_Binoidal x x' y y' f f' ≈ f ⨂ f'.
Proof. exact (bimap_id_left_right f' f). Qed.

(** *** One-variable associator naturality

    Each of the three premonoidal associator squares is the joint square
    [to_tensor_assoc_natural] with identities in the two untouched
    positions.  For the left and right squares one [bimap id id ≈ id]
    cleanup aligns the identity-padded corner with the plain identity of
    the compound object; the middle square is on the nose. *)

Lemma Monoidal_assoc_natural_left {x y z w : C} (g : x ~> y) :
  (g ⨂ id[(z ⨂ w)%object]) ∘ to (@tensor_assoc C M x z w)
    ≈ to (@tensor_assoc C M y z w) ∘ ((g ⨂ id[z]) ⨂ id[w]).
Proof.
  transitivity ((g ⨂ (id[z] ⨂ id[w])) ∘ to (@tensor_assoc C M x z w)).
  - apply compose_respects; [|reflexivity].
    apply bimap_respects; [reflexivity|].
    symmetry; apply bimap_id_id.
  - apply to_tensor_assoc_natural.
Qed.

Lemma Monoidal_assoc_natural_right {x y z w : C} (i : z ~> w) :
  (id[x] ⨂ (id[y] ⨂ i)) ∘ to (@tensor_assoc C M x y z)
    ≈ to (@tensor_assoc C M x y w) ∘ (id[(x ⨂ y)%object] ⨂ i).
Proof.
  transitivity (to (@tensor_assoc C M x y w) ∘ ((id[x] ⨂ id[y]) ⨂ i)).
  - apply to_tensor_assoc_natural.
  - apply compose_respects; [reflexivity|].
    apply bimap_respects; [|reflexivity].
    apply bimap_id_id.
Qed.

(** *** The premonoidal structure of a monoidal category

    Every field is the corresponding monoidal datum: the unit, unitors
    and associator are shared, centrality of the structural maps is the
    all-central lemma, the unitor naturality squares and the coherence
    laws coincide definitionally (the binoidal ⋉ / ⋊ over
    [Monoidal_Binoidal] reduce to [bimap] with an identity), and the
    associator squares are the one-variable lemmas above. *)

Definition Monoidal_Premonoidal : @Premonoidal C Monoidal_Binoidal :=
  @Build_Premonoidal C Monoidal_Binoidal
    (@I C M)
    (fun x => @unit_left C M x)
    (fun x => @unit_right C M x)
    (fun x y z => @tensor_assoc C M x y z)
    (fun x => Monoidal_all_central (to (@unit_left C M x)))
    (fun x => Monoidal_all_central (to (@unit_right C M x)))
    (fun x y z => Monoidal_all_central (to (@tensor_assoc C M x y z)))
    (fun x y g => to_unit_left_natural g)
    (fun x y g => to_unit_right_natural g)
    (fun x y z w g => Monoidal_assoc_natural_left g)
    (fun x z w y h => to_tensor_assoc_natural (id[x]) h (id[y]))
    (fun x y z w i => Monoidal_assoc_natural_right i)
    (fun x y => triangle_identity)
    (fun x y z w => pentagon_identity).

End MonoidalPremonoidal.

(** ** Direction 2: an all-central premonoidal category is monoidal

    The converse engine.  [all_central] is taken as an explicit
    hypothesis rather than a class field so that consumers can
    instantiate it with a computed witness — Monad/Kleisli/Commutative.v
    applies it with the centrality of all Kleisli morphisms of a
    commutative strong monad, and Structure/Premonoidal/Centre.v uses
    the same recipe with `1-projections for the centre. *)

Section AllCentralMonoidal.

Context {C : Category}.
Context `{B : @Binoidal C}.
Context `{P : @Premonoidal C B}.

Variable all_central : ∀ (x y : C) (f : x ~> y), central f.

(** *** The tensor bifunctor

    On objects the tensor is the binoidal one; on morphisms it is the
    interleaved composite [composite_ff'].  Identity preservation is
    [composite_id_left] plus functoriality of the one-sided tensoring;
    composition preservation is the one-sided interchange
    [composite_ff'_comp_l], whose centrality hypothesis is the sole use
    of [all_central]. *)

Lemma Premonoidal_Tensor_respects (x y : C ∏ C) :
  Proper (equiv ==> equiv)
         (fun fg : x ~{C ∏ C}~> y => composite_ff' (fst fg) (snd fg)).
Proof.
  intros f g E.
  destruct E as [E1 E2].
  now rewrite E1, E2.
Qed.

Lemma Premonoidal_Tensor_id (x : C ∏ C) :
  composite_ff' (id[fst x]) (id[snd x]) ≈ id[(fst x ⊗ snd x)%object].
Proof.
  rewrite composite_id_left.
  exact (@fmap_id C C (@inj_right C B (fst x)) (snd x)).
Qed.

Lemma Premonoidal_Tensor_comp {x y z : C ∏ C}
      (f : y ~{C ∏ C}~> z) (g : x ~{C ∏ C}~> y) :
  composite_ff' (fst f ∘ fst g) (snd f ∘ snd g)
    ≈ composite_ff' (fst f) (snd f) ∘ composite_ff' (fst g) (snd g).
Proof using all_central.
  apply composite_ff'_comp_l.
  apply all_central.
Qed.

Definition Premonoidal_Tensor : (C ∏ C) ⟶ C :=
  @Build_Functor (C ∏ C) C
    (fun p => (fst p ⊗ snd p)%object)
    (fun x y (fg : x ~{C ∏ C}~> y) => composite_ff' (fst fg) (snd fg))
    Premonoidal_Tensor_respects
    Premonoidal_Tensor_id
    (fun x y z f g => Premonoidal_Tensor_comp f g).

(** *** The monoidal structure

    With [bimap] over [Premonoidal_Tensor] definitionally equal to
    [composite_ff'], every [Build_Monoidal] field is one of the
    [composite_ff']-phrased corollaries of Structure/Premonoidal.v: the
    identity-padded unitor squares and their from-forms, the joint
    associator squares (derived there from the three one-variable ones
    with no centrality hypothesis), and the padded triangle and
    pentagon. *)

Definition Premonoidal_Monoidal : @Monoidal C :=
  @Build_Monoidal C
    (@premon_I C B P)
    Premonoidal_Tensor
    (fun x => @premon_unit_left C B P x)
    (fun x => @premon_unit_right C B P x)
    (fun x y z => @premon_assoc C B P x y z)
    (fun x y g => premon_unit_left_natural_ff' g)
    (fun x y g => premon_unit_left_natural_from_ff' g)
    (fun x y g => premon_unit_right_natural_ff' g)
    (fun x y g => premon_unit_right_natural_from_ff' g)
    (fun x y z w v u g h i => premon_joint_assoc_natural g h i)
    (fun x y z w v u g h i => premon_joint_assoc_natural_from g h i)
    (fun x y => premon_triangle_ff')
    (fun x y z w => premon_pentagon_ff').

(* The induced monoidal tensor acts on morphism pairs exactly by
   [composite_ff']; the agreement is definitional and recorded for
   downstream rewriting. *)
Corollary Premonoidal_Monoidal_bimap {x x' y y' : C}
          (f : x ~> y) (f' : x' ~> y') :
  f ⨂[Premonoidal_Monoidal] f' ≈ composite_ff' f f'.
Proof. reflexivity. Qed.

End AllCentralMonoidal.
