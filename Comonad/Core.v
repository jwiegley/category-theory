Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Comonads: the covariant API *)

(* nLab:      https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   A comonad on a category C is an endofunctor W : C ⟶ C equipped with a
   counit ε : W ⟹ Id (here [extract]) and a comultiplication δ : W ⟹ W ○ W
   (here [duplicate]), subject to the two counit laws ε ∘ δ ≈ id and
   W ε ∘ δ ≈ id, and to coassociativity δ ∘ δ ≈ W δ ∘ δ (writing W ε and W δ
   for the fmap image of a component, and reading each composite through the
   appropriate instance of W).

   Theory/Monad.v defines [Comonad := @Monad (C^op) (W^op)]: a comonad is
   exactly a monad on the opposite category.  Because duality is built into
   this library so that C^op^op = C holds by reflexivity, each comonad law IS
   the corresponding monad law with its composites read backwards — no
   separate record is needed, and none is introduced here.  This file
   provides the covariant reading of that definition: the accessors
   [extract], [duplicate] and [extend] are definitional op-reads of [ret],
   [join] and [bind], and every law below is the corresponding monad law
   transported by [exact] (at most up to symmetry of ≈, where the op-read
   arrives in the reversed orientation). *)

(* [Comonad C W] is a Definition that unfolds to the class
   [@Monad (C^op) (W^op)], but typeclass resolution keys on the head constant
   of a goal and does not look through this unfolding.  Declaring [Comonad]
   an existing class lets a comonad witness in scope be found when the
   accessors below insert their implicit [Comonad] argument, mirroring how
   [ret] and [join] resolve their implicit [Monad] argument.  Goals headed by
   [Monad] are untouched: the two heads are distinct, so neither search space
   leaks into the other.

   The declaration is kept here, in the comonad API module, rather than beside
   the [Comonad] definition in Theory/Monad.v: this file is the canonical
   entry point for the comonad API, so any code wanting class behaviour for
   [Comonad] holes and [Context] binders imports it, and imposing library-wide
   class resolution on the bare definition is avoided. *)
Existing Class Comonad.

Section ComonadAPI.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(** The counit ε : W ⟹ Id, componentwise: the op-read of [ret]. *)
Definition extract {x : C} : W x ~> x := @ret (C^op) (W^op) H x.

(** The comultiplication δ : W ⟹ W ○ W, componentwise: the op-read of
    [join]. *)
Definition duplicate {x : C} : W x ~> W (W x) := @join (C^op) (W^op) H x.

(** Co-Kleisli extension (cobind): the op-read of [bind], see
    [extend_op_bind] just below. *)
Definition extend {x y : C} (f : W x ~> y) : W x ~> W y :=
  fmap[W] f ∘ duplicate.

(** [extend] agrees definitionally with the [bind] of the opposite monad. *)
Lemma extend_op_bind {x y : C} (f : W x ~> y) :
  extend f ≈ @bind (C^op) (W^op) H y x f.
Proof. reflexivity. Qed.

(** Naturality of the counit — ε is a natural transformation W ⟹ Id.
    Op-read of [fmap_ret]. *)
Lemma extract_natural {x y : C} (f : x ~> y) :
  f ∘ extract ≈ extract ∘ fmap[W] f.
Proof. exact (@fmap_ret (C^op) (W^op) H y x f). Qed.

(** Naturality of the comultiplication — δ is a natural transformation
    W ⟹ W ○ W.  Op-read of [join_fmap_fmap]. *)
Lemma duplicate_natural {x y : C} (f : x ~> y) :
  fmap[W] (fmap[W] f) ∘ duplicate ≈ duplicate ∘ fmap[W] f.
Proof. exact (@join_fmap_fmap (C^op) (W^op) H y x f). Qed.

(** Counit law ε_W ∘ δ ≈ id: op-read of the right unit law [join_ret]. *)
Lemma extract_duplicate {x : C} : extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_ret (C^op) (W^op) H x). Qed.

(** Counit law W ε ∘ δ ≈ id: op-read of the left unit law [join_fmap_ret]. *)
Lemma fmap_extract_duplicate {x : C} : fmap[W] extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_fmap_ret (C^op) (W^op) H x). Qed.

(** Coassociativity δ_W ∘ δ ≈ W δ ∘ δ: op-read of the associativity law
    [join_fmap_join], which arrives in the symmetric orientation. *)
Lemma duplicate_duplicate {x : C} :
  duplicate ∘ @duplicate x ≈ fmap[W] duplicate ∘ @duplicate x.
Proof.
  symmetry.
  exact (@join_fmap_join (C^op) (W^op) H x).
Qed.

(** The co-Kleisli triple laws for [extend].  Together with [extract] these
    present the comonad in extension form, dually to the ret/bind
    presentation of a monad; Comonad/CoKleisli.v uses them to relate
    co-Kleisli composition to [extend]. *)

Corollary extract_extend {x y : C} (f : W x ~> y) : extract ∘ extend f ≈ f.
Proof.
  unfold extend.
  rewrite comp_assoc.
  rewrite <- extract_natural.
  rewrite <- comp_assoc.
  rewrite extract_duplicate.
  cat.
Qed.

Corollary extend_extract {x : C} : extend extract ≈ id[W x].
Proof. exact fmap_extract_duplicate. Qed.

Corollary extend_comp {x y z : C} (f : W y ~> z) (g : W x ~> y) :
  extend f ∘ extend g ≈ extend (f ∘ extend g).
Proof.
  unfold extend.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- duplicate_duplicate.
  rewrite (comp_assoc (fmap[W] (fmap[W] g))).
  rewrite duplicate_natural.
  now rewrite !comp_assoc.
Qed.

(** [duplicate] is the extension of the identity, and [fmap] factors through
    [extend]: the Kleisli-style and functorial presentations agree. *)

Corollary extend_id_duplicate {x : C} : extend (id[W x]) ≈ duplicate.
Proof. unfold extend; cat. Qed.

Corollary fmap_extend_extract {x y : C} (f : x ~> y) :
  extend (f ∘ extract) ≈ fmap[W] f.
Proof.
  unfold extend.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite fmap_extract_duplicate.
  cat.
Qed.

End ComonadAPI.

(** [extend] respects ≈ in its morphism argument, so it can be rewritten
    under.  (Declared outside the section so the instance is exported with
    fully general arguments.) *)
#[export] Instance extend_respects
  {C : Category} {W : C ⟶ C} {H : @Comonad C W} {x y} :
  Proper (equiv ==> equiv) (@extend C W H x y).
Proof.
  proper.
  unfold extend.
  now rewrites.
Qed.

Notation "extract[ W ]" := (@extract _ W _ _)
  (at level 9, format "extract[ W ]") : category_scope.
Notation "duplicate[ W ]" := (@duplicate _ W _ _)
  (at level 9, format "duplicate[ W ]") : category_scope.
Notation "extend[ W ]" := (@extend _ W _ _ _)
  (at level 9, format "extend[ W ]") : category_scope.
