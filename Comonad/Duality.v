Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.CoKleisli.
Require Import Category.Comonad.Coalgebra.

Generalizable All Variables.

(** * Duality for comonads: the transfer package and both resolutions *)

(* nLab:      https://ncatlab.org/nlab/show/comonad
   nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   Theory/Monad.v defines [Comonad := @Monad (C^op) (W^op)], and duality is
   built into this library so that C^op^op = C and (W^op)^op = W hold by
   reflexivity.  This file packages the consequences of that choice for the
   theory of resolutions:

   - the conversions between comonads on C and monads on C^op — and,
     mirrored, between monads on C and comonads on C^op — are the identity,
     with round trips holding by [reflexivity]
     ([op_Monad_of_Comonad], [Comonad_of_op_Monad], [op_Comonad_of_Monad],
     [Monad_of_op_Comonad]);

   - every adjunction F ⊣ U (F : D ⟶ C the left adjoint) induces a comonad
     on C with endofunctor F ◯ U ([Adjunction_Comonad]), the formal dual of
     [Adjunction_Monad] in Monad/Adjunction.v: dualize the adjunction with
     Adjunction/Opposite.v to U^op ⊣ F^op and take the monad it induces on
     C^op.  That monad lives on the composite F^op ◯ U^op, while the goal
     [@Comonad C (F ◯ U)] unfolds to a monad on (F ◯ U)^op.  The two
     composites share their object and morphism maps definitionally, but
     Compose rebuilds its functor-law fields per application, so the two
     functor records are distinct terms; the comonad is therefore assembled
     by [Build_Monad] with every field taken unchanged from the dual monad
     (the field types are convertible across the two composites — no law is
     re-proved);

   - the two canonical resolutions of a comonad arise from the monad
     resolutions of Monad/Kleisli/Adjunction.v and
     Monad/Eilenberg/Moore/Adjunction.v by dualizing: for the co-Kleisli
     category the forgetful functor x ↦ W x is LEFT adjoint to the cofree
     one ([CoKleisli_Adjunction]), and likewise for the co-Eilenberg–Moore
     category of coalgebras ([CoEM_Adjunction]) — under op the free/
     forgetful pair of the monad world trades sides, which is why a comonad
     is resolved as forgetful ⊣ cofree.  Each adjunction is literally the
     [Opposite_Adjunction] of its monad counterpart; the covariant reading
     lemmas beside them record what the functors, units and counits are in
     terms of [extract], [duplicate] and [extend] of Comonad/Core.v, each
     holding by [reflexivity] or by a single identity law.  The composite
     Forget ◯ Cofree recovers W on the nose for both resolutions
     ([CoKleisli_Comonad_agrees], [CoEM_Comonad_agrees]), dually to
     [Kleisli_Monad_agrees] and [EM_Monad_agrees]. *)

(* The two resolutions as extremes

   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
   nLab: https://ncatlab.org/nlab/show/comonadic+functor

   Among the adjunctions inducing a given comonad, the two resolutions
   of this file occupy the extreme positions.  On the monad side the
   Kleisli adjunction is initial and the Eilenberg–Moore adjunction
   terminal in the category of adjunctions inducing T; and because
   (−)^op is covariant on functors, dualization preserves that
   orientation, so the co-Kleisli resolution is likewise initial and the
   co-Eilenberg–Moore resolution terminal.  Every inducing adjunction
   therefore receives a canonical comparison functor from the former and
   sends one into the latter, and the comparison into coalgebras being
   an equivalence is what it means for the inducing adjunction's left
   adjoint to be comonadic.

   The transfer package below is what makes this duality a theorem
   scheme rather than a pair of parallel constructions.  Since
   [Comonad C W] IS [@Monad (C^op) (W^op)] and the op involution is
   definitional, every monad theorem in the library is already a comonad
   theorem: instantiate it at (C^op, W^op) and read the composites
   backwards.  The files of the Comonad/ directory are exactly such
   readings, and no comonad law is ever proved twice.

   A single adjunction exhibits the whole family of standard examples.
   On a cartesian closed category the currying adjunction e × − ⊣ e ⇒ −
   induces, in one order, the state monad e ⇒ (e × −) and, in the other,
   the store comonad (e ⇒ −) × e; its left adjoint e × − is itself the
   environment comonad, and its right adjoint e ⇒ − the reader monad.
   Env, Reader, State and Store are in this sense one adjunction viewed
   four ways (Instance/Coq/Comonad/Env.v, Instance/Coq/Comonad/Store.v). *)

(** ** The transfer package

    [Comonad C W] IS [@Monad (C^op) (W^op)] by definition, so all four
    conversions below are the identity function and both round trips hold
    by [reflexivity].  They are provided as named coercion points: writing
    [op_Monad_of_Comonad H] in a proof records the direction in which a
    witness is being read, which the bare [H] does not. *)

Section MonadComonadDuality.

Context {C : Category}.
Context {W : C ⟶ C}.

Definition op_Monad_of_Comonad (H : @Comonad C W) : @Monad (C^op) (W^op) := H.

Definition Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) : @Comonad C W := H.

Lemma Comonad_of_op_Monad_of_Comonad (H : @Comonad C W) :
  Comonad_of_op_Monad (op_Monad_of_Comonad H) = H.
Proof. reflexivity. Qed.

Lemma op_Monad_of_Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) :
  op_Monad_of_Comonad (Comonad_of_op_Monad H) = H.
Proof. reflexivity. Qed.

(** Mirrored: a monad on C is the same thing as a comonad on C^op.  Both
    typecheck because (C^op)^op = C and (W^op)^op = W hold by
    reflexivity. *)

Definition op_Comonad_of_Monad (H : @Monad C W) : @Comonad (C^op) (W^op) := H.

Definition Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) : @Monad C W := H.

Lemma Monad_of_op_Comonad_of_Monad (H : @Monad C W) :
  Monad_of_op_Comonad (op_Comonad_of_Monad H) = H.
Proof. reflexivity. Qed.

Lemma op_Comonad_of_Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) :
  op_Comonad_of_Monad (Monad_of_op_Comonad H) = H.
Proof. reflexivity. Qed.

End MonadComonadDuality.

(** ** The comonad induced by an adjunction

    Every adjunction F ⊣ U induces the monad U ◯ F on the domain of F
    (Monad/Adjunction.v) and, dually, the comonad F ◯ U on its codomain:
    the counit ε is the counit of the adjunction, and the comultiplication
    is F η U.  (These covariant readings hold inside the sealed proof of the
    Qed-opaque [Adjunction_Monad], so — unlike the reflexivity-backed
    agreement lemmas elsewhere in this file — they are not exposed here as
    lemmas about [extract]/[duplicate] of the induced comonad.)  Rather than
    re-deriving the laws from the zig-zag
    identities, dualize: Adjunction/Opposite.v turns A : F ⊣ U into
    A^op : U^op ⊣ F^op, whose [Adjunction_Monad] is a monad on C^op with
    endofunctor F^op ◯ U^op.  The target class [@Comonad C (F ◯ U)]
    unfolds to [@Monad (C^op) ((F ◯ U)^op)]; the two composites agree on
    objects and morphisms definitionally (only their Qed-sealed functor-law
    fields are distinct terms), so every monad field transports unchanged
    and [Build_Monad] just repackages the dual monad. *)

Section AdjunctionComonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Definition Adjunction_Comonad (A : F ⊣ U) : @Comonad C (F ◯ U) :=
  let M : @Monad (C^op) (F^op ◯ U^op) :=
    Adjunction_Monad (Opposite_Adjunction F U A) in
  @Build_Monad (C^op) ((F ◯ U)^op)
    (fun x => @ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @fmap_ret (C^op) (F^op ◯ U^op) M x y f)
    (fun x => @join_fmap_join (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_fmap_ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_ret (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @join_fmap_fmap (C^op) (F^op ◯ U^op) M x y f).

End AdjunctionComonad.

(** ** The co-Kleisli resolution: forgetful ⊣ cofree

    Dualizing the Kleisli resolution of the opposite monad
    (Monad/Kleisli/Adjunction.v) yields the initial resolution of the
    comonad W through its co-Kleisli category (Comonad/CoKleisli.v):

    - [CoKleisli_Forget] : CoKleisli ⟶ C sends x to W x and a co-Kleisli
      morphism f : W x ~> y to its extension [extend f] — under the
      comparison with coalgebras it forgets a cofree coalgebra to its
      carrier, whence the name;
    - [CoKleisli_Cofree] : C ⟶ CoKleisli is the identity on objects and
      sends f : x ~> y to the co-Kleisli morphism f ∘ extract;
    - [CoKleisli_Adjunction] : CoKleisli_Forget ⊣ CoKleisli_Cofree — for a
      comonad the forgetful side is the LEFT adjoint, since op trades the
      sides of the free ⊣ forgetful resolution of the monad W^op.

    Because both hom-sets of the transposition are literally the same
    setoid W x ~> y, the adjunction isomorphism is the identity map, and
    the readings of the functors, unit and counit below are definitional
    except where a single identity law intervenes. *)

Section CoKleisliAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoKleisli_Forget : @CoKleisli C W H ⟶ C :=
  Opposite_Functor (@Kleisli_Forget (C^op) (W^op) H).

Definition CoKleisli_Cofree : C ⟶ @CoKleisli C W H :=
  Opposite_Functor (@Kleisli_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. *)

Lemma CoKleisli_Forget_obj (x : C) : CoKleisli_Forget x = W x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Forget_fmap {x y : C} (f : W x ~{C}~> y) :
  fmap[CoKleisli_Forget] f ≈ extend f.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_obj (x : C) : CoKleisli_Cofree x = x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[CoKleisli_Cofree] f ≈ f ∘ extract.
Proof. reflexivity. Qed.

Definition CoKleisli_Adjunction : CoKleisli_Forget ⊣ CoKleisli_Cofree :=
  Opposite_Adjunction _ _ (@Kleisli_Adjunction (C^op) (W^op) H).

(** The counit of the adjunction is the counit of the comonad. *)

Lemma CoKleisli_counit_agrees {x : C} :
  @counit _ _ _ _ CoKleisli_Adjunction x ≈ @extract C W H x.
Proof. reflexivity. Qed.

(** The unit at x is the identity arrow on W x, read as the co-Kleisli
    morphism x ~{CoKleisli}~> CoKleisli_Cofree (W x). *)

Lemma CoKleisli_unit_agrees {x : C} :
  @unit _ _ _ _ CoKleisli_Adjunction x ≈ id[W x].
Proof. reflexivity. Qed.

(** The comultiplication of the comonad induced by this adjunction (dually
    to Monad/Adjunction.v it is the CoKleisli_Forget-image of the unit) is
    duplicate. *)

Lemma CoKleisli_duplicate_agrees {x : C} :
  fmap[CoKleisli_Forget] (@unit _ _ _ _ CoKleisli_Adjunction x)
    ≈ @duplicate C W H x.
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers W: the composite Forget ◯ Cofree is naturally
    isomorphic to W, with identity components. *)

Theorem CoKleisli_Comonad_agrees : CoKleisli_Forget ◯ CoKleisli_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  exact (@fmap_extend_extract C W H x y f).
Qed.

End CoKleisliAdjunction.

(** ** The co-Eilenberg–Moore resolution: forgetful ⊣ cofree

    Dualizing the Eilenberg–Moore resolution of the opposite monad
    (Monad/Eilenberg/Moore/Adjunction.v) yields the terminal resolution of
    W through its category of coalgebras (Comonad/Coalgebra.v):

    - [CoEM_Forget] : CoEilenbergMoore ⟶ C projects a coalgebra to its
      carrier and a coalgebra homomorphism to its underlying arrow;
    - [CoEM_Cofree] : C ⟶ CoEilenbergMoore sends x to the cofree coalgebra
      (W x, δ_x) — its costructure map is duplicate — and f : x ~> y to
      the homomorphism carried by fmap[W] f;
    - [CoEM_Adjunction] : CoEM_Forget ⊣ CoEM_Cofree, with the forgetful
      side again the left adjoint. *)

Section CoEilenbergMooreAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoEM_Forget : @CoEilenbergMoore C W H ⟶ C :=
  Opposite_Functor (@EM_Forget (C^op) (W^op) H).

Definition CoEM_Cofree : C ⟶ @CoEilenbergMoore C W H :=
  Opposite_Functor (@EM_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. *)

Lemma CoEM_Forget_obj (x : @CoEilenbergMoore C W H) : CoEM_Forget x = `1 x.
Proof. reflexivity. Qed.

Lemma CoEM_Forget_fmap {x y : @CoEilenbergMoore C W H}
      (f : x ~{@CoEilenbergMoore C W H}~> y) :
  fmap[CoEM_Forget] f ≈ t_alg_hom[f].
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_carrier (x : C) : `1 (CoEM_Cofree x) = W x.
Proof. reflexivity. Qed.

(** The costructure map of the cofree coalgebra on x is duplicate. *)

Lemma CoEM_Cofree_coalg (x : C) :
  t_alg[`2 (CoEM_Cofree x)] ≈ @duplicate C W H x.
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  t_alg_hom[fmap[CoEM_Cofree] f] ≈ fmap[W] f.
Proof. reflexivity. Qed.

Definition CoEM_Adjunction : CoEM_Forget ⊣ CoEM_Cofree :=
  Opposite_Adjunction _ _ (@EM_Adjunction (C^op) (W^op) H).

(** The counit of the adjunction is the counit of the comonad. *)

Lemma CoEM_counit_agrees {x : C} :
  @counit _ _ _ _ CoEM_Adjunction x ≈ @extract C W H x.
Proof.
  unfold counit; cbn.
  cat.
Qed.

(** The unit at a coalgebra acts by its costructure map, stated on the
    underlying arrow of the coalgebra homomorphism. *)

Lemma CoEM_unit_agrees {y : @CoEilenbergMoore C W H} :
  t_alg_hom[@unit _ _ _ _ CoEM_Adjunction y] ≈ t_alg[`2 y].
Proof.
  unfold unit; cbn.
  rewrite fmap_id.
  cat.
Qed.

(** The comultiplication of the comonad induced by this adjunction is
    duplicate. *)

Lemma CoEM_duplicate_agrees {x : C} :
  fmap[CoEM_Forget] (@unit _ _ _ _ CoEM_Adjunction (CoEM_Cofree x))
    ≈ @duplicate C W H x.
Proof.
  cbn.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers W: the composite Forget ◯ Cofree is naturally
    isomorphic to W, with identity components. *)

Theorem CoEM_Comonad_agrees : CoEM_Forget ◯ CoEM_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End CoEilenbergMooreAdjunction.
