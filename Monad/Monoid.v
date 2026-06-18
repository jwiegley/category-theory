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

Section MonoidMonad.

Context {C : Category}.
Context {M : C ⟶ C}.

Definition Endofunctors `(C : Category) := ([C, C]).

Theorem Monoid_Monad :
  @MonoidObject (Endofunctors C) Compose_Monoidal M ↔ Monad M.
Proof.
  split; intros m.
  - refine {| join := transform[mappend[m]]
            ; ret  := transform[mempty[m]] |}; intros.
    + symmetry.
      apply (@naturality _ _ _ _ (@mempty _ _ _ m)).
    + pose proof (@mappend_assoc _ _ _ m x) as X; simpl in X.
      autorewrite with categories in X.
      symmetry; assumption.
    + pose proof (@mempty_right _ _ _ m x) as X; simpl in X.
      autorewrite with categories in X.
      assumption.
    + pose proof (@mempty_left _ _ _ m x) as X; simpl in X.
      autorewrite with categories in X.
      assumption.
    + symmetry.
      apply (@naturality _ _ _ _ (@mappend _ _ _ m)).
  - unshelve (refine {| mempty  := _
                      ; mappend := _ |}).
    + transform; intros.
      * exact ret.
      * simpl.
        symmetry.
        apply fmap_ret.
      * simpl.
        apply fmap_ret.
    + transform; intros.
      * exact join.
      * simpl.
        symmetry.
        apply join_fmap_fmap.
      * simpl.
        apply join_fmap_fmap.
    + simpl; intros; cat.
      apply join_ret.
    + simpl; intros; cat.
      apply join_fmap_ret.
    + simpl; intros; cat.
      symmetry.
      apply join_fmap_join.
Defined.

End MonoidMonad.
