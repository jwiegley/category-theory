Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   A monad on a category C is an endofunctor M : C ⟶ C equipped with two
   natural transformations: a unit ret (η : Id ⟹ M) and a multiplication
   join (μ : M ○ M ⟹ M), satisfying the associativity law join ∘ fmap join ≈
   join ∘ join (μ ∘ Mμ ≈ μ ∘ μM) and the two unit laws join ∘ fmap ret ≈ id
   (μ ∘ Mη ≈ id) and join ∘ ret ≈ id (μ ∘ ηM ≈ id). Equivalently, a monad is
   a monoid object in the endofunctor category [C, C] with composition as the
   tensor.

   This is the join/return presentation. Its bind-based reformulation is
   recorded below as [bind], with the usual Haskell notations m >>= f and
   f >> g. The naturality squares for η and μ are kept explicit as the laws
   [fmap_ret] and [join_fmap_fmap] (in many treatments these are folded into
   "η and μ are natural transformations"). *)

Section Monad.

Context `{M : C ⟶ C}.

Class Monad := {
  ret {x}  : x ~> M x;          (* unit η : Id    ⟹ M *)
  join {x} : M (M x) ~> M x;    (* mult μ : M ○ M ⟹ M *)

  (* naturality of the unit η: ret ∘ f ≈ fmap f ∘ ret *)
  fmap_ret {x y} (f : x ~> y) : ret ∘ f ≈ fmap f ∘ ret;

  (* associativity μ ∘ Mμ ≈ μ ∘ μM *)
  join_fmap_join {x} : join ∘ fmap (@join x) ≈ join ∘ join;
  (* left unit law μ ∘ Mη ≈ id *)
  join_fmap_ret  {x} : join ∘ fmap (@ret x) ≈ id;
  (* right unit law μ ∘ ηM ≈ id *)
  join_ret       {x} : join ∘ @ret (M x) ≈ id;

  (* naturality of the multiplication μ: join ∘ fmap (fmap f) ≈ fmap f ∘ join *)
  join_fmap_fmap {x y} (f : x ~> y) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Arguments Monad {C} M.

Notation "ret[ M ]" := (@ret _ M _ _)
  (at level 9, format "ret[ M ]") : category_scope.
Notation "join[ M ]" := (@join _ M _ _)
  (at level 9, format "join[ M ]") : category_scope.

Section MonadLib.

Context `{@Monad C M}.

Definition bind {x y : C} (f : x ~> M y) : M x ~> M y :=
  join ∘ fmap[M] f.

End MonadLib.

Notation "m >>= f" := (bind f m) (at level 42, right associativity) : morphism_scope.
Notation "f >> g" := (f >>= fun _ => g)%morphism
  (at level 81, right associativity) : morphism_scope.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(* nLab: https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   A comonad is the formal dual of a monad: a counit ε : M ⟹ Id and a
   comultiplication δ : M ⟹ M ○ M satisfying the dual coassociativity and
   counit laws. Since duality is C^op^op = C by reflexivity here, it is
   obtained for free as a monad on the opposite category. *)

Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).
