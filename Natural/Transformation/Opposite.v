Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * The opposite (dual) of a natural transformation. *)

(* nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   Oppositization is covariant on functors but reverses 2-cells: a natural
   transformation `N : F ⟹ G` between `F G : C ⟶ D` yields the opposite
   transformation `N^op : G^op ⟹ F^op` (note the swap of source and target).
   The component of `N^op` at `x` is `N x` itself, only reread through the
   duality: `N x : F x ~> G x` in `D` is the same morphism as `G^op x ~> F^op x`
   in `D^op`. Accordingly the naturality square of `N^op` is just the naturality
   square of `N` with its two orientations swapped, so the `naturality` field of
   `N^op` is `N`'s `naturality_sym` (and vice versa) with object indices
   transposed — no rewriting is needed, matching the built-in duality of
   [Transform]. This makes op the 2-functor `Cat^co ⟶ Cat`: a natural
   transformation `F^op ⟹ G^op` corresponds to one `G ⟹ F`, not `F ⟹ G`. *)

Definition Opposite_Transform `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  G^op ⟹ F^op :=
  @Build_Transform (C^op) (D^op) (G^op) (F^op) N
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality_sym C D F G N y x f)
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality C D F G N y x f).

Notation "N ^op" := (@Opposite_Transform _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : transform_scope.

Open Scope transform_scope.

(* The op functor is an involution on natural transformations: applying it twice
   recovers `N` definitionally, since (C^op)^op = C and (F^op)^op = F hold by
   reflexivity and `N^op` reuses `N`'s components. *)

Corollary Opposite_Transform_invol `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  (N^op)^op = N.
Proof. reflexivity. Qed.
