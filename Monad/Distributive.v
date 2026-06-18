Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** * Distributive law for composing monads *)

(* nLab: https://ncatlab.org/nlab/show/distributive+law
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_law_between_monads

   Monads do not compose in general: for a monad M and a functor N there is no
   canonical monad structure on M ◯ N. A distributive law supplies the missing
   coherence. In its full Beck (1969) form a distributive law of N over M is a
   natural transformation N ◯ M ⟹ M ◯ N satisfying four laws (compatibility
   with the two units and the two multiplications), under which the composite
   carries a monad structure.

   The structure recorded here is the weaker [mprod]/swap presentation of Jones
   and Duponcheel ("Composing Monads", Yale tech report YALEU/DCS/RR-1004,
   1993), which is exactly the half of a distributive law needed to make M ◯ N
   a monad and is consumed as such in [Monad.Compose]. Rather than a bare swap
   N ◯ M ⟹ M ◯ N, the data is a single operation

       mprod : N (M (N A)) ~> M (N A)

   that pushes the inner N past the outer M, collapsing one layer. M is a full
   monad while N need only be a strong lax monoidal functor (so it has a unit
   [pure] but not necessarily a multiplication). The composite M ◯ N then has
   unit ret[M] ∘ pure[N] (both units stacked) and multiplication
   join[M] ∘ fmap[M] mprod, and the four laws below are precisely what make
   those satisfy the monad axioms; see [Monad.Compose]. *)

Section MonadDistributive.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

Class Monad_Distributive := {
  (* The swap/product operation pushing the inner N past the outer M. *)
  mprod {A} : N (M (N A)) ~> M (N A);

  (* Naturality of mprod: it is a natural transformation N ◯ M ◯ N ⟹ M ◯ N. *)
  mprod_fmap_fmap {A B} (f : A ~> B) :
    @mprod B ∘ fmap[N] (fmap[M ◯ N] f) ≈ fmap[M ◯ N] f ∘ @mprod A;
  (* Left unit: mprod absorbs the inner unit pure[N]. *)
  mprod_pure {A} : @mprod A ∘ pure[N] ≈ id;
  (* Right unit: applied to the stacked unit ret[M] ∘ pure[N], mprod is ret[M]. *)
  mprod_fmap_pure {A} : @mprod A ∘ fmap[N] (ret[M] ∘ pure[N]) ≈ ret[M];
  (* Associativity: mprod commutes with the composite multiplication
     join[M] ∘ fmap[M] mprod, so the induced join on M ◯ N is associative. *)
  mprod_fmap_join_fmap_mprod {A} :
    @mprod A ∘ fmap[N] (join[M] ∘ fmap[M] (@mprod A))
      ≈ join[M] ∘ fmap[M] (@mprod A) ∘ @mprod (M (N A))
}.

End MonadDistributive.

Arguments Monad_Distributive {C _} M {_} N {_ _}.
