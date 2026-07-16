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

(* Where monads come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/monad
   nLab:  https://ncatlab.org/nlab/show/monad+(in+computer+science)
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Moggi, "Notions of computation and monads", Information and
          Computation 93(1), 1991

   The concept predates its name by a decade.  Godement introduced it in
   the appendix of "Topologie algébrique et théorie des faisceaux"
   (Hermann, 1958) as the device behind the canonical flabby resolution
   of a sheaf; the abstract notion, known in that era as the "standard
   construction", was studied by Huber ("Homotopy theory in general
   categories", Mathematische Annalen 144, 1961), who is credited with
   the observation that every adjunction F ⊣ U endows the composite
   U ◯ F with monad structure — realized in this library as
   [Adjunction_Monad] in Monad/Adjunction.v.  Whether every monad so
   arises was answered affirmatively twice in the same year: Kleisli
   ("Every standard construction is induced by a pair of adjoint
   functors", Proceedings of the AMS 16(3), 1965) rebuilt the adjunction
   from the free algebras, and Eilenberg and Moore (op. cit.) from all
   algebras, coining "triple" along the way.  Both resolutions are
   present here — Monad/Kleisli.v with Monad/Kleisli/Adjunction.v, and
   [TAlgebra] of Monad/Algebra.v with Monad/Eilenberg/Moore/Adjunction.v
   — and among the adjunctions inducing a given monad the first is
   initial, the second terminal.  Beck's monadicity theorem then
   characterizes which functors are, up to equivalence, forgetful
   functors from algebras (Monad/Monadicity/Beck.v).  The name "monad"
   itself is Bénabou's ("Introduction to bicategories", Springer LNM 47,
   1967), and the monoid-object remark of the header above — Mac Lane's
   slogan that a monad is just a monoid in the category of endofunctors
   ("Categories for the Working Mathematician", 1971) — is proved as a
   genuine equivalence by [Monoid_Monad] in Monad/Monoid.v.

   Two further readings organize the mathematics.  As an algebraic
   theory in packaged form, a monad carries its variety of algebras
   with it: Linton ("Some aspects of equational categories", La Jolla
   1965 conference proceedings, Springer 1966) proved finitary monads
   on Set equivalent to Lawvere theories, the thread taken up in
   Theory/Lawvere/Monad.v, while non-finitary monads reach further —
   the algebras of the ultrafilter monad are exactly the compact
   Hausdorff spaces (Manes, "A triple theoretic construction of compact
   algebras", Springer LNM 80, 1969).  As a generalized closure
   operator — on a poset category a monad is precisely one, the unit
   giving extensivity and [join] idempotency — the concept categorifies
   to the idempotent monads of reflective subcategories in
   Construction/Reflective/Idempotent.v.

   Computationally, a value of type M x is a computation that may
   perform effects while producing an x.  Moggi (LICS 1989; op. cit.
   1991) interpreted the effects of programming languages — state,
   exceptions, nondeterminism, continuations — as strong monads on a
   cartesian closed category, the strength hypothesis being the reason
   Monad/Strong.v exists; Wadler ("The essence of functional
   programming", POPL 1992) carried the discipline into Haskell, where
   effects coexist with purity.  Under this reading [ret] embeds a pure
   value, [bind] sequences two effectful steps, and programs x ~> M y
   compose as morphisms of the Kleisli category.  The bind presentation
   is equivalent to the join/return one used in this file (Manes,
   "Algebraic Theories", Springer 1976; Moggi 1991, Def. 1.2), and is
   the surface syntax elaborated Haskell-style in
   Instance/Coq/Monad.v. *)

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
