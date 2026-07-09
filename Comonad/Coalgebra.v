Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * Coalgebras over a comonad; the co-Eilenberg–Moore category *)

(* nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   For a comonad (W, extract, duplicate) = (W, ε, δ) on a category C — see
   Comonad/Core.v for the covariant API — a W-coalgebra on an object a is a
   costructure map γ : a ~> W a ([w_coalg]) satisfying the counit law
   ε ∘ γ ≈ id ([w_counit_law]) and the coaction law W γ ∘ γ ≈ δ ∘ γ
   ([w_coaction]).  A morphism of W-coalgebras (a, γ^a) ~> (b, γ^b) is a
   C-morphism f : a ~> b intertwining the costructure maps,
   γ^b ∘ f ≈ W f ∘ γ^a ([w_coalg_hom_commutes]).

   Since [Comonad C W] is by definition [@Monad (C^op) (W^op)]
   (Theory/Monad.v), a W-coalgebra is exactly an Eilenberg–Moore algebra
   ([TAlgebra], Monad/Algebra.v) for that opposite monad, and the category
   of W-coalgebras — the co-Eilenberg–Moore category C_W — is obtained
   here, dually to Monad/Eilenberg/Moore.v, as the opposite of the
   Eilenberg–Moore category of the opposite monad, rather than by
   re-proving the category laws:

       CoEilenbergMoore := (EilenbergMoore (W^op))^op

   Because duality is built into this library so that C^op^op = C holds by
   reflexivity, the two presentations agree definitionally: the classes
   [WCoalgebra]/[WCoalgebraHom] below are covariant re-readings of
   [TAlgebra]/[TAlgebraHom] over the opposite monad, converted in both
   directions field by field with [exact] (no proofs are re-done), and the
   hom-sets of [CoEilenbergMoore] are literally the algebra homomorphisms
   of the opposite monad ([coeilenberg_moore_hom], which holds by
   reflexivity).  The covariant category [WCoalgebras] assembled from the
   classes below is isomorphic in Cat to [CoEilenbergMoore]
   ([WCoalgebras_CoEilenbergMoore_Iso]); both functors are the identity on
   carriers and underlying morphisms, and the natural isomorphisms
   witnessing the two round trips have identity components. *)

(* The covariant coalgebra class.  Its three fields are, definitionally,
   the fields of [@TAlgebra (C^op) (W^op) H a]: the costructure map read
   covariantly, the counit law as the op-read of [t_id] (whose [ret] is
   [extract]), and the coaction law as the op-read of [t_action] (whose
   [join] is [duplicate] and whose [fmap] is [fmap[W]], with each composite
   read backwards).  See [WCoalgebra_to_TAlgebra] below. *)

Class WCoalgebra {C : Category} (W : C ⟶ C) {H : @Comonad C W} (a : C) := {
  w_coalg : a ~> W a;

  w_counit_law : @extract C W H a ∘ w_coalg ≈ id;
  w_coaction :
    fmap[W] w_coalg ∘ w_coalg ≈ @duplicate C W H a ∘ w_coalg
}.

Notation "w_coalg[ F ]" := (@w_coalg _ _ _ _ F)
  (at level 9, format "w_coalg[ F ]") : morphism_scope.

(* A homomorphism of W-coalgebras: an underlying arrow f : a ~> b commuting
   with the costructure maps, γ^b ∘ f ≈ W f ∘ γ^a.  Definitionally this is
   [TAlgebraHom] over the opposite monad with source and target swapped
   (the op-read reverses homs); see [WCoalgebraHom_to_TAlgebraHom]. *)

Class WCoalgebraHom {C : Category} (W : C ⟶ C) {H : @Comonad C W}
      (a b : C) (F : @WCoalgebra C W H a) (G : @WCoalgebra C W H b) := {
  w_coalg_hom : a ~> b;

  w_coalg_hom_commutes :
    w_coalg[G] ∘ w_coalg_hom ≈ fmap[W] w_coalg_hom ∘ w_coalg[F]
}.

Notation "w_coalg_hom[ f ]" := (@w_coalg_hom _ _ _ _ _ _ _ f)
  (at level 9, format "w_coalg_hom[ f ]") : morphism_scope.

Section CoEilenbergMoore.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(** ** Definitional conversions with algebras over the opposite monad

    Each conversion transports every field by [exact]: the statements are
    definitionally equal, so no equational reasoning is involved. *)

Definition WCoalgebra_to_TAlgebra {a : C} (F : @WCoalgebra C W H a) :
  @TAlgebra (C^op) (W^op) H a :=
  @Build_TAlgebra (C^op) (W^op) H a
    (@w_coalg C W H a F)
    (@w_counit_law C W H a F)
    (@w_coaction C W H a F).

Definition TAlgebra_to_WCoalgebra {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  @WCoalgebra C W H a :=
  @Build_WCoalgebra C W H a
    (@t_alg (C^op) (W^op) H a F)
    (@t_id (C^op) (W^op) H a F)
    (@t_action (C^op) (W^op) H a F).

(** The costructure map is untouched by the round trip (and likewise in the
    other direction): the conversions only repackage fields. *)

Lemma WCoalgebra_to_TAlgebra_alg {a : C} (F : @WCoalgebra C W H a) :
  t_alg[WCoalgebra_to_TAlgebra F] ≈ w_coalg[F].
Proof. reflexivity. Qed.

Lemma TAlgebra_to_WCoalgebra_coalg {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  w_coalg[TAlgebra_to_WCoalgebra F] ≈ t_alg[F].
Proof. reflexivity. Qed.

(* A coalgebra homomorphism (a, γ^a) ~> (b, γ^b) is an algebra homomorphism
   over the opposite monad from (b, γ^b) to (a, γ^a): the op-read reverses
   the direction of the underlying arrow, while the commuting square is the
   same C-equation. *)

Definition WCoalgebraHom_to_TAlgebraHom {a b : C}
  {F : @WCoalgebra C W H a} {G : @WCoalgebra C W H b}
  (f : @WCoalgebraHom C W H a b F G) :
  @TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F) :=
  @Build_TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F)
    (@w_coalg_hom C W H a b F G f)
    (@w_coalg_hom_commutes C W H a b F G f).

Definition TAlgebraHom_to_WCoalgebraHom {a b : C}
  {F : @TAlgebra (C^op) (W^op) H a} {G : @TAlgebra (C^op) (W^op) H b}
  (f : @TAlgebraHom (C^op) (W^op) H b a G F) :
  @WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G) :=
  @Build_WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G)
    (@t_alg_hom (C^op) (W^op) H b a G F f)
    (@t_alg_hom_commutes (C^op) (W^op) H b a G F f).

(** ** The co-Eilenberg–Moore category, by duality *)

Definition CoEilenbergMoore : Category :=
  (@EilenbergMoore (C^op) (W^op) H)^op.

(** The hom-sets of the co-Eilenberg–Moore category are definitionally the
    algebra homomorphisms of the opposite monad, source and target
    swapped. *)

Lemma coeilenberg_moore_hom (x y : CoEilenbergMoore) :
  (x ~{CoEilenbergMoore}~> y) =
  @TAlgebraHom (C^op) (W^op) H ``y ``x (projT2 y) (projT2 x).
Proof. reflexivity. Qed.

(** ** The covariant category of W-coalgebras

    Mirrors Monad/Eilenberg/Moore.v: objects are pairs of a carrier and a
    coalgebra on it, morphisms are coalgebra homomorphisms compared on
    their underlying arrows, and identities and composition are inherited
    from C.  The composition obligation pastes the two commuting squares,
    dually to the corresponding obligation there. *)

Program Definition WCoalgebras : Category := {|
  obj     := ∃ a : C, @WCoalgebra C W H a;
  hom     := fun x y => @WCoalgebraHom C W H ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => w_coalg_hom[f] ≈ w_coalg_hom[g] |};
  id      := fun _ => {| w_coalg_hom := id |};
  compose := fun _ _ _ f g => {| w_coalg_hom := w_coalg_hom[f] ∘ w_coalg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite w_coalg_hom_commutes.
  rewrite <- comp_assoc.
  rewrite w_coalg_hom_commutes.
  now rewrite comp_assoc.
Qed.

(** ** The isomorphism of categories, in Cat

    Both functors keep the carrier and the underlying arrow fixed and
    convert the packaging; on hom-setoids they are the identity.  The two
    round trips are witnessed by natural isomorphisms whose components
    have identity underlying arrows. *)

#[local] Obligation Tactic := program_simpl.

Program Definition WCoalgebras_to_CoEM : WCoalgebras ⟶ CoEilenbergMoore := {|
  fobj := fun x => (``x; WCoalgebra_to_TAlgebra (projT2 x));
  fmap := fun x y f => WCoalgebraHom_to_TAlgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Definition CoEM_to_WCoalgebras : CoEilenbergMoore ⟶ WCoalgebras := {|
  fobj := fun x => (``x; TAlgebra_to_WCoalgebra (projT2 x));
  fmap := fun x y f => TAlgebraHom_to_WCoalgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* The two round trips fix the carrier and the costructure map on the
   nose; only the record packaging is rebuilt.  Each component of the two
   natural isomorphisms is therefore carried by an identity arrow. *)

Program Definition coem_roundtrip (x : CoEilenbergMoore) :
  WCoalgebras_to_CoEM (CoEM_to_WCoalgebras x) ≅[CoEilenbergMoore] x := {|
  to   := {| t_alg_hom := id |};
  from := {| t_alg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Definition wcoalgebras_roundtrip (x : WCoalgebras) :
  CoEM_to_WCoalgebras (WCoalgebras_to_CoEM x) ≅[WCoalgebras] x := {|
  to   := {| w_coalg_hom := id |};
  from := {| w_coalg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Lemma WCoalgebras_to_CoEM_inverse :
  WCoalgebras_to_CoEM ◯ CoEM_to_WCoalgebras ≈ Id[CoEilenbergMoore].
Proof.
  exists coem_roundtrip.
  intros x y f; cbn; cat.
Qed.

Lemma CoEM_to_WCoalgebras_inverse :
  CoEM_to_WCoalgebras ◯ WCoalgebras_to_CoEM ≈ Id[WCoalgebras].
Proof.
  exists wcoalgebras_roundtrip.
  intros x y f; cbn; cat.
Qed.

Definition WCoalgebras_CoEilenbergMoore_Iso :
  WCoalgebras ≅[Cat] CoEilenbergMoore :=
  @Build_Isomorphism Cat WCoalgebras CoEilenbergMoore
    WCoalgebras_to_CoEM CoEM_to_WCoalgebras
    WCoalgebras_to_CoEM_inverse CoEM_to_WCoalgebras_inverse.

End CoEilenbergMoore.
