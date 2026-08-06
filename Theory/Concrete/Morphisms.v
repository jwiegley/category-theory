Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Concrete.

Generalizable All Variables.

(** * Underlying injections and surjections in a concrete category *)

(* nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Exercise 1.6.iv, printed p. 47, and Definition 1.6.18,
              printed p. 45
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.5, Exercise 9, printed p. 21

   Riehl's Exercise 1.6.iv is that a faithful functor reflects monomorphisms
   and, dually, epimorphisms; that is [faithful_reflects_monic] and
   [faithful_reflects_epic] in Theory/Functor.v.  She then draws the corollary
   this file proves: in a CONCRETE category — one paired with a faithful
   functor to sets, Theory/Concrete.v's [Concrete] — a morphism whose
   underlying function is injective is a monomorphism, and one whose
   underlying function is surjective is an epimorphism.

   The two proofs are short and symmetric, and both run entirely through
   Theory/Concrete.v's [concrete_arrow_eq]: to make two arrows of `C`
   equivalent under `≈` it suffices that their underlying functions agree
   pointwise, and that is where the injectivity or surjectivity hypothesis is
   spent.  Note the direction of the corollary.  The converses are out of
   scope: nothing here says that a monic of a concrete category has injective
   underlying function, and no counterexample to that is exhibited either.

   Both hypotheses are Lib/Setoid.v's setoid-level classes, so they are stated
   up to `≈` and not up to `=`: [injective] reads `f a ≈ f b → a ≈ b` in the
   two underlying setoids, and [surjective] is the split form, carrying a
   chosen preimage.  The conclusions are Theory/Morphisms.v's [Monic] and
   [Epic], whose cancellation laws are likewise `≈` throughout; no statement
   in this file uses `=` on morphisms.

   Layering note: the general lemmas need only Theory/Concrete.v, but the
   second half of the file instantiates them at the roster of
   Instance/Concrete.v, so the file as a whole depends on the instance layer.
   Theory/Concrete.v itself already depends on Instance/Sets.v, since `Sets`
   is the codomain named in the definition of [Concrete]. *)

Section ConcreteMorphisms.

Context {C : Category}.
Context `{Con : @Concrete C}.

(* Injective underlying function implies monic.  Cancelling `f` on the left of
   `f ∘ g1 ≈ f ∘ g2` is done element by element: at each point of the
   underlying set of the source, both sides are `f`'s function applied to the
   corresponding point of `g1` and `g2`, so injectivity separates them, and
   [concrete_arrow_eq] lifts the pointwise conclusion back to `C`. *)
Lemma concrete_injective_monic {x y : C} (f : x ~> y) :
  injective (concrete_fun f) → Monic f.
Proof.
  intros Hinj.
  destruct Hinj as [Hinj].
  constructor; intros z g1 g2 Hg.
  apply concrete_arrow_eq; intro a.
  apply Hinj.
  (* Both sides are the underlying function of a composite, by [fmap_comp]. *)
  transitivity (concrete_fun (f ∘ g1) a).
  { symmetry; exact (fmap_comp (Functor:=underlying) f g1 a). }
  transitivity (concrete_fun (f ∘ g2) a).
  { exact (concrete_fun_respects _ _ Hg a). }
  exact (fmap_comp (Functor:=underlying) f g2 a).
Qed.

(* Surjective underlying function implies epic: the mirror image.  A point of
   the underlying set of the TARGET is hit by some point `a` of the source, and
   the two composites agree at `a`; the underlying functions of `g1` and `g2`
   are setoid maps, so that agreement transports along the chosen preimage. *)
Lemma concrete_surjective_epic {x y : C} (f : x ~> y) :
  surjective (concrete_fun f) → Epic f.
Proof.
  intros Hsur.
  constructor; intros z g1 g2 Hg.
  apply concrete_arrow_eq; intro b.
  destruct (@surj _ _ _ _ Hsur b) as [a Ha].
  rewrite <- Ha.
  transitivity (concrete_fun (g1 ∘ f) a).
  { symmetry; exact (fmap_comp (Functor:=underlying) g1 f a). }
  transitivity (concrete_fun (g2 ∘ f) a).
  { exact (concrete_fun_respects _ _ Hg a). }
  exact (fmap_comp (Functor:=underlying) g2 f a).
Qed.

End ConcreteMorphisms.

(** ** The corollary at work: [Coq], via [Coq_Concrete] *)

(* Non-vacuity of both lemmas at a real concrete category.  `Coq`
   (Instance/Coq.v) is concrete via [Coq_Concrete] (Instance/Concrete.v:146),
   whose underlying-set functor reads a type as a setoid under Leibniz
   equality.  So `injective` and `surjective` below are the ordinary
   element-level notions for the two functions chosen here, and the
   conclusions are genuine cancellation properties in `Coq` — genuine because
   `Coq`'s hom-setoids are not trivial, as Instance/Concrete.v's
   [Coq_two_arrows] records. *)

Definition bool_to_nat (b : bool) : nat := if b then 1%nat else 0%nat.

(* This one statement is `=` rather than `≈`, and deliberately so: it relates
   ELEMENTS of `bool` and `nat`, not morphisms.  Under [Coq_Underlying] those
   two carriers are setoids whose `≈` IS Leibniz equality, so this is already
   the `≈`-shaped premise [injective] asks for, and it is used as such
   directly below. *)
Lemma bool_to_nat_inj (a b : bool) : bool_to_nat a = bool_to_nat b → a = b.
Proof.
  destruct a, b; simpl; solve [ reflexivity | discriminate ].
Qed.

#[local] Instance bool_to_nat_injective :
  injective (concrete_fun (Con:=Coq_Concrete) (bool_to_nat : bool ~{Coq}~> nat)).
Proof.
  constructor; intros a b Hab.
  exact (bool_to_nat_inj a b Hab).
Qed.

(* Predecessor is surjective: every `y` is `pred (S y)`.  It is not injective
   either (`pred 0` and `pred 1` are both `0`, both by computation), so the
   two halves above are exercised by two different arrows rather than by one
   arrow that happens to be bijective. *)
#[local] Instance Coq_pred_surjective :
  surjective (concrete_fun (Con:=Coq_Concrete) (Nat.pred : nat ~{Coq}~> nat)).
Proof.
  constructor; intro y.
  exists (S y); reflexivity.
Qed.

Definition Coq_bool_to_nat_Monic : Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  concrete_injective_monic (Con:=Coq_Concrete) bool_to_nat bool_to_nat_injective.

Definition Coq_pred_Epic : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  concrete_surjective_epic (Con:=Coq_Concrete) Nat.pred Coq_pred_surjective.

(** ** The same two conclusions through the reflection lemmas *)

(* The corollary can also be reached by first establishing the property in
   `Sets` and then reflecting it along the faithful functor, which is what
   Riehl's exercise proper supplies.  Both routes are recorded because the
   second is a non-vacuity witness for [faithful_reflects_monic] and
   [faithful_reflects_epic] themselves: the hypothesis genuinely holds and the
   conclusion is a genuine monic (respectively epic) of `Coq`.

   No claim is made that the two routes produce the same proof term — they are
   different derivations of the same statement, and `Monic`/`Epic` are
   record types whose inhabitants are not compared here. *)

Definition Coq_bool_to_nat_Monic_reflected :
  Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  faithful_reflects_monic Coq_Underlying bool_to_nat
    (fst (injectivity_is_monic (fmap[Coq_Underlying] bool_to_nat))
       (fun a b (Hab : bool_to_nat a = bool_to_nat b) => bool_to_nat_inj a b Hab)).

(* For epis the `Sets`-side ingredient comes from this file's own
   [concrete_surjective_epic] at [Sets_Concrete] (Theory/Concrete.v:234),
   whose underlying-set functor is the identity: there `concrete_fun h` IS `h`,
   so the lemma reads "a surjective setoid map is epic in `Sets`".
   Instance/Sets.v states the corresponding biconditional as
   `surjectivity_is_epic`, but that proof is a sketch stopped before
   completion, so the name never enters the environment and cannot be used
   here; the header of Instance/Sets.v documents the size obstruction behind
   the missing direction. *)
Definition Sets_surjective_epic {X Y : SetoidObject} (h : X ~{Sets}~> Y) :
  surjective h → Epic h :=
  concrete_surjective_epic (Con:=Sets_Concrete) h.

Definition Coq_pred_Epic_reflected : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  faithful_reflects_epic Coq_Underlying Nat.pred
    (Sets_surjective_epic (fmap[Coq_Underlying] Nat.pred) Coq_pred_surjective).
