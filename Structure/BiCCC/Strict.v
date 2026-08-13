(* Strict initiality at the
   concrete categories Sets and FinSet (Seven Sketches §1.2.1 Exercise 1.25). *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.

Generalizable All Variables.

(* ---- Sets ---- *)

(* Seven Sketches §1.2.1 Exercise 1.25, at [Sets]: a setoid carrying a
   morphism into the empty setoid is itself isomorphic to it. *)
Definition Sets_initial_strict {x : Sets}
  (f : x ~{Sets}~> @initial_obj Sets Sets_Initial) :
  x ≅ @initial_obj Sets Sets_Initial :=
  @initial_strict Sets Sets_Cartesian Sets_Closed Sets_Initial x f.

(* The concrete reading Fong & Spivak give the exercise: a set with a function
   to the empty set is itself empty.  Unfolded to elements this needs no
   isomorphism at all -- the morphism's own action lands in [False] -- and
   that is exactly why the exercise is an exercise. *)
Lemma Sets_initial_strict_empty {x : Sets}
  (f : x ~{Sets}~> @initial_obj Sets Sets_Initial) : carrier x -> False.
Proof. intro a; exact (f a). Qed.

(* ---- FinSet ---- *)

Definition FinSet_initial_strict {x : FinSet}
  (f : x ~{FinSet}~> @initial_obj FinSet FinSet_Initial) :
  x ≅ @initial_obj FinSet FinSet_Initial :=
  @initial_strict FinSet FinSet_Cartesian FinSet_Closed FinSet_Initial x f.

(* Concretely in the skeletal model: an object of [FinSet] is a natural
   number, the initial object is [0], and a morphism [x ~> 0] is a function
   [Fin.t x -> Fin.t 0].  Strictness says [x] must itself be [0], which we can
   state as a genuine equality of objects because [FinSet] is skeletal
   ([FinSet_Skeletal], Instance/FinSet/Skeleton.v). *)
Lemma FinSet_initial_strict_zero (x : nat)
  (f : x ~{FinSet}~> @initial_obj FinSet FinSet_Initial) : x = 0%nat.
Proof.
  destruct x as [|n]; [ reflexivity | ].
  exact (Fin.case0 (fun _ => S n = 0%nat) (f Fin.F1)).
Qed.
