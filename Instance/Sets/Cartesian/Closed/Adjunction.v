Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.

Generalizable All Variables.

(** * The currying adjunction in [Sets], where the counit computes *)

(* nLab: https://ncatlab.org/nlab/show/exponential+object
   Book: Riehl, "Category Theory in Context", Dover 2016; §2.1
         (Representable functors), Example 2.1.6(iv)

   Structure/Cartesian/Closed/Adjunction.v builds (- × S) ⊣ (-)^S over an
   arbitrary cartesian closed category. This file instantiates it at [Sets],
   the category of setoids, through [Sets_Cartesian] and [Sets_Closed], and
   checks that the abstract packaging computes to the expected concrete maps.

   Because [Sets_Closed] takes the exponential y^S to be the setoid of
   ≈-respecting maps S → y and [uncurry] to be λp. f (fst p) (snd p), the
   counit — which the general file already identifies with [eval] — is
   function application:

       counit (h, s) = h s,

   which [Sets_counit_apply] proves by [reflexivity]: the two sides are
   convertible, not merely ≈-related. Note what kind of statement that is. It
   relates two ELEMENTS of the carrier of a setoid, not two morphisms, so
   [reflexivity] there is a claim about computation in this model; the variant
   [Sets_counit_apply_eq] states it with Leibniz =, which is strictly stronger
   than the ≈ form and is legitimate here only because both sides are carrier
   elements that happen to be convertible. Every = appearing in this file and
   in Structure/Cartesian/Closed/Adjunction.v relates elements of a carrier
   type; no morphism is compared with = in either file. This is a statement
   about these two files, not a claim about the rest of the library.

   The middle of the file discharges the vacuity worry. A hom-setoid whose ≈
   were trivial would make the equations below hold for uninteresting reasons,
   so a concrete non-identity morphism is transposed and its transpose is
   shown to be non-constant — a genuine inequality of setoid maps
   ([curry_plus_not_constant]). The witness is addition on [NatSet], the
   natural numbers under Leibniz equality; the transpose is n ↦ (m ↦ n + m),
   and the counit applied to (curry plus_map 2, 3) computes to 5.

   Finally [Sets_Curry_Representable] is Riehl's Example 2.1.6(iv) in literal
   form: "The functor Hom(− × A, B) : Set^op → Set that sends a set X to the
   set of functions X × A → B is represented by the set B^A of functions from
   A to B." Here Set is [Sets], so "set" means setoid and "function" means
   ≈-respecting map, and the natural bijection is an isomorphism in the
   functor category [Sets^op, Sets].

   One elaboration note, since it shapes how the statements below are
   written. Several equations are between elements of a carrier rather than
   between morphisms, and [Instance/Sets.v] exports a global [Setoid False]
   instance ([False_Setoid]); when the side of a ≈ that Coq elaborates first
   has a type still blocked on instance resolution, that global instance is
   picked and the statement is rejected. The remedy used throughout is to put
   the side whose type is immediately known on the left, or to name the arrow
   with its type ascribed first (as [Sets_counit] does). This is a matter of
   elaboration order only; no statement is weakened by it. *)

(** ** The counit computes to function application *)

(* The counit of the currying adjunction at [Sets], named with its type
   ascribed so that applications of it elaborate without further hints. *)
Definition Sets_counit (S y : Sets) : (y ^ S) × S ~{Sets}~> y :=
  @counit _ _ _ _ (Curry_Adjunction S) y.

(* It is evaluation, as the general theory already says. *)
Lemma Sets_counit_eval (S y : Sets) : Sets_counit S y ≈ eval.
Proof. reflexivity. Qed.

(* And in the model it computes: the pair of a setoid map h : S → y and a
   point s of S is sent to h s. Both sides are elements of the carrier of y,
   compared with that setoid's ≈. *)
Lemma Sets_counit_apply (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) ≈ h s.
Proof. reflexivity. Qed.

(* The same fact with Leibniz equality. This is strictly stronger than
   [Sets_counit_apply], and it is stated only because both sides are elements
   of a carrier type — not morphisms — and are convertible in this model. It
   is not an equality of morphisms and licenses no such equality elsewhere. *)
Lemma Sets_counit_apply_eq
  (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) = h s.
Proof. reflexivity. Qed.

(* The two transposes compute to the expected maps: currying fixes the first
   coordinate, uncurrying pairs the arguments. By [curry_adj_to] and
   [curry_adj_from] these are the adjunction's ⌊-⌋ and ⌈-⌉. Both are
   definitional unfoldings in this model ([reflexivity] closes them); their
   content is the identification of [Sets_Closed]'s transposes with λ-
   abstraction and application, not a new equation. *)
Lemma Sets_curry_apply
  (S x y : Sets) (f : x × S ~{Sets}~> y) (a : carrier x) (s : carrier S) :
  f (a, s) ≈ curry f a s.
Proof. reflexivity. Qed.

Lemma Sets_uncurry_apply
  (S x y : Sets) (g : x ~{Sets}~> y ^ S) (p : carrier (x × S)) :
  g (fst p) (snd p) ≈ uncurry g p.
Proof. reflexivity. Qed.

(** ** A concrete witness: addition on the natural numbers *)

(* The natural numbers as a setoid, with ≈ taken to be Leibniz equality on
   [nat]. The hom-setoid (NatSet × NatSet ~> NatSet) is then pointwise
   equality of functions on pairs — a non-trivial relation, which is what
   makes the equations below carry content rather than hold vacuously. *)
Program Definition NatSet : Sets := {|
  carrier   := nat;
  is_setoid := {| equiv := fun n m : nat => n = m |}
|}.

(* Addition, as a morphism NatSet × NatSet ~> NatSet of [Sets]: a genuinely
   non-identity, non-projection arrow. *)
Program Definition plus_map : NatSet × NatSet ~{Sets}~> NatSet := {|
  morphism := fun p => (fst p + snd p)%nat
|}.

(* Its transpose is n ↦ (m ↦ n + m); at 2 and 3 that computes to 5. Leibniz
   equality is used between two ELEMENTS of [nat] (the carrier of NatSet),
   never between morphisms; the two sides are convertible. *)
Example curry_plus_compute : curry plus_map 2%nat 3%nat = 5%nat.
Proof. reflexivity. Qed.

(* The counit consumes the transpose again: it applies curry plus_map 2, that
   is (m ↦ 2 + m), to 3. Again an equality of elements of [nat]. *)
Example counit_plus_compute :
  Sets_counit NatSet NatSet (curry plus_map 2%nat, 3%nat) = 5%nat.
Proof. reflexivity. Qed.

(* The round trip of the hom-set bijection on this concrete arrow. Here the
   comparison IS between morphisms of [Sets], so it is stated with ≈. *)
Example uncurry_curry_plus : uncurry (curry plus_map) ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.

(* The same round trip taken through the adjunction's own transposes, using
   the general law ⌈⌊f⌋⌉ ≈ f of Theory/Adjunction.v. *)
Example adj_roundtrip_plus :
  from (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet)
       (to (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet) plus_map)
    ≈ plus_map.
Proof.
  exact (@to_adj_comp_law _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet
                          plus_map).
Qed.

(* And the universal property in elementary form: evaluation after the
   transpose recovers the original arrow. *)
Example eval_curry_plus :
  eval ∘ first (curry plus_map) ≈ plus_map.
Proof. exact (ump_exponents plus_map). Qed.

(* Non-vacuity as a genuine inequality: the transpose of addition is not a
   constant family, so the bijection above is not an identification of two
   one-element setoids. Concretely 2 + 0 and 0 + 0 differ. *)
Example curry_plus_not_constant :
  (curry plus_map 2%nat ≈ curry plus_map 0%nat) -> False.
Proof.
  intros HA.
  specialize (HA 0%nat).
  simpl in HA.
  discriminate.
Qed.

(** ** Riehl's Example 2.1.6(iv), literally *)

(* The functor Hom(− × A, B) : Sets^op ⟶ Sets ... *)
Definition Sets_Curry_Presheaf (A B : Sets) : Sets^op ⟶ Sets :=
  Curry_Presheaf A B.

(* ... is represented by B^A, the setoid of ≈-respecting maps A → B. *)
Definition Sets_Curry_Representable (A B : Sets) :
  Representable (Sets_Curry_Presheaf A B) := Curry_Representable A B.

(* On the concrete witness: the representation carries the transpose of
   addition back to addition itself, an ≈ between morphisms of [Sets]. *)
Example Sets_repr_plus :
  transform (to (Curry_Representation NatSet NatSet)) NatSet (curry plus_map)
    ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.
