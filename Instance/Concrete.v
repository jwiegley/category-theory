Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Rel.

Generalizable All Variables.

(* Obligation discipline: with the default tactic, Program discharges some
   obligations and names the variables of the rest itself, and both behaviours
   have varied across the Coq versions this library supports.  Setting the
   tactic to [idtac] makes every obligation below the raw field type, with
   variables introduced by name in the proof — the same discipline
   Construction/Free/Quiver/Concrete.v uses. *)
#[local] Obligation Tactic := idtac.

(** * The concrete-category roster: Coq, CMon, and Rel *)

(* nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.7, printed p. 26
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Definition 1.6.18, printed p. 45
   Paper:     Freyd, "Homotopy is not concrete", Lecture Notes in Mathematics
              168, Springer 1970, pp. 25-34

   This file instantiates [Concrete] (Theory/Concrete.v) at the in-tree
   categories for which Mac Lane's §I.7 remark has content, and settles the
   negative half of that remark for Rel as precisely as the library permits.
   `Sets` itself is handled in Theory/Concrete.v, twice over — by the identity
   functor and by global elements.

   Positive instances here
   -----------------------

   [Coq_Concrete]  — Instance/Coq.v's category of types and functions, via the
     functor sending a type to itself under Leibniz equality.  Morphism
     equivalence in `Coq` is already pointwise `=`, so this functor is the
     identity on hom-setoids and faithfulness is the identity implication.

   [CMon_Concrete] — Instance/CMon.v's category of commutative monoids, via
     `CMon_Forget` (Instance/CMon.v:169).  That file's header comment at lines
     166-168 asserts faithfulness without proving it; [CMon_Forget_Faithful]
     below supplies the proof.

   [Rel_Concrete]  — Instance/Rel.v's category of sets and relations, via the
     direct-image (powerset) functor.  See the discussion of the negative
     result below for why this instance is worth having.

   Algebraic categories beyond CMon are cross-referenced, not depended on.
   Theory/Algebra/Monoid/Hom.v already proves `Mon_Forget_Faithful`, but its
   `Mon` is the category of monoid OBJECTS internal to an ambient monoidal
   category, whose forgetful functor lands in that ambient category rather
   than in `Sets`; it therefore does not yield a `Concrete` instance without
   first fixing the ambient category to `Sets`, which is not done here.
   Theory/Lawvere/Sets.v's `ev1_Faithful` does land in `Sets`, but only under
   its reachability hypothesis, so it too is left as a cross-reference.

   The negative half of Mac Lane's §I.7 remark, for Rel
   ---------------------------------------------------

   Mac Lane lists Rel alongside Toph as a category that is not concrete.  Read
   literally — "Rel has no faithful functor to sets" — that is too strong,
   and this file does not assert it: [Rel_Concrete] below exhibits a faithful
   functor.  What is true, and what is proved here, concerns the EVIDENT
   candidate, the assignment sending a set to itself:

   [Rel_hom_is_not_a_function] — the elementary obstruction.  Instance/Rel.v's
     `some_number` (line 161), the strict order `<` on nat, is a morphism of
     Rel that is not the graph of any function nat → nat.  So the evident
     underlying-set assignment `X ↦ X` cannot be extended to arrows at all,
     and there is nothing to check faithfulness of.

   [Rel_subsingleton_not_Faithful] — the sharp obstruction, stated for every
     candidate at once.  No functor `U : Rel ⟶ Sets` whose value at the
     one-element set is a subsingleton can be faithful, because Rel has two
     distinct endorelations of the one-element set ([Rel_two_arrows]) which
     any such `U` must send to the same function.  The evident underlying-set
     candidate would have `U 1` a singleton, so it is covered.

   [Rel_Concrete] is the complement of that result and is what keeps it from
     being overread.  The direct-image functor sends a set `X` to its powerset
     and a relation to its direct-image map; it is faithful because probing a
     relation with singletons recovers it.  Its value at the one-element set
     has two elements, so it escapes [Rel_subsingleton_not_Faithful] exactly
     as it must.  Conclusion: Rel is concrete, but not via its evident
     forgetful functor — which is the reading of Mac Lane's remark this
     development adopts, and it is an erratum against the literal reading.

   Deferral, disclosed
   -------------------

   The Toph half of the remark — Freyd's 1970 theorem that the pointed
   homotopy category has no faithful functor to sets — is out of scope, is
   not proved, and is not assumed.  The library has no homotopy category, so
   the statement is not expressible in-tree at all.  Theory/Concrete.v's
   header records the same deferral.

   Vacuity
   -------

   Each positive instance is accompanied by two parallel morphisms shown
   DISTINCT in the relevant hom-setoid ([Coq_two_arrows], [CMon_two_arrows],
   [Rel_two_arrows]).  Faithfulness is an injectivity statement, so it would
   be content-free over trivial hom-setoids; these witnesses show it is not. *)

(** ** Coq: types and functions *)

(* Every type is a setoid under Leibniz equality, and every function respects
   it.  `Coq`'s own hom-equivalence is pointwise `=`, which is exactly the
   hom-equivalence of the image setoids, so this functor neither adds nor
   loses information on arrows. *)
Program Definition Coq_Underlying : Coq ⟶ Sets := {|
  fobj := fun A => {| carrier   := A
                    ; is_setoid := {| equiv        := @eq A
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun _ _ f => {| morphism := f |}
|}.
Next Obligation. intros A B f a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; reflexivity. Qed.
Next Obligation. intros A B C f g a; reflexivity. Qed.

(* Faithfulness is the identity implication: both `≈`s unfold to pointwise
   Leibniz equality of the same function. *)
#[export] Instance Coq_Underlying_Faithful : Faithful Coq_Underlying.
Proof.
  constructor; intros A B f g Hfg.
  exact Hfg.
Qed.

#[export] Instance Coq_Concrete : Concrete Coq := {|
  underlying          := Coq_Underlying;
  underlying_faithful := Coq_Underlying_Faithful
|}.

(* Non-vacuity for [Coq_Concrete]: `negb` and the identity are parallel arrows
   `bool ~> bool` that differ in the hom-setoid, whose `≈` is pointwise `=`.
   (Stated with `→ False`: hom-equivalence here is `Type`-valued, so `¬` —
   which forces `Prop` — does not apply.) *)
Lemma Coq_two_arrows : @id Coq bool ≈ negb → False.
Proof.
  intro Heq.
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(** ** CMon: commutative monoids *)

(* The proof Instance/CMon.v's lines 166-168 only assert.  Equivalence of
   homomorphisms in `CMon` (`CMonHom_Setoid`) is by definition pointwise
   equivalence of the underlying setoid maps, which is what `CMon_Forget`
   records, so injectivity of its hom-map is the identity implication. *)
#[export] Instance CMon_Forget_Faithful : Faithful CMon_Forget.
Proof.
  constructor; simpl; intros M N f g Hfg a.
  exact (Hfg a).
Qed.

#[export] Instance CMon_Concrete : Concrete CMon := {|
  underlying          := CMon_Forget;
  underlying_faithful := CMon_Forget_Faithful
|}.

(* The natural numbers under Leibniz equality, as a setoid. *)
Definition nat_setoid_object : SetoidObject :=
  {| carrier   := nat
   ; is_setoid := {| equiv := @eq nat ; setoid_equiv := eq_equivalence |} |}.

(* The additive monoid of natural numbers, used only to show that `CMon` has
   parallel morphisms that differ. *)
Definition nat_CMon : CMonObject.
Proof.
  unshelve refine {| cmon_setoid := nat_setoid_object
                   ; cmon_zero   := 0%nat
                   ; cmon_plus   := Nat.add |}.
  - intros a b c; simpl; symmetry; apply PeanoNat.Nat.add_assoc.
  - intros a b; simpl; apply PeanoNat.Nat.add_comm.
  - intros a; simpl; reflexivity.
Defined.

(* The constant-zero endomorphism of `nat_CMon`; it preserves the unit and the
   operation, so it is a genuine homomorphism. *)
Definition nat_CMon_zero_hom : CMonHom nat_CMon nat_CMon.
Proof.
  unshelve refine (Build_CMonHom nat_CMon nat_CMon _ _ _).
  - refine {| morphism := fun _ => 0%nat |}.
  - simpl; reflexivity.
  - intros a b; simpl; reflexivity.
Defined.

(* Non-vacuity for [CMon_Concrete]: the identity and the constant-zero
   homomorphism are parallel arrows of `CMon` that differ in the hom-setoid,
   whose `≈` is pointwise equivalence of the underlying maps. *)
Lemma CMon_two_arrows : @id CMon nat_CMon ≈ nat_CMon_zero_hom → False.
Proof.
  intro Heq.
  specialize (Heq 1%nat).
  simpl in Heq.
  discriminate.
Qed.

(** ** Rel: sets and relations, the negative half *)

(* An auxiliary arithmetic fact, proved here to keep the file's dependencies
   to the ones already present in Instance/Rel.v. *)
Lemma nat_neq_succ (n : nat) : n = S n → False.
Proof.
  induction n as [|n IH]; intro Hn.
  - discriminate.
  - apply IH.
    now injection Hn.
Qed.

(* Instance/Rel.v's `some_number` (line 161) is the strict order `<` on nat,
   read as a relation nat ⇸ nat.  It is not the graph of any function: if it
   were the graph of `f`, then `f 0` would have to be simultaneously the
   unique natural number above 0 and its own successor.

   This is the elementary form of Mac Lane's negative remark.  The evident
   underlying-set assignment for Rel — send a set to itself — has no action on
   arrows to define, because Rel's arrows are not functions between the
   underlying sets. *)
Theorem Rel_hom_is_not_a_function (f : nat → nat) :
  (∀ x y : nat, some_number x y ↔ f x = y) → False.
Proof.
  intro Hgraph.
  (* `f 0` is above 0, since `f 0 = f 0`. *)
  assert (H0 : some_number 0%nat (f 0%nat)) by now apply Hgraph.
  (* `S (f 0)` is also above 0, so the graph reading forces `f 0 = S (f 0)`. *)
  assert (HS : some_number 0%nat (S (f 0%nat))).
  { unfold some_number in *.
    apply PeanoNat.Nat.lt_lt_succ_r, H0. }
  apply (nat_neq_succ (f 0%nat)).
  now apply Hgraph.
Qed.

(* The two endorelations of the one-element set: the identity (the diagonal,
   which relates the point to itself) and the empty relation.  In Rel's
   hom-setoid, whose `≈` is pointwise `↔`, they differ.  A one-element SET has
   only one endofunction, so this pair already shows Rel's hom-setoids are
   strictly larger than the corresponding function sets. *)
Definition Rel_empty : (unit : Rel) ~{Rel}~> (unit : Rel) :=
  fun _ _ => False.

Lemma Rel_two_arrows : @id Rel unit ≈ Rel_empty → False.
Proof.
  intro Heq.
  apply (Heq tt tt).
  (* `id` in Rel is `Singleton`, so the point is related to itself. *)
  constructor.
Qed.

(* The sharp negative result.  Any candidate underlying-set functor for Rel
   that sends the one-element set to a subsingleton — as the evident
   "underlying set" candidate would — is not faithful, because it must
   identify the two arrows of [Rel_two_arrows].

   Note what is and is not claimed: this refutes a FAMILY of candidates,
   selected by their value at the one-element set.  It does not say Rel is
   non-concretizable, and [Rel_Concrete] below shows it is not. *)
Theorem Rel_subsingleton_not_Faithful (U : Rel ⟶ Sets)
        (Hsub : ∀ a b : carrier (U (unit : Rel)), a ≈ b) :
  Faithful U → False.
Proof.
  intro HF.
  apply Rel_two_arrows.
  apply (fmap_inj (F:=U)).
  simpl; intro a.
  apply Hsub.
Qed.

(** ** Rel: sets and relations, the positive half *)

(* The direct-image functor `P : Rel ⟶ Sets`.  An object `X` is sent to its
   powerset — `Ensemble X`, compared by pointwise `↔` — and a relation
   `R ⊆ X × Y` to the map taking a subset `S ⊆ X` to its image
   `{ y | ∃ x ∈ S, R x y }`.  This is the Kleisli presentation of Rel over
   the powerset monad read as a functor into sets. *)
Program Definition Rel_Powerset : Rel ⟶ Sets := {|
  fobj := fun X => {| carrier   := X → Prop
                    ; is_setoid := {| equiv := fun S T => ∀ x, S x ↔ T x |} |};
  fmap := fun X Y R =>
            {| morphism := fun S y => (exists x : X, S x ∧ R x y)%type |}
|}.
Next Obligation.
  (* the powerset setoid: pointwise `↔` is an equivalence *)
  (* `↔` here is Category.Lib's `iffT`, a pair of maps, so the two directions
     are reached with [fst] and [snd] rather than [proj1]/[proj2]. *)
  intros X; constructor.
  - intros S a; split; intro Ha; exact Ha.
  - intros S T HST a; split; [ exact (snd (HST a)) | exact (fst (HST a)) ].
  - intros S T U HST HTU a; split; intro Ha.
    + exact (fst (HTU a) (fst (HST a) Ha)).
    + exact (snd (HST a) (snd (HTU a) Ha)).
Qed.
Next Obligation.
  (* the direct image of a fixed relation respects `≈` of subsets *)
  intros X Y R S T HST b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact (fst (HST a) Ha).
  - exact HR.
  - exact (snd (HST a) Ha).
  - exact HR.
Qed.
Next Obligation.
  (* equivalent relations have equal direct images *)
  intros X Y R R' HRR' S b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact Ha.
  - exact (fst (HRR' a b) HR).
  - exact Ha.
  - exact (snd (HRR' a b) HR).
Qed.
Next Obligation.
  (* the direct image along the diagonal is the identity on subsets *)
  intros X S a; split; intro Hin.
  - destruct Hin as [b [HSb Hdiag]].
    now destruct Hdiag.
  - exists a.
    split; [ exact Hin | constructor ].
Qed.
Next Obligation.
  (* direct image takes relational composites to composites of maps *)
  intros X Y Z R R' S c; split.
  - intros [a [Ha [b [HR' HR]]]].
    exists b; split; [ exists a; split; assumption | exact HR ].
  - intros [b [[a [Ha HR']] HR]].
    exists a; split; [ exact Ha | exists b; split; assumption ].
Qed.

(* Faithfulness: probe the direct-image map with the singleton subsets.  If
   `R` and `R'` have the same direct images then they agree on every
   `{x}`, hence everywhere. *)
#[export] Instance Rel_Powerset_Faithful : Faithful Rel_Powerset.
Proof.
  constructor; simpl; intros X Y R R' Himg x y.
  specialize (Himg (fun a => a = x) y).
  split; intro Hxy.
  - destruct Himg as [Hfwd _].
    destruct Hfwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
  - destruct Himg as [_ Hbwd].
    destruct Hbwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
Qed.

#[export] Instance Rel_Concrete : Concrete Rel := {|
  underlying          := Rel_Powerset;
  underlying_faithful := Rel_Powerset_Faithful
|}.

(* The powerset functor escapes [Rel_subsingleton_not_Faithful] exactly where
   it must: its value at the one-element set has two distinct elements, the
   empty subset and the whole set.  So the hypothesis of that theorem is not
   met, and no contradiction arises with [Rel_Concrete]. *)
Lemma Rel_Powerset_unit_not_subsingleton :
  (∀ a b : carrier (Rel_Powerset (unit : Rel)), a ≈ b) → False.
Proof.
  intro Hsub.
  apply (Hsub (fun _ => False) (fun _ => True) tt).
  exact I.
Qed.
