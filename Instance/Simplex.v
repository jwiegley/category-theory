Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Simplex, the simplicial category Δ *)

(* nLab:      https://ncatlab.org/nlab/show/simplex+category
   Wikipedia: https://en.wikipedia.org/wiki/Simplicial_category
   Book:      Mac Lane, "Categories for the Working Mathematician",
              2nd ed., §I.2 (p. 12) and §VII.5, "The Simplicial Category"

   The simplicial category: objects are the natural numbers, with [n]
   standing for the canonical n-element ordinal [Fin.t n] carried by its
   linear order, and the morphisms [m ~> n] are the ORDER-PRESERVING
   functions [Fin.t m → Fin.t n].  A morphism is a function together with
   a monotonicity witness; the hom-setoid compares only the FUNCTION part,
   pointwise, exactly as Instance/FinSet.v:119 compares its morphisms
   through [fun_setoid].  The witness is proof data carried along, never
   compared — two morphisms with the same underlying function are equal in
   this category whatever their monotonicity proofs.

   WHICH Δ.  This is the "algebraist's Δ", which includes the empty
   ordinal [0]: the objects are ALL the finite ordinals, so what is built
   here is also called the AUGMENTED simplex category.  This is Mac Lane's
   Δ — §I.2 (p. 12) puts the finite ordinals and their monotone maps among
   the first examples of a category, and §VII.5 develops Δ with objects
   the finite ordinals indexed by n ∈ ℕ, the empty one among them.  It is
   the variant for which Δ is the free monoidal category containing a
   monoid, with [0] the tensor unit, which is what makes including [0]
   worth the trouble.  The "topologist's Δ" drops [0], keeping only the
   nonempty ordinals, because a simplex has at least one vertex; that is
   the shape category of simplicial sets proper, it is the full
   subcategory of this one on the positive naturals, and it is not
   separately built here.  Both conventions are in print under the name Δ,
   so the reading is stated rather than assumed.

   WHAT IS AND IS NOT PROVEN HERE.  The category, the inclusion into
   FinSet with faithfulness and a witnessed statement of non-fullness, the
   face and degeneracy generators, and ALL FIVE simplicial identities are
   proven below.  What is NOT proven is the converse, generating half of
   Mac Lane's §VII.5 theorem: that the faces and degeneracies GENERATE Δ,
   and that the five identities are a complete set of relations presenting
   it.  That is the Eilenberg–Zilber normal-form argument (every morphism
   of Δ factors uniquely as a composite of degeneracies followed by a
   composite of faces), and it is deferred; nothing below depends on it,
   and no statement below is weakened by its absence.  Simplicial sets
   (presheaves on this category), the nerve, and geometric realization are
   likewise out of scope. *)

(* Why Δ, and where it leads

   nLab: https://ncatlab.org/nlab/show/simplex+category
   nLab: https://ncatlab.org/nlab/show/simplicial+set

   Δ is the shape category of homotopy theory.  Presheaves on its full
   subcategory of NONEMPTY ordinals are the simplicial sets — presheaves
   on the whole of the category built here, empty ordinal included, are
   the AUGMENTED simplicial sets — and the passage between simplicial sets
   and topological spaces, geometric realization on the left and the
   singular complex on the right, is the adjunction that makes them a
   combinatorial model for spaces.  That adjunction is the reason Kan
   wrote "Adjoint functors" (1958) in the first place: as
   Theory/Kan/Extension.v:46-47 records, Kan introduced adjoints "to
   codify the formal properties of the passage between spaces and
   simplicial sets", and Theory/Kan/Extension.v:90-92 adds that geometric
   realization is "the left Kan extension of a cosimplicial space along
   the Yoneda embedding, the nerve its restricted-Yoneda right adjoint".
   Structure/Coend.v:113 records the same realization as a single coend.
   Each of those three passages is prose about a category that, until now,
   the library did not have; this file supplies it.

   The algebraic reading is equally load-bearing.  Δ is the free monoidal
   category containing a monoid: ordinal addition is the tensor, [0] is
   the unit, and [1] carries the universal monoid, whose multiplication is
   the unique map [2 ~> 1] and whose unit is the unique map [0 ~> 1]
   (nLab, "simplex category").  Consequently a monoid in any monoidal
   category is a strict monoidal functor out of Δ, which is why Mac Lane
   places §VII.5 inside the chapter on monoids rather than in a chapter on
   topology.  Dually Δ^op is the walking comonoid, and the bar resolution
   of a monad — the simplicial object whose face maps are built from the
   multiplication and whose degeneracies are built from the unit — is
   exactly a functor out of it; Comonad/Core.v:103-105 cites that
   "simplicial bar resolution of a comonad" as founding cotriple
   cohomology (Barr–Beck, Springer LNM 80, 1969).

   Within this library Δ arrives as a subcategory of the skeletal finite
   sets already in tree.  Instance/FinSet.v:88-89 anticipates precisely
   this, noting "the simplex category Δ embedding into FinSet" in its
   discussion of Grandis's symmetric simplicial sets ("Finite sets and
   symmetric simplicial sets", Theory and Applications of Categories 8,
   2001); the inclusion [Simplex_FinSet] below realizes that remark, and the
   accompanying non-fullness result measures the gap — FinSet has all
   functions between finite ordinals, Δ keeps only the monotone ones, and
   the swap on the two-element set is the smallest witness that the
   difference is real.

   NOTE on names: the name this category usually gets is Δ, and THAT is the
   collision that matters -- [Δ] in this tree is the diagonal functor
   (Functor/Diagonal.v:57, with notations Δ[J](c) and Δ(c) at :50/:54).
   Lowercase [delta] is also taken, by comonoid comultiplication
   (Theory/Algebra/Comonoid.v:41), though capitalization would keep them
   apart.  The generators here are therefore [sface] and [sdegen] at the
   categorical level and [fin_skip], [fin_dup] at the level of underlying
   functions, and the category itself is [Simplex].  (No ASCII [Delta]
   identifier exists in tree, and none is introduced -- but that spelling
   was never the live conflict.) *)

(** ** The order on a finite ordinal

    Monotonicity is stated through [Fin.to_nat] and the standard library's
    order on [nat], rather than through a bespoke inductive relation.  Two
    reasons.  First, a [Prop]-valued relation is adequate HERE, unlike in
    Instance/Omega.v, whose [le_t] must be [Type]-valued precisely because
    there the order proofs ARE the morphisms and must eliminate into the
    [Type]-valued hom-sets of an arbitrary target category; here the order
    proof is a side condition on a morphism, is never eliminated into, and
    is never compared, so [Prop] costs nothing.  Second, routing through
    [Fin.to_nat] puts every obligation in reach of [lia] after a single
    rewrite, which is what makes the simplicial identities tractable
    below. *)

Definition fin_nat {n : nat} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Definition fin_bound {n : nat} (i : Fin.t n) : Nat.lt (fin_nat i) n :=
  proj2_sig (Fin.to_nat i).

Definition fin_le {n : nat} (i j : Fin.t n) : Prop :=
  Nat.le (fin_nat i) (fin_nat j).

Lemma fin_nat_inj {n : nat} (i j : Fin.t n) : fin_nat i = fin_nat j → i = j.
Proof. apply Fin.to_nat_inj. Qed.

Lemma fin_nat_FS {n : nat} (i : Fin.t n) : fin_nat (Fin.FS i) = S (fin_nat i).
Proof. unfold fin_nat; simpl; now destruct (Fin.to_nat i). Qed.

Lemma fin_nat_F1 {n : nat} : fin_nat (@Fin.F1 n) = 0%nat.
Proof. reflexivity. Qed.

(** ** Monotone maps

    A morphism of Δ is a function on ordinals together with a proof that
    it preserves the order.  The coercion lets a [Monotone m n] be applied
    directly to an element. *)

Record Monotone (m n : nat) : Type := {
  mono_map :> Fin.t m → Fin.t n;
  mono_ord : ∀ i j : Fin.t m, fin_le i j → fin_le (mono_map i) (mono_map j)
}.

Arguments mono_map {m n} _ _.
Arguments mono_ord {m n} _ {i j} _.

(** ** The category

    Identity and composition of functions preserve monotonicity, so the
    underlying-function category structure of Instance/FinSet.v lifts
    verbatim; the equivalence, being pointwise equality of the function
    parts, makes composition a congruence for the same reason it does
    there. *)

Program Definition Simplex : Category := {|
  obj := nat;
  hom := Monotone;
  homset := fun m n =>
    {| equiv := fun f g => ∀ i, mono_map f i = mono_map g i |};
  id := fun _ => {| mono_map := fun i => i |};
  compose := fun _ _ _ f g =>
    {| mono_map := fun i => mono_map f (mono_map g i) |}
|}.
Next Obligation.
  (* Pointwise equality of function parts is an equivalence. *)
  constructor.
  - intros f i; reflexivity.
  - intros f g Hfg i; symmetry; apply Hfg.
  - intros f g h Hfg Hgh i; transitivity (mono_map g i);
      [ apply Hfg | apply Hgh ].
Qed.
Next Obligation.
  (* A composite of monotone maps is monotone. *)
  now apply mono_ord, mono_ord.
Qed.
Next Obligation.
  (* Composition respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i; simpl.
  rewrite (Hg i); apply Hf.
Qed.

(** ** The inclusion into FinSet

    Forgetting monotonicity is a functor into the skeletal finite sets of
    Instance/FinSet.v:116.  It is the identity on objects, so it is wide;
    it is injective on hom-sets, so it is faithful; and it is not full,
    for which see [Simplex_FinSet_not_Full] below. *)

Program Definition Simplex_FinSet : Simplex ⟶ FinSet := {|
  fobj := fun n => n;
  fmap := fun m n f => mono_map f
|}.

(* Wide: the inclusion is the identity on objects, so every object of
   FinSet is hit, and hit exactly once. *)
Lemma Simplex_FinSet_wide (n : nat) : Simplex_FinSet n = n.
Proof. reflexivity. Qed.

(* Faithful: the hom-setoid of [Simplex] compares exactly the data the
   inclusion retains, so its hom-maps are injective on the nose. *)
Lemma Simplex_fmap_inj {m n : nat} (f g : @hom Simplex m n) :
  (∀ i, mono_map f i = mono_map g i) → f ≈ g.
Proof. intro H; exact H. Qed.

#[export] Program Instance Simplex_FinSet_Faithful : Faithful Simplex_FinSet.

(** ** Not full

    The inclusion is a wide subcategory that is genuinely non-full: FinSet
    has morphisms between ordinals that Δ does not.  The smallest witness
    is the swap on the two-element set, which is a bijection [Fin.t 2 →
    Fin.t 2] and therefore a morphism [2 ~> 2] of FinSet, but reverses the
    order and so is not the image of any morphism of [Simplex].

    [Full] (Theory/Functor.v:331) packages fullness as a chosen preimage
    [prefmap] together with [fmap_sur], the proof that it is a section of
    [fmap].  Given such a preimage for the swap, its monotonicity applied
    to [0 ≤ 1] would give [1 ≤ 0] in the ordinal [2]. *)

Definition fin2_swap (i : Fin.t 2%nat) : Fin.t 2%nat :=
  Fin.caseS' i (fun _ => Fin.t 2%nat) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Example fin2_swap_F1 : fin2_swap Fin.F1 = Fin.FS Fin.F1 := eq_refl.
Example fin2_swap_FS : fin2_swap (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(* The sharp content, independent of how fullness is packaged: no
   morphism of [Simplex] has the swap as its underlying function.
   Monotonicity applied to 0 ≤ 1 would give swap 0 ≤ swap 1, i.e. 1 ≤ 0. *)
Lemma no_monotone_swap (f : @hom Simplex 2%nat 2%nat) :
  (∀ i, mono_map f i = fin2_swap i) → False.
Proof.
  intro Hf.
  assert (Hle : fin_le (mono_map f Fin.F1) (mono_map f (Fin.FS Fin.F1))).
  { apply mono_ord; unfold fin_le, fin_nat; simpl; lia. }
  rewrite (Hf Fin.F1), (Hf (Fin.FS Fin.F1)) in Hle.
  unfold fin_le, fin_nat in Hle; simpl in Hle; lia.
Qed.

(* Non-fullness follows: a [Full] structure would supply exactly such a
   morphism as the chosen preimage of the swap. *)
Lemma Simplex_FinSet_not_Full : Full Simplex_FinSet → False.
Proof.
  intro H.
  pose (g := fin2_swap
             : @hom FinSet (Simplex_FinSet 2%nat) (Simplex_FinSet 2%nat)).
  exact (no_monotone_swap (@prefmap _ _ _ H 2%nat 2%nat g)
                          (@fmap_sur _ _ _ H 2%nat 2%nat g)).
Qed.

(** ** Faces and degeneracies

    The generators of Δ.  On underlying functions, the i-th face
    [fin_skip i] is the monotone injection [Fin.t n → Fin.t (S n)] whose
    image omits [i], and the i-th degeneracy [fin_dup i] is the monotone
    surjection [Fin.t (S n) → Fin.t n] that takes the value [i] twice.
    [fin_weak] is the order-preserving inclusion [Fin.t n → Fin.t (S n)]
    that keeps the numeral fixed; it is how an index that the textbook
    identities reuse at two consecutive ordinals is transported.

    All three are built through [Fin.of_nat_lt] from an explicit numeral,
    rather than by structural recursion on [Fin.t].  The point is that
    [Fin.to_nat_of_nat] then computes [fin_nat] of each generator in one
    rewrite, turning every law below into [nat] arithmetic that [lia]
    discharges — where a recursive definition would need a nested
    [Fin.caseS'] induction for each of the five identities.  The terms
    still evaluate on closed input, because [Fin.of_nat_lt] recurses on
    the numeral and the ordinal, never on the bound proof (see the
    computing Examples below). *)

Program Definition fin_weak {n : nat} (i : Fin.t n) : Fin.t (S n) :=
  Fin.of_nat_lt (p := fin_nat i) _.
Next Obligation. pose proof (fin_bound i); lia. Qed.

Program Definition fin_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  Fin.t (S n) :=
  Fin.of_nat_lt
    (p := if Nat.ltb (fin_nat x) (fin_nat i)
          then fin_nat x else S (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound x); destruct (Nat.ltb (fin_nat x) (fin_nat i)); lia.
Qed.

Program Definition fin_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  Fin.t n :=
  Fin.of_nat_lt
    (p := if Nat.leb (fin_nat x) (fin_nat i)
          then fin_nat x else Nat.pred (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound i); pose proof (fin_bound x).
  destruct (Nat.leb (fin_nat x) (fin_nat i)) eqn:E.
  - apply Nat.leb_le in E; lia.
  - apply Nat.leb_gt in E; lia.
Qed.

Lemma fin_nat_weak {n : nat} (i : Fin.t n) : fin_nat (fin_weak i) = fin_nat i.
Proof. unfold fin_nat, fin_weak; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  fin_nat (fin_skip i x)
    = if Nat.ltb (fin_nat x) (fin_nat i) then fin_nat x else S (fin_nat x).
Proof. unfold fin_nat, fin_skip; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  fin_nat (fin_dup i x)
    = if Nat.leb (fin_nat x) (fin_nat i)
      then fin_nat x else Nat.pred (fin_nat x).
Proof. unfold fin_nat, fin_dup; now rewrite Fin.to_nat_of_nat. Qed.

(* The uniform decision procedure for every law about the generators:
   reduce the goal to an equation between ordinals, push each generator
   through to its numeral, split every boolean comparison, and close the
   resulting arithmetic with [lia].  Rewriting is repeated after each
   split because the comparisons of one generator have the numerals of
   another nested inside them. *)
Ltac fin_arith :=
  apply fin_nat_inj;
  repeat (rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  repeat (match goal with
          | [ |- context[Nat.ltb ?a ?b] ] => destruct (Nat.ltb_spec a b)
          | [ |- context[Nat.leb ?a ?b] ] => destruct (Nat.leb_spec a b)
          end;
          rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  lia.

Lemma fin_weak_monotone {n : nat} (x y : Fin.t n) :
  fin_le x y → fin_le (fin_weak x) (fin_weak y).
Proof. unfold fin_le; now rewrite !fin_nat_weak. Qed.

Lemma fin_skip_monotone {n : nat} (i : Fin.t (S n)) (x y : Fin.t n) :
  fin_le x y → fin_le (fin_skip i x) (fin_skip i y).
Proof.
  unfold fin_le; rewrite !fin_nat_skip.
  destruct (Nat.ltb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.ltb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

Lemma fin_dup_monotone {n : nat} (i : Fin.t n) (x y : Fin.t (S n)) :
  fin_le x y → fin_le (fin_dup i x) (fin_dup i y).
Proof.
  unfold fin_le; rewrite !fin_nat_dup.
  destruct (Nat.leb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.leb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

(* The generators as morphisms of [Simplex]. *)

Definition sface {n : nat} (i : Fin.t (S n)) : @hom Simplex n (S n) :=
  {| mono_map := fin_skip i; mono_ord := @fin_skip_monotone n i |}.

Definition sdegen {n : nat} (i : Fin.t n) : @hom Simplex (S n) n :=
  {| mono_map := fin_dup i; mono_ord := @fin_dup_monotone n i |}.

(* The generators evaluate on closed input, by [eq_refl].  The values are
   chosen to pin down the intended combinatorics rather than merely to
   witness that something reduces: δ_1 : 2 ~> 3 is checked at BOTH points
   of its domain, so the Examples certify that its image omits exactly the
   value 1, and σ_1 : 3 ~> 2 is checked at all three points, so they
   certify that it takes the value 1 exactly twice. *)

(* δ_1 : 2 ~> 3 omits the value 1 — it sends 0 ↦ 0 and 1 ↦ 2. *)
Example sface_skips_at_0 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sface_skips_at_1 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 2%nat := eq_refl.

(* σ_1 : 3 ~> 2 repeats the value 1 — it sends 0 ↦ 0, 1 ↦ 1 and 2 ↦ 1. *)
Example sdegen_repeats_at_0 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sdegen_repeats_at_1 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 1%nat := eq_refl.

Example sdegen_repeats_at_2 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS (Fin.FS Fin.F1)))
    = 1%nat := eq_refl.

(** ** The five simplicial identities

    The nLab ("simplex category") states them, in the cosimplicial form
    appropriate to Δ itself, as

      (1)  δ_j ∘ δ_i = δ_i ∘ δ_{j-1}        for i < j
      (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        for i ≤ j
      (3)  σ_j ∘ δ_i = δ_i ∘ σ_{j-1}        for i < j
      (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
      (5)  σ_j ∘ δ_i = δ_{i-1} ∘ σ_j        for i > j+1

    Subtraction on indices does not survive the passage to [Fin.t], where
    an index carries the size of the ordinal it indexes.  Each identity is
    therefore reindexed to its equivalent shift-free form, substituting
    [j := j+1] in (1) and (3) and [i := i+1] in (5), which replaces every
    [_-1] by an increment on the other side.  The reindexed (1) below is
    not a departure from the book: it is Mac Lane's own equation (11) of
    §VII.5 (delta_i delta_j = delta_{j+1} delta_i for i <= j) on the nose,
    and the reindexed (2)-(5) likewise match his (12)-(13):

      (1)  δ_i ∘ δ_j = δ_{j+1} ∘ δ_i        for i ≤ j
      (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        for i ≤ j
      (3)  σ_{j+1} ∘ δ_i = δ_i ∘ σ_j        for i ≤ j
      (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
      (5)  σ_j ∘ δ_{i+1} = δ_i ∘ σ_j        for j < i

    In these statements an index reused at two consecutive ordinals is
    transported by [fin_weak] (same numeral, next ordinal), and an index
    incremented by one is [Fin.FS] — so the side conditions are stated on
    [fin_nat], which both transports respect ([fin_nat_weak],
    [fin_nat_FS]).  All five are proven. *)

(* (1) δ_i ∘ δ_j = δ_{j+1} ∘ δ_i  for i ≤ j. *)
Theorem simplicial_face_face {n : nat} (i j : Fin.t (S n)) (H : fin_le i j) :
  sface (fin_weak i) ∘ sface j ≈ sface (Fin.FS j) ∘ sface i.
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (2) σ_j ∘ σ_i = σ_i ∘ σ_{j+1}  for i ≤ j. *)
Theorem simplicial_degen_degen {n : nat} (i j : Fin.t n) (H : fin_le i j) :
  sdegen j ∘ sdegen (fin_weak i) ≈ sdegen i ∘ sdegen (Fin.FS j).
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (3) σ_{j+1} ∘ δ_i = δ_i ∘ σ_j  for i ≤ j. *)
Theorem simplicial_degen_face_lt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.le (fin_nat i) (fin_nat j)) :
  sdegen (Fin.FS j) ∘ sface (fin_weak i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.

(* (4a) σ_j ∘ δ_j = id. *)
Theorem simplicial_degen_face_eq {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (fin_weak j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (4b) σ_j ∘ δ_{j+1} = id. *)
Theorem simplicial_degen_face_succ {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (Fin.FS j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (5) σ_j ∘ δ_{i+1} = δ_i ∘ σ_j  for j < i. *)
Theorem simplicial_degen_face_gt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.lt (fin_nat j) (fin_nat i)) :
  sdegen (fin_weak j) ∘ sface (Fin.FS i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.
