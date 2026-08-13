Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(** * The skeleton equivalence: finite setoids and finite ordinals *)

(* nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   Mac Lane's motivating example for equivalence of categories
   (Categories for the Working Mathematician, 2nd ed., §I.4, printed
   pp. 17-18): the category of all finite sets and the skeletal category
   of finite ordinals are equivalent, and equivalent is the most that can
   be asked of them.  This file supplies the missing half over the
   library's existing skeleton (Instance/FinSet.v:116: objects [nat],
   morphisms all functions [Fin.t m → Fin.t n]), builds the two functors,
   and proves the comparison cells.

   [Set_f] is a category of FINITE SETOIDS.  An object bundles a
   [SetoidObject] (Instance/Sets.v:113), a natural number, and an
   isomorphism in [Sets] from the setoid to the canonical one — Mac Lane's
   chosen bijection [θ_X : X ≅ #X].  Morphisms, identities, composition
   and the hom-setoid are those of [Sets] verbatim, so the evident functor
   [Set_f ⟶ Sets] is FULLY FAITHFUL — but it is NOT injective on objects,
   so [Set_f] is not a subcategory of [Sets].  An audit of the first commit
   was right to insist on the distinction, and the file's own centrepiece
   depends on it: [two_swap] and [finset_obj 2] have the SAME underlying
   setoid and differ only in the bijection they carry, which is exactly
   what makes the counit at [two_swap] a transposition rather than an
   identity.  Were [Set_f] a full subcategory of [Sets], those two objects
   would be one object and the asymmetry below would collapse.  An
   isomorphism of [Set_f] is nonetheless an isomorphism of [Sets] on the
   nose
   ([setf_iso] and [sets_iso] repackage the same four fields and carry no
   content of their own).  Finiteness is meant in the setoid sense —
   finitely many equivalence classes — so a carrier may be infinite;
   [parity_two] below is [nat] under equality of parity, an object of
   [Set_f] of cardinality 2.

   THE WITNESS IS DATA, NOT AN ASSERTION.  [fs_theta] is a field of the
   object record, so the cardinal functor [Card] can read it off and act
   on morphisms by Mac Lane's formula [# f = θ_Y ∘ f ∘ θ_X⁻¹].  Were
   finiteness recorded instead as a [Prop]-valued existential, its witness
   could not be eliminated into [Type], so it would be unavailable to
   [Card]'s morphism map, and producing one for every object at once is
   exactly what a choice principle does.  This is the discipline the library keeps
   throughout — chosen pullbacks, the chosen lifts of [Cleaving]
   (Theory/Fibration.v), the split [Full] class of Theory/Functor.v, and
   the split [EssentiallySurjective] class of Theory/Equivalence.v, whose
   header records that the classical full + faithful + essentially
   surjective criterion is otherwise equivalent to the axiom of choice.
   Every constant below is closed under the global context.

   The equivalence is not assembled by hand.  Awodey's two characteristic
   conditions (Category Theory, 1st ed. Carnegie Mellon pre-print,
   September 2005, §7.8, unnumbered remark, printed p. 178) are discharged
   for this instance — [FinSet_Incl] is shown full, faithful and
   essentially surjective — and [FinSet_Setf_Equivalence] is
   [FF_ESO_Equivalence] (Theory/Equivalence/FullFaithful.v:160) applied to
   those three witnesses.  Two things are worth saying plainly about that
   route:

   - Fullness and faithfulness hold definitionally here, and are to that
     extent content-free: the inclusion hands the underlying function
     straight through, so [prefmap] gives it back and [fmap_inj] is the
     identity.  What the inclusion does add is a respectfulness proof, so
     the section law of [Full] is an equation of underlying functions
     rather than of records — which is all the class asks, since it is
     stated up to ≈.  The one mathematical input is [fin_map]: on the
     canonical setoids ≈ IS Leibniz equality, so every function between
     them is respectful.
   - Essential surjectivity carries the content, and it is exactly the
     chosen [fs_theta] read backwards.  [Card] is then not an independent
     construction: it agrees with the quasi-inverse that
     [FF_ESO_Equivalence] produces on objects and on morphisms up to
     conversion ([Card_quasi_inverse_fobj], [Card_quasi_inverse_fmap]),
     which is why [Card_is_quasi_inverse] holds by [reflexivity].

   THE ASYMMETRY (Awodey, op. cit., §7.8, Example 7.23, printed
   pp. 176-177).  One round trip is strict and the other is not:

   - [Card ◯ FinSet_Incl] is the identity functor on the nose — its object
     map and its morphism map are Leibniz-equal to the identity's, by
     [eq_refl] ([Card_Incl_fobj_strict], [Card_Incl_fmap_strict]), and the
     comparison cell that [FF_ESO_Equivalence] computes at every object is
     literally the identity morphism ([Incl_unit_is_identity]) — its
     COMPONENTS are, in both directions; the isomorphism RECORD is not
     [iso_id], since the two carry different proof fields.  This is
     the effect of giving the canonical objects the identity bijection.
   - [FinSet_Incl ◯ Card] is compared to the identity only by the natural
     isomorphism [Incl_Card_theta], whose components are the chosen
     [θ].  At [two_swap] — whose carrier is already the canonical
     [Fin.t 2], but whose chosen bijection is the transposition — the
     comparison component is that transposition and provably not the
     identity ([counit_at_two_swap_not_identity]), and the composite
     replaces the carried bijection by the identity one
     ([Incl_Card_forgets_theta]).

   What is deliberately NOT claimed is a Leibniz disequality
   [FinSet_Incl ◯ Card ≠ Id[Set_f]] of functors or of objects: nothing
   here establishes one, the objects compared differ only in the bijection
   they carry, and no statement below rests on such a disequality.  The
   asymmetry is stated where Awodey states it, at the comparison cells.

   SKELETALITY AND CARDINALITY (Fong and Spivak, Seven Sketches in
   Compositionality, CUP 2019, §3.2.5, printed p. 88).  [FinSet_skeletal]
   is the first statement in the tree about isomorphisms of [FinSet] —
   Instance/FinSet.v contains no occurrence of [Isomorphism] at all, and
   its satellites only require the module.  An isomorphism [m ≅ n] forces
   [m = n], by counting: [fin_enum] enumerates [Fin.t n] without
   repetition, and each enumeration embeds in the image of the other
   ([fin_bijection_index]).  Hence [setf_cardinality A], the index
   the object carries, is THE index it is isomorphic to
   ([setf_cardinality_unique]), and Cantor's reading follows: setf_cardinality is
   constant on isomorphism classes and separates them
   ([setf_cardinality_iso_invariant], [setf_cardinality_complete],
   [setf_cardinality_classifies]).

   WHERE [=] APPEARS, AND WHY.  Morphisms are compared with ≈ throughout;
   the exceptions are deliberate and each is flagged where it is stated.
   (a) Equality of OBJECTS is the point of [FinSet_skeletal] and of the
   cardinality theorems — there [=] is what is being proved.  (b) The
   strictness lemmas compare morphisms and functor components with [=];
   each is genuinely stronger than the ≈ or ≅ statement it refines, and
   says so at the statement.  Most of them sit in the asymmetry section,
   but not all — [Card_quasi_inverse_fmap] is one and appears with the
   equivalence.  (b') Beyond those five classes the file also states a few
   equalities of Types and of booleans (carrier identifications, and the
   counting kit's list lengths); they are not comparisons of categorical
   data at all, and are listed here only so this taxonomy is not read as
   exhaustive.  (c) Equations
   between ELEMENTS of a canonical setoid [fin_setoid n] are written [=]
   because [Fin_Setoid]'s equivalence IS Leibniz equality, so there [=] and
   ≈ are the same relation and nothing is being strengthened.  (d) Two
   statements compare elements of [parity_setoid], whose ≈ is equality of
   parity; there [=] is strictly stronger, deliberately, and each says so.
   (e) [setf_sets_iso], [sets_setf_iso] and [Incl_Card_forgets_theta]
   compare isomorphism RECORDS — carried data, not morphisms.

   SCOPE.  This is the finite concrete case only.  No general [Skeleton]
   vocabulary is introduced: the statement that every category has a
   skeleton is itself equivalent to the axiom of choice (nLab, "skeleton
   of a category"), and Theory/Equivalence.v's header records the
   library's decision to confine skeletons to concrete instances such as
   this one. *)

(* Why a category and its skeleton are the same, and why that took work

   nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

   Counting is the oldest piece of mathematics, and this file is its
   categorical form.  To say that a finite set has n elements is to
   choose a bijection with the standard n-element set; Cantor's move
   was to make the number secondary and the bijection primary, so that
   two sets have the same cardinality precisely when some bijection
   exists (Fong and Spivak, Seven Sketches in Compositionality, CUP
   2019, §3.2.5, present cardinality in exactly this isomorphism-class
   reading; the in-file constant is named [setf_cardinality] only to avoid
   shadowing an unrelated [cardinality] in Theory/Metacategory.v).  The categorical statement adds functoriality: the
   assignment of a number to a set is not merely well defined on
   isomorphism classes, it is a functor, and the choice of bijections
   through which it acts on maps is invisible in the result up to
   natural isomorphism.

   Mac Lane introduces equivalence of categories through this very
   example (CWM §I.4, printed pp. 17-18), and the reason it must be
   equivalence rather than isomorphism is visible in the objects
   themselves: the ordinal 2 is one object, whereas the two-element
   sets form a proper class, so no bijection of object collections is
   available and none should be wanted.  Awodey draws the moral in
   §7.8 (printed p. 178): the two conditions that characterize an
   equivalence — full and faithful, and essentially surjective — are
   each visibly satisfied by the inclusion, while the composite in one
   order is the identity and in the other only isomorphic to it.  This
   is the concrete case of the principle of equivalence: a property of
   categories that distinguishes the ordinals from the finite sets is
   not a categorical property at all, and skeletality — which does
   distinguish them — is exactly such a non-invariant property (nLab,
   "skeleton of a category").

   The constructive reading is what the setoid presentation buys.
   Classically one says "every finite set is isomorphic to some
   ordinal" and then chooses, for every set at once, an isomorphism;
   that choice is the axiom of choice, and Theory/Equivalence.v's
   header traces the standard responses to it (Makkai's anafunctors;
   the univalent-foundations dissolution).  Here the choice is made
   once, by the object, and carried: an object of [Set_f] IS a setoid
   together with its counting.  The cardinal functor then exists
   outright, and the equivalence is closed under the global context.
   The same trade recurs across the library wherever a universal
   property is turned into an operation.

   Within this tree the result completes a corner that
   Instance/FinSet.v had left open.  That file builds the skeleton for
   its computational virtues — objects are literal numbers, object
   equality is decidable, and the topos structure on it evaluates by
   [eq_refl] (Instance/FinSet/Topos.v) — and its header explains what
   the skeleton is FOR.  What was missing is the reason one is entitled
   to use it in place of the finite sets at all.  That reason is the
   equivalence proved here, together with [FinSet_skeletal], which says
   the skeleton is a skeleton: it has one object per isomorphism class,
   no more. *)

(** ** The canonical n-element setoid *)

Definition fin_setoid (n : nat) : SetoidObject := {|
  carrier := Fin.t n;
  is_setoid := Fin_Setoid
|}.

(* A setoid map, packaged from its respectfulness proof in the shape the
   proofs below produce.  Nothing here is specific to finiteness. *)
Definition setoid_map {X Y : SetoidObject} (f : X → Y)
  (Hf : ∀ a b, a ≈ b → f a ≈ f b) : X ~{Sets}~> Y :=
  Build_SetoidMorphism X (is_setoid X) Y (is_setoid Y) f Hf.

(* On the canonical setoids the equivalence is Leibniz equality, so EVERY
   function between them is respectful: this is exactly why the inclusion
   below is full. *)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid m ~{Sets}~> fin_setoid n :=
  setoid_map (X := fin_setoid m) (Y := fin_setoid n) f
    (fun a b H => f_equal f H).

(** ** Counting: a bijection of finite ordinals pins the ordinal *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | O => nil
  | Datatypes.S k => Fin.F1 :: List.map Fin.FS (fin_enum k)
  end.

(* Stated locally rather than taken from the standard library, whose name
   for it moved between the supported versions. *)
Lemma length_of_map {A B : Type} (h : A → B) (l : list A) :
  List.length (List.map h l) = List.length l.
Proof.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma fin_enum_length (n : nat) : List.length (fin_enum n) = n.
Proof.
  induction n as [| k IH]; simpl.
  - reflexivity.
  - now rewrite length_of_map, IH.
Qed.

Lemma fin_enum_full {n : nat} (i : Fin.t n) : List.In i (fin_enum n).
Proof.
  induction n as [| k IH].
  - exact (Fin.case0 (fun i => List.In i (fin_enum 0)) i).
  - apply (Fin.caseS' i (fun i => List.In i (fin_enum (Datatypes.S k)))).
    + now left.
    + intro q; right.
      now apply List.in_map.
Qed.

(* Injectivity of [Fin.FS], proved through a local partial inverse rather
   than by [injection] on a dependent constructor, so that it holds by
   plain reduction on every supported version. *)
(* NOTE ON THE NAME.  Instance/FinSet/Classifier.v:223 and
   Instance/FinSet/Pushout.v:193 already export a [fin_pred], with a
   DIFFERENT type — theirs takes a default value and returns a [Fin.t n],
   this one returns an [option].  Since all three live under
   Instance/FinSet/, the suffix here keeps a reader who greps from
   conflating them. *)
Definition fin_pred_option {n : nat} (i : Fin.t (Datatypes.S n)) : option (Fin.t n) :=
  Fin.caseS' i (fun _ => option (Fin.t n)) None (fun q => Some q).

Lemma FS_injective {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof.
  intro H.
  apply (f_equal fin_pred_option) in H.
  simpl in H.
  now injection H.
Qed.

(* [Fin.FS] is injective, so it carries duplicate-freeness along. *)
Lemma nodup_map_FS {k : nat} (l : list (Fin.t k)) :
  List.NoDup l → List.NoDup (List.map Fin.FS l).
Proof.
  induction l as [| a l IH]; simpl; intro Hnd.
  - constructor.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq Hq']].
      apply FS_injective in Hq; subst.
      contradiction.
    + now apply IH.
Qed.

Lemma fin_enum_nodup (n : nat) : List.NoDup (fin_enum n).
Proof.
  induction n as [| k IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq _]].
      discriminate Hq.
    + now apply nodup_map_FS.
Qed.

(* Two finite ordinals connected by mutually inverse maps have the same
   index: each enumeration embeds into the image of the other without
   repetition, so the two lengths bound one another. *)
Lemma fin_bijection_index {m n : nat}
  (f : Fin.t m → Fin.t n) (g : Fin.t n → Fin.t m)
  (fg : ∀ j, f (g j) = j) (gf : ∀ i, g (f i) = i) : m = n.
Proof.
  assert (Hle : ∀ (p q : nat) (u : Fin.t p → Fin.t q) (v : Fin.t q → Fin.t p),
             (∀ j, u (v j) = j) → (q <= p)%nat).
  { intros p q u v uv.
    rewrite <- (fin_enum_length q), <- (fin_enum_length p).
    rewrite <- (length_of_map u (fin_enum p)).
    apply List.NoDup_incl_length.
    - apply fin_enum_nodup.
    - intros j Hj.
      apply List.in_map_iff.
      exists (v j); split; [apply uv | apply fin_enum_full]. }
  apply Nat.le_antisymm.
  - exact (Hle n m g f gf).
  - exact (Hle m n f g fg).
Qed.

(** ** The category of finite setoids *)

(* An object is a setoid, a number, and a CHOSEN isomorphism between them
   in [Sets] — Mac Lane's [θ_X : X ≅ #X], carried as data.  Two objects
   with the same underlying setoid but different chosen bijections are
   different objects; [two_swap] below is the case that makes the
   asymmetry of the two round trips visible. *)
Record FinSetoid : Type := {
  fs_obj : SetoidObject;
  fs_card : nat;
  fs_theta : @Isomorphism Sets fs_obj (fin_setoid fs_card)
}.

(* Morphisms, identities, composition, hom-setoid and all five laws are
   [Sets]' own, so nothing is re-proved and the forgetful functor to [Sets]
   is fully faithful.  It is NOT a subcategory: the object map forgets the
   carried bijection and is therefore not injective (see the header). *)
Definition Set_f : Category := {|
  obj := FinSetoid;
  hom := fun A B => fs_obj A ~{Sets}~> fs_obj B;
  homset := fun A B => @homset Sets (fs_obj A) (fs_obj B);
  id := fun A => @id Sets (fs_obj A);
  compose := fun A B C f g => @compose Sets (fs_obj A) (fs_obj B) (fs_obj C) f g;
  compose_respects := fun A B C =>
    @compose_respects Sets (fs_obj A) (fs_obj B) (fs_obj C);
  id_left := fun A B => @id_left Sets (fs_obj A) (fs_obj B);
  id_right := fun A B => @id_right Sets (fs_obj A) (fs_obj B);
  comp_assoc := fun A B C D =>
    @comp_assoc Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D);
  comp_assoc_sym := fun A B C D =>
    @comp_assoc_sym Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D)
|}.

(* An isomorphism of [Set_f] and an isomorphism in [Sets] between the
   underlying setoids are the same four fields: these two transports
   typecheck by conversion and carry no mathematical content.  They exist
   only so that the direction of the packaging is explicit at use sites. *)
Definition setf_iso {A B : Set_f}
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) : A ≅[Set_f] B :=
  @Build_Isomorphism Set_f A B (to i) (from i)
    (iso_to_from i) (iso_from_to i).

Definition sets_iso {A B : Set_f}
  (i : A ≅[Set_f] B) : @Isomorphism Sets (fs_obj A) (fs_obj B) :=
  @Build_Isomorphism Sets (fs_obj A) (fs_obj B) (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(* The packaging is inverse on the nose in both directions.  Stated with
   Leibniz equality rather than ≈ because that is the claim: no data is
   lost or renamed, the two transports are the same four fields. *)
Example setf_sets_iso (A B : Set_f) (i : A ≅[Set_f] B) :
  setf_iso (sets_iso i) = i.
Proof. now destruct i. Qed.

Example sets_setf_iso (A B : Set_f)
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) :
  sets_iso (@setf_iso A B i) = i.
Proof. now destruct i. Qed.

(** ** The inclusion of finite ordinals *)

(* The canonical objects: [Fin.t n] counted by the IDENTITY bijection.
   Mac Lane makes this choice too ("choose [θ_n = 1_n]"), and it is what
   makes the [Card ◯ FinSet_Incl] round trip strict below — tested, not
   asserted: [Card_conjugation_moves_constant] exhibits an object of the
   same underlying setoid carrying the transposition instead, at which the
   conjugation [θ ∘ f ∘ θ⁻¹] does move a morphism. *)
Definition finset_obj (n : nat) : FinSetoid := {|
  fs_obj := fin_setoid n;
  fs_card := n;
  fs_theta := iso_id
|}.

Program Definition FinSet_Incl : FinSet ⟶ Set_f := {|
  fobj := finset_obj;
  fmap := fun m n f => fin_map f
|}.

(** ** The cardinal functor *)

(* The two halves of the carried bijection.  Note the asymmetry already
   present here: on the ordinal side the round trip is Leibniz equality
   (the canonical setoid is discrete), on the setoid side only ≈ — which
   is the whole point of allowing an object like [parity_two], where
   [θ⁻¹ (θ a)] is a DIFFERENT natural number of the same parity.  The [=]
   in [theta_to_from] is [Fin_Setoid]'s ≈ written out, not a
   strengthening of it. *)
Lemma theta_to_from {A : Set_f} (i : Fin.t (fs_card A)) :
  to (fs_theta A) (from (fs_theta A) i) = i.
Proof. exact (iso_to_from (fs_theta A) i). Qed.

Lemma theta_from_to {A : Set_f} (a : fs_obj A) :
  from (fs_theta A) (to (fs_theta A) a) ≈ a.
Proof. exact (iso_from_to (fs_theta A) a). Qed.

(* Where the setoid discipline earns its keep: [Card] is well defined on
   ≈-classes of morphisms precisely because the chosen enumeration is
   respectful.  Over a discrete source it would come free by [f_equal] —
   that is precisely [fin_map] — but [Set_f] has objects like [parity_two]
   where it does not.  (Both conclusions
   are equations in [Fin.t (fs_card _)], where ≈ is Leibniz equality, so
   the [=] is that setoid's ≈.) *)
Lemma card_map_respects {A B : Set_f} (f g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  f ≈ g →
  to (fs_theta B) (f (from (fs_theta A) i))
    = to (fs_theta B) (g (from (fs_theta A) i)).
Proof.
  intro Hfg.
  exact (proper_morphism (to (fs_theta B)) _ _ (Hfg (from (fs_theta A) i))).
Qed.

Lemma card_map_comp {A B C : Set_f} (f : B ~{Set_f}~> C) (g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  to (fs_theta C) (f (g (from (fs_theta A) i)))
    = to (fs_theta C)
        (f (from (fs_theta B) (to (fs_theta B) (g (from (fs_theta A) i))))).
Proof.
  exact (proper_morphism (to (fs_theta C)) _ _
           (proper_morphism f _ _
              (symmetry (theta_from_to (g (from (fs_theta A) i)))))).
Qed.

(* Mac Lane's cardinal functor [#]: on objects the carried index, on
   morphisms [# f = θ_Y ∘ f ∘ θ_X⁻¹].  Definable without any choice
   principle exactly because [fs_theta] is data. *)
Program Definition Card : Set_f ⟶ FinSet := {|
  fobj := fs_card;
  fmap := fun A B f i => to (fs_theta B) (f (from (fs_theta A) i))
|}.
Next Obligation.
  repeat intro.
  now apply card_map_respects.
Qed.
Next Obligation. now apply theta_to_from. Qed.
Next Obligation. now apply card_map_comp. Qed.

(** ** The inclusion is full, faithful and essentially surjective *)

(* Awodey's two characteristic conditions, discharged for this instance.
   Fullness and faithfulness are definitional — [prefmap] returns the
   underlying function and [fmap_inj] is the identity — so as stated they
   would hold of any functor that is the identity on hom-carriers; the
   mathematical input is upstream, in [fin_map].  Essential surjectivity
   is the substantive one: the chosen [fs_theta], inverted. *)
Definition FinSet_Incl_Full : @Full FinSet Set_f FinSet_Incl :=
  @Build_Full FinSet Set_f FinSet_Incl
    (fun m n g i => g i)
    (fun m n g i => eq_refl).

Definition FinSet_Incl_Faithful : @Faithful FinSet Set_f FinSet_Incl :=
  @Build_Faithful FinSet Set_f FinSet_Incl (fun m n f g H => H).

Definition FinSet_Incl_EssSurj :
  @EssentiallySurjective FinSet Set_f FinSet_Incl :=
  @Build_EssentiallySurjective FinSet Set_f FinSet_Incl
    fs_card
    (fun A => @setf_iso (finset_obj (fs_card A)) A (iso_sym (fs_theta A))).

(** ** The equivalence *)

(* Mac Lane's example, obtained through the general criterion rather than
   by hand.  This is the constant to audit with [Print Assumptions]. *)
Definition FinSet_Setf_Equivalence : EquivalenceOfCategories FinSet_Incl :=
  @FF_ESO_Equivalence FinSet Set_f FinSet_Incl
    FinSet_Incl_Full FinSet_Incl_Faithful FinSet_Incl_EssSurj.

Lemma Card_is_quasi_inverse :
  @quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence ≈ Card.
Proof.
  exists (fun A => iso_id).
  intros A B f i.
  reflexivity.
Qed.

(* Sharper than the ≈ above, and the reason it went through by [reflexivity]:
   the quasi-inverse produced by [FF_ESO_Equivalence] and [Card] have the
   SAME object map and the SAME morphism map up to conversion — Leibniz
   equality, not merely ≈.  (The two functor records are still distinct
   terms: they carry different proofs of the three functor laws, which is
   why the comparison above is stated with ≈.) *)
Example Card_quasi_inverse_fobj (A : Set_f) :
  fobj[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] A
    = fobj[Card] A := eq_refl.

Example Card_quasi_inverse_fmap {A B : Set_f} (f : A ~> B) :
  fmap[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] f
    = fmap[Card] f := eq_refl.

(** ** The two comparison cells, stated with [Card] *)

(* The issue's two cells, now phrased with [Card] itself: [# ∘ S ≈ Id]
   and [θ : Id ≅ S ∘ #].  [Card_Incl_id] is proved by [reflexivity] at
   every component (see the strictness lemmas below); [Incl_Card_theta]
   genuinely needs the two round trips. *)
Definition Card_Incl_id : Card ◯ FinSet_Incl ≈ Id[FinSet].
Proof.
  exists (fun n => iso_id).
  intros m n f i.
  reflexivity.
Defined.

Definition Incl_Card_theta : Id[Set_f] ≈ FinSet_Incl ◯ Card.
Proof.
  exists (fun A => @setf_iso A (finset_obj (fs_card A)) (fs_theta A)).
  intros A B f a.
  (* [f a] first travels along the round trip at A, then back along the
     round trip at B; both cancellations are [theta_from_to]. *)
  transitivity (f (from (fs_theta A) (to (fs_theta A) a))).
  - exact (proper_morphism f _ _ (symmetry (theta_from_to a))).
  - exact (symmetry
             (theta_from_to (f (from (fs_theta A) (to (fs_theta A) a))))).
Defined.

Definition Card_Equivalence : EquivalenceOfCategories Card :=
  @Build_EquivalenceOfCategories Set_f FinSet Card FinSet_Incl
    Card_Incl_id Incl_Card_theta.

Definition Incl_Card_theta_iso : Id[Set_f] ≅[Fun] FinSet_Incl ◯ Card :=
  equiv_iso Incl_Card_theta.

(** ** Skeletality *)

(* [FinSet] is skeletal: isomorphic objects are EQUAL.  The conclusion is
   a Leibniz equality of objects, and that is deliberate — equality of
   objects always yields an isomorphism, whereas the converse is precisely
   what a category with repeated isomorphism classes lacks, and SAYING it
   holds here is what the word skeletal means.  Fong and Spivak's §3.2.5 reading needs
   exactly this: the index a finite set is isomorphic to is determined,
   not merely determined up to isomorphism.

   Not vacuous in either direction: the hypothesis is inhabited by
   non-identity isomorphisms ([FinSet_swap_iso], with
   [FinSet_swap_not_identity] showing it is not the identity), and the
   conclusion has bite ([FinSet_one_not_iso_two]). *)
Theorem FinSet_skeletal {m n : FinSet} (i : m ≅ n) : m = n.
Proof.
  exact (fin_bijection_index (to i) (from i) (iso_to_from i) (iso_from_to i)).
Qed.

(** ** Cardinality *)

(* Cardinality as an isomorphism invariant.  The definition simply reads
   the carried index; the theorems say that this is forced —
   [setf_cardinality A] is the unique n with [FinSet_Incl n ≅ A], it is
   constant on isomorphism classes (Cantor's reading), and it separates
   them. *)
(* NOTE ON THE NAME.  Theory/Metacategory.v:415 exports a [cardinality]
   that counts the identity arrows of a metacategory — an unrelated notion.
   The prefix here marks this one as the cardinality of an object of
   [Set_f], so the two cannot be confused. *)
Definition setf_cardinality (A : Set_f) : nat := fs_card A.

Definition setf_cardinality_iso (A : Set_f) : FinSet_Incl (setf_cardinality A) ≅ A :=
  @eso_iso FinSet Set_f FinSet_Incl FinSet_Incl_EssSurj A.

Lemma setf_cardinality_unique (A : Set_f) (n : nat) :
  FinSet_Incl n ≅ A → n = setf_cardinality A.
Proof.
  intro i.
  apply FinSet_skeletal.
  apply (@FullyFaithful FinSet Set_f FinSet_Incl
           FinSet_Incl_Full FinSet_Incl_Faithful).
  exact (iso_compose (iso_sym (setf_cardinality_iso A)) i).
Qed.

Theorem setf_cardinality_iso_invariant (A B : Set_f) :
  A ≅ B → setf_cardinality A = setf_cardinality B.
Proof.
  intro i.
  apply setf_cardinality_unique.
  exact (iso_compose i (setf_cardinality_iso A)).
Qed.

Theorem setf_cardinality_complete (A B : Set_f) :
  setf_cardinality A = setf_cardinality B → A ≅ B.
Proof.
  intro H.
  apply (iso_compose (setf_cardinality_iso B)).
  rewrite <- H.
  exact (iso_sym (setf_cardinality_iso A)).
Qed.

Corollary setf_cardinality_classifies (A B : Set_f) :
  (A ≅ B) ↔ (setf_cardinality A = setf_cardinality B).
Proof.
  split.
  - apply setf_cardinality_iso_invariant.
  - apply setf_cardinality_complete.
Qed.

(** ** The asymmetry of the two round trips *)

(* The strict side.  These three are Leibniz equalities and are genuinely
   stronger than the ≈ / ≅ statements they refine: [Card_Incl_id] compares
   the two functors only up to natural isomorphism, whereas here the
   object map and the morphism map of [Card ◯ FinSet_Incl] are the
   identity's, and the comparison cell computed by [FF_ESO_Equivalence] is
   the identity morphism itself.  All three hold by [eq_refl]. *)
Lemma Card_Incl_fobj_strict (n : FinSet) : fobj[Card ◯ FinSet_Incl] n = n.
Proof. reflexivity. Qed.

Lemma Card_Incl_fmap_strict {m n : FinSet} (f : m ~> n) :
  fmap[Card ◯ FinSet_Incl] f = f.
Proof. reflexivity. Qed.

Lemma Incl_unit_is_identity (n : FinSet) :
  to (@equivalence_unit_at FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence n)
    = id[n].
Proof. reflexivity. Qed.

(** ** Concrete objects *)

(* The non-strict side, at a concrete object.  [two_swap] has the
   canonical carrier [Fin.t 2] but carries the transposition as its chosen
   bijection, so [FinSet_Incl (Card two_swap)] and [two_swap] have the same
   underlying setoid and differ exactly in the choice. *)
Definition fin_swap2 (i : Fin.t 2) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Lemma fin_swap2_involutive (i : Fin.t 2) : fin_swap2 (fin_swap2 i) = i.
Proof.
  apply (Fin.caseS' i (fun i => fin_swap2 (fin_swap2 i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => fin_swap2 (fin_swap2 (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => fin_swap2 (fin_swap2 (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Definition fin_swap2_iso :
  @Isomorphism Sets (fin_setoid 2) (fin_setoid 2) :=
  @Build_Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
    (fin_map fin_swap2) (fin_map fin_swap2)
    fin_swap2_involutive fin_swap2_involutive.

Definition two_swap : FinSetoid := {|
  fs_obj := fin_setoid 2;
  fs_card := 2;
  fs_theta := fin_swap2_iso
|}.

Definition FinSet_swap_iso : @Isomorphism FinSet (2 : nat) (2 : nat) :=
  @Build_Isomorphism FinSet (2 : nat) (2 : nat) fin_swap2 fin_swap2
    fin_swap2_involutive fin_swap2_involutive.

Example FinSet_swap_not_identity :
  to FinSet_swap_iso ≈ @id FinSet (2 : nat) → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  discriminate H.
Qed.

(* PROJECTION, not computation: the statement is [2 = 2], so the only
   content here is that the hypothesis typechecks — that a non-identity
   isomorphism can be supplied. The inhabitation evidence proper is
   [FinSet_swap_iso] together with [FinSet_swap_not_identity]. *)
Example FinSet_skeletal_at_swap : (2 = 2)%nat :=
  FinSet_skeletal FinSet_swap_iso.

Example FinSet_one_not_iso_two :
  @Isomorphism FinSet (1 : nat) (2 : nat) → False.
Proof.
  intro i.
  apply FinSet_skeletal in i.
  discriminate i.
Qed.

(* The comparison cell at [two_swap] computes to the transposition, and
   is provably not the identity — contrast [Incl_unit_is_identity], which
   holds at EVERY object of [FinSet]. *)
Example counit_at_two_swap :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) Fin.F1 = Fin.FS Fin.F1.
Proof. reflexivity. Qed.

Example counit_at_two_swap_not_identity :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) ≈ @id Set_f two_swap → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  simpl in H.
  discriminate H.
Qed.

(* The cardinal functor at work: [two_swap] and [finset_obj 2] have the
   same underlying setoid, so the IDENTITY function is a morphism between
   them — and [# f = θ_Y ∘ f ∘ θ_X⁻¹] conjugates it into the
   transposition.  This is the conjugation formula doing something. *)
(* PROJECTION, not computation: [Card]'s object part IS [fs_card], so this
   reads off a field rather than exercising the functor. The computational
   evidence is [Card_parity_succ_F1]/[_FS] below, which run through the
   enumeration. *)
Example Card_two_swap : Card two_swap = 2%nat := eq_refl.

Example Card_conjugates_theta :
  fmap[Card] (fin_map (fun i : Fin.t 2 => i)
                : finset_obj 2 ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(* And the test behind the claim at [finset_obj]: at [two_swap], which
   carries the transposition rather than the identity, [Card] conjugates
   the constant map [fun _ => F1] into the constant map [fun _ => FS F1].
   Had the canonical objects been given a non-identity bijection, the
   [Card ◯ FinSet_Incl] round trip would move morphisms in just this way
   and could not have been strict. *)
Example Card_conjugation_moves_constant :
  fmap[Card] (fin_map (fun _ : Fin.t 2 => Fin.F1)
                : two_swap ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(* Sharper, and available here only because both sides have literally the
   same underlying setoid and index, so the two chosen bijections have the
   same type: the composite replaces the carried bijection by the identity
   one.  (This is a Leibniz equality of isomorphisms, not of morphisms;
   what it compares is carried DATA.) *)
Example Incl_Card_forgets_theta :
  fs_theta (FinSet_Incl (Card two_swap)) = fs_theta two_swap → False.
Proof.
  intro H.
  apply (f_equal (fun i : @Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
                  => to i Fin.F1)) in H.
  simpl in H.
  discriminate H.
Qed.

(** ** A finite setoid whose carrier is infinite *)

(* [nat] under equality of parity: two equivalence classes, infinitely
   many inhabitants.  It is an object of [Set_f] of cardinality 2, so
   [Set_f] is not a relabelling of [FinSet] — and the cardinal functor
   computes on it. *)
Program Definition parity_setoid : SetoidObject := {|
  carrier := nat;
  is_setoid := {| equiv := fun x y => Nat.odd x = Nat.odd y |}
|}.

Definition parity_index (i : Fin.t 2) : nat :=
  Fin.caseS' i (fun _ => nat) (0%nat) (fun _ => 1%nat).

Definition parity_enum (x : nat) : Fin.t 2 :=
  if Nat.odd x then Fin.FS Fin.F1 else Fin.F1.

Lemma parity_enum_respects (a b : nat) :
  Nat.odd a = Nat.odd b → parity_enum a = parity_enum b.
Proof. intro H; unfold parity_enum; now rewrite H. Qed.

Lemma parity_index_respects (i j : Fin.t 2) :
  i = j → Nat.odd (parity_index i) = Nat.odd (parity_index j).
Proof. intro H; now subst. Qed.

Lemma parity_to_from (i : Fin.t 2) : parity_enum (parity_index i) = i.
Proof.
  apply (Fin.caseS' i (fun i => parity_enum (parity_index i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => parity_enum (parity_index (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => parity_enum (parity_index (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Lemma parity_from_to (a : nat) :
  Nat.odd (parity_index (parity_enum a)) = Nat.odd a.
Proof.
  unfold parity_enum.
  destruct (Nat.odd a) eqn:Ha; now simpl.
Qed.

Definition parity_iso : @Isomorphism Sets parity_setoid (fin_setoid 2) :=
  @Build_Isomorphism Sets parity_setoid (fin_setoid 2)
    (setoid_map (X := parity_setoid) (Y := fin_setoid 2)
       parity_enum parity_enum_respects)
    (setoid_map (X := fin_setoid 2) (Y := parity_setoid)
       parity_index parity_index_respects)
    parity_to_from parity_from_to.

Definition parity_two : FinSetoid := {|
  fs_obj := parity_setoid;
  fs_card := 2;
  fs_theta := parity_iso
|}.

Lemma succ_respects (a b : nat) :
  Nat.odd a = Nat.odd b → Nat.odd (Datatypes.S a) = Nat.odd (Datatypes.S b).
Proof.
  intro H.
  rewrite !Nat.odd_succ, <- !Nat.negb_odd.
  now rewrite H.
Qed.

Definition parity_succ : parity_two ~{Set_f}~> parity_two :=
  setoid_map (X := parity_setoid) (Y := parity_setoid)
    Datatypes.S succ_respects.

(* The carrier is [nat]: an object of [Set_f] is finite in the setoid sense
   — finitely many EQUIVALENCE CLASSES — so its carrier type need not be. *)
(* PROJECTION: an identification of carriers, holding because [parity_two]
   was built over [parity_setoid] whose carrier is [nat]. It records that a
   two-element object may have an infinite carrier; it proves nothing about
   the finiteness witness. *)
Example parity_carrier_is_nat : carrier (fs_obj parity_two) = nat := eq_refl.

(* The round trip at [parity_two] is the identity only up to ≈: it sends 3
   to 1.  The [=] here is Leibniz equality of natural numbers and is
   therefore STRICTLY STRONGER than the ≈ of [parity_setoid], under which
   3 and 1 are equal — which is exactly why the statement has content, and
   exactly what [theta_from_to] can and cannot say. *)
Example parity_round_trip_moves_3 :
  parity_index (parity_enum 3) = 1%nat := eq_refl.

(* PROJECTION, for the same reason as [Card_two_swap]: [setf_cardinality]
   is defined as [fs_card], so this reads off the carried index. What makes
   the index CORRECT is [setf_cardinality_unique], and what computes is
   [Card_parity_succ_F1]/[_FS]. *)
Example cardinality_parity_two : setf_cardinality parity_two = 2%nat := eq_refl.

Example Card_parity_succ_F1 :
  fmap[Card] parity_succ Fin.F1 = Fin.FS Fin.F1 := eq_refl.

Example Card_parity_succ_FS :
  fmap[Card] parity_succ (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(* The counit at [parity_two], computed.  Again Leibniz equality of
   natural numbers, strictly stronger than [parity_setoid]'s ≈: the
   component does not merely land in the even class, it returns 0. *)
Example counit_at_parity_two :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence parity_two) Fin.F1 = 0%nat := eq_refl.

(** ** Bridge to the general skeleton theory *)

(* [Skeletal C] (Theory/Skeleton.v) is by definition [∀ x y, x ≅ y → x = y],
   which is exactly [FinSet_skeletal] above with its binders made explicit.
   The two were proved independently -- this file's concrete counting
   argument, and the general theory's abstract class -- so the bridge is a
   restatement, not a second proof: [FinSet] is the tree's witness that the
   [Skeletal] class is inhabited by a category whose skeletality is a real
   theorem rather than a definitional accident.

   [FinSet_Skeleton] then packages [FinSet] as a [Skeleton] of itself via
   [Skeleton_of_Skeletal]; that is the trivial route, and the non-trivial
   witness for the [Skeleton] record lives in Theory/Skeleton/Separation.v. *)

Theorem FinSet_Skeletal : Skeletal FinSet.
Proof. intros m n i; exact (FinSet_skeletal i). Qed.

Definition FinSet_Skeleton : Skeleton FinSet :=
  Skeleton_of_Skeletal FinSet_Skeletal.
