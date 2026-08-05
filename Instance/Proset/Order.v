Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

Generalizable All Variables.

(** * Preorders as thin categories: the round trip, order reversal, total
      orders, and infima as limits *)

(* Book: Mac Lane, "Categories for the Working Mathematician",
         Springer GTM 5, 2nd ed. 1998, §I.2 (construction 7, definition 4)
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.2
   Book: Fong and Spivak, "Seven Sketches in Compositionality",
         CUP 2019, §§1.2.2 and 1.3.1
   nLab: https://ncatlab.org/nlab/show/thin+category
   nLab: https://ncatlab.org/nlab/show/preorder
   nLab: https://ncatlab.org/nlab/show/total+order

   Instance/Proset.v:33 builds the thin category of a preorder; this file
   closes the circle and works out the order theory the correspondence buys.

   MAC LANE §I.2 AND ITS ROUND TRIP.  That section lists among its examples
   of categories the one attached to a preordered set: objects the elements,
   one arrow x → y for each instance of x ≤ y.  (The internal numbering used
   in the citation above — construction 7, definition 4 — is as given by the
   issue this file answers, and has not been checked against the book here;
   the section reference is the reliable part.)  Read in reverse,
   a category determines a preorder on its objects — "x ≤ y when there is an
   arrow x ~> y" — and the two passages are meant to be mutually inverse on
   thin categories.  Both legs are proved below, and both are MEASURED rather
   than asserted:

     - [hom_preorder_Proset] recovers R from [Proset P] up to pointwise
       logical equivalence, not up to equality of relations.  The gap is
       exactly Coq's Prop/Type divide: Structure/Thin.v's [hom_preorder]
       squashes the hom into [inhabited], and [inhabited (R x y)] is not the
       same term as [R x y].  [hom_preorder_Proset_eq] then shows that
       propositional and functional extensionality — taken as explicit
       hypotheses, so that no axiom enters the development — close the gap
       to an honest equality.

     - [thin_Proset_iso] gives the other leg as an isomorphism in [Cat].
       Instance/Cat.v:28-30 discloses that its [Functor_Setoid] identifies
       functors up to natural isomorphism, so an isomorphism there is only an
       EQUIVALENCE of categories.  More than that is proved, and recorded
       separately so the extra strength is checkable rather than asserted:
       [thin_Proset_iso_obj] shows both functors are the identity on objects
       definitionally, and [thin_Proset_roundtrip_hom] with
       [Proset_thin_roundtrip_hom] show their morphism actions invert each
       other up to `≈`.  That is an identity-on-objects isomorphism in the
       setoid sense the library uses everywhere.  It is NOT an equality of
       functors, and it is weaker than the [eq_refl]-level inverse pair the
       order-reversal isomorphism below achieves.

     - The backward functor needs [HomChoice] — an arrow produced from the
       bare fact that one exists.  It is taken as an explicit hypothesis
       (Structure/Thin.v), and it costs nothing where it is actually wanted:
       [proset_HomChoice] discharges it for every [Proset], whose homs are
       already Props, so [Proset_roundtrip] is hypothesis-free.  Separately,
       [hom_Proset_Faithful_iff_Thin] pins the role of thinness exactly: the
       forward functor is faithful precisely when the category is thin.

   ORDER REVERSAL (Riehl §1.2).  The opposite of the thin category of P is
   the thin category of the reversed order.  Here the two categories have
   CONVERTIBLE objects and homs, so [Proset_op_iso] is an isomorphism whose
   two morphism actions are mutually inverse by [eq_refl] — see
   [Proset_op_roundtrip] and [Proset_op_hom].  This is much stronger than the
   equivalence that `≅[Cat]` records, and stronger than the round trip above.
   The reversed preorder is stdlib's [Basics.flip] with stdlib's
   [flip_PreOrder] instance; nothing needed constructing.

   SEVEN SKETCHES §1.2.2.  Four items from that section are settled here.
   The axiom comparison — every [Equivalence] is a [PreOrder], and a
   symmetric [PreOrder] is an [Equivalence] — is [Equivalence_is_PreOrder]
   and [PreOrder_Symmetric_is_Equivalence].  The first direction already
   exists in stdlib as [Equivalence_PreOrder] and is re-derived here only so
   that both halves stand side by side over one carrier and one relation; for
   the second, a [Search] over the modules this file loads returns no stdlib
   lemma of that shape.  The discrete and codiscrete preorders on
   an arbitrary carrier are [discrete_rel] and [codiscrete_rel], with
   [codiscrete_terminal] and [discrete_initial] locating them as the top and
   the bottom of the preorder structures on a fixed carrier under refinement
   (the identity map being monotone), each characterized uniquely up to
   mutual refinement.  Comparability is [comparable], distinguished from
   decidability by three theorems rather than by a remark.  And a total order
   is a preorder in which every two elements are comparable
   ([TotalOrder_iff_all_comparable]).

   SEVEN SKETCHES §1.3.1.  Infimum and supremum are introduced under their
   order-theoretic names and identified with the limit and the colimit of the
   two-object discrete diagram: [infimum_iff_limit] and
   [supremum_iff_colimit], stated over Structure/Limit.v:129's [IsALimit] and
   Instance/Discrete.v:37's [DiscreteCat] on [bool].  Instance/Poset.v:50-51
   announces the dictionary entry as prose ("a product is a meet, and more
   generally the limit over a subset is its greatest lower bound"); these two
   theorems prove it at the two-object shape, for an ARBITRARY preorder.  The
   tree does already contain one instance of the identification — the
   cartesian structure on the walking arrow, whose product object is
   Instance/Two/Monoidal.v:37's [two_meet] fed to [Two_Cartesian] at :80 —
   but that is a single fixed two-element order presented as a [Cartesian]
   instance rather than as a limit over a discrete diagram.

   SCOPE NOTE on the general identification lemma.  The library contains no
   thin-category-wide "a limit is a meet" lemma: a case-insensitive search of
   every .v file for [infimum], [supremum], "greatest lower" and "least
   upper" returns exactly one hit, the prose of Instance/Poset.v:51.  The
   general lemma is tracked as issue #737, which has not landed at the time
   of writing.  The two theorems below are therefore
   proved DIRECTLY, at the two-object discrete shape, over an arbitrary
   preorder (totality is not needed for the identification — only for
   existence, which is [TotalOrder_meet] and [TotalOrder_join]).  When the
   general lemma lands, these become its specialization; until then they
   stand on their own and depend on nothing that does not exist.

   WHAT IS NOT CLAIMED.  The correspondence proved here is between preorders
   and thin categories one object-set at a time.  It is not lifted to an
   equivalence between a category of preorders and a category of thin
   categories, and no adjunction between [Proset] and [hom_preorder] is
   stated.  The morphism leg of the correspondence already exists in another
   guise: Construction/Enriched/Two.v:175-215 identifies enriched functors
   between preorders enriched in the walking arrow with monotone maps. *)

(** ** Thinness of prosets and posets *)

(* Instance/Proset.v:39 declares the hom-setoid equivalence of a proset to be
   [True], so thinness holds by the unit constructor.  This is the bridge
   between Instance/Proset.v's construction and Structure/Thin.v's predicate,
   in the same relation as Instance/Discrete.v's [DiscreteCat_Discrete] to
   Structure/Discrete.v:28. *)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R) :
  Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(* A poset is a proset with antisymmetry imposed, and Instance/Poset.v:117
   defines it as literally [Proset P], so the thin category is the same
   object; antisymmetry constrains the OBJECTS (making the category skeletal,
   Instance/Poset.v:20), not the homs. *)
Lemma Poset_is_Proset {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P H = Proset P.
Proof. reflexivity. Qed.

Lemma poset_thin {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) :
  Thin (@Poset A R P H).
Proof. exact (proset_thin P). Qed.

(* Antisymmetry is exactly skeletality of the thin category: mutually related
   objects are isomorphic by [thin_iso], and antisymmetry forces them equal. *)
Lemma poset_skeletal {A : Type} {R : relation A} (P : PreOrder R)
      (H : @Antisymmetric A eq eq_equiv R) (x y : A) :
  x ≅[@Poset A R P H] y → x = y.
Proof. intro i; exact (H x y (to i) (from i)). Qed.

(** ** Round trip, leg one: the preorder of the thin category of P is P *)

(* Recovery up to pointwise logical equivalence.  Note this is [iffT] (the
   library rebinds `↔`, Lib/Foundation.v:72), so the two directions carry
   computational content: forward eliminates the [inhabited] witness (legal,
   since the goal [R x y] is itself a Prop), backward is [inhabits]. *)
Theorem hom_preorder_Proset {A : Type} {R : relation A} (P : PreOrder R)
        (x y : A) :
  hom_preorder (Proset P) x y ↔ R x y.
Proof.
  split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(* Measuring the gap.  The recovery above is NOT an equality of relations:
   [hom_preorder (Proset P)] is the relation [fun x y => inhabited (R x y)],
   a different term from [R].  Under propositional and functional
   extensionality it becomes one, and both are taken here as explicit
   hypotheses of the lemma — nothing is assumed globally, and
   [Print Assumptions] on this constant stays clean. *)
Theorem hom_preorder_Proset_eq {A : Type} {R : relation A} (P : PreOrder R)
        (prop_ext : ∀ p q : Prop, (p <-> q) → p = q)
        (fun_ext : ∀ f g : A → A → Prop, (∀ x y : A, f x y = g x y) → f = g) :
  hom_preorder (Proset P) = R.
Proof.
  apply fun_ext; intros x y.
  apply prop_ext; split.
  - intro H; destruct H as [r]; exact r.
  - exact (fun r => inhabits r).
Qed.

(** ** Round trip, leg two: the thin category of the hom-preorder *)

(* The comparison functor, defined for an ARBITRARY category: identity on
   objects, sending an arrow to the fact that it exists.  Every obligation is
   an equation in the target hom-setoid, which Instance/Proset.v:39 declares
   to be [True]. *)
Program Definition hom_Proset_Functor (C : Category) :
  C ⟶ Proset (hom_PreOrder C) := {|
  fobj := fun x => x;
  fmap := fun x y f => inhabits f
|}.

(* Thinness is exactly the faithfulness of that comparison.  Forward: the
   hypothesis of [fmap_inj] is an equation in the trivial setoid, so it is
   free, and its conclusion is thinness.  Backward: immediate. *)
Theorem hom_Proset_Faithful_iff_Thin (C : Category) :
  Faithful (hom_Proset_Functor C) ↔ Thin C.
Proof.
  split.
  - intros F x y f g.
    destruct F as [inj].
    exact (inj x y f g I).
  - intro T.
    constructor; intros x y f g _; apply T.
Qed.

(* On a proset the choice hypothesis of Structure/Thin.v is discharged: the
   homs of [Proset P] are the Props [R x y], so eliminating [inhabited] lands
   back in Prop and is permitted. *)
Definition proset_HomChoice {A : Type} {R : relation A} (P : PreOrder R) :
  HomChoice (Proset P) :=
  fun x y h => match h return R x y with inhabits r => r end.

(* The backward comparison functor, for a thin C with a choice of arrows.
   [fmap_respects] holds because any two chosen arrows are parallel, and the
   two functor laws because their two sides are parallel; all three are
   [Thin C]. *)
Program Definition Proset_hom_Functor {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  Proset (hom_PreOrder C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y h => ch x y h
|}.

(* The isomorphism in [Cat].  Both composites are the identity on objects, and
   every `≈` involved is an equation between parallel arrows of a thin
   category, so the natural-isomorphism data [Functor_Setoid]
   (Theory/Functor.v:148) asks for is discharged by the [cat_simpl] obligation
   tactic. *)
Program Definition thin_Proset_iso {C : Category}
        (T : Thin C) (ch : HomChoice C) :
  C ≅[Cat] Proset (hom_PreOrder C) := {|
  to   := hom_Proset_Functor C;
  from := Proset_hom_Functor T ch
|}.

(** *** Measuring the strength of that isomorphism

    Instance/Cat.v:28-30 records that `≅[Cat]` means equivalence of
    categories, because [Functor_Setoid] compares functors up to natural
    isomorphism.  The three facts below say more: the comparison is the
    identity on objects on the nose, and the two morphism actions invert each
    other up to `≈`. *)

Lemma thin_Proset_iso_obj {C : Category} (T : Thin C) (ch : HomChoice C)
      (x : C) :
  (fobj[hom_Proset_Functor C] x = x) ∧
  (fobj[Proset_hom_Functor T ch] x = x).
Proof. split; reflexivity. Qed.

Lemma thin_Proset_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (f : x ~> y) :
  fmap[Proset_hom_Functor T ch] (fmap[hom_Proset_Functor C] f) ≈ f.
Proof. apply T. Qed.

Lemma Proset_thin_roundtrip_hom {C : Category} (T : Thin C) (ch : HomChoice C)
      {x y : C} (h : x ~{Proset (hom_PreOrder C)}~> y) :
  fmap[hom_Proset_Functor C] (fmap[Proset_hom_Functor T ch] h) ≈ h.
Proof. exact I. Qed.

(* The hypothesis-free corollary: a proset is recovered from its own
   hom-preorder, with [proset_HomChoice] supplying the only hypothesis and
   [proset_thin] the other. *)
Definition Proset_roundtrip {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ≅[Cat] Proset (hom_PreOrder (Proset P)) :=
  thin_Proset_iso (proset_thin P) (proset_HomChoice P).

(** ** Order reversal: the opposite of a thin category (Riehl §1.2) *)

(* The reversed preorder is stdlib's [Basics.flip] with stdlib's
   [flip_PreOrder]; both already exist, so nothing is defined here.  The two
   categories below have convertible objects and convertible homs — the first
   because Construction/Opposite.v:106 keeps [obj] and the second because it
   sets hom[C^op] x y := hom[C] y x, which for a proset is [R y x], which is
   [Basics.flip R x y] by delta. *)

Lemma Proset_op_obj {A : Type} {R : relation A} (P : PreOrder R) :
  obj[(Proset P)^op] = obj[Proset (flip_PreOrder P)].
Proof. reflexivity. Qed.

Lemma Proset_op_hom {A : Type} {R : relation A} (P : PreOrder R) (x y : A) :
  (x ~{(Proset P)^op}~> y) = (x ~{Proset (flip_PreOrder P)}~> y).
Proof. reflexivity. Qed.

Program Definition Proset_op_to {A : Type} {R : relation A} (P : PreOrder R) :
  (Proset P)^op ⟶ Proset (flip_PreOrder P) := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

Program Definition Proset_op_from {A : Type} {R : relation A}
        (P : PreOrder R) :
  Proset (flip_PreOrder P) ⟶ (Proset P)^op := {|
  fobj := fun x => x;
  fmap := fun x y f => f
|}.

(* Both round trips on morphisms hold by [eq_refl] — not merely up to `≈`.
   Together with the identity object maps that makes [Proset_op_iso] below an
   isomorphism of categories in the textbook sense (a bijection on objects and
   on each hom), rather than only the equivalence that `≅[Cat]` on its own
   records (Instance/Cat.v:28-30).  What is NOT claimed is equality of the
   composite functors with [Id]: their [fobj] and [fmap] agree with [Id]'s by
   [eq_refl], but their law fields are the opaque obligation constants
   [Program] generated, which are not [eq_refl]-equal to [Id]'s. *)

Lemma Proset_op_roundtrip {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{(Proset P)^op}~> y) :
  fmap[Proset_op_from P] (fmap[Proset_op_to P] f) = f.
Proof. reflexivity. Qed.

Lemma Proset_op_roundtrip' {A : Type} {R : relation A} (P : PreOrder R)
      (x y : A) (f : x ~{Proset (flip_PreOrder P)}~> y) :
  fmap[Proset_op_to P] (fmap[Proset_op_from P] f) = f.
Proof. reflexivity. Qed.

Program Definition Proset_op_iso {A : Type} {R : relation A}
        (P : PreOrder R) :
  ((Proset P)^op)%category ≅[Cat] Proset (flip_PreOrder P) := {|
  to   := Proset_op_to P;
  from := Proset_op_from P
|}.

(** ** Preorders versus equivalence relations (Seven Sketches §1.2.2) *)

(* Dropping symmetry from an equivalence relation leaves a preorder; adding
   it back to a preorder restores an equivalence relation.  The first
   direction duplicates stdlib's [Equivalence_PreOrder]; it is restated so
   that the pair reads as one comparison over a fixed carrier and relation.
   For the second, [Search Symmetric PreOrder Equivalence] over the modules
   this file loads returns nothing from stdlib. *)

Lemma Equivalence_is_PreOrder {A : Type} (R : relation A) :
  Equivalence R → PreOrder R.
Proof.
  intro E; constructor.
  - exact (@Equivalence_Reflexive A R E).
  - exact (@Equivalence_Transitive A R E).
Qed.

Lemma PreOrder_Symmetric_is_Equivalence {A : Type} (R : relation A) :
  PreOrder R → Symmetric R → Equivalence R.
Proof.
  intros P S; constructor.
  - exact (@PreOrder_Reflexive A R P).
  - exact S.
  - exact (@PreOrder_Transitive A R P).
Qed.

(** ** The discrete and codiscrete preorders on a carrier (§1.2.2) *)

(* The two extreme preorder structures on an arbitrary [Type]: equality, and
   the relation that always holds.  [discrete_rel] is the order-theoretic
   shadow of Instance/Discrete.v:37's [DiscreteCat] (whose homs are exactly
   equality proofs); [codiscrete_rel] is the shadow of the codiscrete
   category, which Structure/Discrete.v's header mentions as the other
   adjoint. *)

Definition discrete_rel (A : Type) : relation A := fun x y => x = y.

Definition codiscrete_rel (A : Type) : relation A := fun _ _ => True.

Definition discrete_PreOrder (A : Type) : PreOrder (discrete_rel A).
Proof.
  constructor.
  - intro x; reflexivity.
  - intros x y z Hxy Hyz; exact (eq_trans Hxy Hyz).
Defined.

Definition codiscrete_PreOrder (A : Type) : PreOrder (codiscrete_rel A).
Proof. constructor; [ intro x; exact I | intros x y z _ _; exact I ]. Defined.

(* "Terminal", made precise.  Preorder structures on a FIXED carrier are
   compared by refinement: R refines S when the identity map on the carrier
   is monotone from R to S, i.e. when every R-instance is an S-instance.
   [codiscrete_rel] is a top for this comparison, and any other top agrees
   with it; [discrete_rel] is a bottom among REFLEXIVE relations, and any
   other such bottom agrees with it.  This is deliberately a statement about
   preorder structures on ONE fixed carrier.  Whether the codiscrete category
   is also terminal in [Cat] is a different question and is left open here —
   Instance/Cat.v:28-30's `≅` compares functors up to natural isomorphism, and
   [codiscrete_all_iso] below shows every pair of objects of the codiscrete
   category is isomorphic, which makes that question subtler than it looks. *)

Definition Refines {A : Type} (R S : relation A) : Prop :=
  ∀ x y : A, R x y → S x y.

Theorem codiscrete_terminal {A : Type} (R : relation A) :
  Refines R (codiscrete_rel A).
Proof. intros x y _; exact I. Qed.

Theorem codiscrete_terminal_unique {A : Type} (S : relation A) :
  (∀ R : relation A, Refines R S) → ∀ x y : A, S x y <-> codiscrete_rel A x y.
Proof.
  intros top x y; split.
  - intro; exact I.
  - exact (top (codiscrete_rel A) x y).
Qed.

Theorem discrete_initial {A : Type} (R : relation A) :
  Reflexive R → Refines (discrete_rel A) R.
Proof. intros refl x y e; destruct e; exact (refl x). Qed.

Theorem discrete_initial_unique {A : Type} (S : relation A) :
  Reflexive S →
  (∀ R : relation A, Reflexive R → Refines S R) →
  ∀ x y : A, S x y <-> discrete_rel A x y.
Proof.
  intros refl bot x y; split.
  - exact (bot (discrete_rel A) (fun z => eq_refl) x y).
  - exact (discrete_initial S refl x y).
Qed.

(* The categorical reading of the top: from every proset on A there is an
   identity-on-objects functor into the codiscrete one, because every arrow
   has somewhere to go. *)
Program Definition to_codiscrete {A : Type} {R : relation A} (P : PreOrder R) :
  Proset P ⟶ Proset (codiscrete_PreOrder A) := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => I
|}.

(* And why the codiscrete preorder is as far from a poset as possible: all
   its objects are isomorphic, so it is skeletal only when A is a
   subsingleton. *)
Lemma codiscrete_all_iso {A : Type} (x y : A) :
  x ≅[Proset (codiscrete_PreOrder A)] y.
Proof. exact (thin_iso (proset_thin (codiscrete_PreOrder A)) I I). Qed.

(** ** Comparability, and how it differs from decidability (§1.2.2) *)

(* Two elements are comparable when the order relates them one way or the
   other AND the witness records which way: `∨` is Lib/Foundation.v:79's
   notation for [sum], so [comparable] is Type-valued and can be matched on
   to compute.  That is the whole point — [TotalOrder_meet] below builds the
   binary infimum by dispatching on it.

   Comparability is NOT decidability.  Decidability of R at (x, y) settles
   [R x y] one way or the other; comparability settles which of [R x y] and
   [R y x] holds but says nothing about the negation of either, and the two
   are only related through extra data.  Three theorems below measure the
   distinction instead of describing it: [comparable_of_decidable_total]
   builds comparability from decidability plus Prop-valued totality (the
   [\/] can be eliminated because the goal it feeds is itself a Prop);
   [comparable_total] extracts Prop-valued totality back; and
   [decidable_of_comparable] exhibits a sufficient route from comparability to
   decidability, which needs reflexivity, antisymmetry AND a decision
   procedure for equality on the carrier — strictly more input than
   comparability alone.  (Those three are shown sufficient, not necessary.)
   Construction/Enriched/Two.v:65's [tpre_dec] is the
   decidability side of the same coin: that file needs to COMPUTE a truth
   value in the walking arrow for every pair, which comparability alone
   would not supply. *)

Definition comparable {A : Type} (R : relation A) (x y : A) : Type :=
  R x y ∨ R y x.

Definition decidable_rel {A : Type} (R : relation A) : Type :=
  ∀ x y : A, R x y ∨ ¬ R x y.

Lemma comparable_of_decidable_total {A : Type} (R : relation A) :
  decidable_rel R → (∀ x y : A, R x y \/ R y x) →
  ∀ x y : A, comparable R x y.
Proof.
  intros dec tot x y.
  destruct (dec x y) as [h|n].
  - exact (inl h).
  - right.
    destruct (tot x y) as [h|h].
    + contradiction.
    + exact h.
Qed.

Lemma comparable_total {A : Type} (R : relation A) (x y : A) :
  comparable R x y → R x y \/ R y x.
Proof. intros [h|h]; [ left | right ]; exact h. Qed.

Lemma decidable_of_comparable {A : Type} (R : relation A) :
  Reflexive R →
  (∀ x y : A, R x y → R y x → x = y) →
  (∀ x y : A, (x = y) ∨ ¬ (x = y)) →
  (∀ x y : A, comparable R x y) →
  decidable_rel R.
Proof.
  intros refl anti eqdec cmp x y.
  destruct (cmp x y) as [h|h].
  - exact (inl h).
  - destruct (eqdec x y) as [e|ne].
    + destruct e; exact (inl (refl x)).
    + right; intro hxy; exact (ne (anti x y hxy h)).
Qed.

(* In a discrete preorder an element is comparable with itself and with
   nothing else (§1.2.2): the only arrows are the identities. *)

Lemma discrete_comparable_self {A : Type} (x : A) :
  comparable (discrete_rel A) x x.
Proof. exact (inl eq_refl). Qed.

Lemma discrete_incomparable {A : Type} (x y : A) :
  x ≠ y → comparable (discrete_rel A) x y → False.
Proof. intros ne [e|e]; [ exact (ne e) | exact (ne (eq_sym e)) ]. Qed.

(** ** Total (linear) orders, Mac Lane §I.2 definition 4 *)

(* A total order is a preorder that is antisymmetric and in which every two
   elements are comparable.  The class is [Type]-valued because
   [total_comparable] is: a Prop-valued totality would not let the meet below
   be computed.  Antisymmetry is stated in the elementary form and converted
   to Instance/Poset.v's [Antisymmetric] shape by [TotalOrder_Antisymmetric],
   so that the thin category is built by Instance/Poset.v:116's [Poset]
   rather than by a fresh construction. *)

Class TotalOrder {A : Type} (R : relation A) : Type := {
  total_preorder   : PreOrder R;
  total_antisym    : ∀ x y : A, R x y → R y x → x = y;
  total_comparable : ∀ x y : A, comparable R x y
}.

Definition TotalOrder_Antisymmetric {A : Type} {R : relation A}
           (T : TotalOrder R) : @Antisymmetric A eq eq_equiv R :=
  @total_antisym A R T.

Definition TotalOrder_Category {A : Type} {R : relation A}
           (T : TotalOrder R) : Category :=
  @Poset A R (@total_preorder A R T) (TotalOrder_Antisymmetric T).

Lemma TotalOrder_Category_thin {A : Type} {R : relation A} (T : TotalOrder R) :
  Thin (TotalOrder_Category T).
Proof. exact (proset_thin (@total_preorder A R T)). Qed.

(* The characterization asked for in §1.2.2: over a fixed antisymmetric
   preorder, being a total order IS "every two elements are comparable". *)
Theorem TotalOrder_iff_all_comparable {A : Type} (R : relation A)
        (P : PreOrder R) (anti : ∀ x y : A, R x y → R y x → x = y) :
  TotalOrder R ↔ (∀ x y : A, comparable R x y).
Proof.
  split.
  - exact (fun T => @total_comparable A R T).
  - intro cmp.
    exact {| total_preorder := P
           ; total_antisym := anti
           ; total_comparable := cmp |}.
Qed.

(** *** (ℕ, ≤) as a total order, and its reverse *)

Definition nat_TotalOrder : TotalOrder PeanoNat.Nat.le := {|
  total_preorder   := PeanoNat.Nat.le_preorder;
  total_antisym    := partial_order_antisym PeanoNat.Nat.le_partialorder;
  total_comparable := fun x y =>
    match le_ge_dec x y with
    | left  h => inl h
    | right h => inr h
    end
|}.

(* The thin category of (ℕ, ≤).  Instance/Proset.v:47 and Instance/Poset.v:120
   both already export a [LessThanEqualTo_Category] for this order (a clash
   Test/Poset.v:35-41 documents), so no third name is introduced; this one is
   built through [TotalOrder_Category] to exercise the class. *)
Definition Nat_TotalOrder_Category : Category :=
  TotalOrder_Category nat_TotalOrder.

(* The reverse of (ℕ, ≤) is (ℕ, ≥) on the nose: stdlib defines [ge n m] as
   [m <= n], and [Basics.flip le x y] reduces to [le y x], so the two
   relations are convertible. *)
Lemma flip_le_is_ge (x y : nat) :
  Basics.flip PeanoNat.Nat.le x y = ge x y.
Proof. reflexivity. Qed.

(* Hence the opposite of the thin category of (ℕ, ≤) is the thin category of
   (ℕ, ≥), by the general order-reversal isomorphism above. *)
Definition Nat_op_iso :
  ((Proset PeanoNat.Nat.le_preorder)^op)%category
    ≅[Cat] Proset (flip_PreOrder PeanoNat.Nat.le_preorder) :=
  Proset_op_iso PeanoNat.Nat.le_preorder.

(* And the reversed order is itself a total order, so the opposite category
   is again the thin category of a total order. *)
Definition flip_TotalOrder {A : Type} {R : relation A} (T : TotalOrder R) :
  TotalOrder (Basics.flip R) := {|
  total_preorder   := flip_PreOrder (@total_preorder A R T);
  total_antisym    := fun x y hxy hyx => @total_antisym A R T x y hyx hxy;
  total_comparable := fun x y =>
    match @total_comparable A R T x y with
    | inl h => inr h
    | inr h => inl h
    end
|}.

Definition nat_ge_TotalOrder : TotalOrder (Basics.flip PeanoNat.Nat.le) :=
  flip_TotalOrder nat_TotalOrder.

(** ** Infima and suprema, and their categorical identification (§1.3.1) *)

(* Order-theoretic names first: m is an infimum (greatest lower bound) of x
   and y when it is a lower bound and dominates every lower bound.  The
   connectives are Lib/Foundation.v:78-79's, so these are [Type]-valued;
   nothing is eliminated from Prop into Type, the Prop components are only
   carried. *)

Definition IsInfimum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R m x ∧ R m y) ∧ (∀ n : A, R n x → R n y → R n m).

Definition IsSupremum {A : Type} (R : relation A) (x y m : A) : Type :=
  (R x m ∧ R y m) ∧ (∀ n : A, R x n → R y n → R m n).

(* The two notions are one notion read in two directions, and the identity is
   definitional, not merely provable. *)
Lemma supremum_is_flipped_infimum {A : Type} (R : relation A) (x y m : A) :
  IsSupremum R x y m = IsInfimum (Basics.flip R) x y m.
Proof. reflexivity. Qed.

(* The two-object discrete diagram in the thin category of P, picking out x
   at [false] and y at [true].  Instance/Discrete.v:52's [DiscreteCat_Functor]
   turns any function out of a [Type] into a functor out of the discrete
   category on it. *)
Definition PairDiagram {A : Type} {R : relation A} (P : PreOrder R)
           (x y : A) : DiscreteCat bool ⟶ Proset P :=
  DiscreteCat_Functor (C:=Proset P) (fun b : bool => if b then y else x).

(* A lower bound of x and y IS a cone over the pair diagram (Structure/Cone.v
   :24 for the legs, :51 for the bundle with an apex), and an upper bound IS a
   COCONE over it — which Structure/Cone.v:72 defines as a cone over the
   opposed diagram, exactly the type written below.  These two constructors
   are separated out so that the mediating arrow supplied by [ump_limit] has
   an apex Coq can see is [n]. *)

Definition pair_cone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (lx : R n x) (ly : R n y) : Cone (PairDiagram P x y).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact ly | exact lx ].
  - intros b b' f; exact I.
Defined.

Definition pair_cocone {A : Type} {R : relation A} (P : PreOrder R)
           (x y n : A) (ux : R x n) (uy : R y n) :
  Cone ((PairDiagram P x y)^op).
Proof.
  unshelve econstructor.
  { exact n. }
  unshelve econstructor.
  - intro b; destruct b; [ exact uy | exact ux ].
  - intros b b' f; exact I.
Defined.

(* THE IDENTIFICATION.  Being an infimum of x and y is being a limit of that
   diagram, with the apex pinned (Structure/Limit.v:129's [IsALimit]).  Note
   what each half costs.  Building the limit needs: the two legs (the lower
   bound), cone coherence (an equation in the trivial hom-setoid, hence
   free), the mediating arrow (the greatest-lower-bound clause), and its
   uniqueness (again free, by thinness).  Reading the limit back needs only
   the legs and the mediator.  Totality is nowhere used — this holds over an
   arbitrary preorder. *)
Theorem infimum_iff_limit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsInfimum R x y m ↔ IsALimit (PairDiagram P x y) m.
Proof.
  split.
  - intros [[lx ly] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact ly | exact lx ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n lx ly.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cone P x y n lx ly))).
Qed.

(* The dual identification.  Structure/Limit.v:158 defines a colimit of F as a
   limit of F^op, so the apex-pinned colimit of the pair diagram is
   [IsALimit ((PairDiagram P x y)^op) m]; unfolding, its legs are arrows
   x ~> m and y ~> m of [Proset P], i.e. upper bounds, and its mediator is
   the least-upper-bound clause. *)
Theorem supremum_iff_colimit {A : Type} {R : relation A} (P : PreOrder R)
        (x y m : A) :
  IsSupremum R x y m ↔ IsALimit ((PairDiagram P x y)^op) m.
Proof.
  split.
  - intros [[ux uy] med].
    unshelve refine {| limit_acone := _ |}.
    + unshelve refine {| vertex_map := _ |}.
      * intro b; destruct b; [ exact uy | exact ux ].
      * intros b b' f; exact I.
    + intro N.
      unshelve refine {| unique_obj := _ |}.
      * exact (med (vertex_obj[N])
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) false)
                 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) true)).
      * intro b; exact I.
      * intros v _; exact I.
  - intro L.
    split.
    + split.
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) false).
      * exact (@vertex_map _ _ _ _ (@limit_acone _ _ _ _ L) true).
    + intros n ux uy.
      exact (unique_obj (@ump_limit _ _ _ _ L (pair_cocone P x y n ux uy))).
Qed.

(** *** Existence in a total order

    The identification above needs no totality; EXISTENCE does.  In a total
    order the meet of x and y is whichever of the two is below the other,
    which is exactly what the Type-valued [comparable] lets us compute. *)

Definition tmeet {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => x
  | inr _ => y
  end.

Definition tjoin {A : Type} {R : relation A} (T : TotalOrder R) (x y : A) : A :=
  match @total_comparable A R T x y with
  | inl _ => y
  | inr _ => x
  end.

Theorem TotalOrder_meet {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsInfimum R x y (tmeet T x y).
Proof.
  unfold tmeet.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n lx ly; exact lx.
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n lx ly; exact ly.
Qed.

Theorem TotalOrder_join {A : Type} {R : relation A} (T : TotalOrder R)
        (x y : A) : IsSupremum R x y (tjoin T x y).
Proof.
  unfold tjoin.
  destruct (@total_comparable A R T x y) as [h|h].
  - split; [ split | ].
    + exact h.
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) y).
    + intros n ux uy; exact uy.
  - split; [ split | ].
    + exact (@PreOrder_Reflexive A R (@total_preorder A R T) x).
    + exact h.
    + intros n ux uy; exact ux.
Qed.

(* Combining the two: the thin category of a total order has a limit and a
   colimit for every two-object discrete diagram. *)

Definition TotalOrder_pair_limit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit (PairDiagram (@total_preorder A R T) x y) (tmeet T x y) :=
  fst (infimum_iff_limit (@total_preorder A R T) x y (tmeet T x y))
      (TotalOrder_meet T x y).

Definition TotalOrder_pair_colimit {A : Type} {R : relation A}
           (T : TotalOrder R) (x y : A) :
  IsALimit ((PairDiagram (@total_preorder A R T) x y)^op) (tjoin T x y) :=
  fst (supremum_iff_colimit (@total_preorder A R T) x y (tjoin T x y))
      (TotalOrder_join T x y).

(** *** Worked instance: (ℕ, ≤), with min and max *)

Theorem nat_min_infimum (x y : nat) :
  IsInfimum PeanoNat.Nat.le x y (PeanoNat.Nat.min x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_min_l x y).
  - exact (PeanoNat.Nat.le_min_r x y).
  - intros n lx ly; exact (PeanoNat.Nat.min_glb x y n lx ly).
Qed.

Theorem nat_max_supremum (x y : nat) :
  IsSupremum PeanoNat.Nat.le x y (PeanoNat.Nat.max x y).
Proof.
  split; [ split | ].
  - exact (PeanoNat.Nat.le_max_l x y).
  - exact (PeanoNat.Nat.le_max_r x y).
  - intros n ux uy; exact (PeanoNat.Nat.max_lub x y n ux uy).
Qed.

Definition nat_min_limit (x y : nat) :
  IsALimit (PairDiagram PeanoNat.Nat.le_preorder x y) (PeanoNat.Nat.min x y) :=
  fst (infimum_iff_limit PeanoNat.Nat.le_preorder x y (PeanoNat.Nat.min x y))
      (nat_min_infimum x y).

Definition nat_max_colimit (x y : nat) :
  IsALimit ((PairDiagram PeanoNat.Nat.le_preorder x y)^op)
           (PeanoNat.Nat.max x y) :=
  fst (supremum_iff_colimit PeanoNat.Nat.le_preorder x y
         (PeanoNat.Nat.max x y))
      (nat_max_supremum x y).

(** *** Worked instance: the two-element order

    The smallest order in which the identification has content: [false] below
    [true], with conjunction the meet and disjunction the join. *)

Definition bool_le (x y : bool) : Prop := x = true → y = true.

Definition bool_PreOrder : PreOrder bool_le.
Proof.
  constructor.
  - intros x h; exact h.
  - intros x y z Hxy Hyz h; exact (Hyz (Hxy h)).
Defined.

Definition bool_TotalOrder : TotalOrder bool_le.
Proof.
  unshelve refine {| total_preorder := bool_PreOrder |}.
  - intros x y Hxy Hyx.
    destruct x, y; try reflexivity.
    + symmetry; exact (Hxy eq_refl).
    + exact (Hyx eq_refl).
  - intros x y.
    destruct x.
    + right; intro h; reflexivity.
    + left; intro h; discriminate h.
Defined.

Theorem bool_andb_infimum (x y : bool) :
  IsInfimum bool_le x y (andb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n lx ly h; destruct x, y; simpl;
      solve [ reflexivity | exact (lx h) | exact (ly h) ].
Qed.

Theorem bool_orb_supremum (x y : bool) :
  IsSupremum bool_le x y (orb x y).
Proof.
  split; [ split | ].
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - destruct x, y; simpl; intro h; try reflexivity; exact h.
  - intros n ux uy h; destruct x, y; simpl in *;
      solve [ reflexivity | exact (ux h) | exact (uy h) | discriminate h ].
Qed.

Definition bool_andb_limit (x y : bool) :
  IsALimit (PairDiagram bool_PreOrder x y) (andb x y) :=
  fst (infimum_iff_limit bool_PreOrder x y (andb x y)) (bool_andb_infimum x y).

Definition bool_orb_colimit (x y : bool) :
  IsALimit ((PairDiagram bool_PreOrder x y)^op) (orb x y) :=
  fst (supremum_iff_colimit bool_PreOrder x y (orb x y))
      (bool_orb_supremum x y).

(* The two-element order is a poset, so its thin category is skeletal; and
   the meet computed by the class matches the boolean conjunction. *)

Example bool_tmeet_true_false : tmeet bool_TotalOrder true false = false.
Proof. reflexivity. Qed.

Example bool_tjoin_true_false : tjoin bool_TotalOrder true false = true.
Proof. reflexivity. Qed.

(** ** Sanity: what the constructions reduce to

    Each of these holds by [eq_refl], so together they pin down that nothing
    above is stated at one remove from the concrete objects it is about.
    Numerals carry [%nat] because Lib/Foundation.v:9 closes [nat_scope]. *)

(* The thin category of a total order has the carrier as its objects and the
   order itself as its homs. *)
Example nat_order_obj : obj[Nat_TotalOrder_Category] = nat.
Proof. reflexivity. Qed.

Example nat_order_hom (x y : nat) :
  (x ~{Nat_TotalOrder_Category}~> y) = PeanoNat.Nat.le x y.
Proof. reflexivity. Qed.

(* Box: the reverse order, concretely.  Reading an arrow of the OPPOSITE thin
   category as a proposition gives [ge] on the nose — this is
   [flip_le_is_ge] seen through Construction/Opposite.v:106's hom reversal,
   and it is what [Nat_op_iso] packages as an isomorphism of categories. *)
Example nat_op_hom_is_ge (x y : nat) :
  (x ~{((Proset PeanoNat.Nat.le_preorder)^op)%category}~> y) = ge x y.
Proof. reflexivity. Qed.

(* The meet of a total order computes. *)
Example nat_tmeet_3_5 : tmeet nat_TotalOrder 3%nat 5%nat = 3%nat.
Proof. reflexivity. Qed.

Example nat_tjoin_3_5 : tjoin nat_TotalOrder 3%nat 5%nat = 5%nat.
Proof. reflexivity. Qed.

(* [Thin] is inhabited on the two examples the tree already ships.  The poset
   one is fully qualified because Instance/Proset.v:47 and Instance/Poset.v:120
   both export the name (Test/Poset.v:35-41). *)

Definition thin_proset_nat : Thin (Proset PeanoNat.Nat.le_preorder) :=
  proset_thin PeanoNat.Nat.le_preorder.

Definition thin_poset_nat :
  Thin Category.Instance.Poset.LessThanEqualTo_Category :=
  poset_thin PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).
