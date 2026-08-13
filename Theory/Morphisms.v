Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Morphisms.

Context {C : Category}.

Open Scope type_scope.

(* Special classes of morphisms and their relationships: idempotents and
   involutions, sections and retractions (split mono/epi), epimorphisms and
   monomorphisms, and the implications between them. Throughout, the laws use
   the hom-setoid equivalence `≈` rather than Coq's `=`. *)

(* nLab: https://ncatlab.org/nlab/show/idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Idempotence

   An endomorphism `f : x ~> x` is idempotent when `f ∘ f ≈ f` (idem). *)

Class Idempotent `(f : x ~> x) := {
  idem : f ∘ f ≈ f             (* idempotency law: f ∘ f ≈ f *)
}.

(* nLab: https://ncatlab.org/nlab/show/involution
   Wikipedia: https://en.wikipedia.org/wiki/Involution_(mathematics)

   An endomorphism `f : x ~> x` is involutive when it is its own inverse,
   `f ∘ f ≈ id` (invol). *)

Class Involutive `(f : x ~> x) := {
  invol : f ∘ f ≈ id           (* involution law: f ∘ f ≈ id *)
}.

(* For an involution g, precomposition by g is its own inverse, so it may be
   moved across an equation: f ≈ g ∘ h  iff  g ∘ f ≈ h. *)
Lemma flip_invol {x y} (f h : x ~> y) (g : y ~> y) `{@Involutive _ g} :
  f ≈ g ∘ h ↔ g ∘ f ≈ h.
Proof.
  split; intros.
  - rewrite X, comp_assoc, invol; cat.
  - rewrite <- X, comp_assoc, invol; cat.
Qed.

(* nLab: https://ncatlab.org/nlab/show/split+monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Section f` witnesses that `f : x ~> y` is a split monomorphism: it has a
   left inverse `section : y ~> x` with `section ∘ f ≈ id` (section_comp).
   Equivalently, f is a section of the retraction `section`. Every such f is
   monic (sections_are_monic). Note the naming convention used here: a value
   of `Section f` records that f itself splits, the field `section` being the
   accompanying retraction. *)

Class Section `(f : x ~> y) := {
  section : y ~> x;               (* the retraction (left inverse) of f *)
  section_comp : section ∘ f ≈ id (* left inverse law: section ∘ f ≈ id *)
}.

(* nLab: https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Retraction f` witnesses that `f : x ~> y` is a split epimorphism: it has a
   right inverse `retract : y ~> x` with `f ∘ retract ≈ id` (retract_comp).
   Equivalently, f is a retraction of the section `retract`. Every such f is
   epic (retractions_are_epic). As with `Section`, a value of `Retraction f`
   records that f itself splits, the field `retract` being its section. *)

Class Retraction `(f : x ~> y) := {
  retract : y ~> x;               (* the section (right inverse) of f *)
  retract_comp : f ∘ retract ≈ id (* right inverse law: f ∘ retract ≈ id *)
}.

(* nLab: https://ncatlab.org/nlab/show/split+idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   A split idempotent `split_idem : x ~> x` factors through an object y as a
   retraction `split_idem_r : x ~> y` followed by a section
   `split_idem_s : y ~> x`, with `split_idem_s ∘ split_idem_r ≈ split_idem`
   (split_idem_sr) and `split_idem_r ∘ split_idem_s ≈ id` (split_idem_rs). The
   two laws TOGETHER force `split_idem` to be idempotent, and neither does so
   alone: `split_idem_rs` does not mention `split_idem` at all, and
   `split_idem_sr` only names it. The derivation is `split_idem_Idempotent`
   below, and it uses both. The mediating object y is exposed as
   `split_idem_retract`. *)

Class SplitIdempotent {x y : C} := {
  split_idem_retract := y;                  (* the splitting object y *)

  split_idem    : x ~> x;                   (* the idempotent on x *)
  split_idem_r  : x ~> split_idem_retract;  (* retraction x ~> y *)
  split_idem_s  : split_idem_retract ~> x;  (* section y ~> x *)
  split_idem_sr : split_idem_s ∘ split_idem_r ≈ split_idem;
                                            (* s ∘ r ≈ split_idem *)
  split_idem_rs : split_idem_r ∘ split_idem_s ≈ id
                                            (* r ∘ s ≈ id on y *)
}.

(* nLab: https://ncatlab.org/nlab/show/epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   `Epic f` witnesses that `f : x ~> y` is an epimorphism: f is
   right-cancellable, `g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2` for all parallel
   `g1 g2 : y ~> z` (epic). This is exactly `Monic f` in `C^op`. *)

Class Epic {x y} (f : x ~> y) := {
  epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
                                  (* right cancellation: g1∘f ≈ g2∘f → g1 ≈ g2 *)
}.

(* nLab: https://ncatlab.org/nlab/show/monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Monomorphism

   `Monic f` witnesses that `f : x ~> y` is a monomorphism: f is
   left-cancellable, `f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2` for all parallel
   `g1 g2 : z ~> x` (monic). This is exactly `Epic f` in `C^op`. *)

Class Monic {x y} (f : x ~> y) := {
  monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
                                  (* left cancellation: f∘g1 ≈ f∘g2 → g1 ≈ g2 *)
}.

(* A bimorphism is both epic and monic; a split epi is a retraction and a
   split mono is a section (the converse implications above hold via
   retractions_are_epic and sections_are_monic). *)

Definition Bimorphic `(f : x ~> y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : x ~> y) := Retraction f.
Definition SplitMono `(f : x ~> y) := Section f.

Corollary id_idem : ∀ x, Idempotent (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_invol : ∀ x, Involutive (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_monic : ∀ x, Monic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_left in X.
  assumption.
Qed.

Corollary id_epic : ∀ x, Epic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_right in X.
  assumption.
Qed.

#[local] Hint Unfold Bimorphic : core.
#[local] Hint Unfold SplitEpi : core.
#[local] Hint Unfold SplitMono : core.

Section Lemmas.

Variables x y : C.
Variable f : x ~> y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

(* Every split epimorphism is an epimorphism. *)
Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  transitivity (g2 ∘ (f ∘ retract0));
    [ now apply compose_respects |];
  transitivity (g1 ∘ (f ∘ retract0));
    [| now apply compose_respects ].
  reassociate_right.
Qed.

(* Every split monomorphism is a monomorphism. *)
Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  transitivity ((section0 ∘ f) ∘ g2);
    [ now apply compose_respects |];
  transitivity ((section0 ∘ f) ∘ g1);
    [| now apply compose_respects ].
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

(* Epimorphisms are closed under composition. *)
Definition epi_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic f → Epic g → Epic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply epic0, epic1.
  reassociate_left.
Qed.

(* Epimorphisms cancel on the LEFT: if a composite is epic, the arrow applied
   LAST is epic.  (Mac Lane, CWM 2nd ed., §I.5 Exercise 1; Riehl, CTiC, Lemma
   1.2.11(ii'); Awodey §2.9 Exercise 2(c).)  Anything g1, g2 agreeing after f
   already agrees after f ∘ g, and the composite cancels.

   Note the asymmetry: nothing follows about g.  A composite can be epic with
   its FIRST factor far from epic -- see [sets_epic_left_factor_only] in
   Instance/Sets.v for a witness. *)
Definition epic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic (f ∘ g) → Epic f.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@epic x z (f ∘ g) H w g1 g2).
  rewrite !comp_assoc.
  now rewrite Hgg.
Qed.

(* Monomorphisms cancel on the RIGHT: if a composite is monic, the arrow
   applied FIRST is monic.  (Mac Lane §I.5 Exercise 1; Riehl Lemma 1.2.11(ii);
   Awodey §2.9 Exercise 2(b), and §5.1 for the subobject reading -- a
   factorization between subobjects is automatically monic, recorded as
   [sub_le_monic] in Theory/Subobject.v.)

   This is the exact dual of [epic_cancel], and Riehl's section is about
   deriving one from the other through C^op rather than proving both.  That
   derivation cannot be performed HERE: Construction/Opposite.v requires
   Theory/Isomorphism.v, which requires this file, so importing the opposite
   category into it is a cycle (verified).  The dual route is carried out one
   layer up instead, in Theory/Morphisms/Duality.v, where [monic_cancel_op]
   re-derives this statement from [epic_cancel] with no second argument. *)
Definition monic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic (f ∘ g) → Monic g.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@monic x z (f ∘ g) H w g1 g2).
  rewrite <- !comp_assoc.
  now rewrite Hgg.
Qed.

(* Monomorphisms are closed under composition. *)
Definition monic_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic f → Monic g → Monic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply monic1, monic0.
  reassociate_right.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Split pairs and the idempotents they produce *)

(* Mac Lane, CWM 2nd ed., §I.5 ("Monics, Epis, and Zeros"), printed p. 19.
   CITED BY LOCATION; the printed text was not consulted and no sentence of
   it is reproduced here.  The in-tree catalog entry indexes the item as
   [maclane:I.5:def5] and summarizes it as: "When g h = 1_a, g is called a
   split epi, h a split monic, and the composite f = h g is an idempotent"
   (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:def5) -- the
   letter names of the lemma below are that summary's.
   nLab: https://ncatlab.org/nlab/show/split+epimorphism
   nLab: https://ncatlab.org/nlab/show/idempotent

   The nLab page on split epimorphisms records the same fact in the form
   "the pair (e,s) is a splitting of the idempotent s∘e : A→A" (retrieved
   2026-08).

   Half of a one-sided inverse pair is an idempotent.  If g ∘ h ≈ id then the
   OTHER composite h ∘ g absorbs itself, because the inner g ∘ h cancels:

     (h ∘ g) ∘ (h ∘ g) ≈ h ∘ (g ∘ h) ∘ g ≈ h ∘ id ∘ g ≈ h ∘ g.

   Nothing forces h ∘ g to be the identity in turn; when it is not, the
   idempotent is a genuinely non-trivial one.  Two files exhibit such a pair
   and REFUTE the identity for the other composite, so this lemma is not
   witnessed by identities alone: Instance/FinSet/Regular.v
   ([finset_point]/[finset_bang], with [finset_collapse_not_id]) and
   Instance/Sets/Split.v ([sets_incl23]/[sets_retr32], with
   [sets_incl_retr_not_id]). *)

Lemma split_pair_idempotent {x y : C} (g : x ~> y) (h : y ~> x) :
  g ∘ h ≈ id → Idempotent (h ∘ g).
Proof.
  intro Hgh.
  constructor.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g h g).
  rewrite Hgh, id_left.
  reflexivity.
Qed.

(* Idempotence transports along `≈`, the hom-setoid equivalence. *)
Lemma idempotent_respects {x : C} (f g : x ~> x) :
  f ≈ g → Idempotent f → Idempotent g.
Proof.
  intros Hfg [Hf].
  constructor.
  rewrite <- Hfg.
  exact Hf.
Qed.

(* [SplitIdempotent] above states the two splitting laws, and its header
   points here for the idempotence they force.  This is that derivation: the
   retraction/section pair r, s satisfies r ∘ s ≈ id, so s ∘ r is idempotent
   by [split_pair_idempotent], and s ∘ r ≈ split_idem transports it -- one
   splitting law for each step, which is why neither law alone would do.
   Before this lemma nothing in the tree derived the idempotence of a
   [SplitIdempotent]'s [split_idem] field.
   The class was CONCLUDED in exactly two places -- [id_idem] (:129 of this
   file) and [Extend_idem] (Construction/Karoubi/Universal.v:163, the image of
   a Karoubi object's idempotent under a functor) -- and every remaining
   occurrence of it was a HYPOTHESIS (Construction/Karoubi.v:227,
   Construction/Karoubi/Universal.v:54, Instance/Sets/Karoubi.v:54,61,81). *)
Lemma split_idem_Idempotent {x y : C} (S : @SplitIdempotent x y) :
  Idempotent (@split_idem x y S).
Proof.
  apply (idempotent_respects (@split_idem_s x y S ∘ @split_idem_r x y S)).
  - exact (@split_idem_sr x y S).
  - exact (split_pair_idempotent _ _ (@split_idem_rs x y S)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Regular (von Neumann regular) arrows *)

(* Mac Lane, CWM 2nd ed., §I.5 Exercise 7, printed p. 21 -- again CITED BY
   LOCATION, not quoted; the printed text was not consulted.  The in-tree
   catalog summarizes the exercise as: "Call an arrow f : a -> b in a
   category C regular when there exists g : b -> a with f g f = f.  Show f is
   regular whenever it has either a left or a right inverse, and prove that
   in Set every arrow f : a -> b with a nonempty is regular"
   (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:ex7).
   Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Von_Neumann_regular_ring

   An arrow f is REGULAR when some g runs backwards along it well enough to
   reproduce f, i.e. f ∘ g ∘ f ≈ f.  The equation is von Neumann's, from
   ring theory: a ring is regular when for every a there is an x with
   a = a x a (von Neumann, "On Regular Rings", Proc. Natl. Acad. Sci. USA
   22(12), 1936, pp. 707-713), and modern usage says VON NEUMANN REGULAR to
   keep the notion apart from the unrelated regular rings of commutative
   algebra (Wikipedia, "Von Neumann regular ring", retrieved 2026-08).  The
   semigroup version -- an element a with a x a = a -- was adapted from that
   ring condition and introduced by J. A. Green, "On the structure of
   semigroups" (1951), at David Rees's suggestion (Wikipedia, "Regular
   semigroup", retrieved 2026-08).  The two articles name the witness x
   differently: "weak inverse" for rings, "pseudoinverse" for semigroups.
   Neither calls it a quasi-inverse, so PSEUDOINVERSE is the word used
   throughout this development.

   The pseudoinverse g need not be unique, and neither composite f ∘ g nor
   g ∘ f need be an identity.  What they are is idempotent, which is the
   content of [regular_composites_idempotent] below -- a direct computation
   from the regularity law, NOT an instance of [split_pair_idempotent] above
   (that lemma wants one of the composites to be the identity outright, which
   is precisely what regularity drops).

   Regularity is weaker than either one-sided invertibility:
   [regular_of_section] and [regular_of_retraction] below give both
   implications, and Instance/FinSet/Regular.v exhibits an arrow that is
   regular yet neither a section nor a retraction ([finset_shift3]).  It is
   also a real restriction on an arrow rather than a triviality, and two
   categories witness that: Instance/Two.v exhibits an arrow of the interval
   category that is monic and epic and NOT regular ([TwoXY_not_regular]), and
   Instance/FinSet/Regular.v refutes regularity for the unique arrow 0 → 1
   ([finset_empty_to_one_not_regular]).  Both work for the same blunt reason,
   that the only candidate pseudoinverse would be an arrow the category does
   not have; Instance/Sets/Regular.v shows the bluntness is forced rather
   than convenient, since over [Sets] regularity can be undecided
   ([sets_coarsen_not_regular_absurd]).

   The definition is stated with the library's `∃`, which is Type-valued
   (`sigT`, Lib/Foundation.v:61,66), so a regularity witness is DATA: the
   pseudoinverse can be projected out and computed with.  That is what makes
   the FinSet result of Instance/FinSet/Regular.v an executable finite search
   rather than a bare existence claim, and it is why the four constructions
   below that PRODUCE such data -- [regular_of_section],
   [regular_of_retraction], [regular_epic_retraction] and
   [regular_monic_section] -- end in [Defined] rather than [Qed]. *)

Definition RegularMorphism `(f : x ~> y) := ∃ g : y ~> x, f ∘ g ∘ f ≈ f.

(* An arrow with a LEFT inverse is regular: the left inverse is already a
   pseudoinverse, since f ∘ (s ∘ f) ≈ f ∘ id ≈ f. *)
Definition regular_of_section `(f : x ~> y) : Section f → RegularMorphism f.
Proof.
  intros [s Hs].
  exists s.
  rewrite <- comp_assoc, Hs.
  apply id_right.
Defined.

(* An arrow with a RIGHT inverse is regular: dually, (f ∘ r) ∘ f ≈ id ∘ f. *)
Definition regular_of_retraction `(f : x ~> y) :
  Retraction f → RegularMorphism f.
Proof.
  intros [r Hr].
  exists r.
  rewrite Hr.
  apply id_left.
Defined.

(* Both composites built from a pseudoinverse are idempotent:
     (f ∘ g) ∘ (f ∘ g) ≈ ((f ∘ g) ∘ f) ∘ g ≈ f ∘ g,
     (g ∘ f) ∘ (g ∘ f) ≈ g ∘ ((f ∘ g) ∘ f) ≈ g ∘ f.
   Proved here from the regularity law alone.  (The Wikipedia "Regular
   semigroup" article states the corresponding semigroup fact for a PROPER
   inverse b -- one satisfying both a b a = a and b a b = b -- rather than
   for an arbitrary pseudoinverse; the computation above shows the weaker
   hypothesis already suffices, so no claim is being borrowed here.) *)
Lemma regular_composites_idempotent {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ∘ f ≈ f → Idempotent (f ∘ g) ∧ Idempotent (g ∘ f).
Proof.
  intro Hg.
  split; constructor.
  - rewrite (comp_assoc (f ∘ g) f g), Hg.
    reflexivity.
  - rewrite <- comp_assoc, (comp_assoc f g f), Hg.
    reflexivity.
Qed.

(* Under a cancellation hypothesis the converses hold.  These two lemmas are
   what make the choice discussion of Instance/FinSet/Regular.v and
   Instance/Sets/Regular.v precise rather than hand-waved:
   [regular_epic_retraction], quantified over the arrows of [Sets], IS the
   implication [blanket_regularity_entails_splitting] from the blanket
   principle "every arrow with inhabited domain is regular" to "every such
   epimorphism splits", and over [Sets] the latter already decides every
   proposition ([blanket_splitting_entails_LEM]).  A regular EPI splits:
   cancel f on the right of (f ∘ g) ∘ f ≈ id ∘ f. *)
Definition regular_epic_retraction `(f : x ~> y) :
  RegularMorphism f → Epic f → Retraction f.
Proof.
  intros [g Hg] E.
  exists g.
  apply (@epic x y f E y (f ∘ g) id).
  rewrite Hg.
  symmetry.
  apply id_left.
Defined.

(* Dually, a regular MONO splits: cancel f on the left of
   f ∘ (g ∘ f) ≈ f ∘ id. *)
Definition regular_monic_section `(f : x ~> y) :
  RegularMorphism f → Monic f → Section f.
Proof.
  intros [g Hg] M.
  exists g.
  apply (@monic x y f M x (g ∘ f) id).
  rewrite comp_assoc, Hg.
  symmetry.
  apply id_right.
Defined.

End Morphisms.

#[export] Hint Unfold Bimorphic : core.
#[export] Hint Unfold SplitEpi : core.
#[export] Hint Unfold SplitMono : core.

(* Section/retraction duality: if `section` is the left inverse witnessing
   that f is a split mono, then f exhibits `section` as a split epi. *)
Definition flip_Section {C : Category} `(f : x ~> y)
           (s : @Section C x y f) : @Retraction C y x section.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

(* Dual of flip_Section: if `retract` is the right inverse witnessing that f
   is a split epi, then f exhibits `retract` as a split mono. *)
Definition flip_Retraction {C : Category} `(f : x ~> y)
           (s : @Retraction C x y f) : @Section C y x retract.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
