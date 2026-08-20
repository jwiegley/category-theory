Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** * Pushouts in Grp: the free product with amalgamation *)

(* Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
         §III.3, book p. 66 / PDF p. 75 (maclane:III.3:remark3)
   nLab:      https://ncatlab.org/nlab/show/pushout
   Wikipedia: https://en.wikipedia.org/wiki/Free_product  (amalgamation)

   Mac Lane's remark that pushouts exist in Grp, with the classical
   refinement that monic legs give monic injections and identify the
   vertex as the free product with amalgamation.

   AN ERRATUM IN THE ISSUE (#325).  Its "Current state" paragraph says
   "The Top clause and the entire Grp clause are absent -- no Top or Grp
   category in-tree".  That was true when the catalog was written and is
   FALSE now: Instance/Grp.v and Instance/Top.v both exist, several such
   categories having been built earlier in the same campaign.  What was
   genuinely absent is the pushouts, and that is what this file and
   Instance/Top/Pushout.v supply.

   THE CONSTRUCTION.  B *_A C is presented by generators and relations,
   in the inductive-setoid-quotient idiom of Instance/Mod/Free.v and
   Instance/Ab/Tensor.v: [AmTerm] is a formal word over the two carriers
   with the three group formers, and [am_eq] is the congruence generated
   by exactly (i) the two groups' own equivalences, (ii) multiplicativity
   of the two insertions, (iii) the amalgamation [am_l (f a) ~ am_r (g a)],
   (iv) the three left-handed group laws, (v) congruence for the two
   operations, and (vi) symmetry and transitivity.

   WHAT THAT PRESENTATION BUYS, MEASURED.  Every group law is a
   CONSTRUCTOR, so [AmalgamGrp] is a record literal with NO proof
   obligation of its own.  [am_eval] is a [Fixpoint], so the mediator's
   multiplication law closes by [reflexivity] -- recorded, not inferred
   from which tactic fired, by the [eq_refl] controls
   [ctl_grp_med_unit] / [ctl_grp_med_mul] in Test/ProbePushoutGrpTop.v.
   Two facts are DERIVED rather than posted: reflexivity of [am_eq]
   ([am_eq_refl], the [am_one] case going through [ae_unit_l am_one] and
   its own symmetry), and unit-preservation by the two insertions
   (Instance/Grp.v's [Build_GrpHom'], whose redundancy argument is
   cancellation in the quotient).  The UMP costs two inductions: one
   over the CONGRUENCE ([am_eval_respects], twelve cases, of which the
   glue case is the only consumer of the cocone hypothesis) and one over
   the WORD ([am_med_unique], five cases).  The file carries two more
   outside the UMP -- [am_eq_refl] and [Grp_Cocartesian]'s
   [fork_respects] -- so four in total; an earlier draft said "the whole
   price is two inductions", which undercounted.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  [Grp_HasPushouts] is the
   deliverable.  The chosen pushout's apex and both injections are the
   hand-built ones at LEIBNIZ EQUALITY ([Grp_pushout_apex_is_AmalgamGrp]
   and siblings, [eq_refl]), as are the carrier and all three group
   operations.  [pushout_med] is NOT [am_med] on the nose: Structure/
   Pushout.v states [pushout_ump] as a [Qed] lemma, so [unique_obj] is
   applied to an opaque constant -- the equation holds up to [≈]
   ([Grp_pushout_med_is_am_med]) and the strict form is a pinned negative
   with DONOR OPACITY as its diagnosed cause, paired with the identical
   negative on the Top side so the cause is visibly not about groups.

   MAC LANE'S MONIC-LEGS REFINEMENT: DELIVERED AT SPLIT STRENGTH, AND THE
   GAP IS STATED RATHER THAN GLOSSED.  [Grp_split_legs_monic_injections]
   proves that if both legs SPLIT then both injections are monic, through
   Structure/Pushout/Split.v, where the argument is generic: feed the
   cocone [(id, f ∘ retraction)] to the universal property.  Read down to
   elements by Instance/Grp.v's own [Grp_injectivity_is_monic], this says
   the two insertions are INJECTIVE ([am_inj1_injective],
   [am_inj2_injective]).  The refinement for merely MONIC legs is NOT
   delivered.  It is, for groups, the Schreier normal-form theorem for
   amalgamated free products, whose usual proof (van der Waerden's trick)
   builds an action on alternating normal forms and so must CHOOSE coset
   transversals for f(A) in B and g(A) in C; carrying those transversals
   as data would be the house-idiom fix, and the remaining development --
   normal forms, the action, its well-definedness on the congruence -- is
   a large piece of combinatorial group theory that is not attempted here.
   No claim is made that the split hypothesis is necessary; it is not, and
   no in-tree witness separates "monic" from "split monic" in Grp either,
   so the strictness of the gap is argued rather than proved.

   AND THE OTHER HALF OF MAC LANE'S SENTENCE IS DEFINITIONAL, NOT PROVED.
   "The vertex is the amalgamated product" holds here because the vertex
   IS the presented group B *_A C by construction.  Nothing below relates
   it to an independent definition -- via normal forms, or via a subgroup
   generated inside some ambient group -- so this is an identification by
   fiat of notation, and the reader should not read it as a theorem.

   THE FREE PRODUCT, AND WHY THIS SUBSUMES A SEPARATE ISSUE.
   [Grp_free_product] is an INSTANCE of the amalgamated product rather
   than a second construction, and both its injections are split monic
   with NO hypothesis, because each constant leg factors through the
   other.  Read that precisely, because an earlier draft of this header
   overstated it: what is discharged is the strictly weaker FACTORIZATION
   hypothesis ([Grp_fp_inl_Section] goes through
   [am_inj1_Section_of_factor], not [am_inj1_Section_of_Retraction]), and
   Mac Lane's own monic-legs hypothesis is in fact FALSE for this span --
   the legs are CONSTANT maps, which are not injective into a nontrivial
   group and so not monic.  This is therefore Mac Lane's CONCLUSION
   reached by a different and weaker hypothesis, NOT an instance of his
   refinement.  [Grp_Cocartesian] then
   exhibits the free product as the COPRODUCT of Grp, which the tree did
   not have (issue #1194 owns the Grp free product; nothing in tree
   instantiated [Cocartesian Grp]).  CROSS-REFERENCE, and read it
   precisely: the GENERAL bridge "a pushout over the initial object is the
   binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and is NOT
   built here.  What is built is the ad-hoc Grp instance, in which the
   pushout's commutation hypothesis is discharged once by [Grp_fp_cocone]
   and what remains is literally the coproduct's universal property.

   THE SPAN IS THE CONSTANT ONE, NOT THE ZERO OBJECT, AND THAT IS A
   UNIVERSE DECISION.  Classically the free product is the pushout over
   the TRIVIAL group, and that span's legs even SPLIT --
   [Grp_zero_hom_Section] proves it, its retraction being [Grp_one].  But
   Instance/Grp.v declares [Grp_zero_hom] over [GrpObject@{Set Set Set}]
   (and [Grp_trivial@{u}] over [GrpObject@{u Set u}], one binder where the
   record wants more), the donor defect Instance/Grp/Quotient/Colimit.v
   already records and which confines that whole file to [Set]-sized
   groups.  Building the free product on it would inherit the pin.  It is
   built on the CONSTANT legs instead, which needs no zero object: the
   cocone condition is automatic because every homomorphism preserves the
   unit ([Grp_fp_cocone]), and each leg factors through the other by a
   third constant map ([grp_const_absorb]).  [Grp_zero_hom_Section] is
   kept as the honest record of the route not taken.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS, WITH THE CAUSE PROBED.
   Two separate facts, and they point opposite ways.

   (1) [AmalgamGrp@{u u0 .. u8}] displays THREE separate universe triples
   in its binder -- one per group -- while its constraint block contains
   [u = u0], ..., [u = u7]: all nine collapse.  Reading the binder alone
   gets this wrong.  But the identification is NOT the amalgamation's
   doing, and that is probed rather than assumed: the bare definition
   [fun (A B : GrpObject) (f : @hom Grp A B) => B], which mentions no
   pushout at all, already elaborates at [GrpObject@{u0 u0 u0}] for BOTH
   objects.  Naming a single Grp hom is what identifies the levels; the
   amalgam adds nothing.  [Grp_HasPushouts@{u u0}] correspondingly carries
   only [u < u0], and no [Set] appears in either constraint block.

   (2) NO [Set] APPEARS ANYWHERE IN THIS FILE'S PRINCIPAL CONSTANTS,
   including the free-product layer: [Grp_free_product@{u u0}] is
   [GrpObject@{u u u} -> GrpObject@{u u u} -> GrpObject@{u u u}] with only
   [u < u0], and [Grp_Cocartesian@{u u0}] is [Cartesian@{u u0}] with the
   two levels kept apart.  That is the payoff of the constant-leg span
   described above, and the BOUNDARY is guarded in
   Test/ProbePushoutGrpTop.v rather than asserted: two formability
   negatives reject the DONOR constants [Grp_zero_hom] and
   [Grp_zero_hom_Section] at a group declared strictly above [Set] (a
   genuine "Cannot enforce Set = bg"), against controls that form
   [AmalgamGrp], the chosen pushout, [Grp_free_product], [Grp_fp_inl] and
   [grp_const] at that very level, plus controls naming the two donor
   constants at [Set]-level groups so the negatives are about the universe
   and not about a missing reference.

   NON-VACUITY.  A negative fact about a generated congruence cannot come
   from induction on it, so every separation here maps OUT of the quotient
   through a concrete homomorphism into [Z2]: [fp_generators_distinct]
   shows the free product does not merge the two summands' generators, and
   [fp_inl_injective] that it does not merge distinct elements of one
   summand.  THE CONTRAST that makes the amalgamation content rather than
   bookkeeping is [amalgam_over_Z2_merges]: over the SAME two groups,
   amalgamating along the identity DOES merge the very pair the free
   product keeps apart.

   WHAT IS NOT DELIVERED.  No normal form, hence no word problem, no
   coefficient uniqueness and no decision procedure for [am_eq]; the
   Schreier refinement above; no proof that the split hypothesis is
   strictly weaker than monicity (no in-tree monic-but-not-split group
   homomorphism is exhibited); no HNN extension; no Bass-Serre theory; no
   van Kampen theorem, and in particular no connection to
   Instance/Top/FundamentalGroupoid.v; no functoriality of the pushout in
   the span; no comparison with Instance/Grp/Free.v's free group (the free
   product of two free groups is not shown free); and no infinite/indexed
   free products.  The [Grp_Cocartesian] instance is registered
   [#[export]], so importers acquire it; no LIBRARY file imports this
   one -- only Test/ProbePushoutGrpTop.v does. *)

(** ** Formal words *)

Inductive AmTerm (B C : GrpObject) : Type :=
  | am_l   : carrier B → AmTerm
  | am_r   : carrier C → AmTerm
  | am_one : AmTerm
  | am_mul : AmTerm → AmTerm → AmTerm
  | am_inv : AmTerm → AmTerm.

Arguments am_l {B C} _.
Arguments am_r {B C} _.
Arguments am_one {B C}.
Arguments am_mul {B C} _ _.
Arguments am_inv {B C} _.

(** ** The generated congruence *)

Inductive am_eq {A B C : GrpObject}
                (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  : AmTerm B C → AmTerm B C → Type :=
  (* the two insertions respect the groups' own equivalences *)
  | ae_l_resp : ∀ b b' : carrier B,
      b ≈ b' → am_eq (am_l b) (am_l b')
  | ae_r_resp : ∀ c c' : carrier C,
      c ≈ c' → am_eq (am_r c) (am_r c')
  (* the two insertions preserve multiplication *)
  | ae_l_mul : ∀ b b' : carrier B,
      am_eq (am_l (grp_mul B b b')) (am_mul (am_l b) (am_l b'))
  | ae_r_mul : ∀ c c' : carrier C,
      am_eq (am_r (grp_mul C c c')) (am_mul (am_r c) (am_r c'))
  (* the amalgamation: the span is coequalized *)
  | ae_glue : ∀ a : carrier A,
      am_eq (am_l (f a)) (am_r (g a))
  (* the group laws, in their left-handed form *)
  | ae_assoc : ∀ u v w,
      am_eq (am_mul (am_mul u v) w) (am_mul u (am_mul v w))
  | ae_unit_l : ∀ u, am_eq (am_mul am_one u) u
  | ae_inv_l : ∀ u, am_eq (am_mul (am_inv u) u) am_one
  (* congruence for the two operations *)
  | ae_mul_cong : ∀ u u' v v',
      am_eq u u' → am_eq v v' →
      am_eq (am_mul u v) (am_mul u' v')
  | ae_inv_cong : ∀ u u',
      am_eq u u' → am_eq (am_inv u) (am_inv u')
  (* symmetry and transitivity; reflexivity is derived below *)
  | ae_sym : ∀ u v, am_eq u v → am_eq v u
  | ae_trans : ∀ u v w, am_eq u v → am_eq v w → am_eq u w.

Arguments ae_l_resp {A B C f g} _ _ _.
Arguments ae_r_resp {A B C f g} _ _ _.
Arguments ae_l_mul {A B C f g} _ _.
Arguments ae_r_mul {A B C f g} _ _.
Arguments ae_glue {A B C f g} _.
Arguments ae_assoc {A B C f g} _ _ _.
Arguments ae_unit_l {A B C f g} _.
Arguments ae_inv_l {A B C f g} _.
Arguments ae_mul_cong {A B C f g} _ _ _ _ _ _.
Arguments ae_inv_cong {A B C f g} _ _ _.
Arguments ae_sym {A B C f g} _ _ _.
Arguments ae_trans {A B C f g} _ _ _ _ _.

Section AmalgamCore.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* Reflexivity is DERIVED rather than posted as a constructor.  Every
   former has a congruence rule except [am_one], and the unit itself is
   reached by [ae_unit_l am_one] composed with its own symmetry. *)
Lemma am_eq_refl (u : AmTerm B C) : am_eq f g u u.
Proof.
  induction u as [b | c | | u IHu v IHv | u IHu].
  - apply ae_l_resp; reflexivity.
  - apply ae_r_resp; reflexivity.
  - exact (ae_trans _ _ _ (ae_sym _ _ (ae_unit_l am_one)) (ae_unit_l am_one)).
  - exact (ae_mul_cong _ _ _ _ IHu IHv).
  - exact (ae_inv_cong _ _ IHu).
Qed.

Definition AmSetoid : Setoid (AmTerm B C) := {|
  equiv := am_eq f g;
  setoid_equiv :=
    Build_Equivalence (am_eq f g) am_eq_refl (ae_sym) (ae_trans)
|}.

Definition AmCarrier : SetoidObject := {|
  carrier := AmTerm B C;
  is_setoid := AmSetoid
|}.

(* The amalgamated free product B *_A C.  Every group law is a
   CONSTRUCTOR of [am_eq], so the record below is a literal with no proof
   obligation of its own -- the [Instance/Mod/Free.v] payoff. *)
Definition AmalgamGrp : GrpObject := {|
  grp_setoid := AmCarrier;
  grp_unit := am_one;
  grp_mul := am_mul;
  grp_inv := am_inv;
  grp_mul_respects := fun u u' Hu v v' Hv => ae_mul_cong _ _ _ _ Hu Hv;
  grp_mul_assoc := ae_assoc;
  grp_mul_unit_l := ae_unit_l;
  grp_mul_inv_l := ae_inv_l
|}.

(** ** The two injections *)

Definition am_inj1_map
  : SetoidMorphism (grp_setoid B) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_l |}.
  intros b b' Hb; exact (ae_l_resp b b' Hb).
Defined.

Definition am_inj2_map
  : SetoidMorphism (grp_setoid C) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_r |}.
  intros c c' Hc; exact (ae_r_resp c c' Hc).
Defined.

Definition am_inj1 : B ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj1_map (fun b b' => ae_l_mul b b').

Definition am_inj2 : C ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj2_map (fun c c' => ae_r_mul c c').

(* The pushout square commutes: this IS the [ae_glue] constructor. *)
Lemma am_square : am_inj1 ∘[Grp] f ≈ am_inj2 ∘[Grp] g.
Proof. intro a; exact (ae_glue a). Qed.

End AmalgamCore.

Arguments AmalgamGrp {A B C} f g.
Arguments am_inj1 {A B C} f g.
Arguments am_inj2 {A B C} f g.

(** ** The mediating homomorphism *)

Section AmalgamMediator.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).

(* Evaluation of a formal word in a competing group.  A [Fixpoint], so
   the three homomorphism laws of the mediator hold DEFINITIONALLY. *)
Fixpoint am_eval (t : AmTerm B C) : carrier Q :=
  match t with
  | am_l b => grp_map q1 b
  | am_r c => grp_map q2 c
  | am_one => grp_unit Q
  | am_mul u v => grp_mul Q (am_eval u) (am_eval v)
  | am_inv u => grp_inv Q (am_eval u)
  end.

Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(* Well-definedness on the quotient, by induction on the derivation.  The
   glue case is the ONLY one that consumes [Hcomm]; every other case is a
   law of [Q] or of one of the two homomorphisms. *)
Lemma am_eval_respects (u v : AmTerm B C) (H : am_eq f g u v) :
  am_eval u ≈ am_eval v.
Proof using All.
  induction H; simpl.
  - now apply proper_morphism.
  - now apply proper_morphism.
  - now apply grp_map_mul.
  - now apply grp_map_mul.
  - exact (Hcomm a).
  - now apply grp_mul_assoc.
  - now apply grp_mul_unit_l.
  - now apply grp_mul_inv_l.
  - now apply grp_mul_respects.
  - now apply grp_inv_respects_law.
  - now symmetry.
  - now transitivity (am_eval v).
Qed.

Definition am_eval_map
  : SetoidMorphism (grp_setoid (AmalgamGrp f g)) (grp_setoid Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := am_eval |}.
  intros u v Huv; exact (am_eval_respects u v Huv).
Defined.

Definition am_med : AmalgamGrp f g ~{Grp}~> Q :=
  Build_GrpHom' am_eval_map (fun u v => reflexivity _).

Lemma am_med_inj1 : am_med ∘[Grp] am_inj1 f g ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma am_med_inj2 : am_med ∘[Grp] am_inj2 f g ≈ q2.
Proof. intro c; reflexivity. Qed.

(* Uniqueness, by induction on the WORD rather than on the congruence: a
   competing homomorphism is pinned on the two insertions by hypothesis
   and on the three formers by its own homomorphism laws. *)
Lemma am_med_unique (v : AmalgamGrp f g ~{Grp}~> Q)
      (H1 : v ∘[Grp] am_inj1 f g ≈ q1)
      (H2 : v ∘[Grp] am_inj2 f g ≈ q2) :
  am_med ≈ v.
Proof.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
  - symmetry; exact (grp_map_unit v).
  - transitivity (grp_mul Q (grp_map v s) (grp_map v t)).
    + now apply grp_mul_respects.
    + symmetry; exact (grp_map_mul v s t).
  - transitivity (grp_inv Q (grp_map v s)).
    + now apply grp_inv_respects_law.
    + symmetry; exact (grp_map_inv v s).
Qed.

End AmalgamMediator.


(** ** The universal property, packaged *)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_HasPushouts : HasPushouts Grp := {|
  pushout := fun A B C f g =>
    {| Pull         := AmalgamGrp f g;
       pullback_fst := am_inj1 f g;
       pullback_snd := am_inj2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (am_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := am_med f g q1 q2 Hcomm |}.
  - split.
    + exact (am_med_inj1 f g q1 q2 Hcomm).
    + exact (am_med_inj2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (am_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(** ** The chosen pushout, and what reduces *)

Definition Grp_pushout {A B C : GrpObject}
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) : IsPushout f g :=
  @pushout Grp Grp_HasPushouts A B C f g.

(* The apex and both injections are the hand-built ones ON THE NOSE. *)
Example Grp_pushout_apex_is_AmalgamGrp {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Example Grp_pushout_in1_is_am_inj1 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

Example Grp_pushout_in2_is_am_inj2 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in2 (Grp_pushout f g) = am_inj2 f g := eq_refl.

(* The carrier of the apex is literally the type of formal words, and the
   group operations are literally the formers. *)
Example Grp_pushout_carrier {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  carrier (AmalgamGrp f g) = AmTerm B C := eq_refl.

Example Grp_pushout_mul {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_mul (AmalgamGrp f g) = am_mul := eq_refl.

Example Grp_pushout_unit {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_unit (AmalgamGrp f g) = am_one := eq_refl.

Example Grp_pushout_inv {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_inv (AmalgamGrp f g) = am_inv := eq_refl.

(* The mediator's action on the two generating families reduces. *)
Example am_med_on_left {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (b : carrier B) :
  grp_map (am_med f g q1 q2 Hcomm) (am_l b) = grp_map q1 b := eq_refl.

Example am_med_on_right {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (c : carrier C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_r c) = grp_map q2 c := eq_refl.

(* [pushout_med], by contrast, does NOT reduce to [am_med]: Structure/
   Pushout.v states [pushout_ump] as a [Qed] lemma, so [unique_obj] is
   applied to an opaque constant.  The equation holds up to [≈], which is
   what the universal property gives; the strict form is pinned as a
   negative in Test/ProbePushoutGrpTop.v, with the opacity as its
   diagnosed cause. *)
Lemma Grp_pushout_med_is_am_med {A B C Q : GrpObject}
      (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
      (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  pushout_med (Grp_pushout f g) Hcomm ≈ am_med f g q1 q2 Hcomm.
Proof.
  apply (pushout_med_unique (Grp_pushout f g) Hcomm).
  - exact (am_med_inj1 f g q1 q2 Hcomm).
  - exact (am_med_inj2 f g q1 q2 Hcomm).
Qed.

(** ** Mac Lane's monic-legs refinement, at split strength *)

Section GrpSplitRefinement.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* The generic statements of Structure/Pushout/Split.v, transported to the
   named injections.  The transport is by CONVERSION -- [pushout_in1
   (Grp_pushout f g)] IS [am_inj1 f g], recorded above by [eq_refl] -- so
   each of these is an [exact] of the generic term. *)
Definition am_inj1_Section (Sg : Section g) : Section (am_inj1 f g) :=
  pushout_in1_Section_of_Retraction (Grp_pushout f g) Sg.

Definition am_inj2_Section (Sf : Section f) : Section (am_inj2 f g) :=
  pushout_in2_Section_of_Retraction (Grp_pushout f g) Sf.

(* The weaker hypothesis the free product actually uses: not that the
   opposite leg splits, but that one leg FACTORS through the other. *)
Definition am_inj1_Section_of_factor (r : C ~{Grp}~> B)
           (Hr : r ∘[Grp] g ≈ f) : Section (am_inj1 f g) :=
  pushout_in1_Section (Grp_pushout f g) r Hr.

Definition am_inj2_Section_of_factor (s : B ~{Grp}~> C)
           (Hs : s ∘[Grp] f ≈ g) : Section (am_inj2 f g) :=
  pushout_in2_Section (Grp_pushout f g) s Hs.

Theorem am_inj1_Monic (Sg : Section g) : Monic (am_inj1 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj1_Section Sg)). Qed.

Theorem am_inj2_Monic (Sf : Section f) : Monic (am_inj2 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj2_Section Sf)). Qed.

(* The refinement in the shape Mac Lane states it, at split strength: both
   legs split, therefore both injections are monic AND the vertex is the
   amalgamated product -- the latter definitionally, [AmalgamGrp f g]
   being the apex on the nose. *)
Theorem Grp_split_legs_monic_injections (Sf : Section f) (Sg : Section g) :
  Monic (am_inj1 f g) * Monic (am_inj2 f g).
Proof. exact (am_inj1_Monic Sg, am_inj2_Monic Sf). Qed.

(* Read down to elements through Instance/Grp.v's own characterization of
   monomorphisms: split legs make the two insertions INJECTIVE.  The
   hypotheses are spelled with [am_eq f g], which IS the apex's [≈] by
   construction ([AmSetoid]), so no coercion or transport intervenes. *)
Corollary am_inj1_injective (Sg : Section g) :
  ∀ b b' : carrier B, am_eq f g (am_l b) (am_l b') → b ≈ b'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj1 f g)) (am_inj1_Monic Sg)).
Qed.

Corollary am_inj2_injective (Sf : Section f) :
  ∀ c c' : carrier C, am_eq f g (am_r c) (am_r c') → c ≈ c'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj2 f g)) (am_inj2_Monic Sf)).
Qed.

End GrpSplitRefinement.

(** ** The free product, as the pushout along the constant legs *)

(* The constant homomorphism at the unit.  Multiplicativity is the unit's
   own idempotence, so [Build_GrpHom'] supplies unit-preservation. *)
Definition grp_const_map (A G : GrpObject)
  : SetoidMorphism (grp_setoid A) (grp_setoid G).
Proof.
  unshelve notypeclasses refine {| morphism := fun _ => grp_unit G |}.
  intros a b _; reflexivity.
Defined.

Definition grp_const (A G : GrpObject) : A ~{Grp}~> G.
Proof.
  refine (Build_GrpHom' (grp_const_map A G) _).
  intros a b; simpl.
  symmetry; apply grp_mul_unit_l.
Defined.

(* THE ROUTE NOT TAKEN, and why.  The free product is classically the
   pushout over the TRIVIAL group, and that span's legs even SPLIT --
   [Grp_zero_hom]'s retraction is [Grp_one], the two composites living in
   a hom-set Instance/Grp.v has already proved to be a singleton.  The
   lemma is recorded here because it is the honest classical statement.
   But [Instance/Grp.v]'s [Grp_zero_hom] is declared over
   [GrpObject@{Set Set Set}] -- a donor pin of the family
   Instance/Grp/Quotient/Colimit.v records for [Grp_trivial] -- so
   everything built on it would be confined to [Set]-sized groups.  The
   free product below therefore goes through the CONSTANT legs instead,
   which needs no zero object and carries no pin; the probe file pins the
   donor's rejection above [Set] against this file's acceptance there. *)
Definition Grp_zero_hom_Section (G : GrpObject) : Section (Grp_zero_hom G).
Proof.
  unshelve refine {| section := Grp_one G |}.
  exact (Grp_zero_hom_unique Grp_trivial
           (Grp_one G ∘[Grp] Grp_zero_hom G) (@id Grp Grp_trivial)).
Defined.

(* B * C: the amalgam along the two constant legs.  This is an INSTANCE of
   the amalgamated product, not a second construction.

   THE SPAN APEX PLAYS NO ROLE, and that is visible rather than argued:
   [AmTerm B C] does not mention the apex at all, and the apex enters
   [am_eq] only through [ae_glue a], whose statement here is
   [am_l (grp_unit B) ~ am_r (grp_unit C)] for EVERY [a] -- one relation,
   repeated, and already derivable from the two insertions'
   unit-preservation.  [B] is taken as the apex only because it is at
   hand.  (That the congruences over two different apexes coincide is not
   stated as a lemma; what IS proved is that this object has the
   coproduct's universal property, which is what a consumer needs.) *)
Definition Grp_free_product (B C : GrpObject) : GrpObject :=
  AmalgamGrp (grp_const B B) (grp_const B C).

Definition Grp_fp_inl (B C : GrpObject) : B ~{Grp}~> Grp_free_product B C :=
  am_inj1 (grp_const B B) (grp_const B C).

Definition Grp_fp_inr (B C : GrpObject) : C ~{Grp}~> Grp_free_product B C :=
  am_inj2 (grp_const B B) (grp_const B C).

(* Any pair of homomorphisms out of B and C automatically forms a cocone
   over the constant span, both composites being constant at the unit of
   Q.  So the free product's copairing needs no compatibility hypothesis
   at all. *)
Lemma Grp_fp_cocone {B C Q : GrpObject}
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q) :
  q1 ∘[Grp] grp_const B B ≈ q2 ∘[Grp] grp_const B C.
Proof.
  intro b; simpl.
  transitivity (grp_unit Q).
  - exact (grp_map_unit q1).
  - symmetry; exact (grp_map_unit q2).
Qed.

Definition Grp_fp_merge {B C Q : GrpObject}
           (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  : Grp_free_product B C ~{Grp}~> Q :=
  am_med (grp_const B B) (grp_const B C) q1 q2 (Grp_fp_cocone q1 q2).

(* Both free-product injections are split monic, with NO hypothesis: each
   constant leg factors through the other, via a third constant map. *)
Lemma grp_const_absorb {A A' G : GrpObject} (h : A ~{Grp}~> A') :
  grp_const A' G ∘[Grp] h ≈ grp_const A G.
Proof. intro a; reflexivity. Qed.

Definition Grp_fp_inl_Section (B C : GrpObject) : Section (Grp_fp_inl B C) :=
  am_inj1_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const C B) (grp_const_absorb (grp_const B C)).

Definition Grp_fp_inr_Section (B C : GrpObject) : Section (Grp_fp_inr B C) :=
  am_inj2_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const B C) (grp_const_absorb (grp_const B B)).

Theorem Grp_free_product_injections_Monic (B C : GrpObject) :
  Monic (Grp_fp_inl B C) * Monic (Grp_fp_inr B C).
Proof.
  exact (sections_are_monic _ _ _ (Grp_fp_inl_Section B C),
         sections_are_monic _ _ _ (Grp_fp_inr_Section B C)).
Qed.

(** ** The free product IS the coproduct of Grp

    Cross-reference: the GENERAL bridge "a pushout over the initial object
    is the binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and
    is NOT built here.  What follows is the ad-hoc Grp instance: the
    commutation hypothesis of the pushout's universal property is
    discharged once and for all by [Grp_fp_cocone], leaving exactly the
    coproduct's universal property. *)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_Cocartesian : @Cocartesian Grp := {|
  product_obj := Grp_free_product;
  fork := fun _ _ _ q1 q2 => Grp_fp_merge q1 q2;
  exl := fun B C => Grp_fp_inl B C;
  exr := fun B C => Grp_fp_inr B C
|}.
Next Obligation.
  intros Q B C q1 q1' H1 q2 q2' H2.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - exact (H1 b).
  - exact (H2 c).
  - reflexivity.
  - now apply grp_mul_respects.
  - now apply grp_inv_respects_law.
Qed.
Next Obligation.
  intros Q B C q1 q2 h.
  split.
  - intro Hh.
    split.
    + intro b; exact (Hh (am_l b)).
    + intro c; exact (Hh (am_r c)).
  - intros [Hl Hr].
    symmetry.
    exact (am_med_unique (grp_const B B) (grp_const B C) q1 q2
             (Grp_fp_cocone q1 q2) h Hl Hr).
Qed.

(** ** Non-vacuity

    Nothing below can be proved by induction on [am_eq]: a NEGATIVE fact
    about a generated congruence is only reachable by mapping OUT of the
    quotient, which is what the universal property is for.  Every
    separation here therefore runs through a concrete homomorphism into
    [Instance/Grp.v]'s [Z2]. *)

(* The separating homomorphism out of Z2 * Z2: the identity on the left
   summand, the constant map on the right. *)
Definition fp_probe : Grp_free_product Z2 Z2 ~{Grp}~> Z2 :=
  Grp_fp_merge (@id Grp Z2) (grp_const Z2 Z2).

Example fp_probe_left :
  grp_map fp_probe (@am_l Z2 Z2 true) = true := eq_refl.
Example fp_probe_right :
  grp_map fp_probe (@am_r Z2 Z2 true) = false := eq_refl.

(* The free product does NOT merge the two summands' generators. *)
Theorem fp_generators_distinct :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_r Z2 Z2 true) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid
                 (grp_map fp_probe (@am_l Z2 Z2 true))
                 (grp_map fp_probe (@am_r Z2 Z2 true)))
    by (apply proper_morphism; exact H).
  simpl in Hq.
  discriminate Hq.
Qed.

(* ...and does not merge distinct elements of one summand either, which is
   [Grp_fp_inl_Section] read down to elements. *)
Theorem fp_inl_injective :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_l Z2 Z2 false) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid true false).
  { exact (snd (Grp_injectivity_is_monic (Grp_fp_inl Z2 Z2))
             (fst (Grp_free_product_injections_Monic Z2 Z2))
             true false H). }
  discriminate Hq.
Qed.

(* THE CONTRAST that makes the amalgamation content rather than
   bookkeeping: over the SAME two groups, amalgamating along the identity
   DOES merge the very pair the free product keeps apart. *)
Theorem amalgam_over_Z2_merges :
  am_eq (@id Grp Z2) (@id Grp Z2) (@am_l Z2 Z2 true) (@am_r Z2 Z2 true).
Proof. exact (@ae_glue Z2 Z2 Z2 (@id Grp Z2) (@id Grp Z2) true). Qed.
