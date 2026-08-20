Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.

Generalizable All Variables.

(** * Pushouts in Top: the quotient topology, and adjunction spaces *)

(* Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
         §III.3, book p. 66 / PDF p. 75 (maclane:III.3:remark3)
   nLab:      https://ncatlab.org/nlab/show/pushout
   Wikipedia: https://en.wikipedia.org/wiki/Adjunction_space

   Mac Lane's remark that the Set gluing construction, carried out with
   the quotient topology, gives pushouts in Top -- adjunction spaces being
   the motivating case.

   TWO ERRATA IN THE ISSUE AND ITS SCOPING (#325).  First, its "Current
   state" paragraph says "The Top clause and the entire Grp clause are
   absent -- no Top or Grp category in-tree"; Instance/Top.v and
   Instance/Grp.v both exist now, and what was genuinely absent is the
   pushouts.  Second, and more usefully: it is NOT the case that the tree
   had no quotient-topology donor.  A grep for "quotient" under
   Instance/Top* finds only the homotopy quotient CATEGORY (Toph), but the
   construction is there twice under other names -- Instance/Top.v's
   [CP_open] (the cokernel-pair space, :635) and Instance/Top/Wedge.v's
   [wedge_open], whose surrounding section is literally headed "The
   quotient topology" (:141).  Both are quotient topologies on a sum, and
   this file is that same shape with the relation generalized.

   THE CONSTRUCTION, AND THE ONE PLACE IT DIFFERS FROM ITS DONORS.  The
   points are the coproduct's points -- [Top_pushout_carrier] records by
   [eq_refl] that the carrier IS Instance/Top/Coproduct.v's [sum_carrier].
   The relation is where the difference sits: [CP_rel] and [wedge_rel] are
   already transitive and are written as a [match], whereas an arbitrary
   span has no closed form, so [tp_rel] is an INDUCTIVE equivalence
   closure in the SHAPE of Instance/Sets/Pushout.v's [pushout_eq] --
   the same five constructors in the same order -- RESTATED here for
   spaces.  Read that precisely: this file does NOT [Require]
   Instance/Sets/Pushout.v, so it is a structural copy and not reuse,
   which matters in a tree that elsewhere distinguishes the two.
   The topology is then the [CP_open] / [wedge_open] triple: a
   respect-the-gluing clause plus the two restrictions.  That triple IS
   the quotient topology of [B + C -> (B + C)/~] -- a predicate downstairs
   is open when its preimage is, and a saturated predicate's preimage is
   open exactly when both restrictions are -- and it is what makes
   continuity of the mediator ([tp_med_continuous]) a three-line argument
   with no quotient-topology lemma required.

   NO UNIVERSE WALL IS MET.  Instance/Top/Coproduct.v and
   Instance/Top/Homotopy.v both record that opens of a space live one
   level above its points, which is why a product-of-spaces or a cylinder
   is not formable at the space's own level.  Nothing here quantifies over
   opens: [tp_open] only APPLIES [IsOpen] to restricted predicates, and
   the gluing clause is a Pi over the point type into [Type@{o}], so the
   whole construction stays at the space's own level.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  [Top_HasPushouts] is the
   deliverable.  The chosen pushout's apex and both injections are the
   hand-built ones at LEIBNIZ EQUALITY ([Top_pushout_apex_is_Pushout_Top]
   and siblings, [eq_refl]).  [pushout_med] is NOT [Top_po_med] on the
   nose -- Structure/Pushout.v states [pushout_ump] as a [Qed] lemma, so
   [unique_obj] is applied to an opaque constant; the negative is pinned
   in Test/ProbePushoutGrpTop.v alongside the IDENTICAL negative on the
   Grp side, which is what shows the cause is the donor's opacity and not
   either substrate.  [AdjunctionSpace] names the motivating case and
   [adjunction_glues] is the identification it exists for; nothing
   requires the attaching map to be an inclusion, so the name follows
   classical usage while the general pushout is what is built.

   NON-VACUITY, BOTH WAYS, AND NEITHER BY ASSERTION.  A non-identification
   cannot be read off [tp_rel] by induction, since [tpr_trans] passes
   through arbitrary intermediates; [tp_side] is the invariant that makes
   it reachable, and [empty_span_keeps_summands_apart] uses it to show
   that over the EMPTY span nothing is glued (the glue constructor's
   argument being a point of the empty space).  THE CONTRAST is
   [point_span_merges]: over the ONE-POINT span the two injections agree
   at the very pair Instance/Top/Coproduct.v's
   [point_sum_injections_differ] proves distinct in the coproduct.  So the
   pushout genuinely glues and is not the coproduct read twice -- the same
   shape of argument Instance/Top/Wedge.v's [wedge_is_not_sum] makes for
   the wedge.

   THE EMPTY SPAN IS THE COPRODUCT, AD HOC.  [Top_pushout_empty_iso] is an
   isomorphism in Top between the empty-span pushout and [Sum_Top], both
   legs having [fun u => u] as their underlying function.  CROSS-REFERENCE
   precisely: the GENERAL bridge "a pushout over the initial object is the
   binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and is NOT
   built here or in Instance/Grp/Pushout.v, which carries the
   corresponding ad-hoc Grp instance.  That the isomorphism is not an
   identity is measured rather than asserted: two conversion negatives
   reject the equality of the two [SetoidObject]s (the apex compares
   points by the inductive [tp_rel], the coproduct by [sum_setoid]'s
   [match]) and of the two topologies ([tp_open] carries a gluing clause
   that [sum_open] does not, redundant over the empty span but not
   definitionally absent).

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS, WITH THE CAUSE PROBED.
   [Pushout_Top@{u u0 u1 u2}] displays three separate space levels in its
   binder while its constraint block carries [u = u0] and [u = u1]: the
   three spaces sit at ONE level, an identification and not a bound, the
   same one Instance/Top/Coproduct.v measures for [Sum_Top].  The cause is
   probed and is NOT this construction: the bare definition
   [fun (A B : TopSpace) (f : @hom Top A B) => B] already elaborates with
   both spaces at [TopSpace@{u0}].  Naming a single Top hom is what
   identifies them.  [Top_HasPushouts@{u u0}] carries [u < u0] -- Top's
   own points-below-opens stratification -- and NO [Set] appears in any
   constraint block in this file, AS ON THE GRP SIDE, whose constant-leg
   free-product layer is likewise [Set]-free (measured: zero [Set]
   occurrences across [grp_const], [Grp_free_product], [Grp_fp_inl/inr],
   [Grp_fp_merge], [Grp_fp_inl_Section] and [Grp_Cocartesian]).  The one
   [Set]-pinned constant over there is [Grp_zero_hom_Section], which is
   the route NOT taken.  (An earlier draft of this header claimed the Grp
   free-product layer inherits a [Set] pin; that was false, contradicted
   Instance/Grp/Pushout.v's own measured statement, and was a leftover
   from the refuted first construction.)

   ENGINEERING FINDING, recorded because it cost time.  In
   [tp_rel_to_sum], writing [induction H; simpl] unfolds the sum setoid's
   [match] into its raw [eq_refl]-scaffolded eliminator form, after which
   [symmetry] and [transitivity] fail with an "Illegal application" of
   [@eq_refl] rather than with a missing-instance message.  Dropping the
   [simpl] and closing the two base cases with [inl_respects] /
   [inr_respects] keeps the goal at [≈] and the tactics work.  The related
   trap is that the binders must be written [u v : sum_carrier B C] rather
   than [u v : tp_point] even though the two types are convertible: only
   the [SetoidObject] spelling lets [≈] resolve, and with the [tp_point]
   spelling the statement silently elaborates at Leibniz equality.

   WHAT IS NOT DELIVERED.  No separation or compactness properties of the
   glued space, and in particular nothing about when an adjunction space
   is Hausdorff; no CW-complex or cell-attachment machinery; no mapping
   cylinder or mapping cone; no van Kampen theorem, and so no connection
   to Instance/Top/FundamentalGroupoid.v or to Instance/Grp/Pushout.v's
   amalgamated products; no subspace or general quotient topology as
   free-standing constructions (only the one this pushout needs); no
   indexed pushouts and no colimits of Top in general; no pointed variant,
   so Instance/Top/Wedge.v's [Top_pointed] is untouched; and no monic-legs
   refinement on this side -- Structure/Pushout/Split.v's generic
   statements apply to Top verbatim but no Top span is exhibited whose
   legs split. *)

(** ** The glued point set *)

Section TopPushout.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).

Definition tp_point : Type :=
  (carrier (top_carrier B) + carrier (top_carrier C))%type.

(* The identification generated by the span.  Unlike [Instance/Top.v]'s
   cokernel-pair relation and [Instance/Top/Wedge.v]'s basepoint
   relation -- both of which are already transitive and can be written as
   a [match] -- an arbitrary span has no closed form, so the relation is
   the inductive equivalence closure of Instance/Sets/Pushout.v. *)
Inductive tp_rel : tp_point → tp_point → Type :=
  | tpr_inl : ∀ b b' : carrier (top_carrier B),
      b ≈ b' → tp_rel (Datatypes.inl b) (Datatypes.inl b')
  | tpr_inr : ∀ c c' : carrier (top_carrier C),
      c ≈ c' → tp_rel (Datatypes.inr c) (Datatypes.inr c')
  | tpr_glue : ∀ a : carrier (top_carrier A),
      tp_rel (Datatypes.inl (f a)) (Datatypes.inr (g a))
  | tpr_sym : ∀ u v, tp_rel u v → tp_rel v u
  | tpr_trans : ∀ u v w, tp_rel u v → tp_rel v w → tp_rel u w.

Lemma tp_rel_refl : Reflexive tp_rel.
Proof using All.
  intros [b | c].
  - apply tpr_inl; reflexivity.
  - apply tpr_inr; reflexivity.
Qed.

Definition tp_setoid : Setoid tp_point := {|
  equiv := tp_rel;
  setoid_equiv :=
    Build_Equivalence tp_rel tp_rel_refl tpr_sym tpr_trans
|}.

Definition tp_carrier : SetoidObject := {|
  carrier := tp_point;
  is_setoid := tp_setoid
|}.

(** ** The quotient topology *)

(* The [CP_open] / [wedge_open] shape: a respect-the-gluing clause plus
   the two restrictions.  This IS the quotient topology of the surjection
   [B + C -> (B + C)/~]: a set downstairs is open exactly when its
   preimage upstairs is, and a saturated predicate's preimage is open
   exactly when both restrictions are. *)
Definition tp_open (W : tp_carrier → Type) : Type :=
  ((∀ u v : tp_carrier, tp_rel u v → W u → W v)
     ∧ IsOpen B (fun b => W (Datatypes.inl b))
     ∧ IsOpen C (fun c => W (Datatypes.inr c)))%type.

Lemma tp_respects (U V : tp_carrier → Type) :
  (∀ u, U u ↔ V u) → tp_open U → tp_open V.
Proof using All.
  intros H [HR [HB HC]].
  split; [| split ].
  - intros u v Huv Vu.
    exact (fst (H v) (HR u v Huv (snd (H u) Vu))).
  - exact (open_respects B _ _ (fun b => H (Datatypes.inl b)) HB).
  - exact (open_respects C _ _ (fun c => H (Datatypes.inr c)) HC).
Qed.

Lemma tp_proper (W : tp_carrier → Type) :
  tp_open W → ∀ u v : tp_carrier, u ≈ v → W u → W v.
Proof using All. intros [HR _] u v Huv Wu; exact (HR u v Huv Wu). Qed.

Lemma tp_union (I : Type) (U : I → (tp_carrier → Type)) :
  (∀ i, tp_open (U i)) → tp_open (fun u => { i : I & U i u }).
Proof using All.
  intro H.
  split; [| split ].
  - intros u v Huv [i Hi].
    exact (i; fst (H i) u v Huv Hi).
  - exact (open_union B I (fun i b => U i (Datatypes.inl b))
             (fun i => fst (snd (H i)))).
  - exact (open_union C I (fun i c => U i (Datatypes.inr c))
             (fun i => snd (snd (H i)))).
Qed.

Lemma tp_whole : tp_open (fun _ => poly_unit).
Proof using All.
  split; [| split ].
  - intros u v _ _; exact ttt.
  - exact (open_whole B).
  - exact (open_whole C).
Qed.

Lemma tp_inter (U V : tp_carrier → Type) :
  tp_open U → tp_open V → tp_open (fun u => U u ∧ V u).
Proof using All.
  intros [HRU [HBU HCU]] [HRV [HBV HCV]].
  split; [| split ].
  - intros u v Huv [Uu Vu].
    exact (HRU u v Huv Uu, HRV u v Huv Vu).
  - exact (open_inter B _ _ HBU HBV).
  - exact (open_inter C _ _ HCU HCV).
Qed.

Definition Pushout_Top : TopSpace := {|
  top_carrier   := tp_carrier;
  IsOpen        := tp_open;
  open_respects := tp_respects;
  open_proper   := tp_proper;
  open_union    := tp_union;
  open_whole    := tp_whole;
  open_inter    := tp_inter
|}.

(** ** The injections *)

Definition tp_inl_map : SetoidMorphism (top_carrier B) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros b b' Hb; exact (tpr_inl b b' Hb).
Defined.

Definition tp_inr_map : SetoidMorphism (top_carrier C) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros c c' Hc; exact (tpr_inr c c' Hc).
Defined.

Definition Top_po_in1 : B ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism B Pushout_Top tp_inl_map
    (fun W HW => fst (snd HW)).

Definition Top_po_in2 : C ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism C Pushout_Top tp_inr_map
    (fun W HW => snd (snd HW)).

(* The square commutes: this IS the [tpr_glue] constructor. *)
Lemma Top_po_square : Top_po_in1 ∘[Top] f ≈ Top_po_in2 ∘[Top] g.
Proof using All. intro a; exact (tpr_glue a). Qed.

End TopPushout.

Arguments tp_point {B C}.
Arguments tp_rel {A B C} f g u v.
Arguments tp_open {A B C} f g W.
Arguments Pushout_Top {A B C} f g.
Arguments Top_po_in1 {A B C} f g.
Arguments Top_po_in2 {A B C} f g.

(** ** The mediating continuous map *)

Section TopPushoutMediator.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).

Definition tp_med_fun (u : @tp_point B C) : carrier (top_carrier Q) :=
  match u with
  | Datatypes.inl b => q1 b
  | Datatypes.inr c => q2 c
  end.

Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(* Well-definedness on the quotient, by induction on the derivation.  The
   glue case is the ONLY one that consumes [Hcomm]. *)
Lemma tp_med_respects (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_med_fun u ≈ tp_med_fun v.
Proof using All.
  induction H; simpl.
  - now apply proper_morphism.
  - now apply proper_morphism.
  - exact (Hcomm a).
  - now symmetry.
  - now transitivity (tp_med_fun v).
Qed.

Definition tp_med_map
  : SetoidMorphism (top_carrier (Pushout_Top f g)) (top_carrier Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := tp_med_fun |}.
  intros u v Huv; exact (tp_med_respects u v Huv).
Defined.

(* Continuity.  The preimage of an open [W] is open in the glued space for
   three reasons, one per clause: it respects the gluing because the
   mediator does and [W] is [open_proper]; and its two restrictions are
   the preimages of [W] under [q1] and [q2], open by their continuity.
   NO quotient-topology lemma is needed -- the topology was DEFINED as the
   conjunction that makes this argument go through. *)
Lemma tp_med_continuous : Continuous (Pushout_Top f g) Q tp_med_map.
Proof using All.
  intros W HW.
  split; [| split ].
  - intros u v Huv Wu.
    exact (open_proper Q W HW (tp_med_fun u) (tp_med_fun v)
             (tp_med_respects u v Huv) Wu).
  - exact (continuity q1 W HW).
  - exact (continuity q2 W HW).
Qed.

Definition Top_po_med : Pushout_Top f g ~{Top}~> Q :=
  Build_ContinuousMorphism (Pushout_Top f g) Q tp_med_map tp_med_continuous.

Lemma Top_po_med_in1 : Top_po_med ∘[Top] Top_po_in1 f g ≈ q1.
Proof using All. intro b; reflexivity. Qed.

Lemma Top_po_med_in2 : Top_po_med ∘[Top] Top_po_in2 f g ≈ q2.
Proof using All. intro c; reflexivity. Qed.

Lemma Top_po_med_unique (v : Pushout_Top f g ~{Top}~> Q)
      (H1 : v ∘[Top] Top_po_in1 f g ≈ q1)
      (H2 : v ∘[Top] Top_po_in2 f g ≈ q2) :
  Top_po_med ≈ v.
Proof using All.
  intros [b | c]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
Qed.

End TopPushoutMediator.

Arguments Top_po_med {A B C} f g {Q} q1 q2 Hcomm.

(** ** The universal property, packaged *)

Local Obligation Tactic := idtac.

#[export] Program Instance Top_HasPushouts : HasPushouts Top := {|
  pushout := fun A B C f g =>
    {| Pull         := Pushout_Top f g;
       pullback_fst := Top_po_in1 f g;
       pullback_snd := Top_po_in2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (Top_po_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := Top_po_med f g q1 q2 Hcomm |}.
  - split.
    + exact (Top_po_med_in1 f g q1 q2 Hcomm).
    + exact (Top_po_med_in2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (Top_po_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(** ** The chosen pushout, and what reduces *)

Definition Top_pushout {A B C : TopSpace}
           (f : A ~{Top}~> B) (g : A ~{Top}~> C) : IsPushout f g :=
  @pushout Top Top_HasPushouts A B C f g.

Example Top_pushout_apex_is_Pushout_Top {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Example Top_pushout_in1_is_Top_po_in1 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

Example Top_pushout_in2_is_Top_po_in2 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in2 (Top_pushout f g) = Top_po_in2 f g := eq_refl.

(* The glued point set is the coproduct's point set on the nose: the
   pushout topology differs from the coproduct topology only in the
   respect-the-gluing clause, not in its points. *)
Example Top_pushout_carrier {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  carrier (top_carrier (Pushout_Top f g))
    = carrier (sum_carrier B C) := eq_refl.

(** ** Adjunction spaces

    The motivating case of Mac Lane's remark: [X] with [Y] attached along
    [f : A -> Y], for a subspace inclusion [i : A -> X].  Nothing here
    requires [i] to be an inclusion; the name follows the classical usage,
    and the general pushout is what is built. *)

Definition AdjunctionSpace {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y) : TopSpace :=
  Pushout_Top i f.

Definition adjunction_in_base {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : X ~{Top}~> AdjunctionSpace i f := Top_po_in1 i f.

Definition adjunction_in_attached {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : Y ~{Top}~> AdjunctionSpace i f := Top_po_in2 i f.

(* The attaching identification, which is what the construction exists
   for: a point of [A] and its image under [f] become the same point. *)
Lemma adjunction_glues {A X Y : TopSpace}
      (i : A ~{Top}~> X) (f : A ~{Top}~> Y) (a : carrier (top_carrier A)) :
  adjunction_in_base i f (i a) ≈ adjunction_in_attached i f (f a).
Proof. exact (@tpr_glue A X Y i f a). Qed.

(** ** Non-vacuity: the gluing is real, and it is confined to the span *)

(* Which summand a glued point came from.  This is the invariant that
   makes a NEGATIVE statement about [tp_rel] reachable: no induction on a
   generated equivalence yields a non-identification directly, because
   [tpr_trans] passes through arbitrary intermediates. *)
Definition tp_side {B C : TopSpace} (u : @tp_point B C) : bool :=
  match u with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Lemma tp_side_invariant {B C : TopSpace}
      (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
      (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_side u = tp_side v.
Proof.
  induction H; simpl; try reflexivity.
  - contradiction.
  - now symmetry.
  - now transitivity (tp_side v).
Qed.

(* Over the EMPTY span the two summands stay apart: the glue constructor
   is unusable, its argument being a point of the empty space. *)
Theorem empty_span_keeps_summands_apart {B C : TopSpace}
        (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
        (b : carrier (top_carrier B)) (c : carrier (top_carrier C)) :
  tp_rel f g (Datatypes.inl b) (Datatypes.inr c) → False.
Proof.
  intro H.
  pose proof (tp_side_invariant f g _ _ H) as Hs.
  simpl in Hs.
  discriminate Hs.
Qed.

(* THE CONTRAST.  Over the ONE-POINT span the two injections agree at the
   very pair that Instance/Top/Coproduct.v's [point_sum_injections_differ]
   proves distinct in the coproduct.  So the pushout genuinely glues, and
   is not the coproduct read twice -- the same shape of argument
   Instance/Top/Wedge.v's [wedge_is_not_sum] makes for the wedge. *)
Theorem point_span_merges :
  @tp_rel Point_Top Point_Top Point_Top
    (@id Top Point_Top) (@id Top Point_Top)
    (Datatypes.inl ttt) (Datatypes.inr ttt).
Proof.
  exact (@tpr_glue Point_Top Point_Top Point_Top
           (@id Top Point_Top) (@id Top Point_Top) ttt).
Qed.

(** ** The pushout over the empty space IS the coproduct

    Cross-reference: the GENERAL bridge "a pushout over the initial object
    is the binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and
    is NOT built here.  What follows is the ad-hoc Top instance, the
    counterpart of Instance/Grp/Pushout.v's [Grp_Cocartesian].  Both
    comparison maps are the IDENTITY on points; all the content is in the
    two topologies and the two setoids agreeing. *)

Section EmptySpanIsCoproduct.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(* Stated over [sum_carrier B C] rather than over [tp_point], although
   the two types are convertible: writing the binder as the SetoidObject
   is what lets [≈], [symmetry] and [transitivity] resolve the sum setoid
   -- with a [tp_point] binder they default to Leibniz equality and the
   proof does not elaborate. *)
Lemma tp_rel_to_sum (u v : sum_carrier B C) (H : tp_rel Ef Eg u v) :
  u ≈ v.
Proof using All.
  induction H.
  - now apply inl_respects.
  - now apply inr_respects.
  - contradiction.
  - now symmetry.
  - now transitivity v.
Qed.

Lemma sum_rel_to_tp (u v : sum_carrier B C) (H : u ≈ v) :
  tp_rel Ef Eg u v.
Proof using All.
  destruct u as [b | c], v as [b' | c']; simpl in H.
  - exact (@tpr_inl Empty_Top B C Ef Eg b b' H).
  - contradiction.
  - contradiction.
  - exact (@tpr_inr Empty_Top B C Ef Eg c c' H).
Qed.

Definition tp_to_sum_map
  : SetoidMorphism (top_carrier (Pushout_Top Ef Eg)) (sum_carrier B C).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (tp_rel_to_sum u v Huv).
Defined.

Definition tp_from_sum_map
  : SetoidMorphism (sum_carrier B C) (top_carrier (Pushout_Top Ef Eg)).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (sum_rel_to_tp u v Huv).
Defined.

Definition tp_to_sum : Pushout_Top Ef Eg ~{Top}~> Sum_Top B C.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Pushout_Top Ef Eg) (Sum_Top B C) tp_to_sum_map _).
  intros W HW.
  split; [| split ]; [| exact (fst HW) | exact (snd HW) ].
  intros u v Huv Wu.
  exact (sum_proper B C W HW u v (tp_rel_to_sum u v Huv) Wu).
Defined.

Definition tp_from_sum : Sum_Top B C ~{Top}~> Pushout_Top Ef Eg.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Sum_Top B C) (Pushout_Top Ef Eg) tp_from_sum_map _).
  intros W HW.
  exact (fst (snd HW), snd (snd HW)).
Defined.

(* An isomorphism in Top.  Both legs have [fun u => u] as their underlying
   function, so each composite is the identity function and the two
   coherence obligations close by reflexivity of the target setoid. *)
Definition Top_pushout_empty_iso : Pushout_Top Ef Eg ≅[Top] Sum_Top B C.
Proof using All.
  unshelve refine {| to := tp_to_sum; from := tp_from_sum |}.
  - intro u; apply Equivalence_Reflexive.
  - intro u; apply Equivalence_Reflexive.
Defined.

End EmptySpanIsCoproduct.
