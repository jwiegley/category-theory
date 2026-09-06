Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * A one-level subobject classifier for [Sets], conditionally *)

(* Mac Lane, CWM 2nd ed., §IV.9 construction 1, book p. 105
   ([maclane:IV.9:construction1]).  Verbatim:

     "The characteristic function of a subset S ⊂ X is the two-valued
      function ψ_S : X → {0, 1} on X with the values

          ψ_S x = 0  if x ∈ S ;    ψ_S x = 1  if x ∈ X but x ∉ S .   (1)"

     "Such characteristic functions are often used in probability theory;
      in logic, {0, 1} is the set of two "truth values" with 0 the value
      "truth".  One says that the monomorphism (the typical subset)
      t : {0} → {0, 1} is a "subobject classifier" for the category of
      sets."

     "In general, a subobject classifier for a category C with a terminal
      object 1 is defined to be a monomorphism t : 1 ↣ Ω such that every
      monomorphism m in C is a pullback of t in an unique way.  In other
      words, for each m there exists a unique pullback square

          S ──→ 1
         m│     │t                                                   (3)
          ↓     ↓
          X ─ψ→ Ω ."

   Fong & Spivak, *Seven Sketches in Compositionality*, §7.2.2, printed
   p. 229 ([7sketches:7.2.2:construction-subobject-classifier-set]).  Verbatim:

     "The subobject classifier in Set is the set of booleans,

          Ω_Set := 𝔹 = {true, false}.                              (7.14)"

     "⌜m⌝(y) := true   if m(x) = y for some x ∈ X
                false  otherwise"

     "X = {y ∈ Y | p(y) = true}.                                   (7.15)"

   THE CONVENTION SWAP.  Mac Lane's ψ_S takes the value 0 ON the subset
   and 1 off it, with 0 the value "truth"; Seven Sketches, the tree's
   [FinSet_Classifier] (whose [truth] is [fin_true]) and everything below
   put [true] — here [ptrue], resp. [Powerset_truth_point] — ON the
   subset.  The two conventions differ by the swap 0 ↔ 1, an automorphism
   of the two-element truth object, and this file follows the tree.  Read
   that swap as one of NAMES: [fin_true] is [Fin.F1], the first element
   of [Fin.t 2], so as a numeral it is Mac Lane's 0 and only its name is
   Seven Sketches'; neither [ptrue] nor [Powerset_truth_point] carries a
   numeral at all (a measurement made while landing
   Instance/Fun/Classifier.v, whose sieve classifier carries none
   either).

   WHAT IS DELIVERED, AND AT WHICH STRENGTH.  A genuine
   [@SubobjectClassifier Sets@{o so} Sets_Terminal] instance at ONE
   universe level, CONDITIONALLY, in two shapes:

     [Sets_Classifier     : Untruncate@{o} -> SubobjectClassifier]
        with Ω := [Powerset_Omega] (the level-o [Prop] truth-value setoid
        of Instance/Sets/Powerset.v) and truth := [Powerset_truth_point],
        both read back by [eq_refl];

     [Sets_Classifier_dec : DecImage@{o so} -> SubobjectClassifier]
        with Ω := [BoolSetoid] (a polymorphic two-element setoid — Seven
        Sketches' 𝔹 at level o) and truth := [ptrue], both [eq_refl].

   [Untruncate] says every impredicative truncation at level o can be
   inverted; [DecImage] says every mono's image membership is decidable.
   Neither has an axiom-free inhabitant in this tree.  Both follow from
   informative excluded middle [IEM] at level o, and [DecImage] is in fact
   EQUIVALENT to it ([DecImage_iff_IEM]).

   THE DISCLOSURE, IN THREE PARTS, as the issue's Definition of Done asks.
   (i) NO unconditional axiom-free instance is built here.  (ii) NO
   impossibility theorem is proved here.  (iii) An in-tree impossibility
   proof is out of reach in a precise sense: the classifier IS derivable
   from Coq's own classical axioms — a scratch development compiled
   against this worktree builds the instance out of [classic] and
   [constructive_indefinite_description] (Coq.Logic.ClassicalEpsilon) and
   [Print Assumptions] reports exactly those two — so an in-tree
   impossibility theorem would refute a classically valid statement.  That
   is an ARGUMENT, not a theorem: nothing below proves it, and the
   classical instance is deliberately not shipped.

   WHY A NEW FILE.  Instance/Sets/Powerset.v and
   Instance/Sets/Powerset/Universal.v both Require
   Instance/Sets/Classifier.v, so that file cannot Require either of them
   and the instance whose Ω is [Powerset_Omega] cannot live there.  The
   precedent for a cycle-forced sibling is Structure/Limit/Indexed/Hom.v.

   THE MEASURED FACTS THIS FILE RESTS ON, each compiled.

   - [SubobjectClassifier] takes TWO arguments, a category and a
     [Terminal]; the [HasPullbacks] of its declaring section is used by
     the theorems below the class, not by the class.  Offering
     [Sets_HasPullbacks] as a third argument is an "Illegal application"
     (a TYPING refusal), pinned in the probe.
   - The CLASS is formable at [Sets@{o so}]: this file inhabits it.
   - [classifier_classifies], [Sub_classifier_natural] and
     [Sub_Representable] are NOT: each carries the BOUND [u <= u0] over
     [C : Category@{u u0 u0}] — objects ≤ homs — while
     [Sets@{o so} : Category@{so o o}] has o < so.  The
     refusals are universe inconsistencies (FORMABILITY), and
     [char_reindex] IS accepted at [Sets] as the control.  So at [Sets]
     the classification theorem is replaced by its two round trips,
     section (I) below, which build no object of [Sets] with carrier
     [SubObj x] (their ≈ is still the [SubObj_Setoid] instance).
   - [SubObj x] is a [Type@{so}], so no [{| carrier := SubObj x |}] is an
     [obj[Sets@{o so}]] (control: a hom-setoid IS one), and
     Instance/Sets/Classifier.v's [PropSetoid] is likewise refused
     (controls: [Powerset_Omega] and [BoolSetoid] accepted).  Both are
     pinned.
   - The naive elimination of an impredicative truncation without
     [Untruncate], namely [fun P h => h P (fun p => p)], is refused with
     "Cannot enforce o <= Prop"; the [Prop]-valued instantiation
     [powerset_squash_prop_inert] of Instance/Sets/Powerset/Universal.v
     is the accepted control.  That refusal is exactly what [Untruncate]
     buys, and why this hypothesis and not a weaker one.

   THE RESIZING READING.  A one-level classifier for [Sets] is inter-derivable
   with a resizing-shaped structure: an object Ω of [Sets] at level o with a
   point t, an assignment w carrying every [Type@{o}] to a truth value, an
   introduction and an elimination rule identifying [w P ≈ t] with P, and
   extensionality of Ω at t.  That is the record [SmallClassifierExt], and
   [classifier_iff_small] is the pair of passages, both directions, over an
   arbitrary [Sets@{o so}].  [Sets_Classifier] is built THROUGH it;
   [Sets_Classifier_dec] is built directly from [char_of_dec] and its two law
   lemmas, and [classifier_of_small] of [small_of_IEM] is a THIRD classifier,
   refuted equal to [Sets_Classifier_dec] at [eq_refl] in the probe.  So the
   resizing structure is an engine rather than a by-product: the [sce_ext] field
   of the forward passage spends [char_unique] twice (through
   [subone_pt_classifies]) and [char_respects] once (itself derived, in
   Structure/SubobjectClassifier.v, from [char_pullback], [char_unique], the
   pullback lemma [is_pullback_precompose_iso] and [one_unique]).

   ONE STORY, NOT TWO.  The one-level characteristic map IS the truncation of
   Instance/Sets/Classifier.v's cross-universe one.  Measured strict first, two
   grades and no third:

     value    [char (Sets_Classifier U) m M b
                = Powerset_squash (char_setoid m b)]  by [eq_refl];
     record   the same identification as [SetoidMorphism] records, one
              universe up, is refused at [eq_refl] (a CONVERSION refusal,
              pinned, the two [proper_morphism] certificates being
              separately elaborated) and holds at ≈
              ([bridge_record_equiv]);
     whole    no [Transform] is involved on either side, so there is no
              third grade to measure.

   So Classifier.v's [sets_char_pullback] and [sets_char_unique] and the
   instances here are one construction seen at two levels, joined by
   [Powerset_squash]; they are not parallel developments.

   UNIVERSES.  Every top-level constant of sections (B)–(J) carries explicit
   binders; of section (K)'s ten, the six [FinSet] constants carry none and the
   four [iem_routes_*] carry [@{o so}].  Not one constraint block of this file
   contains a universe EQUATION; the blocks are bounds only.  [Sets_Classifier]
   and everything downstream of [Powerset_Omega] — thirteen constants — carry
   the strict lower bound [Set < o], which is [Prop : Type@{Set+1}] arriving
   through [Powerset_Prop_truth] — a BOUND, never a pin, but not inert: it
   excludes exactly the [Sets] whose carrier universe is the literal [Set].
   Measured: [Sets@{Set so}] and [Sets_Terminal@{so Set}] are formable and
   [Sets_Classifier_dec@{Set so}] is accepted there, while
   [Sets_Classifier@{Set so}] and [Powerset_Omega@{Set}] are refused, so the two
   conditional instances differ in reach as well as in truth object.
   [Sets_Classifier_dec] and the whole [BoolSetoid] route carry no [Set] in any
   binder or block (the [max(Set, …)] in [DecImage]'s and [IEM]'s own sorts is
   the sum type's and is inert).  The six [FinSet] constants of section (K)
   carry a [Set] bound of their own ([Set < u1], [Set < u2]), inherited from
   [FinSet]'s declaration and not from [Powerset_Omega].

   WHAT IS NOT DELIVERED.  No unconditional axiom-free instance and no
   impossibility theorem (see the three-part disclosure above).  No proof that
   [Untruncate] or [DecImage] is underivable — only that this tree has no
   axiom-free inhabitant of either, with [IEM] cited as what would give both.
   No naturality: [Sub_classifier_natural] is not statable at [Sets].  No
   [ElementaryTopos Sets] and no power objects at [Sets].  No functor
   [FinSet ⟶ Sets], so the two accounts below are related in prose and by a
   shared statement shape, not by transport.  The two conditional instances'
   truth objects are NOT compared: no isomorphism [BoolSetoid ≅ Powerset_Omega]
   is built, under [IEM] or otherwise.  No round trip for
   [classifier_iff_small]: the two passages are inter-derivable, and neither
   composite is compared with the identity at any strength.  Nothing here is
   registered as an [Instance] — the hypotheses must not become globally
   resolvable, and neither must a chosen classifier.

   COUNTS, WITH THEIR CRITERIA.  Constants closed under the global context:
   92/92 with zero [Axioms:] lines, counted as the 89 entries [Print Module]
   emits at five-space indent plus the two constructors of [poly_bool] and the
   [Build_*] of [SmallClassifierExt], which it lists only on a continuation line
   or after a [:=]; every one queried FULLY QUALIFIED, and all 92 are in the
   [print-assumptions] gate.  ([Print Module] wraps this module's own head
   across three lines, so a line-anchored sweep of its output harvests no
   spurious name here; and it renders the eighteen [Qed]-closed constants as
   [Parameter] — a display convention, not an axiom.)  [Defined] tokens: 14, of
   which ELEVEN are load-bearing — measured by flipping each ALONE to [Qed]:
   only [IEM_of_DecImage], [sce_pullback] and [char_of_dec_pullback] survive the
   flip, and they are kept [Defined] because they produce data.  Statements
   closed by [:= eq_refl]: 18.  Transitive in-project closure excluding this
   file: 70 modules, with drop-one marginals Instance/Sets/Powerset/Universal
   19, Instance/Sets/Pullback 12, Instance/FinSet/Classifier 2 and every other
   Require 0; of the seventeen Requires, sixteen are textually load-bearing
   (dropping any one stops the build) and only Structure/Pullback is not,
   arriving through Structure/SubobjectClassifier.  Name collisions swept
   whole-word over every [.v] of the build set, instrument-checked at [Full] and
   [Monoid]: no DECLARATION collides with any of the 92 (after one rename
   recorded in the report), the only whole-word hits outside this file and its
   probe being the prose pointers to [Sets_Classifier], [Untruncate] and
   [DecImage] that this same change writes into Instance/Sets/Classifier.v and
   Instance/Sets/Powerset/Universal.v.  This file contributes ZERO [make todo]
   hits; its probe carries the refutation commands. *)

(* ------------------------------------------------------------------------ *)
(** ** (B) The image predicate, and subobjects of the terminal setoid *)

   (* [sets_in_image m b] is Mac Lane's "b ∈ S" and Seven Sketches' "m(x) = y
   for some x": the [Type@{o}]-valued sigma that Instance/Sets/Classifier.v's
   [char_setoid] also computes.  [SubOne P] is the subobject of the terminal
   setoid cut by a proposition P, with [subone_incl] its inclusion; the
   inclusion is monic for EVERY P, because its DOMAIN [SubOne P] is subterminal
   — its setoid is [triv_rel], so any two morphisms into it already agree, which
   is what left-cancellation asks (terminality of the CODOMAIN would not do it:
   the unique map [BoolSetoid ~> 1] is not monic).  Together they let a truth
   value be probed by a subobject of 1, which is how section (D) runs. *)

Definition sets_in_image@{o} {u x : SetoidObject@{o o}}
  (m : SetoidMorphism@{o o o} u x) (b : carrier x) : Type@{o} :=
  ∃ a : carrier u, @equiv _ (is_setoid x) (m a) b.

Definition triv_rel@{o} (P : Type@{o}) : crelation@{o o} P :=
  fun _ _ => poly_unit@{o}.

Lemma triv_equivalence@{o} (P : Type@{o}) : Equivalence@{o o} (triv_rel@{o} P).
Proof. unfold triv_rel; constructor; repeat intro; exact ttt. Qed.

Definition SubOne@{o} (P : Type@{o}) : SetoidObject@{o o} :=
  {| carrier := P
   ; is_setoid := {| equiv := triv_rel@{o} P
                   ; setoid_equiv := triv_equivalence@{o} P |} |}.

Definition subone_incl@{o so} (P : Type@{o}) :
  SubOne@{o} P
    ~{Sets@{o so}}~> (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} P (is_setoid (SubOne@{o} P))
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (fun _ => ttt) _).
  intros ? ? ?; reflexivity.
Defined.

Lemma subone_incl_monic@{o so} (P : Type@{o}) :
  @Monic Sets@{o so} (SubOne@{o} P)
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (subone_incl@{o so} P).
Proof. constructor; intros z g1 g2 _ ?; exact ttt. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The three hypotheses, and the passages between them *)

(* [DecImage] is the issue's "decidability discipline": every mono's
   image membership is decidable.  [Untruncate] inverts the
   impredicative truncation of Instance/Sets/Powerset.v at level o.
   [IEM] is informative excluded middle at level o.  IEM gives both, and
   [DecImage] gives IEM back — the terminal setoid's point is in the
   image of [subone_incl P] exactly when P — so [DecImage] and [IEM] are
   EQUIVALENT.  Whether [Untruncate] implies [IEM] is not settled here
   and no passage in that direction is built. *)

Inductive poly_bool@{u} : Type@{u} := ptrue | pfalse.

Definition BoolSetoid@{o} : SetoidObject@{o o} :=
  {| carrier := poly_bool@{o} ; is_setoid := eq_Setoid@{o} poly_bool@{o} |}.

Definition DecImage@{o so} :=
  ∀ (u x : SetoidObject@{o o}) (m : u ~{Sets@{o so}}~> x),
    @Monic Sets@{o so} u x m →
    ∀ b : carrier x, sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).

Definition Untruncate@{o} := ∀ P : Type@{o}, Powerset_squash@{o} P -> P.

Definition IEM@{o} := ∀ P : Type@{o}, P + (P -> False).

Definition untruncate_of_IEM@{o} (E : IEM@{o}) : Untruncate@{o} :=
  fun P H => match E P with
             | inl p => p
             | inr N => match H False (fun p => N p) with end
             end.
Definition DecImage_of_IEM@{o so} (E : IEM@{o}) : DecImage@{o so} :=
  fun u x m M b => E (sets_in_image@{o} m b).

Definition IEM_of_DecImage@{o so} (D : DecImage@{o so}) : IEM@{o}.
Proof.
  intro P.
  destruct (D (SubOne@{o} P)
              (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
              (subone_incl@{o so} P) (subone_incl_monic@{o so} P) ttt)
    as [ H | N ].
  - left. exact (projT1 H).
  - right. intro p. apply N. exists p. reflexivity.
Defined.

Definition DecImage_iff_IEM@{o so} :
  (DecImage@{o so} -> IEM@{o}) * (IEM@{o} -> DecImage@{o so}) :=
  (IEM_of_DecImage@{o so}, DecImage_of_IEM@{o so}).

Record SmallClassifierExt@{o} : Type@{o+1} := {
  sce_Om : SetoidObject@{o o};
  sce_t  : carrier sce_Om;
  sce_w  : Type@{o} -> carrier sce_Om;
  sce_intro : ∀ P : Type@{o}, P -> @equiv _ (is_setoid sce_Om) (sce_w P) sce_t;
  sce_elim  : ∀ P : Type@{o}, @equiv _ (is_setoid sce_Om) (sce_w P) sce_t -> P;
  sce_ext   : ∀ v v' : carrier sce_Om,
                (@equiv _ (is_setoid sce_Om) v sce_t
                   -> @equiv _ (is_setoid sce_Om) v' sce_t) ->
                (@equiv _ (is_setoid sce_Om) v' sce_t
                   -> @equiv _ (is_setoid sce_Om) v sce_t) ->
                @equiv _ (is_setoid sce_Om) v v'
}.

Definition subone_pt@{o so} {x : SetoidObject@{o o}} (b : carrier x) :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) ~{Sets@{o so}}~> x.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (carrier x) (is_setoid x) (fun _ => b) _).
  intros ? ? ?; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (D) The resizing characterisation *)

(* A one-level classifier for [Sets] is exactly the record below: an
   object Ω at level o, a point t, an assignment w of a truth value to
   every [Type@{o}], introduction and elimination identifying [w P ≈ t]
   with P, and extensionality of Ω at t.  The two passages are
   [classifier_of_small] and [small_of_classifier], packaged as
   [classifier_iff_small].  [sce_ext] on the forward side spends
   [char_unique] twice (through [subone_pt_classifies]) and
   [char_respects] once (through [subone_respects]). *)

(* ---- the converse: a small classifier gives a SubobjectClassifier ---- *)

Definition sce_truth@{o so} (S : SmallClassifierExt@{o}) :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> sce_Om@{o} S.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (carrier (sce_Om@{o} S)) (is_setoid (sce_Om@{o} S))
       (fun _ => sce_t@{o} S) _).
  intros ? ? ?; reflexivity.
Defined.

Definition sce_char@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) : x ~{Sets@{o so}}~> sce_Om@{o} S.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       (carrier (sce_Om@{o} S)) (is_setoid (sce_Om@{o} S))
       (fun b => sce_w@{o} S (sets_in_image@{o} m b)) _).
  intros b b' Hbb'.
  apply (sce_ext@{o} S).
  - intro Hv. apply (sce_intro@{o} S).
    destruct (sce_elim@{o} S _ Hv) as [a Ha].
    exists a. now transitivity b.
  - intro Hv. apply (sce_intro@{o} S).
    destruct (sce_elim@{o} S _ Hv) as [a Ha].
    exists a. transitivity b'; [ exact Ha | now symmetry ].
Defined.

Definition sets_monic_inj@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m) :
  ∀ a a' : carrier u, m a ≈ m a' -> a ≈ a' :=
  snd (injectivity_is_monic m) M.

Definition sce_pullback@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @IsPullback Sets@{o so} x
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (sce_Om@{o} S)
    (sce_char@{o so} S m M) (sce_truth@{o so} S)
    u m (@one Sets@{o so} Sets_Terminal@{so o} u).
Proof.
  constructor.
  - intro a; simpl.
    apply (sce_intro@{o} S). exists a. reflexivity.
  - intros Q q1 q2 Hq.
    assert (Him : ∀ z : carrier Q, sets_in_image@{o} m (q1 z)).
    { intro z. apply (sce_elim@{o} S).
      specialize (Hq z); simpl in Hq. exact Hq. }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine
        (@Build_SetoidMorphism@{o o o}
           (carrier Q) (is_setoid Q) (carrier u) (is_setoid u)
           (fun z => projT1 (Him z)) _).
      intros z z' Hzz'.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | ].
      transitivity (q1 z').
      * exact (proper_morphism q1 _ _ Hzz').
      * symmetry; exact (projT2 (Him z')).
    + split.
      * intro z; simpl. exact (projT2 (Him z)).
      * intro z; simpl. destruct (q2 z); reflexivity.
    + intros v [Hv1 Hv2] z; simpl.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | symmetry; exact (Hv1 z) ].
Defined.

Definition sce_char_unique@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (h : x ~{Sets@{o so}}~> sce_Om@{o} S)
  (HP : @IsPullback Sets@{o so} x
          (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (sce_Om@{o} S)
          h (sce_truth@{o so} S) u m
          (@one Sets@{o so} Sets_Terminal@{so o} u)) :
  h ≈ sce_char@{o so} S m M.
Proof.
  intro b.
  destruct HP as [Hc Hu].
  apply (sce_ext@{o} S).
  - intro Hb.
    apply (sce_intro@{o} S).
    unshelve epose proof
      (Hu (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
          (subone_pt@{o so} b)
          (@one Sets@{o so} Sets_Terminal@{so o} _) _) as U.
    { intro z; simpl; destruct z; exact Hb. }
    destruct (unique_property U) as [U1 _].
    exists (unique_obj U ttt). exact (U1 ttt).
  - intro Hw.
    destruct (sce_elim@{o} S _ Hw) as [a Ha].
    transitivity (h (m a)).
    + symmetry; exact (proper_morphism h _ _ Ha).
    + exact (Hc a).
Qed.

Definition classifier_of_small@{o so} (S : SmallClassifierExt@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  @Build_SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
    (sce_Om@{o} S) (sce_truth@{o so} S)
    (fun u x m M => sce_char@{o so} S m M)
    (fun u x m M => sce_pullback@{o so} S m M)
    (fun u x m M h HP => sce_char_unique@{o so} S m M h HP).

Lemma subone_respects@{o so} (P Q : Type@{o}) (f : P -> Q) (g : Q -> P) :
  @equiv _ (@SubObj_Setoid Sets@{o so}
              (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
    (@Build_SubObj Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
       (SubOne@{o} P) (subone_incl@{o so} P) (subone_incl_monic@{o so} P))
    (@Build_SubObj Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
       (SubOne@{o} Q) (subone_incl@{o so} Q) (subone_incl_monic@{o so} Q)).
Proof.
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := _ ; from := _ |}.
    + unshelve refine (@Build_SetoidMorphism@{o o o} P
        (is_setoid (SubOne@{o} P))
        Q (is_setoid (SubOne@{o} Q)) f _). intros ? ? ?; exact ttt.
    + unshelve refine (@Build_SetoidMorphism@{o o o} Q
        (is_setoid (SubOne@{o} Q))
        P (is_setoid (SubOne@{o} P)) g _). intros ? ? ?; exact ttt.
    + intro z; exact ttt.
    + intro z; exact ttt.
  - intro z; reflexivity.
Qed.

(* ---- forward: a SubobjectClassifier gives a small one ---- *)

Definition sce_of_w@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS) :=
  @char Sets@{o so} Sets_Terminal@{so o} HS (SubOne@{o} P)
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (subone_incl@{o so} P) (subone_incl_monic@{o so} P) ttt.

Lemma sce_of_intro@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) : P ->
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
    (sce_of_w@{o so} HS P)
    (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt).
Proof.
  intro p.
  exact (is_pullback_commutes
           (@char_pullback Sets@{o so} Sets_Terminal@{so o} HS _ _
              (subone_incl@{o so} P) (subone_incl_monic@{o so} P)) p).
Qed.

Lemma sce_of_elim@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) :
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
    (sce_of_w@{o so} HS P)
    (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) -> P.
Proof.
  intro Ht.
  pose proof (is_pullback_ump
    (@char_pullback Sets@{o so} Sets_Terminal@{so o} HS _ _
       (subone_incl@{o so} P) (subone_incl_monic@{o so} P))
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@id Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
    (@one Sets@{o so} Sets_Terminal@{so o}
       (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))) as U.
  unshelve epose proof (U _) as U'.
  { intro z; destruct z; exact Ht. }
  exact (unique_obj U' ttt).
Qed.

Lemma subone_pt_classifies@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (v : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) :
  @IsPullback Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@Ω Sets@{o so} Sets_Terminal@{so o} HS)
    (subone_pt@{o so} v) (@truth Sets@{o so} Sets_Terminal@{so o} HS)
    (SubOne@{o} (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
                   (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))
    (subone_incl@{o so} _) (@one Sets@{o so} Sets_Terminal@{so o} _).
Proof.
  constructor.
  - intro p; simpl. exact p.
  - intros Q q1 q2 Hq.
    assert (Hz : ∀ z : carrier Q,
             @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
               (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)).
    { intro z; specialize (Hq z); simpl in Hq.
      destruct (q2 z); exact Hq. }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (@Build_SetoidMorphism@{o o o}
        (carrier Q) (is_setoid Q) _ (is_setoid (SubOne@{o} _)) Hz _).
      intros ? ? ?; exact ttt.
    + split; intro z; simpl; destruct (q1 z); try destruct (q2 z); reflexivity.
    + intros vv _ z; exact ttt.
Qed.

Lemma sce_of_ext@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (v v' : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
  (f : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) ->
       @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt))
  (g : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) ->
       @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)) :
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v v'.
Proof.
  assert (Hv : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
                 (sce_of_w@{o so} HS
                    (@equiv _
                       (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
                       v (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))).
  { exact (@char_unique Sets@{o so} Sets_Terminal@{so o} HS _ _
             (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
             (subone_pt@{o so} v) (subone_pt_classifies@{o so} HS v) ttt). }
  assert (Hv' : @equiv _
                 (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
                 (sce_of_w@{o so} HS
                    (@equiv _
                       (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
                       v' (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))).
  { exact (@char_unique Sets@{o so} Sets_Terminal@{so o} HS _ _
             (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
             (subone_pt@{o so} v') (subone_pt_classifies@{o so} HS v') ttt). }
  transitivity (sce_of_w@{o so} HS
    (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
       (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt))); [ exact Hv | ].
  transitivity (sce_of_w@{o so} HS
    (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
       (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)));
    [ | symmetry; exact Hv' ].
  exact (@char_respects Sets@{o so} Sets_Terminal@{so o} HS _ _ _
           (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
           (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
           (subone_respects@{o so} _ _ f g) ttt).
Qed.

Definition small_of_classifier@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}) :
  SmallClassifierExt@{o} :=
  {| sce_Om := @Ω Sets@{o so} Sets_Terminal@{so o} HS
   ; sce_t := @truth Sets@{o so} Sets_Terminal@{so o} HS ttt
   ; sce_w := sce_of_w@{o so} HS
   ; sce_intro := sce_of_intro@{o so} HS
   ; sce_elim := sce_of_elim@{o so} HS
   ; sce_ext := sce_of_ext@{o so} HS |}.

Definition classifier_iff_small@{o so} :
  (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
     -> SmallClassifierExt@{o})
  * (SmallClassifierExt@{o}
     -> @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  := (small_of_classifier@{o so}, classifier_of_small@{o so}).

(* ------------------------------------------------------------------------ *)
(** ** (E) The [Untruncate] instance, and the two-element small classifier *)

(* [Sets_Classifier] is the issue's Verification-block name.  Its Ω is
   [Powerset_Omega] and its truth [Powerset_truth_point], both by
   [eq_refl]; the hypothesis is used exactly once, in [sce_elim].
   [small_of_IEM] is Seven Sketches' Ω_Set = 𝔹 as a small classifier. *)

Definition small_of_untruncate@{o} (U : Untruncate@{o}) :
  SmallClassifierExt@{o}.
Proof.
  unshelve refine
    {| sce_Om := Powerset_Omega@{o} ; sce_t := Powerset_truth_point@{o}
     ; sce_w := fun P => Powerset_squash@{o} P |}.
  - intros P p; unfold Powerset_Prop_truth_equiv; split; intros _.
    + exact I.
    + exact (Powerset_squash_intro@{o} p).
  - intros P Hp; unfold Powerset_Prop_truth_equiv in Hp.
    exact (U P (proj2 Hp I)).
  - intros v v' f g; unfold Powerset_Prop_truth_equiv in *; split.
    + intro Hv. exact (proj2 (f (conj (fun _ => I) (fun _ => Hv))) I).
    + intro Hv. exact (proj2 (g (conj (fun _ => I) (fun _ => Hv))) I).
Defined.

Definition Sets_Classifier@{o so} (U : Untruncate@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  classifier_of_small@{o so} (small_of_untruncate@{o} U).

Example sets_classifier_omega@{o so} (U : Untruncate@{o}) :
  @Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)
    = Powerset_Omega@{o} := eq_refl.

Example sets_classifier_truth@{o so} (U : Untruncate@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) ttt
    = Powerset_truth_point@{o} := eq_refl.

Definition small_of_IEM@{o} (E : IEM@{o}) : SmallClassifierExt@{o}.
Proof.
  unshelve refine
    {| sce_Om := BoolSetoid@{o} ; sce_t := ptrue@{o}
     ; sce_w := fun P => match E P with
                         | inl _ => ptrue@{o} | inr _ => pfalse@{o} end |}.
  - intros P p; simpl.
    destruct (E P) as [_|N]; [ reflexivity | exfalso; exact (N p) ].
  - intros P Hp; simpl in Hp.
    destruct (E P) as [p|_]; [ exact p | discriminate Hp ].
  - intros v v' f g; simpl in *.
    destruct v; destruct v'; try reflexivity.
    + symmetry; exact (f eq_refl).
    + exact (g eq_refl).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (F) The per-mono characteristic map, and the [DecImage] instance *)

(* [char_of_dec] is Seven Sketches' ⌜m⌝ built from the decidability of
   ONE mono's image — no global hypothesis appears in its type — with
   the classifying square [char_of_dec_pullback] and the uniqueness
   clause [char_of_dec_unique] proved for it directly.  The global
   instance [Sets_Classifier_dec] is that data taken at every mono, so
   its [char] IS [char_of_dec] by [eq_refl]. *)

Definition SetsDec@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) : Type@{o} :=
  ∀ b : carrier x, sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).

Definition dec_truth@{o so} :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun _ => ptrue@{o}) _).
  intros ? ? ?; reflexivity.
Defined.

Definition char_of_dec@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) : x ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun b => match d b with inl _ => ptrue | inr _ => pfalse end) _).
  intros b b' Hbb'.
  destruct (d b) as [[a Ha] | N]; destruct (d b') as [[a' Ha'] | N'].
  - reflexivity.
  - exfalso. apply N'. exists a. now transitivity b.
  - exfalso. apply N. exists a'.
    transitivity b'; [ exact Ha' | now symmetry ].
  - reflexivity.
Defined.

Lemma char_of_dec_image@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (a : carrier u) :
  char_of_dec@{o so} m M d (m a) = ptrue@{o}.
Proof.
  simpl; unfold char_of_dec; simpl.
  destruct (d (m a)) as [ _ | N ].
  - reflexivity.
  - exfalso. apply N. exists a. reflexivity.
Qed.

Lemma char_of_dec_true_inv@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (b : carrier x) :
  char_of_dec@{o so} m M d b = ptrue@{o} -> sets_in_image@{o} m b.
Proof.
  simpl; unfold char_of_dec; simpl.
  destruct (d b) as [ H | N ].
  - intros _; exact H.
  - intro Hc; discriminate Hc.
Qed.

Lemma char_of_dec_iff@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (b : carrier x) :
  (char_of_dec@{o so} m M d b ≈ dec_truth@{o so} ttt)
    ↔ sets_in_image@{o} m b.
Proof.
  split.
  - exact (char_of_dec_true_inv@{o so} m M d b).
  - intros [a Ha].
    transitivity (char_of_dec@{o so} m M d (m a)).
    + symmetry; exact (proper_morphism (char_of_dec@{o so} m M d) _ _ Ha).
    + exact (char_of_dec_image@{o so} m M d a).
Qed.

Definition char_of_dec_pullback@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) :
  @IsPullback Sets@{o so} x
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) BoolSetoid@{o}
    (char_of_dec@{o so} m M d) dec_truth@{o so}
    u m (@one Sets@{o so} Sets_Terminal@{so o} u).
Proof.
  constructor.
  - intro a; simpl. exact (char_of_dec_image@{o so} m M d a).
  - intros Q q1 q2 Hq.
    assert (Him : ∀ z : carrier Q, sets_in_image@{o} m (q1 z))
      by (intro z; exact (char_of_dec_true_inv@{o so} m M d (q1 z) (Hq z))).
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine
        (@Build_SetoidMorphism@{o o o}
           (carrier Q) (is_setoid Q) (carrier u) (is_setoid u)
           (fun z => projT1 (Him z)) _).
      intros z z' Hzz'.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | ].
      transitivity (q1 z').
      * exact (proper_morphism q1 _ _ Hzz').
      * symmetry; exact (projT2 (Him z')).
    + split.
      * intro z; simpl. exact (projT2 (Him z)).
      * intro z; simpl. destruct (q2 z); reflexivity.
    + intros v [Hv1 Hv2] z; simpl.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | symmetry; exact (Hv1 z) ].
Defined.

Lemma char_of_dec_unique@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (h : x ~{Sets@{o so}}~> BoolSetoid@{o})
  (HP : @IsPullback Sets@{o so} x
          (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) BoolSetoid@{o}
          h dec_truth@{o so} u m (@one Sets@{o so} Sets_Terminal@{so o} u)) :
  h ≈ char_of_dec@{o so} m M d.
Proof.
  intro b.
  destruct HP as [Hc Hu].
  assert (Him : ∀ a : carrier u, h (m a) = ptrue@{o}) by exact Hc.
  destruct (h b) eqn:Hb.
  - unshelve epose proof
      (Hu (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
          (subone_pt@{o so} b)
          (@one Sets@{o so} Sets_Terminal@{so o} _) _) as U.
    { intro t; simpl; exact Hb. }
    destruct (unique_property U) as [U1 _].
    assert (Hin : sets_in_image@{o} m b).
    { exists (unique_obj U ttt). exact (U1 ttt). }
    simpl; unfold char_of_dec; simpl.
    destruct (d b) as [ _ | N ].
    + reflexivity.
    + exfalso; exact (N Hin).
  - simpl; unfold char_of_dec; simpl.
    destruct (d b) as [ [a Ha] | _ ].
    + exfalso.
      assert (Hhb : h (m a) = h b) by exact (proper_morphism h _ _ Ha).
      rewrite (Him a) in Hhb; rewrite Hb in Hhb; discriminate Hhb.
    + reflexivity.
Qed.

Definition Sets_Classifier_dec@{o so} (D : DecImage@{o so}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  @Build_SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
    BoolSetoid@{o} dec_truth@{o so}
    (fun u x m M => char_of_dec@{o so} m M (D u x m M))
    (fun u x m M => char_of_dec_pullback@{o so} m M (D u x m M))
    (fun u x m M h HP => char_of_dec_unique@{o so} m M (D u x m M) h HP).

Example sets_classifier_dec_omega@{o so} (D : DecImage@{o so}) :
  @Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D)
    = BoolSetoid@{o} := eq_refl.

Example sets_classifier_dec_truth@{o so} (D : DecImage@{o so}) :
  @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) ttt
    = ptrue@{o} := eq_refl.

Example sets_classifier_dec_char@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) u x m M
    = char_of_dec@{o so} m M (D u x m M) := eq_refl.

Definition Sets_Classifier_IEM@{o so} (E : IEM@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  Sets_Classifier@{o so} (untruncate_of_IEM@{o} E).

(* ------------------------------------------------------------------------ *)
(** ** (G) The bridge to the cross-universe characteristic map *)

(* Instance/Sets/Classifier.v's [char_setoid] and this file's [char]
   are one map at two levels, joined by [Powerset_squash].  The value
   identification is [eq_refl]; the identification as [SetoidMorphism]
   records holds only at ≈, and its strict form is pinned in
   Test/ProbeClassifier402.v as a CONVERSION refusal. *)

(* the value grade, pointwise on the carrier of Omega, at eq_refl *)
Example bridge_pointwise@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
    = Powerset_squash@{o} (char_setoid@{o so} m b) := eq_refl.

(* the same grade, unfolded: the value IS the truncation of sets_in_image *)
Example bridge_value@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
    = Powerset_squash@{o} (sets_in_image@{o} m b) := eq_refl.

(* the cross-universe char's value IS sets_in_image *)
Example bridge_char_setoid@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (b : carrier x) :
  char_setoid@{o so} m b = sets_in_image@{o} m b := eq_refl.

Definition sets_squash_mor@{o so sso} :
  PropSetoid@{o so} ~{Sets@{so sso}}~> Setoid_Lift@{o so} Powerset_Omega@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       Type@{o} (is_setoid PropSetoid@{o so})
       (carrier Powerset_Omega@{o})
       (Setoid_Lift_instance@{o so} (is_setoid Powerset_Omega@{o}))
       (fun P => Powerset_squash@{o} P) _).
  intros P Q [f g]; split.
  - intro H. exact (H (Powerset_squash@{o} Q)
                      (fun p => Powerset_squash_intro@{o} (f p))).
  - intro H. exact (H (Powerset_squash@{o} P)
                      (fun q => Powerset_squash_intro@{o} (g q))).
Defined.

Lemma bridge_record_equiv@{o so sso} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  SetoidMorphism_Lift@{o so}
    (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M)
    ≈[Sets@{so sso}] sets_squash_mor@{o so sso}
        ∘[Sets@{so sso}] char_setoid@{o so} m.
Proof. intro b; simpl; split; intro H; exact H. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (H) The book's rule: char m b is truth exactly on the image *)

(* Mac Lane's (1) with the 0 ↔ 1 swap, and Seven Sketches' ⌜m⌝ rule. *)

Lemma classifier_of_small_char_iff@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (classifier_of_small@{o so} S)
     u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o}
         (classifier_of_small@{o so} S) ttt)
    ↔ sets_in_image@{o} m b.
Proof.
  split.
  - exact (sce_elim@{o} S (sets_in_image@{o} m b)).
  - exact (sce_intro@{o} S (sets_in_image@{o} m b)).
Qed.

Definition sets_classifier_char_iff@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) ttt)
    ↔ sets_in_image@{o} m b
  := classifier_of_small_char_iff@{o so} (small_of_untruncate@{o} U) m M b.

Definition sets_classifier_dec_char_iff@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D)
     u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o}
         (Sets_Classifier_dec@{o so} D) ttt)
    ↔ sets_in_image@{o} m b
  := char_of_dec_iff@{o so} m M (D u x m M) b.

(* ------------------------------------------------------------------------ *)
(** ** (I) The two round trips, against [Sets_HasPullbacks] *)

(* [classifier_classifies] is not statable at [Sets] (its object
   universe is bounded by its hom universe); what survives are its two
   round trips, which build no object of [Sets] with carrier [SubObj x]
   (their ≈ is still the [SubObj_Setoid] instance).  Both are
   supplied by [:=] with no tactic, over Instance/Sets/Pullback.v's
   [Sets_HasPullbacks], which is named in both statements.  No second
   pullback structure is constructed anywhere in this file. *)

Definition sets_truth_subobject@{o so} (U : Untruncate@{o}) :
  @SubObj Sets@{o so}
    (@Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)) :=
  @truth_subobject Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U).

Definition sets_char_roundtrip@{o so} (U : Untruncate@{o})
  {x : SetoidObject@{o o}}
  (h : x ~{Sets@{o so}}~> @Ω Sets@{o so} Sets_Terminal@{so o}
                             (Sets_Classifier@{o so} U)) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) _ _
    (sub_mono (@sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
                 (@Ω Sets@{o so} Sets_Terminal@{so o}
                    (Sets_Classifier@{o so} U)) x h
                 (sets_truth_subobject@{o so} U)))
    (sub_is_monic (@sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
                 (@Ω Sets@{o so} Sets_Terminal@{so o}
                    (Sets_Classifier@{o so} U)) x h
                 (sets_truth_subobject@{o so} U)))
    ≈ h
  := @classifier_char_roundtrip Sets@{o so} Sets_Terminal@{so o}
       Sets_HasPullbacks@{so o} (Sets_Classifier@{o so} U) x h.

Definition sets_pullback_roundtrip@{o so} (U : Untruncate@{o})
  {x : SetoidObject@{o o}} (s : @SubObj Sets@{o so} x) :
  @sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
    (@Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)) x
    (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) _ _
       (sub_mono s) (sub_is_monic s))
    (sets_truth_subobject@{o so} U)
    ≈ s
  := @classifier_pullback_roundtrip Sets@{o so} Sets_Terminal@{so o}
       Sets_HasPullbacks@{so o} (Sets_Classifier@{o so} U) x s.

(* ------------------------------------------------------------------------ *)
(** ** (J) A concrete decidable mono, with no global hypothesis *)

(* The point [pfalse] of the two-element setoid, included from the
   terminal setoid.  Its image membership is decidable outright, so
   [char_of_dec] applies with no hypothesis at all, and the resulting
   characteristic map is negation — it MOVES both points, so the witness
   is not the generic subobject in disguise.  The mono is proved not
   invertible. *)

Definition dec_false@{o so} :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun _ => pfalse@{o}) _).
  intros ? ? ?; reflexivity.
Defined.

Lemma point_monic@{o so} {x : SetoidObject@{o o}}
  (p : (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) ~{Sets@{o so}}~> x) :
  @Monic Sets@{o so} _ x p.
Proof.
  constructor; intros z g1 g2 _ w.
  destruct (g1 w), (g2 w); reflexivity.
Qed.

Definition dec_false_dec@{o so} : SetsDec@{o so} dec_false@{o so}.
Proof.
  intro b; destruct b.
  - right; intros [a Ha]; simpl in Ha; discriminate Ha.
  - left; exists ttt; reflexivity.
Defined.

Definition char_false@{o so} : BoolSetoid@{o} ~{Sets@{o so}}~> BoolSetoid@{o} :=
  char_of_dec@{o so} dec_false@{o so} (point_monic@{o so} dec_false@{o so})
    dec_false_dec@{o so}.

Example char_false_at_false@{o so} :
  char_false@{o so} pfalse@{o} = ptrue@{o} := eq_refl.

Example char_false_at_true@{o so} :
  char_false@{o so} ptrue@{o} = pfalse@{o} := eq_refl.

Lemma ptrue_neq_pfalse@{o} : ptrue@{o} = pfalse@{o} -> False.
Proof. intro H; discriminate H. Qed.

Lemma dec_false_not_iso@{o so} :
  @IsIsomorphism Sets@{o so} _ _ dec_false@{o so} -> False.
Proof.
  intros [g Hr _].
  exact (ptrue_neq_pfalse@{o} (symmetry (Hr ptrue@{o}))).
Qed.

Example char_of_dec_from_DecImage@{o so} (D : DecImage@{o so}) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) _ _
    dec_false@{o so} (point_monic@{o so} dec_false@{o so})
  = char_of_dec@{o so} dec_false@{o so} (point_monic@{o so} dec_false@{o so})
      (D _ _ dec_false@{o so} (point_monic@{o so} dec_false@{o so})) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (K) [FinSet]: display (7.15) where Ω really is the two-element set *)

(* Unconditional, and pure instantiation: [classifier_classifies] IS
   statable at [FinSet], whose objects are naturals.  [FinSet]'s
   characteristic map reduces on a closed injection, so Seven Sketches'
   ⌜m⌝ computes.  The [eq_refl] for Ω = 2 is stated a third time here
   (Instance/FinSet/Subsets.v has [FinSet_Omega_is_two] and
   Test/ProbePowersetUniversal.v an [Example] [finset_omega_is_two] with
   the same statement, which is why the name below carries a prefix);
   Instance/FinSet/Subsets.v is NOT required, its closure being 99
   modules against this file's 70.  Nothing transports between [FinSet]
   and [Sets]: no functor between them exists in this tree. *)

Definition finset_classifier_classifies (n : obj[FinSet]) :
  @Isomorphism Sets
    {| carrier := @SubObj FinSet n |}
    {| carrier := n ~{FinSet}~> @Ω FinSet FinSet_Terminal FinSet_Classifier |}
  := @classifier_classifies FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier n.

Example finset_classifier_omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.

Definition fin_incl_1_2 : 1%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.

Lemma fin_incl_1_2_monic : @Monic FinSet 1%nat 2%nat fin_incl_1_2.
Proof.
  apply finset_monic_iff_injective.
  intros a b _; rewrite (fin1_unique a), (fin1_unique b); reflexivity.
Qed.

Example finset_char_at_F1 :
  @char FinSet FinSet_Terminal FinSet_Classifier 1%nat 2%nat
    fin_incl_1_2 fin_incl_1_2_monic Fin.F1 = fin_true := eq_refl.

Example finset_char_at_FS :
  @char FinSet FinSet_Terminal FinSet_Classifier 1%nat 2%nat
    fin_incl_1_2 fin_incl_1_2_monic (Fin.FS Fin.F1) = fin_false := eq_refl.

(* The two routes from [IEM] to a classifier, [classifier_of_small] of
   [small_of_IEM] and [Sets_Classifier_dec] of [DecImage_of_IEM], agree
   on all three DATA fields at [eq_refl] — Ω, [char], and the [truth]
   MORPHISM — while the whole records do not (pinned in the probe): what
   differs is exactly the two law fields. *)
Example iem_routes_omega@{o so} (E : IEM@{o}) :
  @Ω Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E))
  = @Ω Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) := eq_refl.

Example iem_routes_char@{o so} (E : IEM@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E)) u x m M b
  = @char Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) u x m M b
  := eq_refl.

Example iem_routes_truth@{o so} (E : IEM@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E))
  = @truth Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) := eq_refl.

Example iem_routes_truth_pt@{o so} (E : IEM@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E)) ttt
  = @truth Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) ttt := eq_refl.
