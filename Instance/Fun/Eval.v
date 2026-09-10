Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * The evaluation functor on a functor category *)

(* Mac Lane §V.3, the opening construction (book p. 115;
   maclane:V.3:construction1); Awodey §8.1's ev_C : Sets^(C^op) ⟶ Sets
   (awodey:8.1:construction-evaluation-functor).
   nLab: https://ncatlab.org/nlab/show/functor+category

   BACKGROUND.  Each object p of the index category P gives the evaluation
   functor E_p : [P, X] ⟶ X, H ↦ H p on objects and σ ↦ σ_p on
   transformations.  It is the partial application at p of the two-variable
   evaluation [P, X] ∏ P ⟶ X — the counit of Cat's exponential — whose
   transpose [J ∏ P, X] ≅ [J, [P, X]] is what turns a diagram of functors
   into a diagram with a parameter.  Its USE, that evaluation preserves and
   creates limits so that limits in [P, X] are computed pointwise, is
   Theorems 1 and 2 of the section and belongs to #425 and #426, not here.

   STALE PREMISES, RE-MEASURED.  The issue's "the fixed-object evaluation
   functor [P, X] ⟶ X is nowhere materialised" is FALSE, and its hit list
   is wrong in two of four entries.
     - Adjunction/Diagonal/Connected.v:700 [EvalAt@{jo jh co ch +} (j : J) :
       [J, C] ⟶ C] IS this functor, general in shape and target, closed
       under the global context, and docs/INDEX.md:93 records it as NEW
       there with a by-type sweep.  [Eval] below has the same two data
       fields at [eq_refl] under [EvalAt]'s own annotation (probe); the
       RECORDS do not convert (probe N1: both are [Program Definition]s with
       opaque law fields).  Also present: Functor/Hom/Yoneda/Natural.v:388
       [YoEvalAt : [C, Sets] ⟶ Sets] and :226 [YoEval : [C, Sets] ∏ C ⟶ Sets]
       (the two-variable one, at Sets, in the OTHER arrow order, bridged by
       [yo_eval_map_alt] :241), and Theory/Shapes.v:254 [One_Eval : [_1, C]
       ⟶ C].  Both [YoEvalAt] and [One_Eval] agree with [Eval] at [eq_refl]
       (probe).
     - The hit list: Theory/Kan/Extension.v:127 is a comment ([Induced] is
       :131); Instance/CMon.v:170 is [CMon_Forget : CMon ⟶ Sets], not out of
       a functor category; Construction/Day.v:921 is the Day tensor; only
       Theory/Lawvere/Sets.v:83 [ev1] is as described.
     - "record [J ∏ P, X] ≅ [J, [P, X]] from [Cat_Closed]": it exists as an
       isomorphism in [Cat], Instance/Cat/Exponential.v:57 [Cat_exp_prod_l]
       — cited by Instance/Fun/Eval/Cat.v's [eval_transpose], not rebuilt.
     - "[Functor/Bifunctor.v] supplies [bimap] but no partial-application
       constructor": Functor/Bifunctor/Partial.v:121 [Partial_l] and :144
       [Partial_r] exist (its INDEX bullet warns about the [Cat_Closed]
       currying route's universe pinning, measured again below).
     - Correct as cited: Structure/Cartesian/Closed.v:75 [eval],
       Instance/Cat/Cartesian/Closed.v:47 [Cat_Closed], Theory/Lawvere/
       Model.v's [Models] as a FULL subcategory of [[law_cat T, C]].

   WHAT IS DELIVERED (11 named constants here plus 17 [Program]
   obligations, 6 in Instance/Fun/Eval/Cat.v, every one closed under the
   global context).
     (1) [Eval (p : P) : [P, X] ⟶ X], annotated [@{jo jh co ch}] through the
         section's [Universe] declaration exactly as [EvalAt] is, in the
         light home the issue asks for (closure 19 files).
     (2) THE TWO-VARIABLE EVALUATION.  [EvalBi : [P, X] ∏ P ⟶ X] with arrow
         action [fmap[K] f ∘ transform[σ] p] — [Cat_Closed]'s order, so
         Instance/Fun/Eval/Cat.v's [CatEval_obj]/[CatEval_map] identify it
         with [Cat]'s own [eval] at [eq_refl] in both fields.  It is built
         directly rather than as [@eval Cat Cat_Cartesian Cat_Closed P X]
         because that route is reachable only at [Cat]'s universes: measured
         in the satellite, the [Cat] route identifies P's and X's object and
         hom levels into ONE universe ([u0 = u1], [u0 = u5], [u0 = u6]),
         while [EvalBi] keeps only [jh = ch].
     (3) PARTIAL APPLICATION AGREES.  [eval_partial_obj] at [eq_refl];
         [eval_partial_map] at [≈] ONLY — [Partial_l]'s action is [bimap s
         id], which carries the [fmap id] the functor law removes (probe N2;
         the same reason [yo_eval_at_map] is stated at [≈]); packaged as
         [eval_partial_iso : Eval p ≅ Partial_l EvalBi p] in [[[P, X], X]]
         with identity components, every obligation auto-discharged; the
         other partial is the functor itself ([eval_partial_r_obj] at
         [eq_refl], [eval_partial_r_map] at [≈]).
     (4) NATURALITY IN THE OBJECT.  [Eval_nat (f : p ~> q) : Eval p ⟹ Eval q]
         with component [fmap[H] f] (both naturality fields are the
         naturality of the evaluated transformation), assembled into
         [EvalFunctor : P ⟶ [[P, X], X]] with [EvalFunctor_obj]/
         [EvalFunctor_map] at [eq_refl].  The GENERAL form is new; the
         construction itself appears at one object of one category as
         Functor/Representable/Functorial.v:403's [wit_ev_tau n : YoEvalAt
         ttt ⟹ YoEvalAt ttt] over [BNat] and [Sets], whose component
         converts with [Eval_nat]'s at [eq_refl] (probe).  [EvalFunctor]
         has no precedent: a tree-wide sweep for a functor into a double
         functor category [[_, _], _] returns only this file.  (An earlier
         revision said "genuinely absent before"; the audit found the
         one-object instance.)
     (5) IN THE PROBE (Test/ProbeFunEval424.v): the identifications with
         [EvalAt], [YoEvalAt] and [One_Eval], each in BOTH data fields at
         [eq_refl] (an earlier revision recorded [One_Eval] on objects
         only, implying a boundary that is not there), and Awodey's
         increment [p424_ev1_via_Eval : Models T Sets ⟶ Sets := Eval
         (law_of_nat 1) ◯ Incl] agreeing with Theory/Lawvere/Sets.v:83's
         [ev1] in both data fields at [eq_refl].  They live in Test/
         because the identified constants sit in heavier layers
         (Adjunction/, Functor/Hom/Yoneda/, Theory/Lawvere/) that no
         Instance/Fun/ file requires.  The Awodey checkbox asks that [ev1]
         be re-expressed "rather than left as a parallel hand-written
         definition": it is NOT met — [ev1] is untouched — the twin shows
         the re-expression is exact, and the edit to the landed file is
         surfaced for John (an earlier revision called the box met).
         The issue's pinned verification name [Eval_partial_application]
         is not declared; the partial-application agreement is delivered
         as [eval_partial_obj]/[eval_partial_map]/[eval_partial_iso].
     (6) THE [EvalAt] DECISION, SURFACED.  Two constants now carry the same
         functor.  Aliasing [EvalAt := Eval] would edit
         Adjunction/Diagonal/Connected.v (with its exact annotation, and a
         re-check of [EvalAt_retracts], [colimit_is_EvalAt] and
         Test/ProbeConnected378.v:343); deleting it is a removal of working
         code.  Neither is done here: docs/INDEX.md:93's "NEW" is corrected
         in place and both remain.

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 17
   constants).
     - Every constant of this file carries exactly one equation, [jh = ch]:
       Instance/Fun.v's [Fun] identifies the hom universes of source and
       target, so every functor into or out of [[P, X]] inherits it.
       [Eval@{jo jh co ch u u0}] carries [jh < u], [jo <= jh], [jh <= u0],
       [co <= u0], [jh = ch] — [EvalAt]'s constraint set exactly.  No
       word-bounded [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r] bound.  Exactly
       four constants carry [prod_rect.*] bounds — [eval_partial_iso],
       [EvalFunctor], [EvalFunctor_obj], [EvalFunctor_map] — and the carrier
       is NOT the passage through [[[P, X], X]]: that category and its
       identity functor carry no such bound (measured); the donor is not
       isolated here.  (An earlier revision attributed the bound to the
       passage.)  The 17 [Program] obligations carry [jh = ch] and no
       stdlib bound.
     - The satellite's [Cat]-routed constants collapse to one universe
       (item (2)) and carry [Basics.compose], [eq_rect] and [prod_rect]
       bounds; see its header.

   COUNTS AND CONVENTIONS.
     - 34 constants closed under the global context: 17 [.glob] declaration
       heads (here 9 [def] + 2 [prf]; the satellite 5 [def] + 1 [prf]) plus
       this file's 17 [Program] obligations, which the [.glob] cannot see
       ([Eval] 3, [EvalBi] 3, [eval_partial_iso] 6, [Eval_nat] 2,
       [EvalFunctor] 3; the satellite has none); zero [Axioms:] lines; the
       gate carries the 17 heads, fully qualified.  (An earlier revision
       said "17/17 constants", counting heads only.)  No [Defined]; eight
       [Qed] tokens here (two lemmas, six obligation proofs written out; all
       obligations opaque by Lib.v's flag) and one in the satellite.
     - Closure 19 files excluding self: Instance/Fun.v costs 5 at the
       margin, Functor/Bifunctor/Partial.v 1, the other seven [Require]s 0.
       No collision: each new name has 0 declaration hits elsewhere in the
       tree.  THE NAME [Eval] AND THE VERNACULAR: [Eval compute in …] and
       [ltac:(eval …)] still work after this file, and [Check Eval] resolves
       to the constant — but at the HEAD of a definition body, [Definition
       f p := Eval p.] is a PARSE error ("'in' expected after [red_expr]"),
       because Coq reads [Eval <red_expr> in <term>]; [(Eval p)],
       [@Eval P X p] and tactic-mode [exact (Eval p)] all work.  Consumers
       (#425, #426) must parenthesise.  Renaming the constant is surfaced
       for John, not done.  (An earlier revision measured only the harmless
       direction.)
     - Test/ProbeFunEval424.v carries 4 refutation commands (1 instrument +
       N1, N2, N3, all CONVERSION — N3 is the [Partial_r] twin of N2, added
       after the audit so the right-hand [≈]-only boundary is guarded too),
       each stripped one at a time in a copy of the whole file; guard
       coverage 23 identifier tokens inside the refutations / 17 also named
       outside, comments stripped, with six exhaustive exceptions (the
       keyword, the three refuted declarations' names, the binder [s], the
       absent name); rename-simulated 7/7 ([Eval], [EvalBi], [EvalAt],
       [Partial_l], [Partial_r], [YoEvalAt], [CatEval], each renamed
       throughout a copy with module paths excluded) with every first break
       on a positive line.  [make todo] grows by those 4 lines only
       (2218 → 2222 against the rebased base 39e583d2), so the issue's
       "adds no new hits" box is not met as written; disclosed.

   NOT DELIVERED.
     - Any preservation or creation of limits by evaluation (#425, #426).
     - An alias or removal of [EvalAt], [YoEvalAt] or [One_Eval] (item (6);
       surfaced).  [YoEval]'s arrow order is not changed; its bridge to this
       order is the existing [yo_eval_map_alt].
     - Replacing [ev1]'s body in Theory/Lawvere/Sets.v (surfaced); the
       re-expression lives in the probe.
     - A general two-variable evaluation at [Cat]'s universes with the
       collapse removed: the collapse is [Cat]'s, measured and disclosed.
     - No edit to Adjunction/Diagonal/Connected.v, Functor/Hom/Yoneda/
       Natural.v, Theory/Shapes.v, Theory/Lawvere/Sets.v or
       Functor/Bifunctor/Partial.v. *)

Section Evaluation.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(** ** The evaluation functor at a fixed object *)

(* Mac Lane §V.3's E_c : [P, X] ⟶ X — objects to their value at p,
   transformations to their component at p.  The same data as
   Adjunction/Diagonal/Connected.v's [EvalAt] (measured, see the header);
   declared here in the light home the issue asks for. *)
Program Definition Eval (p : P) : [P, X] ⟶ X := {|
  fobj := fun H => H p;
  fmap := fun _ _ s => transform[s] p
|}.

(** ** The two-variable evaluation *)

(* The bifunctor [P, X] ∏ P ⟶ X whose partial application at p is [Eval p].
   The arrow action is in [Cat_Closed]'s order, [fmap[K] f ∘ transform[s] p]
   (Instance/Fun/Eval/Cat.v shows the two agree at [eq_refl]); the other
   order, [transform[s] q ∘ fmap[H] f], is the same arrow by naturality and
   is the one Functor/Hom/Yoneda/Natural.v's [YoEval] uses. *)
Program Definition EvalBi : ([P, X] ∏ P) ⟶ X := {|
  fobj := fun Hp => fst Hp (snd Hp);
  fmap := fun Hp Kq sf =>
            fmap[fst Kq] (snd sf) ∘ transform[fst sf] (snd Hp)
|}.
Next Obligation.
  proper; simpl in *.
  rewrite H, X0; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite comp_assoc, (naturality[t0] o1 o0 h), <- comp_assoc.
  reflexivity.
Qed.

(** ** Partial application agrees with the fixed-object evaluation *)

(* On objects: on the nose. *)
Definition eval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(* On arrows: up to ≈ only — [Partial_l]'s action is [bimap s id], which
   still carries the [fmap id] the functor law removes (probe). *)
Lemma eval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l EvalBi p] s.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(* Packaged as an isomorphism of functors in [[P, X], X], with identity
   components. *)
Program Definition eval_partial_iso (p : P) :
  @Isomorphism ([[P, X], X]) (Eval p) (Partial_l EvalBi p) := {|
  to   := {| transform := fun H => id |};
  from := {| transform := fun H => id |}
|}.

(* The other partial application is the functor itself. *)
Definition eval_partial_r_obj (H : [P, X]) (p : P) :
  fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.

Lemma eval_partial_r_map (H : [P, X]) (p q : P) (f : p ~> q) :
  fmap[Partial_r EvalBi H] f ≈ fmap[H] f.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(** ** Naturality in the evaluated object *)

(* Each arrow of P gives a transformation between evaluation functors,
   with component [fmap[H] f] at H; both naturality fields are the
   naturality of the transformation being evaluated. *)
Program Definition Eval_nat {p q : P} (f : p ~> q) : Eval p ⟹ Eval q := {|
  transform := fun H => fmap[H] f
|}.
Next Obligation. symmetry; apply naturality. Qed.
Next Obligation. apply naturality. Qed.

(* Assembled: evaluation is a functor P ⟶ [[P, X], X]. *)
Program Definition EvalFunctor : P ⟶ [[P, X], X] := {|
  fobj := Eval;
  fmap := fun _ _ f => Eval_nat f
|}.
Next Obligation. proper; rewrite X0; reflexivity. Qed.
Next Obligation. apply fmap_comp. Qed.

(* Its actions read back on the nose. *)
Definition EvalFunctor_obj (p : P) : fobj[EvalFunctor] p = Eval p := eq_refl.

Definition EvalFunctor_map {p q : P} (f : p ~> q) (H : [P, X]) :
  transform[fmap[EvalFunctor] f] H = fmap[H] f := eq_refl.

End Evaluation.

Arguments Eval {P X} p.
Arguments EvalBi {P X}.
Arguments EvalFunctor {P X}.
