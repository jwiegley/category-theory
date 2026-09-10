(** * Probe for Instance/Fun/Eval.v and Instance/Fun/Eval/Cat.v (issue #424)

    Pins the measured boundaries of the evaluation functor on a functor
    category: the new [Eval] is Adjunction/Diagonal/Connected.v's [EvalAt]
    in both data fields but not as a record, and the partial application of
    the two-variable evaluation agrees with it on arrows up to [≈] only.  It
    also carries, as positive controls, the identifications with every
    evaluation-shaped functor already in the tree ([EvalAt], [YoEvalAt],
    [One_Eval], [Cat_Closed]'s own [eval]) and Awodey's [ev1] re-expressed
    through the general one.  Every refutation command below was stripped
    ONE AT A TIME in a copy of the whole file and compiled alone with its
    error read, so each refusal is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [Eval p = EvalAt p] is refused at [eq_refl] ("cannot
                     unify Eval p and EvalAt p"): both are [Program
                     Definition]s whose law fields are separate opaque
                     constants (Lib.v makes obligations opaque).  Controls:
                     [fobj] and [fmap] convert at [eq_refl], under
                     [EvalAt]'s own universe annotation.
     N2 CONVERSION   [fmap[Eval p] s = fmap[Partial_l EvalBi p] s] is refused
                     at [eq_refl]: [Partial_l]'s arrow action is [bimap s
                     id], which still carries the [fmap id] the functor law
                     removes.  Controls: the object actions convert, and
                     [eval_partial_map] closes the arrow case at [≈], packaged
                     as [eval_partial_iso].
     N3 CONVERSION   the [Partial_r] twin: [fmap[Partial_r EvalBi H] f =
                     fmap[H] f] is refused at [eq_refl] for the same reason
                     ([bimap id f]); controls [eval_partial_r_obj] at
                     [eq_refl] and [eval_partial_r_map] at [≈].  Added after
                     the audit, which found the boundary measured but
                     unguarded.

    Positive controls, deliberately NOT written as refutations: the
    identifications with [YoEvalAt] and [One_Eval] (both fields each),
    [Cat_Closed]'s evaluation ([CatEval_map]) and the transpose
    ([eval_transpose]); [p424_prior_nat], the one-object instance of
    [Eval_nat] already in the tree (Functor/Representable/Functorial.v's
    [wit_ev_tau]), component for component at [eq_refl]; and
    [p424_ev1_via_Eval], Theory/Lawvere/Sets.v's [ev1] as [Eval (law_of_nat
    1) ◯ Incl], agreeing with [ev1] in both data fields at [eq_refl] (a
    twin: [ev1] itself is not re-expressed).  The universe COLLAPSE of
    routing through [Cat]'s exponential typechecks and so cannot be
    refuted; it is measured by [About] in the headers, not faked as a
    probe.  Note the parenthesised [(Eval p)] wherever the constant heads a
    term: bare [Eval p] at a definition-body head is read as the [Eval … in]
    vernacular.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the three names the refuted
    declarations would introduce, the binder [s] and the instrument's
    absent name — so a renamed or removed constant breaks the build on a
    positive line rather than letting a refutation pass for the wrong
    reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.
Require Import Category.Instance.Fun.Eval.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Theory.Shapes.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Adjunction.Diagonal.Connected.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe424_absent_name.

(** ** A: the new evaluation IS Adjunction/Diagonal/Connected.v's [EvalAt]
       in both data fields, but not as a record *)

Section EvalAtAgreement.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}} (p : P).

(* controls: the two data fields convert *)
Example p424_EvalAt_obj : fobj[Eval p] = fobj[@EvalAt P X p] := eq_refl.

Example p424_EvalAt_map (H K : [P, X]) :
  @fmap _ _ (Eval p) H K = @fmap _ _ (@EvalAt P X p) H K := eq_refl.

(* N1 CONVERSION: the whole records do not — both are [Program
   Definition]s whose law fields are separate opaque constants *)
Fail Example p424_EvalAt_record : Eval p = @EvalAt P X p := eq_refl.

End EvalAtAgreement.

(** ** B: partial application agrees on arrows up to ≈ only *)

Section PartialAgreement.

Context {P X : Category} (p : P) (H K : [P, X]).

(* control: on objects, on the nose *)
Example p424_partial_obj : fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(* N2 CONVERSION: on arrows the partial's action is [bimap s id], carrying
   the [fmap id] the functor law removes *)
Fail Example p424_partial_map (s : H ~{[P, X]}~> K) :
  @fmap _ _ (Eval p) H K s = @fmap _ _ (Partial_l EvalBi p) H K s := eq_refl.

(* control: it closes at ≈, and is packaged as an isomorphism *)
Check (eval_partial_map p H K).
Check (eval_partial_iso p).

(* N3 CONVERSION: the same on the other partial — [Partial_r]'s action is
   [bimap id f], again carrying an [fmap id] *)
Fail Example p424_partial_r_map (q : P) (f : p ~> q) :
  @fmap _ _ (Partial_r EvalBi H) p q f = @fmap _ _ H p q f := eq_refl.

(* controls: on objects on the nose, on arrows at ≈ *)
Example p424_partial_r_obj : fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.
Check (fun (q : P) (f : p ~> q) => eval_partial_r_map H p q f).

End PartialAgreement.

(** ** C: the same data as the tree's other evaluation functors *)

(* at [X := Sets]: Functor/Hom/Yoneda/Natural.v's [YoEvalAt] *)
Example p424_YoEvalAt_obj {C : Category} (c : C) :
  fobj[@Eval C Sets c] = fobj[@YoEvalAt C c] := eq_refl.

Example p424_YoEvalAt_map {C : Category} (c : C) (F G : [C, Sets]) :
  @fmap _ _ (@Eval C Sets c) F G = @fmap _ _ (@YoEvalAt C c) F G := eq_refl.

(* at [P := _1]: Theory/Shapes.v's [One_Eval], both fields *)
Example p424_One_Eval_obj {X : Category} :
  fobj[@Eval _1 X ttt] = fobj[@One_Eval X] := eq_refl.

Example p424_One_Eval_map {X : Category} (F G : [_1, X]) :
  @fmap _ _ (@Eval _1 X ttt) F G = @fmap _ _ (@One_Eval X) F G := eq_refl.

(* the one-object instance of [Eval_nat] already in the tree:
   Functor/Representable/Functorial.v's [wit_ev_tau] over the delooping of
   (ℕ, +) and [Sets], the same component (its [BNat] notation is
   section-local there) *)
Local Notation BNat := (Deloop Nat_Plus).

Example p424_prior_nat (n : nat) (F : [BNat, Sets]) :
  transform[wit_ev_tau n] F = transform[@Eval_nat BNat Sets ttt ttt n] F
  := eq_refl.

(* [Cat_Closed]'s own evaluation, named in Instance/Fun/Eval/Cat.v *)
Check (@CatEval_map).
Check (@eval_transpose).

(** ** D: the Awodey increment — Theory/Lawvere/Sets.v's [ev1] through the
       general evaluation *)

Section Ev1.

Context (T : LawvereTheory).

(* [Models T Sets] is the full subcategory of [[law_cat T, Sets]] cut out
   by [Models_sub]; [ev1] is evaluation at the generator after the
   inclusion. *)
Definition p424_ev1_via_Eval : Models T Sets ⟶ Sets :=
  @Eval (@law_cat T) Sets (law_of_nat 1%nat)
    ◯ @Incl (@Fun (@law_cat T) Sets) (Models_sub T Sets).

Example p424_ev1_obj (M : Models T Sets) :
  fobj[ev1 T] M = fobj[p424_ev1_via_Eval] M := eq_refl.

Example p424_ev1_map (M N : Models T Sets) :
  @fmap _ _ (ev1 T) M N = @fmap _ _ p424_ev1_via_Eval M N := eq_refl.

End Ev1.

(** ** E: readbacks *)

Check (@EvalFunctor_obj).
Check (@EvalFunctor_map).
Check (@eval_partial_r_obj).
Check (@eval_partial_r_map).

(** ** Guard block *)

Check @Eval.
Check @EvalBi.
Check @Eval_nat.
Check @EvalFunctor.
Check @eval_partial_obj.
Check @eval_partial_map.
Check @eval_partial_iso.
Check @CatEval.
Check @CatEval_obj.
Check @eval_is_CatEval_partial_obj.
Check @eval_is_CatEval_partial_map.
Check @EvalAt.
Check @Partial_l.
Check @Partial_r.
Check @bimap.
Check @fmap.
Check @fobj.
