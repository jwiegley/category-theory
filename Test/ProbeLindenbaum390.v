Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Theory.Lindenbaum.

Generalizable All Variables.

(** * Probe for Instance/Theory/Lindenbaum.v (issue #390) *)

(* Mac Lane §IV.6, printed p. 98, Exercise 2 (maclane:IV.6:ex2).

   This file pins, from OUTSIDE the target, every boundary the target's
   header records.  An in-file negative renames in lockstep with the
   constant it guards and so cannot detect a rename; these can.

   Eight negatives in THREE kinds, told apart by the error TEXT rather
   than by label:

     FORMABILITY  ends in a universe clause "Cannot enforce ..."
       N1  [Lind]'s hom universe is identified with its proof universe
       N2  ...and that is [Proset]'s doing, with no [Lind] in the command
       N3  a Type-valued entailment is not a stdlib [relation]
     TYPING       plain "has type ... expected ...", no "cannot unify"
       N4  [Terminal] where [Cartesian] is wanted
       N5  a derivation at one theory is not one at another
     CONVERSION   ends in "cannot unify"
       N6  the two categories of section (G) are not convertible
       N7  the exponential's orientation: q ^ p is s_imp p q, not q p
       N8  [eval] is not the rule [ent_eval] on the nose, only up to ≈

   Plus one scope-free instrument check.  Each negative was stripped ONE
   AT A TIME, the file compiled alone, and the WHOLE error read.

   Every constant a negative names is also named outside every [Fail],
   in the control blocks below. *)

(** ** Instrument check: this must be rejected for the trivial reason *)

Fail Check probe390_no_such_constant_anywhere.

(** ** Controls: every constant the negatives name, outside any [Fail] *)

Check @Sent.
Check @s_var.
Check @s_top.
Check @s_and.
Check @s_imp.
Check @Theo.
Check @Entails.
Check @ent_refl.
Check @ent_cut.
Check @ent_ax.
Check @ent_top.
Check @ent_pair.
Check @ent_fst.
Check @ent_snd.
Check @ent_curry.
Check @ent_eval.
Check @entails_PreOrder.
Check @Lind.
Check @lind_thin.
Check @lind_any_Faithful.
Check @Lind_Terminal.
Check @Lind_Cartesian.
Check @lind_uncurry.
Check @Lind_Closed.
Check @sdenote.
Check @ent_soundness.
Check @LindSound.
Check @LindSound_Faithful.
Check @entails_weaken.
Check @LindWeaken.
Check @sv.
Check @T_empty.
Check @T_mp.
Check @T_all.
Check @not_entails_empty.
Check @entails_mp.
Check @empty_sub_mp.
Check @empty_sub_all.
Check @weaken_not_Full.
Check @no_full_functor_empty_to_all.
Check @no_equivalence_empty_to_all.
Check @sound_not_Full.
Check @sound_misses_False.
Check @sound_not_EssentiallySurjective.

(* Donor constants named by the negatives. *)
Check @Proset.
Check @Category.
Check @terminal_obj.
Check @product_obj.
Check @exponent_obj.
Check @eval.
Check @Thin.
Check @Full.
Check @EssentiallySurjective.
Check @EquivalenceOfCategories.
Check @Props.
Check @Relation_Definitions.relation.
Check @RelationClasses.PreOrder.

(** ** N1, N2: the hom = proof identification, and its donor *)

(* [Lind@{u u0 u1} : Theo@{u0 u1} V -> Category@{u0 u u}] reuses one
   level for hom and for proof in the BINDER, while its constraint block
   carries no equation at all.  Both facts have to be read to get this
   right, and only the binder shows it.

   The two negatives below are rejected at levels declared strictly
   apart; the control on the line before each shows the very same
   application accepted at those levels once hom and proof coincide. *)

Section UniverseProbe.

Universe lo lh lp.
Constraint lh < lp.

Context (Vu : Type@{lo}) (Tu : Theo@{lo lp} Vu).

(* Controls: the category, its objects and a hom all elaborate here. *)
Check (Lind Tu : Category@{lo lh lh}).
Check (obj[Lind Tu]).
Check (fun p q : Sent@{lo} Vu => p ~{Lind Tu}~> q).

(* N1 (FORMABILITY): "Cannot enforce lh = lp because lh < lp". *)
Fail Check (Lind Tu : Category@{lo lh lp}).

Context (Au : Type@{lo}) (Ru : Relation_Definitions.relation Au)
        (Pu : RelationClasses.PreOrder Ru).

(* Control for N2, at the same declared levels. *)
Check (Proset Pu : Category@{lo lh lh}).

(* N2 (FORMABILITY): the donor alone, with no [Lind] in the command,
   is rejected with the identical clause — so the identification is
   inherited from [Proset] and the target introduces none of its own. *)
Fail Check (Proset Pu : Category@{lo lh lp}).

End UniverseProbe.

(** ** N3: entailment must be Prop-valued for [Proset] to accept it *)

(* The target's design note says a Type-valued entailment would not fit
   [Proset], whose relation argument is a stdlib [relation A].  Here is
   a Type-valued one, and the rejection. *)

Inductive TEnt {V : Type} (T : Theo V) : Sent V -> Sent V -> Type :=
  | tent_refl p : TEnt p p
  | tent_cut p q r : TEnt p q -> TEnt q r -> TEnt p r.

(* Controls: the Prop-valued one IS a stdlib relation, and the
   Type-valued one does elaborate as a family. *)
Check (Entails T_empty : Relation_Definitions.relation (Sent bool)).
Check (TEnt T_empty).

(* N3 (FORMABILITY): "Cannot enforce <level> <= Prop".  Note the kind:
   the message opens like a typing mismatch but closes with a universe
   clause, so it is counted with the formability negatives and not with
   N4/N5, whose messages carry no universe clause at all. *)
Fail Definition probe390_tent_relation :
  Relation_Definitions.relation (Sent bool) := TEnt T_empty.

(** ** N4, N5: two typing rejections *)

Section TypingProbe.

Context {V : Type} (T : Theo V) (p q r : Sent V).

(* Control: the product object with the right structure supplied. *)
Check (@product_obj (Lind T) (Lind_Cartesian T) p q).

(* N4 (TYPING): "The term Lind_Terminal T has type Terminal while it is
   expected to have type Cartesian" — a plain mismatch, no
   "cannot unify" and no universe clause.  The three structures are
   three distinct classes on one category. *)
Fail Check (@product_obj (Lind T) (Lind_Terminal T) p q).

End TypingProbe.

(* Control: the derivation exists at its own theory. *)
Check (entails_mp : Entails T_mp (sv true) (sv false)).

(* N5 (TYPING): a derivation at [T_mp] is not one at [T_empty].  The
   theory is an INDEX of the hom-type, so this is a type mismatch and
   not a unification report. *)
Fail Check (entails_mp : Entails T_empty (sv true) (sv false)).

(** ** N6, N7, N8: three conversion rejections *)

(* Control: each category is convertible with itself. *)
Definition probe390_lind_self : Lind T_empty = Lind T_empty := eq_refl.

(* N6 (CONVERSION): different axiom sets, different categories — the
   two [Category] records do not convert.  (Section (G) of the target
   upgrades this from a conversion remark to the statement that no full
   functor, hence no equivalence, connects them.) *)
Fail Definition probe390_two_theories :
  Lind T_empty = Lind T_mp := eq_refl.

Section OrientationProbe.

Context {V : Type} (T : Theo V) (p q : Sent V).

(* Control: Mac Lane's q ^ p IS "p implies q". *)
Definition probe390_exp_orientation :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(* N7 (CONVERSION): and it is not "q implies p".  This guards the one
   place where the library's [exponent_obj x y = y ^ x] convention and
   the book's q^p could silently drift apart. *)
Fail Definition probe390_exp_flipped :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp q p := eq_refl.

(* Control: [eval] IS [lind_uncurry] at the identity derivation, and it
   is ≈-equal to the evaluation RULE, since the category is thin. *)
Definition probe390_eval_unfold :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = lind_uncurry (ent_refl T (s_imp p q)) := eq_refl.

Definition probe390_eval_equiv :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    ≈ ent_eval T p q := lind_thin T _ _ _ _.

(* N8 (CONVERSION): but it is not [ent_eval] on the nose.  This is what
   thinness buys and what it does not: the two derivations are
   identified by ≈ and by nothing stronger. *)
Fail Definition probe390_eval_strict :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = ent_eval T p q := eq_refl.

End OrientationProbe.

(** ** The [Defined] on [entails_weaken] is load-bearing downstream *)

(* Within the target, flipping either [Defined] to [Qed] changes
   nothing.  This readback is what makes the one on [entails_weaken]
   matter: with [Qed] it is rejected with "cannot unify". *)
Example probe390_weaken_reduces (p : Sent bool) :
  entails_weaken empty_sub_mp (ent_refl T_empty p) = ent_refl T_mp p
  := eq_refl.

Example probe390_weaken_fmap (p q : Sent bool) (f : Entails T_empty p q) :
  fmap[LindWeaken empty_sub_mp] f = entails_weaken empty_sub_mp f
  := eq_refl.

(** ** The exercise's claims, exercised from outside *)

(* Product is conjunction, terminal is truth, exponential is
   implication — at Leibniz equality of objects. *)
Example probe390_structure {V} (T : Theo V) (p q : Sent V) :
  (@terminal_obj (Lind T) (Lind_Terminal T) = s_top)
  * (@product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q)
  * (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
       = s_imp p q)
  := (eq_refl, eq_refl, eq_refl).

(* The category is thin, so the transpose is unique for free. *)
Example probe390_thin {V} (T : Theo V) : Thin (Lind T) := lind_thin T.

(* Two axiom sets, two categories: derivable on one side, refuted on
   the other, and no full functor between them. *)
Example probe390_derivable : Entails T_mp (sv true) (sv false) :=
  entails_mp.

Example probe390_underivable :
  Entails T_empty (sv true) (sv false) -> False := not_entails_empty.

Example probe390_not_full :
  Full (LindWeaken empty_sub_mp) -> False := weaken_not_Full.

Example probe390_no_equiv (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False := no_equivalence_empty_to_all F.

(* The comparison with Props: a functor preserving 1, × and ^ on the
   nose, faithful, but neither full nor essentially surjective. *)
Example probe390_sound_functor : Lind T_empty ⟶ Props :=
  LindSound T_empty val_true val_true_empty.

Example probe390_sound_faithful : Faithful (LindSound T_empty val_true
  val_true_empty) := LindSound_Faithful T_empty val_true val_true_empty.

Example probe390_sound_not_full :
  Full (LindSound T_empty val_true val_true_empty) -> False :=
  sound_not_Full.

Example probe390_sound_not_eso :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False := sound_not_EssentiallySurjective.
