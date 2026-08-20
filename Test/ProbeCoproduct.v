(** * Boundary probe: the coproduct roster of Mac Lane §III.3

    Companion to Structure/Biproduct/Cartesian.v,
    Instance/CMon/Coproduct.v, Instance/Ab/Coproduct.v,
    Instance/Mod/Coproduct.v, Instance/Top/Coproduct.v and
    Instance/Top/Wedge.v.  Those files make a number of STRICT claims —
    "by [eq_refl]", "supplied by [:=] with no tactic" — and a number of
    NEGATIVE ones: this does not return on the nose, that is not
    formable at those universes, the other is not statable at all.  The
    positives are guarded by the [Example]s in the files themselves.  This
    file guards the negatives: **if the [Fail] commands here stop failing,
    it breaks the build.**

    Both sides are pinned, in the manner of Test/ProbeQuiverConstructions.v.
    A [Fail] alone proves very little — it passes just as happily when the
    term is ill-typed for an unrelated reason, or when a name has been
    renamed out from under it.  So every negative is paired with a positive
    control that must SUCCEED and that NAMES THE SAME CONSTANTS, so that a
    rename or a refactor breaks the controls loudly rather than turning the
    [Fail]s vacuously green.  That claim was FALSE when this file was first
    written and an audit caught it: [RMod_inr], [bi_inl],
    [cartesian_biproduct] and [biproduct] were each named only inside a
    negative, and renaming any of them left the file compiling clean —
    the [Fail]s passing for "reference not found", which is the same
    failure mode this file records catching once already with
    [WedgeSum_Top].  Controls naming all four were added, and the repair
    was verified the only way that settles it: renaming [RMod_inr] or
    [bi_inl] now BREAKS the compile, where before it did not.

    The import list is the full one of the six
    target files, in their dependency order, for the same reason: a probe
    compiled against a short prefix of its target's imports can fail for
    want of a coercion rather than for the reason advertised.

    The instrument was checked before being trusted: wrapping [Fail] around
    a command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.  Every negative below was
    additionally STRIPPED of its [Fail] once and the resulting error read,
    to confirm the failure KIND; the kinds are recorded beside each probe
    and are of exactly two sorts, kept lexically apart:

      CONVERSION negatives ([Fail Definition … := eq_refl]), which report
      "cannot unify"; and FORMABILITY negatives ([Fail Check] /
      [Fail Definition] at a declared universe), which report a universe
      inconsistency or a typing error.

    A REAL FALSE PASS WAS CAUGHT WHILE WRITING THIS FILE and is recorded
    because the lesson is general: the wedge probe was first written
    against [WedgeSum_Top], a name that does not exist (the object is
    [WedgeSum], the space is [Wedge_Top]).  The [Fail] passed — for
    "reference not found", not for the advertised reason.  Stripping the
    [Fail] and reading the error is what caught it. *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.CMon.Coproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Wedge.

Local Open Scope category_scope.

(** ** Positive controls, part 1: the strict claims hold *)

(* The vocabulary bridge returns the biproduct's own data on the nose. *)
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_product_obj C Z B x y).
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_prod_is_coprod C Z B x y).

(* At Ab, ten of the biproduct record's eleven fields are the CMon ones. *)
Check (fun M N : AbObject => (Ab_inl M N : M ~{Ab}~> Ab_product M N)).
Check (fun M N : AbObject => Ab_exl_inr M N).
Check (fun M N : AbObject => Ab_exr_inl M N).
Check (fun M N : AbObject => ab_zero_mor_is_cmon_zero_mor M N).

(* At R-Mod the underlying arrow of an injection IS Ab's.  BOTH injections
   are named here: an audit found [RMod_inr] occurring ONLY inside
   NEGATIVE 8, so a rename would have made that [Fail] pass for "reference
   not found" while the header promised otherwise. *)
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inl M N) = Ab_inl M N)).
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inr M N) = Ab_inr M N)).

(* The two topological coproducts exist and are what they say. *)
Check (fun X Y : TopSpace => (Sum_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (Wedge_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (WedgeSum X Y : PointedTop)).
Check (fun X Y : PointedTop =>
         (eq_refl : wpoint X Y
                      = carrier (sum_carrier (ptop_space X)
                                             (ptop_space Y)))).

(** ** Conversion negatives *)

Section RoundTripNegatives.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

(* Positive controls for this section: the OBJECT and both PROJECTIONS do
   come back on the nose, and both INJECTIONS come back up to [≈]. *)
Check (fun x y : C => @biproduct_roundtrip_obj C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exr C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inr C Z P B x y).

(* And the four constants the NEGATIVES below name are named here too, so
   that a rename breaks this control rather than turning those [Fail]s
   vacuously green.  An audit found all four occurring only in negatives. *)
Check (fun x y : C =>
         (bi_inl (@cartesian_biproduct C Z P Cart x y),
          bi_inr (@cartesian_biproduct C Z P Cart x y),
          bi_inl (biproduct x y),
          bi_inr (biproduct x y))).

(* NEGATIVE 1 (conversion, "cannot unify").  Sending the derived cartesian
   structure back through Structure/Semiadditive.v's [cartesian_biproduct]
   does NOT return the original injections: the reconstruction defines them
   as the forks [id △ 0] and [0 △ id], which are the originals by product
   uniqueness and not by computation. *)
Fail Definition neg_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) = bi_inl (biproduct x y)
  := eq_refl.

(* NEGATIVE 2 (conversion, "cannot unify").  A fortiori the whole record
   does not return: besides the injections, every law and both
   universal-property fields are rebuilt. *)
Fail Definition neg_roundtrip_record (x y : C) :
  @cartesian_biproduct C Z P Cart x y = biproduct x y := eq_refl.

End RoundTripNegatives.

(* NEGATIVE 3 (conversion, "cannot unify").  The wedge is not the disjoint
   union with a basepoint chosen: [Wedge_Top] carries the gluing relation
   in its setoid AND the respect-the-gluing clause in its topology, and
   [Sum_Top] carries neither.  The control immediately above this section
   shows the two share their POINT TYPE by [eq_refl], which is what makes
   this negative say something. *)
Fail Definition neg_wedge_is_sum (X Y : PointedTop) :
  Wedge_Top X Y = Sum_Top (ptop_space X) (ptop_space Y) := eq_refl.

(** ** Formability negatives: the [Set] pin inherited from Instance/Ab.v *)

(* Instance/Ab.v:227's [Ab_trivial] is declared with NO universe binders,
   at [AbObject@{Set Set Set}] — unlike Instance/CMon/Biproduct.v:72's
   [CMon_trivial@{o}], which is polymorphic.  That pin propagates through
   [Ab_Zero] to everything mentioning a zero morphism, hence to the
   biproduct records and to both derived structures, in Ab and (through
   [RMod_trivial], which uses [Ab_trivial]) in R-Mod.  The DONOR is
   Instance/Ab.v; nothing here repairs it, and it is not claimed
   unavoidable. *)

Section SetPin.

Universe ua.
Constraint Set < ua.

(* Controls: the direct-sum OBJECTS are free of the pin, on both sides. *)
Check (fun M N : AbObject@{ua ua ua} => Ab_product M N).
Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
         RMod_product M N).

(* NEGATIVE 4 (formability, universe inconsistency:
   "Cannot enforce Set = ua"). *)
Fail Check (fun M N : AbObject@{ua ua ua} => Ab_Biproduct M N).

(* NEGATIVE 5 (formability, universe inconsistency, same cause one layer
   up: [RMod_trivial] is built from [Ab_trivial]). *)
Fail Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
              RMod_Biproduct M N).

End SetPin.

(* Controls for negatives 4 and 5 at the pinned level, so that the two
   constants are named by something that must succeed. *)
Check (fun M N : AbObject => Ab_Biproduct M N).
Check (fun (R : RingObject) (M N : RModObject R) => RMod_Biproduct M N).

(** ** Formability negatives: hom and proof universes are identified *)

(* [Cartesian@{u u0}] takes a [Category@{u u0 u0}] — the hom and proof
   universes are IDENTIFIED, not merely bounded — so the bridge of
   Structure/Biproduct/Cartesian.v inherits that and cannot be stated over
   a category whose two levels have been declared apart.  The probe
   declares them SEPARATELY (with [Constraint uh < up]) rather than
   letting an unannotated definition minimize them together, which would
   read as an identification when it was only a bound.

   ATTRIBUTION: this is NOT introduced by [Cartesian], and negative 7
   shows it — the identification is already present at
   Structure/Terminal.v's [Terminal], upstream of everything here.  It is
   a shape of the [Structure/] hierarchy, inherited and not created. *)

Section SeparatedLevels.

Universe uo uh up.
Constraint uh < up.

(* Control: the category itself, and its hom-sets, are fine at these
   separated levels. *)
Check (fun (C : Category@{uo uh up}) (x y : obj[C]) => x ~{C}~> y).

(* NEGATIVE 6 (formability, universe inconsistency:
   "Cannot enforce up = uh"). *)
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).

(* NEGATIVE 7 (formability, same, at the upstream donor — the attribution
   probe). *)
Fail Check (fun C : Category@{uo uh up} => @Terminal C).

End SeparatedLevels.

(* Controls for negatives 6 and 7: both classes are of course formable
   when the two levels are not forced apart. *)
Check (fun C : Category => @Cartesian C).
Check (fun C : Category => @Terminal C).

(** ** Formability negative: the ∃!-package does not transfer to R-Mod *)

(* Instance/Ab/Coproduct.v hands [CMon_bi_is_coproduct] straight over,
   because [AbHom A B] IS [CMonHom A B].  Instance/Mod/Coproduct.v cannot:
   [RModHom] is a record wrapping an [AbHom], so the ∃! ranges over a
   different type and the package has to be rebuilt — which is why that
   file's two universal properties are tactic proofs citing the CMon
   originals rather than [:=]. *)

(* Control: at Ab the transfer is a term. *)
Check (fun (M N P : AbObject) (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) =>
         (CMon_bi_is_coproduct M N P f g
            : ∃! h : Ab_product M N ~{Ab}~> P,
                (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g))).

(* Control naming the R-Mod side's own constants. *)
Check (fun (R : RingObject) (M N P : RModObject R)
           (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
         RMod_is_coproduct M N P f g).

(* NEGATIVE 8 (formability, typing error: "The term f has type
   M ~{RMod R}~> P while it is expected to have type M ~{CMon}~> P"). *)
Fail Check (fun (R : RingObject) (M N P : RModObject R)
                (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
              (CMon_bi_is_coproduct M N P f g
                 : ∃! h : RMod_product M N ~{RMod R}~> P,
                     (h ∘ RMod_inl M N ≈ f) ∧ (h ∘ RMod_inr M N ≈ g))).

(** ** Formability negative: a product topology does not fit *)

(* Instance/Top/Coproduct.v's header says the COPRODUCT half of Mac Lane's
   roster is available in Top while the PRODUCT half is not, and that the
   obstruction is a universe wall rather than a gap in effort.  That is a
   claim about what can be WRITTEN, so it is compiled here rather than
   asserted.  The coproduct's openness predicate only APPLIES [IsOpen] to
   a restricted predicate and so stays at the space's own level; a product
   topology must quantify EXISTENTIALLY over opens of the two factors, and
   an open is a predicate on the carrier, so the quantifier lands one
   universe up. *)

Section ProductTopology.

Universe o.
Context (X Y : TopSpace@{o}).

Definition probe_prod_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(* NEGATIVE 9 (formability, universe-level typing error: the body "has
   type Type@{o+1} while it is expected to have type Type@{o}"). *)
Fail Definition probe_prod_open (W : probe_prod_carrier → Type@{o}) :
  Type@{o} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(* Control: the very same body IS formable one universe up, so what the
   negative locates is the LEVEL and not the shape. *)
Universe o2.
Constraint o < o2.

Definition probe_prod_open_up (W : probe_prod_carrier → Type@{o}) :
  Type@{o2} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(* And a control at the coproduct's own predicate, which DOES fit — the
   contrast the header draws. *)
Check (fun W : sum_carrier X Y → Type@{o} => (sum_open W : Type@{o})).

End ProductTopology.
