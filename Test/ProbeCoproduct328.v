Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Roster.

Generalizable All Variables.
Local Open Scope category_scope.

(** * Probe: strength boundaries of the Mon and Grph coproducts *)

(* Guard file for Instance/Mon/Coproduct.v and
   Construction/Free/Quiver/Coproduct.v, in the Test/ProbeFunnyPoly.v
   convention.

   THE IMPORT LIST IS THE UNION OF THE TWO TARGETS' LISTS, plus
   Instance/Roster.v.  That last one is deliberate and is the ONLY place
   it appears: Instance/Mon/Coproduct.v does NOT require Roster, because
   Roster pulls in Instance/Top and hence the stdlib reals, and an
   algebra file depending on that would invert the layering.  The
   consequence is that the file states its results over
   [@Mon Sets Sets_Product_Monoidal] rather than over Roster's NAME for
   that term.  Those are the same term, and the [Mon_Sets] controls
   below are where that identification is machine-checked and GUARDED --
   it was previously verified only in a scratch probe that could not be
   preserved.

   Every negative is paired with a positive control NAMING ITS OWN
   CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
   constants appearing in the NEGATIVES -- the wider check, which found
   five unguarded negatives in an earlier probe file in this tree.

   All negatives here are CONVERSION negatives ([Fail Definition ...
   := eq_refl]); this file states no formability negative.  Each was
   stripped of its [Fail] once and the resulting message inspected. *)

(** ** Instrument check *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** The Mon_Sets name identification

    Instance/Mon/Coproduct.v is stated over [@Mon Sets
    Sets_Product_Monoidal]; Instance/Roster.v:390 names that same term
    [Mon_Sets].  These controls are the machine-checked bridge. *)

Definition probe_pos_mon_sets_is_the_same_term :
  Mon_Sets = @Mon Sets Sets_Product_Monoidal := eq_refl.

Check (_ : @Cocartesian Mon_Sets).

Check (Mon_Sets_Cocartesian).

Check (Mon_Sets_Initial).

(** ** Mon: beta and eta are not definitional at the morphism level

    The sharp pair is the first negative against
    [fp_beta_l_fun] (checked below): the underlying FUNCTIONS agree on the
    nose, so what fails is the [proper_morphism] certificate that
    [setoid_morphism_compose] rebuilds -- not the mathematics. *)

Section MonNegatives.

Context (A B Q : @Mon Sets Sets_Product_Monoidal).
Context (f : A ~> Q) (g : B ~> Q).

Fail Definition probe_mon_beta_morphism :
  fp_merge A B Q f g ∘ fp_injl A B = f := eq_refl.

Fail Definition probe_mon_eta_morphism :
  fp_merge A B (FreeProd A B) (fp_injl A B) (fp_injr A B)
    = @id (@Mon Sets Sets_Product_Monoidal) (FreeProd A B) := eq_refl.

End MonNegatives.

(* Control naming [id] itself.  The rename simulation over the
   constants appearing in the NEGATIVES found it named by no control --
   [@id] occurs once, inside the eta negative -- so that negative went
   vacuously green on a rename.  Recorded rather than quietly added. *)
Check (fun (C : Category) (x : obj[C]) => @id C x).

(* Positive controls naming Instance/Mon/Coproduct.v's own constants. *)
Check fp_beta_l_fun.
Check fp_beta_l_strict.
Check fp_merge_inl.
Check coprod_is_FreeProd.
Check fp_injl.
Check fp_injr.
Check FreeProd.
Check fp_merge.

(* Non-degeneracy, named so the witness cannot silently go trivial:
   both injections are split monic for ARBITRARY factors, and over
   (nat,+) the two generators provably do not commute. *)
Check fp_injections_Monic.
Check fp_inl_injective.
Check fp_generators_do_not_commute.
Check fp_word_not_left.

(** ** Grph: the forgetful functor does NOT preserve coproducts on the
    nose

    Measured, not assumed.  Two independent causes, both located in
    Construction/Coproduct.v: it is a [Program Definition], so its [hom]
    field has an equation-passing match shape that does not convert
    under binders; and its [homset]'s [setoid_equiv] is a Qed-opaque
    obligation.  The SHARP measurement is the third negative -- [edgeset]
    fails at constructor arguments where [edges] SUCCEEDS at the very
    same arguments.

    THAT SHARP MEASUREMENT WAS CLAIMED HERE BEFORE IT WAS PINNED.  An
    earlier version of this header described it as "the third negative"
    when no [edgeset] negative existed anywhere in the file -- the
    measurement was real but GUARDED BY NOTHING, which is the exact
    distinction this file exists to enforce.  It is pinned below, with
    the [edges] control beside it so the contrast is visible. *)

Section QuiverNegatives.

Context (C D : Category).

Fail Definition probe_quiver_edges_strict :
  @edges (QuiverOfCat (C ∐ D))
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

Fail Definition probe_quiver_record_strict :
  QuiverOfCat (C ∐ D)
    = QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(* THE SHARP ONE: [edgeset] fails at the SAME constructor arguments at
   which [edges] succeeds.  The control immediately below is what makes
   this a contrast rather than an isolated refusal. *)
Fail Definition probe_quiver_edgeset_ll (a b : obj[C]) :
  @edgeset (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edgeset (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

(* Control naming [edgeset] itself, so the negative above cannot go
   vacuously green on a rename -- the [edges] control below names a
   different projection and does not cover it. *)
Check (fun (G : Quiver) (x y : nodes) => @edgeset G x y).

Definition probe_pos_quiver_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

End QuiverNegatives.

(* Positive controls naming Construction/Free/Quiver/Coproduct.v's own
   constants: the nodes and all four edge sets DO agree by eq_refl, and
   the isomorphism is what is delivered in place of the strict form. *)
(* Control naming [edges] itself: the rename simulation over the
   constants in the NEGATIVES found it named by no control, so its
   negative would have gone vacuously green on a rename.  This line is
   the repair, recorded rather than quietly added. *)
Check (fun (G : Quiver) => @edges G).

Check QuiverOfCat_Coproduct_nodes.
Check QuiverOfCat_Coproduct_edges_ll.
Check QuiverOfCat_Coproduct_edges_lr.
Check QuiverOfCat_Coproduct_iso.
Check QuiverCoprod.
Check QuiverOfCat.

(* The two triangles hold at whole-record LEIBNIZ equality -- stronger
   than the Mon side, and worth guarding so a change is noticed. *)
Check QuiverCopair_Inl.
Check QuiverCopair_Inr.

(* Respectfulness IS proved here, unlike the sibling product's
   QuiverPair_unique, which the sibling discloses as unproved. *)
Check QuiverCopair_respects.
Check QuiverCopair_unique.

(* The Cocartesian instance itself, and its derived vocabulary. *)
Check QuiverCategory_Cocartesian.
Check Coprod_is_QuiverCoprod.

(* Non-degeneracy: there is genuinely NO edge between the summands, and
   the two injections are not identified. *)
Check coprod_no_cross_edge.
Check injections_not_equivalent.
Check quiver_coprod_no_edge_lr.
