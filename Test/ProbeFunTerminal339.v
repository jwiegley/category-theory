(** * Boundary probes for Instance/Fun/Terminal.v (issue #339)

    Mac Lane CWM 2nd ed. §III.5 Exercise 5, book p. 74.

    The target ships its own two CONVERSION refutations with controls
    (`Instance/Fun/Terminal.v:601` and `:634`).  This file pins the SEVEN
    boundaries it cannot: six FORMABILITY negatives, which need a section
    declaring universe levels strictly apart and so cannot live in a
    library file, and one three-way SEPARATION that is a positive
    measurement rather than a refutation.

    SIX NEGATIVES, ALL FORMABILITY, in two groups:

      * Negatives 1-5 attribute the hom = proof identification that every
        result about `[C, D]` carries.  FIVE donors do it INDEPENDENTLY --
        `Terminal`, `Cartesian`, `HasIndexedProducts`, `IsIndexedProduct`
        and `Fun` -- each rejected under `Constraint uh < up` against
        controls that name a hom and a family at those very levels.  The
        point of testing all five separately is that blaming the first
        plausible donor would be wrong: `Fun` in fact does MORE than the
        other four, identifying hom with proof in BOTH arguments and the
        two hom levels with each other.

      * Negative 6 is why the target builds `Constant_Functor` instead of
        citing `Functor/Diagonal.v`.  `Diagonal`'s type mentions `[J, C]`
        and so inherits `Fun`'s identification; the constant functor built
        by hand does not, and keeps C's hom and proof APART.  The control
        is that very functor at the very levels the negative is rejected
        at, so the negative is attributable to `Diagonal` and not to the
        section.

    THE SEPARATION (no `Fail` -- three `About`-able definitions):
    `probe_functor_only`, `probe_cone_of_discrete` and
    `probe_limit_of_discrete` measure WHERE the `Set` pin on the
    `Limit`-of-a-discrete-diagram route actually comes from.  Measured
    here rather than assumed, and the result CORRECTS what ONE of this
    tree's own CLAUDE.md bullets says -- the
    `Construction/Coproduct/Indexed.v`/`Instance/Cat/Coproduct.v` one.
    (An earlier revision of this header named three bullets; the other
    two are sound, `Functor/Hom/Limit.v`'s naming both donors and
    `Structure/Limit/Product/Finite.v`'s citing the composite.)

      probe_functor_only      C : Category@{u0 u2 u2}    FREE
      probe_cone_of_discrete  C : Category@{u1 u2 u2}    FREE
      probe_limit_of_discrete C : Category@{u1 Set Set}  PINNED

    So `DiscreteCat_Functor` ALONE does NOT pin the ambient category -- it
    fixes only the SHAPE, at `DiscreteCat@{u Set Set}`.  The ambient pin
    needs a SECOND donor that identifies the shape's hom and proof with
    the ambient's; it takes BOTH.  Read the second half narrowly: the
    `Cone` RECORD is innocent, but that licenses no claim that
    `IsALimit`/`Limit` are the ONLY other donors, and they are not --
    `cone_leg` (`Structure/Limit/Preservation.v:108`, over
    `J : Category@{u u0 u0}` and `C : Category@{u1 u0 u0}`) and
    `IsLimitCone` (`:166`) identify them in exactly the same way, so
    CONE VOCABULARY is among the donors even though the record is not.
    `Structure/Limit/Initial.v`'s own bullet already warns that an
    `ACone` control rules out only `ACone`/`Cone`; an earlier revision of
    this header ran that control and drew the broader conclusion anyway.  The practical conclusion those bullets draw (do not route an
    indexed product through `Limit (DiscreteCat_Functor …)`) is unchanged
    and is what `Instance/Fun/Terminal.v` follows; only the attribution
    was wrong.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.Terminal.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negatives 1-5 (FORMABILITY): five INDEPENDENT donors identify hom
       with proof

    Each is rejected under `Constraint uh < up` while the controls show a
    hom-set and an object family are perfectly formable at those levels.
    Testing them separately is the point: no single one is "the" cause. *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Control: so does a family of its objects -- the shape the indexed
   results quantify over. *)
Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C) => f).

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(* Control: [Cartesian] exists at unconstrained levels.  Same reason as
   the [HasIndexedProducts] control below -- without it the negative
   would survive a rename of [Cartesian] on a reference-not-found
   error. *)
Check @Cartesian.

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* Control: [HasIndexedProducts] EXISTS and elaborates at UNCONSTRAINED
   levels.  Without this line the negative below would still "succeed"
   after a rename of [HasIndexedProducts], on a reference-not-found error
   rather than on the universe boundary -- measured, not guessed: an
   earlier revision omitted it and the rename simulation scored 5/7. *)
Check @HasIndexedProducts.

(* NEGATIVE 3. *)
Fail Check (fun (C : Category@{uo uh up}) => @HasIndexedProducts C).

(* Control: likewise for [IsIndexedProduct], for the same reason. *)
Check @IsIndexedProduct.

(* NEGATIVE 4. *)
Fail Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C)
                (p : C) (proj : forall a, p ~> f a) =>
              @IsIndexedProduct C A f p proj).

(* Control: [Fun] exists at unconstrained levels. *)
Check @Fun.

(* NEGATIVE 5.  [Fun] does MORE than the other four: it identifies hom
   with proof in BOTH arguments and the two hom levels with each other. *)
Fail Check (fun (C D : Category@{uo uh up}) => @Fun C D).

End Donors.

(** ** Negative 6 (FORMABILITY): why the target builds its own constant
       functor rather than citing [Diagonal]

    [Diagonal]'s type mentions the functor category and so inherits
    [Fun]'s identification.  [Constant_Functor], built by hand with
    explicit binders, keeps C's hom and proof APART -- and the control
    below is that functor AT THE VERY LEVELS the negative is rejected at,
    so the rejection is attributable to [Diagonal]. *)

Section DiagonalPin.

Universe co ch cp dro dh.
Constraint ch < cp.

(* Control: the three objects exist at these levels. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => (C, D, T)).

(* Control: so does the terminal object of D. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => @terminal_obj D T).

(* Control: and so does the target's OWN constant functor, at exactly
   these levels -- C's hom and proof strictly apart. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh}) (d : D) =>
         @Constant_Functor@{co ch cp dro dh dh} C D d).

(* Control: and its terminal specialization. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) =>
         @Constant_Terminal_Functor@{co ch cp dro dh} C D T).

(* Control: [Diagonal] exists at unconstrained levels. *)
Check @Diagonal.

(* NEGATIVE 6. *)
Fail Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
                (T : @Terminal D) =>
              fobj[@Diagonal D C] (@terminal_obj D T)).

End DiagonalPin.

(** ** The separation: where the [Set] pin on the [Limit] route comes from

    Not a refutation -- three definitions whose universe signatures are
    the measurement.  Run `About` on each to see it. *)

Definition probe_functor_only
  {C : Category} {A : Type} (f : A -> C) : DiscreteCat A ⟶ C :=
  DiscreteCat_Functor f.

Definition probe_cone_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Cone (DiscreteCat_Functor f).

Definition probe_limit_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Limit (DiscreteCat_Functor f).

(** ** Positive controls for the headline artifacts *)

Check @Functor_Category_Terminal.
Check @Constant_Functor.
Check @Constant_Terminal_Functor.
Check @Fun_iprod.
Check @Fun_iprod_proj.
Check @Fun_IsIndexedProduct.
Check @Fun_HasIndexedProducts.
Check @iprod_jointly_monic.
Check @cartesian_bool_IsIndexedProduct.
Check @Fun_bool_iprod_iso.
Check @terminal_empty_IsIndexedProduct.
Check @Fun_empty_iprod_terminal.

(** The two CONVERSION refutations live in the target with their own
    controls; these name their constants so a rename breaks this file
    too. *)

Check @bool_fam.
Check @Fun_bool_iprod_iso_commutes.
Check @Fun_bool_iprod_iso_inv_commutes.

(** ** MEASURED RENAME-SIMULATION SCORE

    Read off the `Fail` commands themselves, not from memory.

      Negative 1 names [Terminal], [Category]
      Negative 2 names [Cartesian], [Category]
      Negative 3 names [HasIndexedProducts], [Category]
      Negative 4 names [IsIndexedProduct], [Category]
      Negative 5 names [Fun], [Category]
      Negative 6 names [Diagonal], [terminal_obj], [Terminal], [Category],
                       [fobj]

    Excluding core vocabulary ([Category], [fobj]) on the stated ground
    that it is named by almost every file in the tree rather than that it
    is hard to guard, the constants a NEGATIVE names are SEVEN:
    [Terminal], [Cartesian], [HasIndexedProducts], [IsIndexedProduct],
    [Fun], [Diagonal], [terminal_obj].

    Each of the seven is named by a positive control above -- note that
    [Fun_HasIndexedProducts] and [Fun_IsIndexedProduct] do NOT count as
    controls for [HasIndexedProducts] and [IsIndexedProduct], since `_`
    is a word character and a rename of the bare name does not touch
    them; the bare `Check`s in the Donors and DiagonalPin sections are
    what guard those.  TWO measurement defects were found and fixed
    before this score could be stated, and both are recorded rather than
    quietly repaired: (a) three of the seven -- [Cartesian], [Fun] and
    [Diagonal] -- were named ONLY inside their own `Fail`, so a rename
    left the `Fail` succeeding on "reference not found"; bare controls
    for all three are now present; and (b) the simulation itself was
    broken, because it renamed the module paths in the `Require Import`
    lines too, so the file failed to compile for the WRONG REASON and
    every result read as a pass.  A rename simulation must PRESERVE
    `Require`/`From` lines.  Score: 7/7,
    on an unpadded denominator, measured by compiling a renamed copy of
    this file against an instrument-checked baseline and confirming each
    one breaks it. *)
