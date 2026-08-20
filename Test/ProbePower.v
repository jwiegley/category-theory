(** * Boundary probes for powers and copowers

    Companion to Structure/Limit/Power.v and Structure/Limit/Power/Hom.v
    (issue #321; Mac Lane §III.3 def 3 and §III.4 def 4, Riehl §3.5 Examples
    3.5.4 and 3.5.8, Awodey §3.2).  **If the [Fail] commands below stop
    failing, this file breaks the build.**

    THE TWO KINDS OF NEGATIVE ARE KEPT LEXICALLY APART AND ARE NOT DESCRIBED
    WITH ONE WORD.

    (1) FORMABILITY.  Three [Fail Check]s, all about universes.

    Group (1a), two negatives: the smallness side condition at [Sets].  The
    index of [power] / [copower] at [Sets] must live at the universe of the
    CARRIERS of [Sets]' objects, not at the universe of [obj[Sets]], which
    sits strictly above it.  This is the same condition
    Instance/Sets/Products.v's header analyses for [indexed_product] and
    exhibits as a reproduction recipe; the two negatives here are that recipe
    landed as a guarded command, at the power vocabulary.  Two controls at a
    small index show the rejection is the index and not the vocabulary.

    Group (1b), one negative, and it guards an ENGINEERING FINDING rather
    than a mathematical boundary.  Instance/Sets/Products.v:409-424 records
    that letting instance resolution close a [proper_morphism] field can pin
    a constant's index universe to [Set].  Written as a [Program Definition]
    the map [Sets_discrete J → J · 1] raises no obligation at all --
    resolution closes the field during elaboration -- and comes out pinned;
    Structure/Limit/Power/Hom.v therefore supplies that certificate by hand
    under [unshelve refine].  The negative is the [Program] variant, declared
    in this file, applied at an index strictly above [Set]; the control is
    the shipped hand-written constant at the SAME index.  The pair is what
    makes the finding a guarded claim rather than a remembered one.

    (2) CONVERSION.  Three claims of Leibniz equality, all rejected for the
    same underlying reason: in this library a POWER is not an EXPONENTIAL and
    a COPOWER is not a binary product -- the identifications proved in
    Structure/Limit/Power/Hom.v are isomorphisms in [Sets], and nothing
    stronger is available.  These are [Fail Definition ... := eq_refl] and
    not [Fail Example ... : T.]: a failing type ascription would guard only
    the statement, whereas what is claimed is convertibility of two terms.
    Each is paired with a control that DOES hold on the nose, so the
    rejection is attributable to the identification and not to a projection
    being stuck.

    COUNTS.  Six negatives -- three formability, three conversion -- and
    eight positive controls.  This is not a one-to-one pairing: the controls
    of each group serve that group's negatives jointly.  The instrument
    itself was checked -- wrapping [Fail] around a succeeding command reports
    "The command has not failed!" and stops compilation -- and every negative
    was compiled once with the [Fail] stripped, to confirm the error is the
    intended one:

      - group (1a), two reports of "universe inconsistency" -- "Cannot
        enforce o < <anon> because <anon> <= o" and "Cannot enforce o < o
        because o = o" -- each naming the declared level [o];
      - group (1b), one report of "universe inconsistency", "Cannot enforce
        uj <= <anon> because <anon> < uj".  Read that message precisely: it
        does NOT print [Set], and by itself it says only that the constant's
        index universe sits strictly below [uj].  That the level in question
        IS [Set] was measured separately, by elaborating the [Program]
        variant on its own and running [Set Printing Universes. About
        probe_copower_one_from_program.], whose constraint block reads
        [Set < u0, Set = u] -- an EQUALITY on the index universe, which is
        the finding.  The shipped hand-written constant prints [u < u0] and
        no [Set];
      - group (2), three "cannot unify" conversion errors, on
        [carrier (J ⋔ X)] against [carrier (Sets_pow J X)], on [J · Y]
        against [Sets_discrete J × Y], and on [fobj[power_hom_functor J b] c]
        against the exponential of the hom-setoid.

    The import list is the target files' own, in their order, plus both
    target files.  It is deliberately the full list and not a working prefix:
    a probe compiled against a short prefix can pass for the wrong reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.

Generalizable All Variables.

(** ** (1a) The index of a power at [Sets] must be a small type *)

Section BigIndex.

Universes o so.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(* Positive control 1: at a small index the power is formable. *)
Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o} nat X).

(* Positive control 2: and so is the copower. *)
Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o} nat X).

(* Negative 1: indexing by [obj[Sets]] itself is not.  [SetoidObject@{o o}]
   lives at [Type@{o+1}] while the index must live at [Type@{o}] -- the
   universe of the carriers, which is where the small sets are. *)
Fail Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o}
              SetoidObject@{o o} X).

(* Negative 2: dually for the copower. *)
Fail Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o}
              SetoidObject@{o o} X).

End BigIndex.

(** ** (1b) The [Program] form of the copower-of-[1] insertion is pinned to
       [Set], and the shipped hand-written form is not *)

(* This is the variant Structure/Limit/Power/Hom.v declines to use.  It
   raises no obligation: instance resolution closes [proper_morphism] during
   elaboration, the domain's [≈] being Leibniz [eq]. *)
Program Definition probe_copower_one_from_program (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object := {|
  morphism := fun i : J => existT (fun _ : J => poly_unit) i ttt
|}.

Section ProgramPin.

Universe uj.
Constraint Set < uj.

Context (J : Type@{uj}).

(* Positive control 3: the shipped constant applies at this index. *)
Check (Sets_copower_one_from J).

(* Positive control 4: so does the isomorphism built from it. *)
Check (Sets_copower_one J).

(* Negative 3: the [Program] variant does not -- its index universe was
   pinned to [Set] by the resolved certificate. *)
Fail Check (probe_copower_one_from_program J).

End ProgramPin.

(** ** (2) A power is not an exponential, and a copower is not a product *)

Section Conversion.

Context (J : Type).
Context (X Y : obj[Sets]).
Context (C : Category).
Context (b c : C).

(* Positive control 5: the carrier of a power at [Sets] IS the bare function
   type, on the nose. *)
Definition probe_power_carrier_control :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

(* Negative 4: but it is NOT the carrier of the exponential, which is a type
   of setoid MORPHISMS out of the discrete setoid on the index.
   [Sets_power_exponent] relates the two, and only up to isomorphism. *)
Fail Definition probe_power_is_exponent :
  carrier (@power Sets Sets_HasIndexedProducts J X)
  = carrier (Sets_pow J X) := eq_refl.

(* Positive control 6: the carrier of a copower IS the sigma type. *)
Definition probe_copower_carrier_control :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

(* Negative 5: and it is not the product object.  [Sets_copower_prod] is an
   isomorphism in [Sets], not an equality of objects. *)
Fail Definition probe_copower_is_prod :
  @copower Sets Sets_HasIndexedCoproducts J Y
  = (Sets_discrete J × Y)%object := eq_refl.

(* Positive control 7: Riehl's right-hand side [C(X, A)^I] IS a power in
   [Sets], on the nose. *)
Definition probe_rhs_control :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

(* Negative 6: it is not the exponential of the hom-setoid.  The superscript
   in [C(X, A)^I] is this library's [power], not its [^]. *)
Fail Definition probe_rhs_is_exponent :
  fobj[power_hom_functor J b] c
  = Sets_pow J {| carrier := @hom C c b ; is_setoid := @homset C c b |}
  := eq_refl.

(* Positive control 8: the two comparison maps still compute, so the
   rejections above are not a projection being stuck. *)
Definition probe_transform_control (p : C) (ev : ∀ _ : J, p ~> b)
  (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u
  := eq_refl.

End Conversion.
