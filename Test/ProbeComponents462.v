(** * Probe for the connected and path components (issue #462)

    Pins the measured boundaries of the three files #462 adds for Mac
    Lane §V.9 Exercise 1, book p. 135 (PDF p. 144), catalog item
    maclane:V.9:ex1, with the appended Riehl Example 3.3.2
    (riehl:3.3:example2).  The files are Adjunction/Continuity/
    Equalizer.v (right adjoints preserve equalizers, in the elementary
    form, and the refutation it packages), Instance/Top/Components.v
    (the connected-components functor on the locally connected spaces of
    [PTopCat], left adjoint to the discrete functor from the
    propositional sets and with no left adjoint of its own, and the
    reading into all of [Sets] under [Untruncate]) and Instance/Top/
    Components/Paths.v (Riehl's path-components functor as the colimit
    functor after P).  N1-N12 restate refusals that #462's two builders,
    its review and its fold measured in scratch files (LABELS, below);
    every one is recorded in a target header, which cites it by its
    label here.  The positive controls restate the files' claims
    independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First the ten standard-library lines of Instance/Top/Components/
    Paths.v, in its order: that file puts them before its [Category]
    lines, and placed after Category.Lib they shadow Lib/Setoid.v's
    [equiv] ([Locate equiv] then lists Relation_Definitions.equiv
    first, measured), which [p462_components_equiv] below does not
    survive.  Then, target by target in the order named above, the
    [Require] lines each adds to those before it, in its own order, and
    then that target: eight lines and Equalizer.v, twelve and
    Components.v (Theory/Concrete.v required without [Import], as
    Components.v requires it), twelve and Paths.v.  Then five lines for
    the walls: Instance/Top.v and Instance/Top/Forgetful.v (the
    Type-valued [Top] and its discrete functor, N1-N5), and
    Functor/Hom.v, Theory/Kan/Extension.v and Construction/Opposite.v
    (the Yoneda derivation, N12).  Fifty lines, thirty-nine of them
    naming [Category] modules.  Under this list [Print Libraries] in a
    scratch file loads one hundred and thirty [Category] modules, the
    three targets among them, and eight modules of the standard
    library's reals, seven under Reals/Cauchy and the eighth
    Reals/Abstract/ConstructiveReals.  A shorter import list is what
    makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason ("The reference p462_absent_name
    was not found in the current environment."), and each of the forty-nine
    definitions and examples of this file that is not a refutation, wrapped
    in the refutation keyword in a copy of this WHOLE file, stops the build
    at that command with the report that the guarded command had been
    accepted (forty-nine of forty-nine, by a script over the copies).  Every
    negative other than that instrument is a [Definition] or an [Example],
    never a [Check], so that an open evar cannot satisfy it.  Each negative
    was stripped of its refutation keyword in a copy of this WHOLE file, one
    at a time, compiled, and its error read; each of the twelve copies stops
    inside the stripped command (by the File line of its error, compared by
    a script with the command's extent).  The kind recorded is the kind of
    that error, and each negative has positive controls beside it.
    Quotations are Rocq 9.1.1's under this file's import list, with the
    error's environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and <1> to <7> stand for
    the universes a stripped copy names after itself and a serial number.
    The three targets and this file also compile on Coq 8.19.2 and 8.20.1,
    with no warning, overlaid on the prebuilt trees of this library for
    those versions, whose sources of the one hundred and twenty-seven
    modules this file loads besides the three targets are this tree's byte
    for byte (compared by script) but for one, Instance/Top/Prop.v, which
    differs only by the CORRECTION (#462) comment #462 adds.  Each of the
    twelve stripped copies is refused there inside the stripped command, at
    the File line of the Rocq 9.1.1 refusal, and with the Rocq 9.1.1 error
    up to the serial names of universes (compared by a script), with two
    exceptions: Coq 8.19.2 prints the type mismatch of N1 and N2 without the
    parenthetical that names the universe inconsistency, and both older
    versions mark N1's term [Sets@{o so}] (characters 21-32 of its line)
    where Rocq 9.1.1 marks [Sets] (21-25).  Five controls were adjusted to
    reach the older versions, because Coq 8.19.2 refuses a closed constraint
    list that omits the constraints the template-polymorphic [ex],
    [inhabited], [sigT] and [prod] contribute ("Universe constraints are not
    implied by the ones declared"): [tcomp_rel_prop] and [p462_tconnsub]
    take the closed universe list [@{o}] in place of [@{o|}], and the three
    controls one universe up an extensible constraint list in place of the
    closed [@{o h | o < h}].

    KINDS.  Thirteen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1, N2,
    N3, N4, N5, N8, N12), ELIMINATION (N6, N7) and CONVERSION (N9, N10,
    N11): one, seven, two and three.  A UNIVERSE refusal is a type
    mismatch whose parenthetical is a universe inconsistency, or a bare
    universe inconsistency (N8); an ELIMINATION refusal is "Incorrect
    elimination" of a proof of a proposition into a type; a CONVERSION
    refusal is [eq_refl] refused with a "cannot unify" parenthetical.

    LABELS.  The review's TopFun is N1 and its TopProp the control
    [tcomp_rel_prop]; builder-comp's W1, W2 and W3 are N3, N4 and N5,
    its E1' is N7, its AtO N8 and its Conv N9; builder-pi0's M2 is N10
    (its Meas1) and N11 (its Meas3b), and its M1 is N12.  N2 is the
    fold's own, and so is N6, which stands for builder-comp's E1: that
    command matched on a proof of [comp_rel] and returned
    [reflexivity _] where [pmap g x ≈ pmap g y] was expected, so it was
    ill-typed apart from the elimination; N6 extracts a Type-valued
    witness instead, a term well typed but for the elimination.  The
    labels are not constants: each refutation carries its own in a
    comment on the line above it, the instrument's reading "The
    instrument".

    ** Instance/Top/Components.v, ENCODING: the Type-valued [Top]

    Controls: a functor [Top@{h o} ⟶ Sets@{h so}], one universe up, and
    an [Adjunction] record between [Top@{h o}] and [Sets@{h so}]
    ([p462_top_to_sets_up], [p462_top_adj_up]); the component relation
    over [Top], Prop-valued, under the closed universe list [@{o}]
    ([p462_tconnsub], [tcomp_rel_prop]); the three Type-valued
    forms at [Type@{h}] under [o < h] ([p462_tcomp_rel_sigma_up],
    [p462_tcomp_rel_forall_up], [p462_tconnected_up]).

    N1 (UNIVERSE).  The functor into the [Sets] of the point setoids:
      The term "Sets" has type "Category@{so o o}" while it is expected
      to have type "Category@{<1> <2> <3>}" (universe inconsistency:
      Cannot enforce o = <2> because o < h <= <2>).
    N2 (UNIVERSE).  An adjunction one universe up whose right adjoint is
    Instance/Top/Forgetful.v's discrete functor:
      The term "Top_Discrete" has type "Sets@{<1> <3>} ⟶ Top@{<2> <1>}"
      while it is expected to have type "Sets@{h so} ⟶ Top@{h o}"
      (universe inconsistency: Cannot enforce <2> = h because h < <2>).
    N3, N4, N5 (UNIVERSE).  The sum over Type-valued subsets, the
    quasi-component form and connectedness over discrete targets, at the
    points' universe:
      The term "∃ W : X → Type, W x ∧ W y" has type "Type@{o+1}" while
      it is expected to have type "Type@{o}" (universe inconsistency:
      Cannot enforce o < o because o = o).
      The term "∀ U : X → Type, IsOpen X U → U x → U y" has type
      "Type@{o+1}" while it is expected to have type "Type@{o}"
      (universe inconsistency: Cannot enforce o < o because o = o).
      The term "∀ (S : SetoidObject) (g : X → S) (a b : X), W a → W b →
      g a ≈ g b" has type "Type@{max(o+1,<1>,<2>,<3>)}" while it is
      expected to have type "Type@{o}" (universe inconsistency: Cannot
      enforce o < o because o = o).

    ** Instance/Top/Components.v, MAC LANE'S SET: the propositional sets

    Controls: through a [PropEquiv] of the target the truncation is
    eliminated ([p462_transpose_pe], Lib/Setoid/Propositional.v's
    [pequiv_elim_inhabited]) and a continuous map into a discrete space
    respects components ([p462_comp_respect]); into all of [Sets] an
    adjunction makes [Untruncate] merely true and yields the unsquashing
    principle ([p462_unsquash], [p462_unsquash_principle]), and under
    [Untruncate] the adjunction exists ([p462_adj_Sets]); [PSetsSub]'s
    object predicate placed at the points' universe
    ([p462_psets_sub_at_o]), and [PSetsSub] itself at [o := Set]
    ([p462_psets_sub_Set]).

    N6 (ELIMINATION).  A Type-valued witness out of [comp_rel]:
      Incorrect elimination of "H" in the inductive type "ex": the
      return type has sort "Type" while it should be SProp or Prop.
    N7 (ELIMINATION).  The truncated equality of two values, into the
    equality itself:
      Incorrect elimination of "HR" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
    (Both go on: "Elimination of an inductive object of sort Prop is not
    allowed on a predicate in sort "Type" because proofs can be
    eliminated only to build proofs.")
    N8 (UNIVERSE).  [PSetsSub]'s predicate placed at the points'
    universe, at [o := Set]:
      Universe inconsistency. Cannot enforce Set < Set because Set = Set.

    ** Adjunction/Continuity/Equalizer.v: why the proof is direct

    Controls: the two diagrams agree on both objects at [eq_refl]
    ([p462_pair_obj_X], [p462_pair_obj_Y]); right adjoints preserve
    equalizers ([p462_rapl_equalizers]).

    N9 (CONVERSION).  The header's WHY A DIRECT PROOF, at the variable
    functor and the variable pair of a [Section]:
      (cannot unify "U ◯ APair f g" and "APair (fmap[U] f) (fmap[U] g)")

    ** Instance/Top/Components.v: the adjunction and the refutations

    Controls: both transposes and the unit are the identity on points,
    at [eq_refl], for the adjunction at [PSets] and for the one into all
    of [Sets] under [Untruncate] ([p462_to_points], [p462_from_points],
    [p462_unit_points], [p462_Sets_to_points], [p462_Sets_from_points]),
    which the two adjunctions' [Defined] closure allows; D is [PDisc] on
    objects and C's equality is [comp_rel], at [eq_refl]
    ([p462_LDisc_obj], [p462_components_equiv]); the fork on the
    three-point space is an equalizer in [Lconn] that C does not
    preserve ([p462_zig_equalizer], [p462_zig_not_preserved]); the four
    refutations ([p462_no_left_adjoint], [p462_any_left_adjoint],
    [p462_no_left_on_PTop], [p462_PDisc_no_left]); ten theorems at
    [o := Set], the controls whose names end in [_at_Set].

    ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P

    Controls: the arrow part of π₀ IS [Colim_map] of P's, and on a
    representative point it is postcomposition, at [eq_refl]
    ([p462_pi0_fmap], [p462_pi0_fmap_point]); the identity law up to
    [≈] ([p462_pi0_id]) and the underlying functions at [eq_refl]
    ([p462_id_fun]); the endpoint pair in [PTopCat^op] and the Yoneda
    embedding of [PTopCat] ([p462_iota], [p462_yoneda]); the interval
    connected in the two-point form, π₀ of the interval one point and
    π₀ of [PBool] two ([p462_interval_connected], [p462_pi0_interval],
    [p462_pi0_bool]).

    N10 (CONVERSION).  The header's STRENGTHS, the identity law on a
    representative point:
      (cannot unify "fmap[PPi0] (pid X) (ParY; x)" and "(ParY; x)")
    N11 (CONVERSION).  The two setoid maps under it:
      (cannot unify "pmap (pcompose (pid X) x)" and "pmap x")
    N12 (UNIVERSE).  The header's P AND π₀, P derived from the Yoneda
    embedding:
      The term "Curried_CoHom PTopCat" has type "@Functor@{so o o <1>
      <2> <2>} PTopCat@{o so} (@Fun@{so o <3> o <1> <2> <3>}
      (Opposite@{o so} PTopCat@{o so}) Sets@{o <3>})" while it is
      expected to have type "@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D"
      (universe inconsistency: Cannot enforce <2> = o because o < <7>
      <= <2>).

    ** Closure: a readback, not a refutation

    [Print Assumptions] of [right_adjoint_PreservesEqualizers],
    [components_functor], [components_left_adjoint_discrete],
    [components_no_left_adjoint], [components_left_adjoint_discrete_Sets]
    and [PPi0], near the end of this file, each print "Closed under the
    global context".  A [Print Assumptions] cannot refuse, so these lines
    are readbacks and guard nothing; the Makefile's print-assumptions
    gate is where closure is kept.  By the same command all forty-nine
    constants of this file are closed under the global context.

    NOT PINNED HERE.  (a) [About] readbacks as such: the headers' [Set]
    censuses, their attributions to first carriers, and the [Set < o]
    that [p462_psets_sub_at_o] carries, read by [About] in a scratch
    file.  (b) Flip censuses and the closure of the targets under
    [Print Assumptions]: measurements of the build rather than of
    commands.  (c) The refusals of the closed universe lists
    [ibis_cv_ge@{o}] and [ibis_cv_le@{o}] that Coq 8.19.2 and 8.20.1
    make and Rocq 9.1.1 does not (Paths.v's UNIVERSES): a file that
    compiles under all three cannot pin a refusal made by only two.
    (d) The absences the headers record (no comparison of path
    components with connected components, no axiom-free inhabitant of
    [Untruncate], connectedness of the interval in the two-point form
    only): an absence has no command.  (e) builder-comp's E1 as it was
    written (LABELS).

    The guard block at the end names the two hundred and fifty-six
    constants of the three targets, so that a rename breaks this file:
    two of Adjunction/Continuity/Equalizer.v, one hundred and
    twenty-eight of Instance/Top/Components.v and one hundred and
    twenty-six of Instance/Top/Components/Paths.v.  They are exactly the
    entries [Print Module] gives for each, forty-two [Program]
    obligations among them, and the three constructors of the one
    inductive, [zig_pt], which [Print Module] lists under its type; no
    record is declared, so there is no [Build_] constructor to add.
    Each is written fully qualified, so that no short name in scope can
    stand in for it. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Coq.Reals.Cauchy.ConstructiveRcomplete.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.Equalizer.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Subcategory.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Category.Theory.Concrete.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.Components.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Components.Paths.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Open Scope category_scope.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check p462_absent_name.

(** ** Instance/Top/Components.v, ENCODING: the Type-valued [Top] *)

(* CONTROL: a functor out of [Top@{h o}] into the [Sets] one universe up,
   and an [Adjunction] record between them. *)
Definition p462_top_to_sets_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so}) :
  True := I.

Definition p462_top_adj_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so})
  (D : Sets@{h so} ⟶ Top@{h o}) (A : C ⊣ D) : True := I.

(* N1 *)
Fail Definition p462_top_to_sets@{h o so +}
  (C : Top@{h o} ⟶ Sets@{o so}) : True := I.

(* N2 *)
Fail Definition p462_top_adj_discrete@{h o so +}
  (C : Top@{h o} ⟶ Sets@{h so}) (A : C ⊣ Top_Discrete) : True := I.

(* CONTROL: the component relation over [Top], Prop-valued, is formable
   under the closed universe list of the points' universe alone. *)
Definition p462_tconnsub@{o} (X : TopSpace@{o}) (W : X → Prop) : Prop :=
  ∀ φ : X → Prop,
    (∀ z, W z → ex (fun O : X → Type@{o} =>
        inhabited (IsOpen X O) /\ inhabited (O z) /\
        ∀ w, W w → inhabited (O w) → (φ w <-> φ z))) →
    ∀ a b, W a → W b → φ a → φ b.

Definition tcomp_rel_prop@{o} (X : TopSpace@{o}) (x y : X) : Prop :=
  ex (fun W : X → Prop => p462_tconnsub X W /\ W x /\ W y).

(* CONTROL: the Type-valued forms, one universe up. *)
Definition p462_tcomp_rel_sigma_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  { W : X → Type@{o} & (W x * W y)%type }.

Definition p462_tcomp_rel_forall_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

Definition p462_tconnected_up@{o h | o < h +} (X : TopSpace@{o})
  (W : X → Type@{o}) : Type@{h} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(* N3 *)
Fail Definition p462_tcomp_rel_sigma@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  { W : X → Type@{o} & (W x * W y)%type }.

(* N4 *)
Fail Definition p462_tcomp_rel_forall@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

(* N5 *)
Fail Definition p462_tconnected@{o} (X : TopSpace@{o}) (W : X → Type@{o}) :
  Type@{o} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(** ** Instance/Top/Components.v, MAC LANE'S SET: the propositional sets *)

(* N6 *)
Fail Definition p462_comp_rel_witness@{o} (X : PTop@{o}) (x y : X)
  (H : comp_rel X x y) :
  { W : X → Prop & (PConnectedSub X W * W x * W y)%type } :=
  match H with ex_intro _ W (conj HW (conj wx wy)) => existT _ W (HW, wx, wy)
  end.

(* N7 *)
Fail Definition p462_transpose_inh@{o} (X : PTop@{o})
  (S : SetoidObject@{o o}) (g : PMor@{o} X (PDiscrete S)) (x y : X)
  (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  match HR with inhabits h => h end.

(* CONTROL: through a [PropEquiv] of the target the truncation is
   eliminated, and the transposition respects components. *)
Definition p462_transpose_pe@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  @pequiv_elim_inhabited _ _ P _ _ HR.

Definition p462_comp_respect@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) : comp_rel X x y → pmap g x ≈ pmap g y := comp_respect X S P g x y.

(* CONTROL: into all of [Sets], an adjunction makes [Untruncate] merely
   true, and [Untruncate] gives one. *)
Definition p462_unsquash@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited Untruncate@{o} :=
  components_on_all_Sets_Untruncate C' A.

Definition p462_unsquash_principle@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited (∀ Q : Type@{o}, inhabited Q → Q) :=
  components_on_all_Sets_unsquashes C' A.

Definition p462_adj_Sets@{o so | o < so +} (U : Untruncate@{o}) :
  components_functor_Sets@{o so} ⊣ LDisc@{o so} :=
  components_left_adjoint_discrete_Sets U.

(* CONTROL: [PSetsSub]'s object predicate placed at the points' universe
   is formable, with [Set < o] in its block; at the pin, at [so]. *)
Definition p462_psets_sub_at_o@{o so | o < so +} :
  Subcategory@{so o o o} Sets@{o so} :=
  @Build_Subcategory@{so o o o} Sets@{o so}
    (fun S : SetoidObject@{o o} => PropEquivObj S)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition p462_psets_sub_Set@{so | Set < so +} := PSetsSub@{Set so}.

(* N8 *)
Fail Definition p462_psets_sub_o_Set@{so | Set < so +} :=
  p462_psets_sub_at_o@{Set so}.

(** ** Adjunction/Continuity/Equalizer.v: why the proof is direct *)

Section Pair.

Context {C D : Category} (U : C ⟶ D) {x y : C} (f g : x ~> y).

(* CONTROL: the two diagrams agree on objects, at [eq_refl]. *)
Example p462_pair_obj_X :
  fobj[U ◯ APair f g] ParX = fobj[APair (fmap[U] f) (fmap[U] g)] ParX
  := eq_refl.

Example p462_pair_obj_Y :
  fobj[U ◯ APair f g] ParY = fobj[APair (fmap[U] f) (fmap[U] g)] ParY
  := eq_refl.

(* N9 *)
Fail Example p462_pair : U ◯ APair f g = APair (fmap[U] f) (fmap[U] g)
  := eq_refl.

End Pair.

(* CONTROL: right adjoints preserve equalizers, and the refutation. *)
Definition p462_rapl_equalizers@{co do h +} {C : Category@{co h h}}
  {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesEqualizers U := right_adjoint_PreservesEqualizers A.

(** ** Instance/Top/Components.v: the adjunction, at [eq_refl] *)

(* CONTROL: both transposes and the unit are the identity on points. *)
Example p462_to_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (h : components_functor@{o so} X ~{PSets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) h))
    x = `1 h x := eq_refl.

Example p462_from_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (g : X ~{Lconn@{o so}}~> PSetsDisc@{o so} S)
  (x : pt_carrier (`1 X)) :
  `1 (from (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) g) x
    = pmap (`1 g) x := eq_refl.

Example p462_unit_points@{o so | o < so +} (X : Lconn@{o so})
  (x : pt_carrier (`1 X)) :
  pmap (`1 (@unit _ _ _ _ components_left_adjoint_discrete@{o so} X)) x = x
  := eq_refl.

Example p462_Sets_to_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (h : components_functor_Sets@{o so} X ~{Sets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _
                 (components_left_adjoint_discrete_Sets@{o so} U) X S) h)) x
    = h x := eq_refl.

Example p462_Sets_from_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (g : X ~{Lconn@{o so}}~> LDisc@{o so} S) (x : pt_carrier (`1 X)) :
  from (@adj _ _ _ _ (components_left_adjoint_discrete_Sets@{o so} U) X S)
    g x = pmap (`1 g) x := eq_refl.

(* CONTROL: D is [PDisc] on objects and arrows, and C is [comp_rel]. *)
Example p462_LDisc_obj@{o so | o < so +} (S : Sets@{o so}) :
  `1 (fobj[LDisc@{o so}] S) = fobj[PDisc@{o so}] S := eq_refl.

Example p462_components_equiv@{o so | o < so +} (X : Lconn@{o so})
  (x y : pt_carrier (`1 X)) :
  @equiv _ (is_setoid (`1 (fobj[components_functor@{o so}] X))) x y
    = comp_rel (`1 X) x y := eq_refl.

(** ** Instance/Top/Components.v: the concrete equalizer, and the
    non-existence statements *)

(* CONTROL: the fork on the three-point space is an equalizer in [Lconn],
   and C does not preserve it. *)
Definition p462_zig_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LZig@{o so} LTwoIndisc@{o so}
    zig_f@{o so} zig_g@{o so} LBool@{o so} zig_e@{o so} :=
  Lconn_zig_equalizer.

Definition p462_zig_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _
    (fmap[components_functor@{o so}] zig_f@{o so})
    (fmap[components_functor@{o so}] zig_g@{o so})
    (components_functor@{o so} LBool@{o so})
    (fmap[components_functor@{o so}] zig_e@{o so}) → False :=
  components_zig_not_preserved.

(* CONTROL: the refutations, restated. *)
Definition p462_no_left_adjoint@{o so u u0 | o < so, o < u +}
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o u o u0} Lconn@{o so} PSets@{o so}
         L components_functor@{o so}) : False :=
  components_no_left_adjoint L B.

Definition p462_any_left_adjoint@{o so ua ub u u0 +| o < so, o < ua,
    o < ub +}
  (C : Lconn@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o u} PSets@{o so} Lconn@{o so}
         C PSetsDisc@{o so})
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o ub o u0} Lconn@{o so} PSets@{o so}
         L C) : False :=
  discrete_left_adjoint_no_left_adjoint C A L B.

Definition p462_no_left_on_PTop@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} PSets@{o so} PTopCat@{o so}
         C' PSetsDiscTop@{o so}) : False :=
  discrete_no_left_adjoint_on_PTop C' A.

Definition p462_PDisc_no_left@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} Sets@{o so} PTopCat@{o so}
         C' PDisc@{o so}) : False :=
  PDisc_no_left_adjoint C' A.

(* CONTROL: the points may be in [Set]: the ten theorems at [o := Set]. *)
Definition p462_adj_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete@{Set so}.

Definition p462_adj_Sets_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete_Sets@{Set so}.

Definition p462_no_left_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_no_left_adjoint@{Set so u u0}.

Definition p462_any_left_at_Set@{so ua ub u u0 | Set < so, Set < ua,
    Set < ub +} :=
  discrete_left_adjoint_no_left_adjoint@{Set so ua ub u u0}.

Definition p462_unsquash_principle_at_Set@{so u u0 | Set < so,
    Set < u +} :=
  components_on_all_Sets_unsquashes@{Set so u u0}.

Definition p462_unsquash_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_on_all_Sets_Untruncate@{Set so u u0}.

Definition p462_ptop_at_Set@{so u u0 | Set < so, Set < u +} :=
  discrete_no_left_adjoint_on_PTop@{Set so u u0}.

Definition p462_pdisc_at_Set@{so u u0 | Set < so, Set < u +} :=
  PDisc_no_left_adjoint@{Set so u u0}.

Definition p462_zig_at_Set@{so | Set < so +} :=
  components_zig_not_preserved@{Set so}.

Definition p462_swap_at_Set@{so | Set < so +} :=
  components_swap_not_preserved@{Set so}.

(** ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P *)

(* CONTROL: the arrow part of π₀ IS the colimit functor's, and on
   representatives it is postcomposition. *)
Example p462_pi0_fmap@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  fmap[PPi0@{o so p f}] h
    = Colim_map PathColim@{o so p} (PPathPair_map@{o so p} h) := eq_refl.

Example p462_pi0_fmap_point@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParY x) = existT _ ParY (pcompose h x)
  := eq_refl.

(* CONTROL: the identity law, up to [≈], and the underlying functions,
   at [eq_refl]. *)
Definition p462_pi0_id@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) ≈ existT _ ParY x :=
  @fmap_id _ _ PPi0@{o so p f} X (existT _ ParY x).

Example p462_id_fun@{o} (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  (fun u => pmap (pcompose (pid X) x) u) = (fun u => pmap x u) := eq_refl.

(* N10 *)
Fail Example p462_pi0_id_point@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) = existT _ ParY x
  := eq_refl.

(* N11 *)
Fail Example p462_id_setoid_map@{o} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) : pmap (pcompose (pid X) x) = pmap x
  := eq_refl.

(* CONTROL: the endpoint pair as a diagram in [PTopCat^op], and the
   Yoneda embedding of [PTopCat]. *)
Definition p462_iota@{o so +| o < so +} : Parallel ⟶ PTopCat@{o so}^op :=
  @APair (PTopCat@{o so}^op) PInterval@{o} PPoint@{o}
    ival_end0@{o} ival_end1@{o}.

Definition p462_yoneda@{o so +| o < so +} := Curried_CoHom PTopCat@{o so}.

(* N12 *)
Fail Definition p462_P_derived@{o so +| o < so +} :=
  Induced p462_iota ◯ Curried_CoHom PTopCat@{o so}.

(* CONTROL: the interval is connected in Instance/Top/Components.v's
   two-point form; π₀ of the interval and of [PBool]. *)
Definition p462_interval_connected@{o} : PConnectedBool PInterval@{o} :=
  interval_PConnectedBool.

Definition p462_pi0_interval@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PInterval@{o} ≅[Sets@{o so}] unit_setoid_object@{o o}
  := PPi0_PInterval_iso.

Definition p462_pi0_bool@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PBool@{o} ≅[Sets@{o so}] bool_setoid_object@{o o}
  := PPi0_PBool_iso.

(** ** Closure: a readback, not a refutation *)

Print Assumptions right_adjoint_PreservesEqualizers.
Print Assumptions components_functor.
Print Assumptions components_left_adjoint_discrete.
Print Assumptions components_no_left_adjoint.
Print Assumptions components_left_adjoint_discrete_Sets.
Print Assumptions PPi0.

(** ** Guard: the constants of the three targets *)

(* Adjunction/Continuity/Equalizer.v: 2 names. *)
Check Category.Adjunction.Continuity.Equalizer.not_PreservesEqualizers_no_left_adjoint.
Check Category.Adjunction.Continuity.Equalizer.right_adjoint_PreservesEqualizers.

(* Instance/Top/Components.v: 125 names and the constructors of [zig_pt]. *)
Check Category.Instance.Top.Components.adj_from_points.
Check Category.Instance.Top.Components.adj_Sets_from_points.
Check Category.Instance.Top.Components.adj_Sets_to_points.
Check Category.Instance.Top.Components.adj_to_points.
Check Category.Instance.Top.Components.comp_adj_iso.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_4.
Check Category.Instance.Top.Components.comp_adj_iso_U.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_4.
Check Category.Instance.Top.Components.comp_cont.
Check Category.Instance.Top.Components.comp_PropEquiv.
Check Category.Instance.Top.Components.comp_rel.
Check Category.Instance.Top.Components.comp_rel_map.
Check Category.Instance.Top.Components.comp_rel_of_equiv.
Check Category.Instance.Top.Components.comp_rel_sym.
Check Category.Instance.Top.Components.comp_rel_trans.
Check Category.Instance.Top.Components.comp_respect.
Check Category.Instance.Top.Components.comp_respect_U.
Check Category.Instance.Top.Components.comp_setoid_map.
Check Category.Instance.Top.Components.components_equiv.
Check Category.Instance.Top.Components.components_fmap.
Check Category.Instance.Top.Components.components_functor.
Check Category.Instance.Top.Components.components_functor_Sets.
Check Category.Instance.Top.Components.components_left_adjoint_discrete.
Check Category.Instance.Top.Components.components_left_adjoint_discrete_Sets.
Check Category.Instance.Top.Components.components_no_left_adjoint.
Check Category.Instance.Top.Components.components_obj.
Check Category.Instance.Top.Components.components_on_all_Sets_unsquashes.
Check Category.Instance.Top.Components.components_on_all_Sets_Untruncate.
Check Category.Instance.Top.Components.components_swap_not_preserved.
Check Category.Instance.Top.Components.components_unit_points.
Check Category.Instance.Top.Components.components_zig_not_preserved.
Check Category.Instance.Top.Components.CompSet.
Check Category.Instance.Top.Components.CompSetoid.
Check Category.Instance.Top.Components.CompTop.
Check Category.Instance.Top.Components.CompTop_obligation_1.
Check Category.Instance.Top.Components.CompTop_obligation_2.
Check Category.Instance.Top.Components.CompTop_obligation_3.
Check Category.Instance.Top.Components.connected_bool_constant.
Check Category.Instance.Top.Components.connected_no_separation.
Check Category.Instance.Top.Components.discrete_left_adjoint_no_left_adjoint.
Check Category.Instance.Top.Components.discrete_left_adjoint_not_preserved.
Check Category.Instance.Top.Components.discrete_no_left_adjoint_on_PTop.
Check Category.Instance.Top.Components.empty_set_map.
Check Category.Instance.Top.Components.image_connected.
Check Category.Instance.Top.Components.LBool.
Check Category.Instance.Top.Components.Lconn.
Check Category.Instance.Top.Components.Lconn_Sub.
Check Category.Instance.Top.Components.Lconn_swap_equalizer.
Check Category.Instance.Top.Components.Lconn_zig_equalizer.
Check Category.Instance.Top.Components.LDisc.
Check Category.Instance.Top.Components.LDisc_obligation_1.
Check Category.Instance.Top.Components.LDisc_obligation_2.
Check Category.Instance.Top.Components.LDisc_obligation_3.
Check Category.Instance.Top.Components.LDisc_PDisc_fmap.
Check Category.Instance.Top.Components.LDisc_PDisc_obj.
Check Category.Instance.Top.Components.LEmpty.
Check Category.Instance.Top.Components.locconst_restrict.
Check Category.Instance.Top.Components.LocConstOn.
Check Category.Instance.Top.Components.LTwoIndisc.
Check Category.Instance.Top.Components.LZig.
Check Category.Instance.Top.Components.negb_no_fixpoint.
Check Category.Instance.Top.Components.pbool_two_components.
Check Category.Instance.Top.Components.PConnected.
Check Category.Instance.Top.Components.PConnected_Bool.
Check Category.Instance.Top.Components.PConnected_Sep.
Check Category.Instance.Top.Components.PConnectedBool.
Check Category.Instance.Top.Components.PConnectedSep.
Check Category.Instance.Top.Components.PConnectedSub.
Check Category.Instance.Top.Components.pconv_not_locconn.
Check Category.Instance.Top.Components.pdisc_locconn.
Check Category.Instance.Top.Components.PDisc_no_left_adjoint.
Check Category.Instance.Top.Components.PLocConn.
Check Category.Instance.Top.Components.point_connected.
Check Category.Instance.Top.Components.PSets.
Check Category.Instance.Top.Components.PSetsDisc.
Check Category.Instance.Top.Components.PSetsDisc_obj.
Check Category.Instance.Top.Components.PSetsDiscTop.
Check Category.Instance.Top.Components.PSetsOne.
Check Category.Instance.Top.Components.PSetsSub.
Check Category.Instance.Top.Components.PTop_zig_equalizer.
Check Category.Instance.Top.Components.PTwoIndisc_connected.
Check Category.Instance.Top.Components.PTwoIndisc_PLocConn.
Check Category.Instance.Top.Components.PZig.
Check Category.Instance.Top.Components.PZig_connected.
Check Category.Instance.Top.Components.PZig_one_component.
Check Category.Instance.Top.Components.PZig_PLocConn.
Check Category.Instance.Top.Components.squash_id.
Check Category.Instance.Top.Components.squash_id_cont.
Check Category.Instance.Top.Components.squash_rel.
Check Category.Instance.Top.Components.squash_sym.
Check Category.Instance.Top.Components.squash_trans.
Check Category.Instance.Top.Components.SquashSetoid.
Check Category.Instance.Top.Components.swap_e.
Check Category.Instance.Top.Components.swap_L.
Check Category.Instance.Top.Components.swap_map.
Check Category.Instance.Top.Components.swap_set.
Check Category.Instance.Top.Components.union_connected.
Check Category.Instance.Top.Components.unsquash_choice.
Check Category.Instance.Top.Components.unsquash_Untruncate.
Check Category.Instance.Top.Components.Untruncate_unsquash.
Check Category.Instance.Top.Components.zig_a.
Check Category.Instance.Top.Components.zig_b.
Check Category.Instance.Top.Components.zig_c.
Check Category.Instance.Top.Components.zig_e.
Check Category.Instance.Top.Components.zig_e_fun.
Check Category.Instance.Top.Components.zig_e_map.
Check Category.Instance.Top.Components.zig_e_set.
Check Category.Instance.Top.Components.zig_f.
Check Category.Instance.Top.Components.zig_f_map.
Check Category.Instance.Top.Components.zig_f_set.
Check Category.Instance.Top.Components.zig_g.
Check Category.Instance.Top.Components.zig_g_fun.
Check Category.Instance.Top.Components.zig_g_map.
Check Category.Instance.Top.Components.zig_g_set.
Check Category.Instance.Top.Components.zig_lift_fun.
Check Category.Instance.Top.Components.zig_open.
Check Category.Instance.Top.Components.zig_pt.
Check Category.Instance.Top.Components.zig_pt_ind.
Check Category.Instance.Top.Components.zig_pt_rec.
Check Category.Instance.Top.Components.zig_pt_rect.
Check Category.Instance.Top.Components.zig_pt_sind.
Check Category.Instance.Top.Components.zig_setoid.

(* Instance/Top/Components/Paths.v: 126 names. *)
Check Category.Instance.Top.Components.Paths.ibis_clamp.
Check Category.Instance.Top.Components.Paths.ibis_clamp_hi.
Check Category.Instance.Top.Components.Paths.ibis_clamp_id.
Check Category.Instance.Top.Components.Paths.ibis_clamp_ival.
Check Category.Instance.Top.Components.Paths.ibis_clamp_lo.
Check Category.Instance.Top.Components.Paths.ibis_contra.
Check Category.Instance.Top.Components.Paths.ibis_cv_ge.
Check Category.Instance.Top.Components.Paths.ibis_cv_le.
Check Category.Instance.Top.Components.Paths.ibis_inv.
Check Category.Instance.Top.Components.Paths.ibis_left_close.
Check Category.Instance.Top.Components.Paths.ibis_lim.
Check Category.Instance.Top.Components.Paths.ibis_lim_cv.
Check Category.Instance.Top.Components.Paths.ibis_lim_ival.
Check Category.Instance.Top.Components.Paths.ibis_lim_pt.
Check Category.Instance.Top.Components.Paths.ibis_nest.
Check Category.Instance.Top.Components.Paths.ibis_pt.
Check Category.Instance.Top.Components.Paths.ibis_q_pos_inv.
Check Category.Instance.Top.Components.Paths.ibis_right_in.
Check Category.Instance.Top.Components.Paths.ibis_seq.
Check Category.Instance.Top.Components.Paths.ibis_seq_cauchy.
Check Category.Instance.Top.Components.Paths.ibis_seq_in.
Check Category.Instance.Top.Components.Paths.ibis_stage.
Check Category.Instance.Top.Components.Paths.ibis_step.
Check Category.Instance.Top.Components.Paths.ibis_val.
Check Category.Instance.Top.Components.Paths.ibis_val_proper.
Check Category.Instance.Top.Components.Paths.ibis_width.
Check Category.Instance.Top.Components.Paths.ibis_width_bound.
Check Category.Instance.Top.Components.Paths.ibis_width_mono.
Check Category.Instance.Top.Components.Paths.ibis_width_pos.
Check Category.Instance.Top.Components.Paths.ibis_width_small.
Check Category.Instance.Top.Components.Paths.interval_bool_constant.
Check Category.Instance.Top.Components.Paths.interval_bool_endpoints.
Check Category.Instance.Top.Components.Paths.interval_PConnectedBool.
Check Category.Instance.Top.Components.Paths.ival_abs_le.
Check Category.Instance.Top.Components.Paths.ival_end0.
Check Category.Instance.Top.Components.Paths.ival_end1.
Check Category.Instance.Top.Components.Paths.ival_incl.
Check Category.Instance.Top.Components.Paths.ival_incl_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_mult_pred.
Check Category.Instance.Top.Components.Paths.ival_one.
Check Category.Instance.Top.Components.Paths.ival_pred.
Check Category.Instance.Top.Components.Paths.ival_pred_0.
Check Category.Instance.Top.Components.Paths.ival_pred_1.
Check Category.Instance.Top.Components.Paths.ival_scale_map.
Check Category.Instance.Top.Components.Paths.ival_scale_map_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_segment.
Check Category.Instance.Top.Components.Paths.ival_segment_0.
Check Category.Instance.Top.Components.Paths.ival_segment_1.
Check Category.Instance.Top.Components.Paths.ival_segment_map.
Check Category.Instance.Top.Components.Paths.ival_zero.
Check Category.Instance.Top.Components.Paths.IvalSetoid.
Check Category.Instance.Top.Components.Paths.IvalSetoid_obligation_1.
Check Category.Instance.Top.Components.Paths.line_scale.
Check Category.Instance.Top.Components.Paths.line_scale_obligation_1.
Check Category.Instance.Top.Components.Paths.ParSets.
Check Category.Instance.Top.Components.Paths.path_at.
Check Category.Instance.Top.Components.Paths.path_at_obligation_1.
Check Category.Instance.Top.Components.Paths.PathColim.
Check Category.Instance.Top.Components.Paths.pbool_at_point.
Check Category.Instance.Top.Components.Paths.pbool_at_point_obligation_1.
Check Category.Instance.Top.Components.Paths.pbool_at_zero.
Check Category.Instance.Top.Components.Paths.pbool_at_zero_obligation_1.
Check Category.Instance.Top.Components.Paths.PHomSetoid.
Check Category.Instance.Top.Components.Paths.pi0_bool_cocone.
Check Category.Instance.Top.Components.Paths.Pi0_PBool_two.
Check Category.Instance.Top.Components.Paths.PInterval.
Check Category.Instance.Top.Components.Paths.pinterval_point_rel.
Check Category.Instance.Top.Components.Paths.pinterval_rel.
Check Category.Instance.Top.Components.Paths.pline_scale.
Check Category.Instance.Top.Components.Paths.pline_scale_cont.
Check Category.Instance.Top.Components.Paths.PPathPair.
Check Category.Instance.Top.Components.Paths.PPathPair_ev0.
Check Category.Instance.Top.Components.Paths.PPathPair_ev1.
Check Category.Instance.Top.Components.Paths.PPathPair_fmap_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_map.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obj.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_3.
Check Category.Instance.Top.Components.Paths.PPathPair_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_points.
Check Category.Instance.Top.Components.Paths.PPi0.
Check Category.Instance.Top.Components.Paths.PPi0_carrier.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_equiv.
Check Category.Instance.Top.Components.Paths.PPi0_fmap.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_path.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_point.
Check Category.Instance.Top.Components.Paths.PPi0_fobj.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_from_points.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_at.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_inj_point.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_4.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_path.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_fun.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_respects.
Check Category.Instance.Top.Components.Paths.ppoint_at.
Check Category.Instance.Top.Components.Paths.ppostcomp.
Check Category.Instance.Top.Components.Paths.ppostcomp_obligation_1.
Check Category.Instance.Top.Components.Paths.pprecomp.
Check Category.Instance.Top.Components.Paths.pprecomp_obligation_1.
Check Category.Instance.Top.Components.Paths.rball_scale.
