Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.

Generalizable All Variables.

(** * A full reflective subcategory of a cocomplete category is cocomplete

    Mac Lane §V.5 Exercise 3 (book p. 120, `maclane:V.5:ex3`, #434) — the
    colimit half of Riehl's Proposition 4.6.14, whose limit half is
    Construction/Reflective/Limit.v (#373): colimits in a full reflective
    subcategory are computed by reflecting the ambient colimit, so a full
    reflective subcategory of a cocomplete category is cocomplete.  Over
    Construction/Reflective.v:60's [Reflective S] (a [Subcategory] record on
    the ambient [C], with [reflective_full], [reflector : C ⟶ Sub C S] and
    [reflective_adj : reflector ⊣ Incl C S]), for a diagram
    [K : J ⟶ Sub C S] and an ambient colimit [L : Colimit (Incl C S ◯ K)]:
    [reflective_colimit L : Colimit K], with apex
    [reflector R (colimit_apex L)] and injections
    [fmap[reflector R] (colimit_inj L x) ∘ rc_unit_hom (K x)] — the formula
    the issue asks for, both at [eq_refl] — the cocone-level form
    [reflective_colimit_cocone], and the packaging
    [reflective_Cocomplete : @Cocomplete C → @Cocomplete (Sub C S)]
    (canonical, matching Limit.v's [reflective_Complete]; the issue's own
    name [reflective_subcategory_cocomplete] is an alias by [:=]).

    THE ROUTE, six tactic lines in all.  The reflector is a left adjoint,
    so it carries the ambient colimit to a colimit of
    [reflector ◯ (Incl ◯ K)] (Adjunction/Continuity.v:264
    [lapc_is_acolimit]); the counit isomorphism [reflector (Incl x) ≅ x],
    whiskered along [K], is a diagram isomorphism
    [reflective_diagram_iso : reflector ◯ (Incl ◯ K) ≈ K] (Theory/Functor.v's
    [Functor_Setoid]), and Theory/Equivalence/Colimit.v:363's
    [isacolimit_transport] moves the colimit across it with the apex
    untouched; Theory/Equivalence/Limit.v:101's [isalimit_to_limit] repacks.
    Construction/Reflective.v:92's [reflective_counit_iso] is [Qed] and is
    consumed here as DATA, so it is restated transparently as
    [rc_counit_iso], with [rc_unit_hom] its inverse leg.  FULLNESS of the
    inclusion is spent exactly once, in [rc_unit_hom], lifting the unit at
    [Incl x] into the subcategory; FAITHFULNESS is not used at all — unlike
    the limit half, which reflects a limit down along [Incl] through
    [ff_reflect_ump].  The reflector is cocontinuous with no hypothesis
    ([reflective_reflector_Cocontinuous], Continuity.v:255).

    WITNESS.  Over any shape with a terminal object the ambient colimit
    exists in ANY category (Structure/Limit/Initial.v:470
    [terminal_Colimit]), so [reflective_terminal_shape_colimit] needs no
    cocompleteness hypothesis; Test/ProbeReflectiveColimit434.v
    instantiates it at the torsion-free reflection of abelian groups
    (Instance/Ab/TorsionFree.v:525 [TorsionFree_Reflective]) over
    [Ordinal 2] — two objects and a non-identity arrow, so the leg
    condition is exercised — with the apex at [eq_refl].  The
    instantiation lives in the probe because importing
    Instance/Ab/TorsionFree.v here costs 22 modules of closure and makes
    Construction/ depend on Instance/Ab.  No ambient of an in-tree
    reflection ([Ab], [Top], [Ord]) is shown cocomplete, so
    [reflective_Cocomplete] at a concrete reflection stays a conditional —
    the status docs/INHABITATION.md records, the same as
    [reflective_Complete]'s.

    STALE PREMISES (the issue's "Current state", six).  [Cocomplete]
    (Structure/Complete.v:119) is said to have "no concrete instance and
    only a hypothesis use in Theory/Adamek/Corollaries.v": it has three
    inhabitants — [Sets_Cocomplete] (Instance/Sets/Cocomplete.v:485),
    [Subsets_Cocomplete] (Instance/Powerset.v:641),
    [Proset_Cocomplete_of_all_joins] (Instance/Proset/Limit.v:605) — and a
    dozen hypothesis users, none in Adjunction/GAFT.v or its satellites
    ("consumed only as a hypothesis in GAFT" has zero hits).  Both "0 hits"
    greps (`colimits.*subcategory`, `reflective.*colimit`) return one hit
    each, Limit.v's own scope-out paragraph.  [equivalence_creates_colimits]
    is Theory/Equivalence/Limit.v:524, not :582.  The colimit-creation
    vocabulary the issue says is absent exists at
    Structure/Limit/Creation.v:406-440 ([CreatesColimit],
    [StrictlyCreatesColimit], [CreatesAllColimits], [creates_colimit_lift],
    [creation_preserves_colimit], [creates_colimits_Cocomplete]); it is not
    used here, since a reflective inclusion does NOT create colimits (Riehl
    §4.6 ex xi), and probe N4 pins that [reflective_colimit] is not an
    instance of it.  Adjunction/Continuity.v:223 is a section comment, the
    constants being :233-:264, and Construction/Reflective.v:62 is
    [reflector], the record opening at :60.  The donor the issue never
    names is Theory/Equivalence/Colimit.v, whose transports do the work.

    UNIVERSES ([About] under `Set Printing Universes`, all 20 heads).  No
    [Set] anywhere.  Every head carries `u0 = u2` (the ambient's hom level
    identified with [Subcategory]'s, in the binder [C : Category@{u u0 u0}]
    as Limit.v:249-261 records) and the strict `u0 < u4`; the eight heads
    of the shape section carry Limit.v's five block equations (`u0 = u8`,
    `u0 = u10`, `u4 = u11`, `u5 = u9` beside `u0 = u2`), inherited from the
    same donors.  [reflective_Cocomplete] has type
    [Cocomplete@{u7 u12 u0 u} → Cocomplete@{u7 u12 u0 u5}]: the two
    [Cocomplete]s share three of their four levels and differ only in the
    ambient object level — no annotation was needed.  The stdlib caps
    `Basics.compose`, `ID` and Specif's `Projections` are on every head,
    arriving with [radj] from [Reflective] and [Sub].

    MEASURED.  20 `.glob` heads (16 `def`, 4 `prf`), no [Program]
    obligations, all 20 "Closed under the global context", zero `Axioms:`
    lines; the `make print-assumptions` gate carries the 20.  Two
    `Defined`, both LOAD-BEARING (flipped to `Qed` one at a time in a copy
    of the whole file: [rc_unit_hom] stops [rc_iso_to_from],
    [reflective_diagram_iso] stops the readback [reflective_colimit_inj]);
    four `Qed`; five `eq_refl` Examples.  Closure 45 files excluding self
    (Structure/Limit/Initial.v 9 at the margin — the witness —
    Theory/Equivalence/Colimit.v 2, Construction/Reflective.v 1,
    Structure/Complete.v 1, the other twelve `Require`s 0; none of the 16
    is droppable; Limit.v's closure is 36, and Adjunction/Diagonal/Limit.v's
    [HasColimitsOfShape] form was left out because it costs 35 more).
    Zero name collisions for the 20 names (`grep -rlw --include='*.v'`;
    Limit.v's header mentions [reflective_colimit] and
    [reflective_Cocomplete] by design; [reflective_lift] and
    [reflective_incl_adj] are Limit.v's and were avoided).
    Test/ProbeReflectiveColimit434.v mirrors the `Require` list plus
    Structure/Limit/Creation.v and the witness's three modules and carries
    5 refutation commands = 1 instrument + N1 TYPING (the reflected apex is
    an object of [Sub C S], not the ambient apex: "has type obj[C] while it
    is expected to have type obj[Sub C S]") + N2 CONVERSION
    ([Cocomplete (Sub C S) = Cocomplete C] at [eq_refl]) + N3-N4 TYPING
    (the cocone-level result does not ascribe to
    [PreservesColimitCocone K (Incl C S)], nor the colimit to
    [CreatesColimit K (Incl C S)]), each stripped one at a time in a copy
    of the whole file beside its accepted control; six `eq_refl` readbacks;
    guard coverage 20/16 with four exhaustive exceptions (identifier tokens
    inside the five refutation commands / also named outside them, comments
    stripped; the exceptions are the refutation keyword, the two refuted
    Examples' own names and the instrument's absent name);
    rename-simulated 9 library names — [reflective_colimit],
    [colimit_apex], [eq_refl], [Cocomplete], [Sub],
    [reflective_colimit_cocone], [PreservesColimitCocone], [Incl],
    [CreatesColimit] — every first break on a positive line.  `make todo`
    grows by the 5 refutation lines only (2272 → 2277 over #433's tip
    10fdfda4), so the issue's "adds no new hits" box is not met as written
    (disclosed, as in #430 and #433); Coq 8.19 and 8.20 are checked by nix
    source builds of the committed revision, which the PR records.
    Limit.v's header paragraph on the colimit half (:216-222) and its
    docs/INDEX.md bullet's "OPEN" clause are corrected in place, the former
    line-neutrally.

    NOT DELIVERED: creation of colimits by the inclusion, or Riehl §4.6 ex
    xi's counterexample that it need not (no in-tree reflection comes with
    the ambient colimit that would leave the subcategory — a follow-on
    candidate, surfaced in the PR rather than filed); naturality of
    [reflective_diagram_iso] in [K]; the per-shape [HasColimitsOfShape]
    form; any [Cocomplete] inhabitant for an ambient carrying a reflection;
    strict creation, the monadic route through
    Construction/Reflective/Idempotent.v, anything about [Coreflective];
    nothing is registered as an [Instance]; no edit to
    Construction/Reflective.v, Adjunction/Continuity.v,
    Theory/Equivalence/Colimit.v, Structure/Limit/Initial.v or
    Structure/Complete.v. *)

Section ReflectiveColimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

Definition radj : reflector R ⊣ I := reflective_adj R.

(** ** A transparent counit isomorphism

    Construction/Reflective.v's [reflective_counit_iso] is [Qed]; this
    development consumes the isomorphism as DATA (it is whiskered into a
    diagram isomorphism whose components must reduce), so it is restated
    here with [Defined].  Fullness of the inclusion is spent exactly once,
    in [rc_unit_hom]: the unit at [I x] lives in the ambient category and
    has to be lifted into the subcategory. *)

Definition rc_unit_hom (x : Sub C S) : x ~{Sub C S}~> reflector R (I x).
Proof.
  exists (@Category.Theory.Adjunction.unit (Sub C S) C (reflector R) I radj
            (I x)).
  apply (reflective_full R).
Defined.

Lemma rc_iso_to_from (x : Sub C S) :
  @counit (Sub C S) C (reflector R) I radj x ∘ rc_unit_hom x ≈ id.
Proof. apply (@fmap_counit_unit (Sub C S) C (reflector R) I radj x). Qed.

Lemma rc_iso_from_to (x : Sub C S) :
  rc_unit_hom x ∘ @counit (Sub C S) C (reflector R) I radj x ≈ id.
Proof.
  rewrite <- (counit_naturality radj).
  apply (@counit_fmap_unit (Sub C S) C (reflector R) I radj (I x)).
Qed.

Definition rc_counit_iso (x : Sub C S) : reflector R (I x) ≅[Sub C S] x :=
  {| to := @counit (Sub C S) C (reflector R) I radj x
   ; from := rc_unit_hom x
   ; iso_to_from := rc_iso_to_from x
   ; iso_from_to := rc_iso_from_to x |}.

Lemma rc_to (x : Sub C S) :
  to (rc_counit_iso x) ≈ @counit (Sub C S) C (reflector R) I radj x.
Proof. reflexivity. Qed.

Lemma rc_from (x : Sub C S) : from (rc_counit_iso x) ≈ rc_unit_hom x.
Proof. reflexivity. Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** The diagram isomorphism [reflector ◯ (I ◯ K) ≈ K]

    The counit isomorphism at each [K x], with its naturality square: the
    one triangle identity each way and [counit_naturality]. *)

Definition reflective_diagram_iso : (reflector R ◯ (I ◯ K)) ≈ K.
Proof.
  exists (fun x => rc_counit_iso (K x)).
  intros x y f.
  rewrite <- comp_assoc.
  rewrite (rc_to (K x)).
  rewrite <- (counit_naturality radj (fmap[K] f)).
  rewrite comp_assoc.
  rewrite (rc_from (K y)).
  rewrite (rc_iso_from_to (K y)).
  now rewrite id_left.
Defined.

(** ** The reflected colimit

    The reflector, a left adjoint, carries the ambient colimit of [I ◯ K]
    to a colimit of [reflector ◯ (I ◯ K)] (Adjunction/Continuity.v's
    [lapc_is_acolimit]); the diagram isomorphism moves it to [K]
    (Theory/Equivalence/Colimit.v's [isacolimit_transport]); the apex is
    untouched. *)

Definition reflective_colimit (L : Colimit (I ◯ K)) : Colimit K :=
  isalimit_to_limit
    (isacolimit_transport reflective_diagram_iso
       (lapc_is_acolimit radj L)).

Example reflective_colimit_apex (L : Colimit (I ◯ K)) :
  colimit_apex (reflective_colimit L) = reflector R (colimit_apex L)
  := eq_refl.

(* The injections: the reflector applied to the ambient injections, after
   the inverse counit — the formula the issue asks for, on the nose. *)
Example reflective_colimit_inj (L : Colimit (I ◯ K)) (x : J) :
  colimit_inj (colimit_is_acolimit (reflective_colimit L)) x
    = fmap[reflector R] (colimit_inj (colimit_is_acolimit L) x)
        ∘ rc_unit_hom (K x) := eq_refl.

(** ** The cocone-level form *)

Definition reflective_lift_cocone (N : Cocone (I ◯ K)) : Cocone K :=
  cocone_transport reflective_diagram_iso (FCocone (reflector R) N).

Example reflective_lift_cocone_apex (N : Cocone (I ◯ K)) :
  vertex_obj[reflective_lift_cocone N] = reflector R vertex_obj[N]
  := eq_refl.

Example reflective_lift_cocone_inj (N : Cocone (I ◯ K)) (x : J) :
  cocone_inj (reflective_lift_cocone N) x
    = fmap[reflector R] (cocone_inj N x) ∘ rc_unit_hom (K x) := eq_refl.

Definition reflective_colimit_cocone (N : Cocone (I ◯ K))
  (HN : IsColimitCocone N) : IsColimitCocone (reflective_lift_cocone N) :=
  isalimit_limitcone
    (isacolimit_transport reflective_diagram_iso
       (colimitcocone_isacolimit
          (left_adjoint_PreservesColimitCocone radj (I ◯ K) N HN))).

End Shape.

(** ** Mac Lane §V.5 Exercise 3 *)

Definition reflective_Cocomplete (HC : @Cocomplete C) : @Cocomplete (Sub C S) :=
  fun J K => reflective_colimit K (HC J (I ◯ K)).

(* The issue's name for the same constant. *)
Definition reflective_subcategory_cocomplete :
  @Cocomplete C → @Cocomplete (Sub C S) := reflective_Cocomplete.

(* The reflector is cocontinuous, with no hypothesis at all. *)
Definition reflective_reflector_Cocontinuous :
  CocontinuousFunctor (reflector R) := left_adjoint_Cocontinuous radj.

(** ** A hypothesis-free witness

    Over any shape with a terminal object the ambient colimit exists in
    ANY category (Structure/Limit/Initial.v's [terminal_Colimit]), so the
    reflected colimit needs no cocompleteness hypothesis. *)

Definition reflective_terminal_shape_colimit {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) : Colimit K :=
  reflective_colimit K (@terminal_Colimit J C T (I ◯ K)).

Example reflective_terminal_shape_apex {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) :
  colimit_apex (reflective_terminal_shape_colimit T K)
    = reflector R (I (K (@terminal_obj J T))) := eq_refl.

End ReflectiveColimits.
