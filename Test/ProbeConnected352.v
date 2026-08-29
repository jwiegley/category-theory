Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Connected.Components.

Generalizable All Variables.

(** * Probe: the boundaries Theory/Connected/Components.v measures

   That file's header records five rejections and carries no [Fail] of its
   own.  A measurement is not a guard: nothing in the build would notice if
   a donor changed and one of them started to succeed.  This file converts
   each into a pinned negative, beside a control that must SUCCEED, so that
   the boundary breaks the build loudly rather than silently moving.

   The import list is the target's own, in the target's order, with the
   target itself appended.  A probe compiled against a shorter prefix can
   fail for a missing-reference or missing-coercion reason and read as a
   genuine mathematical rejection.

   THREE KINDS, and here they really are distinguishable — the error TEXT
   separates them, not merely the label:

     CONVERSION   (negatives 1 and 2) ends in
                  `(cannot unify "X" and "Y")`
     TYPING       (negative 3) reports `has type ... while it is expected
                  to have type ...` with NO `cannot unify` clause and no
                  universe clause
     FORMABILITY  (negatives 4 and 5) ends in
                  `(universe inconsistency: Cannot enforce ...)`

   Each negative below was stripped of its [Fail] and its whole error read,
   not merely its tail; the distinguishing phrase is quoted at each. *)

(** ** Instrument check

   This command must ERROR at compile time ("The command has not failed!"),
   which is what confirms that a [Fail] wrapping a SUCCEEDING command is
   itself rejected.  Read its scope precisely: it does NOT detect a [Fail]
   that accepted everything, since such a [Fail] would compile here too.
   What it rules out is the commoner accident — a [Fail] silently treated
   as a no-op — and it is checked first because the whole file rests on
   it. *)
Fail Fail Check Category.

(** ** Negatives 1 and 2 — CONVERSION

   [zigzag_fmap] recurses on the CHAIN.  At a variable chain it is stuck
   and rebuilds nothing, so neither functor law holds definitionally.  The
   controls are the SAME statements at [zz_nil], which DO close by
   [eq_refl]: that is what locates the failure at the recursion rather than
   at [Id] or at [◯], and it is why [zigzag_fmap_id] and
   [zigzag_fmap_compose] are proved by induction in the target. *)

Section Conversion.
Context {C D E : Category}.

(* NEGATIVE 1.  Stripped, this reports:
     The term "eq_refl" has type "zigzag_fmap Id[C] s = zigzag_fmap Id[C] s"
     while it is expected to have type "zigzag_fmap Id[C] s = s"
     (cannot unify "zigzag_fmap Id[C] s" and "s").                        *)
Fail Definition probe_fmap_id_variable (x y : C) (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s := eq_refl.

(* CONTROL 1: at the empty chain the same statement DOES close. *)
Definition probe_fmap_id_nil (x : C) :
  zigzag_fmap Id[C] (zz_nil x) = zz_nil x := eq_refl.

(* NEGATIVE 2.  Stripped, this reports:
     (cannot unify "zigzag_fmap (G ◯ F) s"
              and "zigzag_fmap G (zigzag_fmap F s)").                     *)
Fail Definition probe_fmap_comp_variable (F : C ⟶ D) (G : D ⟶ E)
  (x y : C) (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s) := eq_refl.

(* CONTROL 2: at the empty chain it closes. *)
Definition probe_fmap_comp_nil (F : C ⟶ D) (G : D ⟶ E) (x : C) :
  zigzag_fmap (G ◯ F) (zz_nil x) = zigzag_fmap G (zigzag_fmap F (zz_nil x))
  := eq_refl.

(* CONTROLS naming the constants the two negatives depend on, so that
   renaming any of them breaks a command OUTSIDE a [Fail]. *)
Check @zigzag_fmap.
Check @zigzag_fmap_id.
Check @zigzag_fmap_compose.
Check @ZigZag.
Check @zz_nil.

End Conversion.

(** ** Negative 3 — TYPING

   [Proper (equiv ==> equiv) fobj[F]] is CONVERTIBLE with the type of
   [zigzag_fmap F], but the elaborator does not unfold [Proper] and
   [respectful] while unifying, so the certificate is rejected as a
   record-literal field assignment.

   THE CONTROL IS THE LITERAL TERM, not an eta-expansion of it: control 3a
   discharges the field with [exact (@zigzag_fmap C D F)] — character for
   character what the [Fail] rejects — and [Print] on the result returns
   the very record literal that was refused,
   [{| morphism := fobj[F]; proper_morphism := @zigzag_fmap C D F |}].
   So the same term is rejected as a definition body and accepted when
   built by script, which is what makes this a fact about unification and
   not about the term, and is why [pi0_fmap] in the target is built with
   [unshelve refine].  Control 3b keeps the eta-expanded form because that
   is what the shipped [pi0_fmap] actually stores. *)

Section Typing.
Universes o so hc hd.
Context {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F : C ⟶ D).

(* NEGATIVE 3.  Stripped, this reports — with NO `cannot unify` clause and
   no universe clause, which is what separates it from the other four:
     The term "@zigzag_fmap C D F" has type
      "∀ x y : obj[C], ZigZag x y → ZigZag (fobj[F] x) (fobj[F] y)"
     while it is expected to have type "Proper (equiv ==> equiv) fobj[F]". *)
Fail Definition probe_proper_as_field :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D :=
  {| morphism := fobj[F]; proper_morphism := @zigzag_fmap C D F |}.

(* CONTROL 3a: the LITERAL rejected term, supplied by a one-step script. *)
Definition probe_proper_literal :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  exact (@zigzag_fmap C D F).
Defined.

(* CONTROL 3b: the eta-expanded form the shipped [pi0_fmap] stores. *)
Definition probe_proper_by_script :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

End Typing.

(* CONTROL: [proper_morphism] is named OUTSIDE a [Fail].  Without this,
   renaming that field would make negative 3 fire for a missing-reference
   reason and pass vacuously — the field is otherwise mentioned only
   inside the [Fail] itself. *)
Check @proper_morphism.

Check @pi0.
Check @pi0_fmap.
Check @pi0_fmap_at.

(** ** Negatives 4 and 5 — FORMABILITY

   The target spells out universe binders in three places and reports the
   annotation as LOAD-BEARING.  Each clone below has the target's body with
   the binders removed and nothing else changed, so the comparison is
   attributable to the annotation alone.

   No explicit universe instance is written inside either [Fail]: a [Fail]
   carrying one can pass for an arity reason on another Coq version, which
   would make the guard vacuous without anything noticing. *)

(* An unannotated clone of [zigzag_fmap]. *)
Fixpoint probe_zigzag_fmap_unann {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) : ZigZag (F x) (F y) :=
  match s in ZigZag a b return ZigZag (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  end.

(* Unannotated clones of the [pi0_proj] chain. *)
Definition probe_ObjSetoid_unann (C : Category) : SetoidObject :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence obj[C] |} |}.

Definition probe_coarser_unann (C : Category) :
  SetoidCoarser (A:=probe_ObjSetoid_unann C) (@ZigZag C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

Definition probe_pi0_unann (C : Category) : SetoidObject :=
  SetsQuotient (probe_ObjSetoid_unann C) (@ZigZag C) (zigzag_Equivalence C).

Definition probe_pi0_proj_unann (C : Category) :
  probe_ObjSetoid_unann C ~{Sets}~> probe_pi0_unann C :=
  sets_quot_proj (probe_ObjSetoid_unann C) (@ZigZag C)
    (zigzag_Equivalence C) (probe_coarser_unann C).

Section FormabilityHom.
Universes uo uhc uhd.
Constraint uhc < uhd.
Context (Cu : Category@{uo uhc uhc}) (Du : Category@{uo uhd uhd}).
Context (Fu : Cu ⟶ Du) (a b : Cu) (s : ZigZag a b).

(* CONTROLS: the two categories, the functor and the chain are all
   formable with the hom universes declared STRICTLY apart, so the
   negative below cannot be firing merely on the section's levels. *)
Check Cu.
Check Du.
Check Fu.
Check s.

(* CONTROL 5: the SHIPPED, annotated [zigzag_fmap] applies across them. *)
Check (zigzag_fmap Fu s).

(* NEGATIVE 5.  Stripped, this reports:
     The term "Fu" has type "@Functor@{uo uhc uhc uo uhd uhd} Cu Du"
     while it is expected to have type "@Functor@{...} ?C ?D"
     (universe inconsistency: Cannot enforce uhd = uhc because uhc < uhd).
   The expected type shows the two hom universes IDENTIFIED — which is the
   minimization the target's binders undo. *)
Fail Check (probe_zigzag_fmap_unann Fu s).

End FormabilityHom.

Section FormabilityObj.
Universes vo vh.
Constraint vh < vo.
Context (Cv : Category@{vo vh vh}).

(* CONTROLS at a category whose homs sit STRICTLY BELOW its objects. *)
Check Cv.
Check (obj[Cv]).

(* CONTROL 4: the SHIPPED, annotated [pi0_proj] IS formable here.  This is
   the discriminating half: same body, only the binders differ. *)
Check (pi0_proj Cv).

(* NEGATIVE 4.  Stripped, this reports:
     The term "Cv" has type "Category@{vo vh vh}"
     while it is expected to have type "Category@{...}"
     (universe inconsistency: Cannot enforce vh = vo because vh < vo).
   The three elided levels are one and the same freshly generated level, so
   the expected type shows ALL THREE of C's universes identified.  (Elided
   here as in negative 5: the generated names vary per compilation and are
   not quotable.) *)
Fail Check (probe_pi0_proj_unann Cv).

End FormabilityObj.

(* CONTROLS naming the public constants the formability negatives are
   about, outside any [Fail]. *)
Check @pi0_proj.
Check @pi0_proj_at.
Check @ObjSetoid.
Check @pi0_coarser.
Check @zigzag_Equivalence.
Check @sets_quot_proj.
Check @SetsQuotient.
Check @SetoidCoarser.

(** ** Controls for the headline results the target claims

   These are not boundaries; they are here so that a rename or a change of
   statement in the target breaks THIS file too. *)
Check @Connected.
Check @ConnectedNonempty.
Check @Zero_Connected.
Check @Zero_not_ConnectedNonempty.
Check @connected_readings_differ.
Check @connected_iff_pi0_subsingleton.
Check @ConnectedComponent.
Check @Component_Incl.
Check @Component_Connected.
Check @Component_reindex_equiv.
Check @eso_connected.
Check @equivalence_connected.
Check @image_connected_not_connected.
Check @DiscreteCat_bool_not_connected.
Check @Parallel_Connected.
Check @Pi0.

(* Controls for the connected-diagram section (Riehl §3.4).  These guard
   the derived notion the same way: a rename in the target breaks here. *)
Check @ConnectedDiagram.
Check @ConnectedNonemptyDiagram.
Check @connected_diagram_of_nonempty.
Check @connected_diagram_reindex.
Check @connected_diagram_pi0.
Check @pi0_connected_diagram.
Check @Parallel_ConnectedDiagram.
Check @bool_diagram_not_connected.
