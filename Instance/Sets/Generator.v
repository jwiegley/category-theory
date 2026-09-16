Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(* Separators of [Sets]: the singleton, the terminal object, and the one
   object that is not one

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/well-pointed+category

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 127 (PDF p. 136), Definition 4 is the source: a set of
   objects GENERATES a category when, for every parallel pair h ≠ h',
   some member s of the set carries an f : s → c with h ∘ f ≠ h' ∘ f.
   Mac Lane's two examples are the one-point set for sets and the
   integers for abelian groups.  Awodey, "Category Theory" (1st ed.,
   Carnegie Mellon pre-print, September 2005), §7.2, printed p. 154
   (PDF p. 163), gives the single-object form and the characterization by
   faithfulness of the representable; Riehl, "Category Theory in
   Context", 2nd ed., Definition 4.7.7, printed p. 177 (PDF p. 197),
   gives the family form and names the dual, and her Epilogue §E.4,
   printed p. 257 (PDF p. 277), recalls it as clause (vi) of Giraud's
   theorem.  This file supplies the [Sets] half of Mac Lane's two
   examples, stated against Structure/Generator.v's [IsSeparator] and
   [Generator]; the other half is Instance/Ab/Generator.v, with
   Instance/Grp/Generator.v alongside for Awodey's group example.

   RIEHL'S SPELLING IS THE CONTRAPOSITIVE.  Riehl (and Mac Lane) write
   the condition as "f ≠ g implies some h with f ∘ h ≠ g ∘ h".  Over a
   [Type]-valued hom-setoid with no decision procedure for ≈, NEITHER
   form implies the other: the cancellation form yields only ¬∀ from
   f ≉ g, never the witnessing h, and the negative form yields only
   ¬¬(f ≈ g) from agreeing tests, never f ≈ g; they become
   interderivable under decidability of ≈ on the hom-setoid in question
   (an earlier revision of this paragraph called the negative form
   "strictly weaker", an ordering an audit showed does not hold in either
   direction).  Structure/Generator.v therefore states
   the positive cancellation law — all precompositions agree implies the
   arrows agree — exactly as Adjunction/SAFT.v:99's [Cogenerator] states
   its dual, and every statement below is in that form.  No weakened
   negative form is proved here, in either direction.

   THE PRIOR ART, AND WHY THIS FILE IS NOT A DUPLICATE.  Issue #447's
   "Current state" paragraph says that a search for
   Generator/Separator/SeparatingFamily/Generates finds exactly one
   [Cogenerator] record and that there is "NO definition of a separating
   set / separator / generating family anywhere".  That is STALE, and the
   correction is recorded here rather than silently worked around.
   Theory/Concrete.v already carries, under Awodey's §1.5 Remark 1.7
   reading of concreteness:

     - [Class Separator (t : C)] at :174, a one-field class whose field
       [separates] is the same cancellation law as [IsSeparator];
     - [Concrete_of_Separator] at :183 and [Separator_of_Faithful] at
       :197 — BOTH directions of the Awodey equivalence with
       faithfulness of [fobj[Curried_Hom C] t] (Functor/Hom.v:60),
       already proved;
     - [WellPointedCategory] at :218, the terminal-object case;
     - [Sets_Separator] at :279, an [#[export] Instance] proving that
       [@terminal_obj Sets Sets_Terminal] separates [Sets], with
       [Sets_point] at :273 as its probe;
     - [Sets_empty_not_Separator] at :299, the empty setoid as a
       non-example, using [empty_setoid_object] at :296.

   So the issue's Awodey checkbox "the terminal object generates Sets"
   was already discharged in the CLASS vocabulary before this file
   existed.  What was missing, and what this file adds, is the same
   content in the vocabulary issue #447 froze — [IsSeparator] and the
   [Generator] record of Structure/Generator.v — the SINGLETON reading
   (a different object from the terminal object, measured below), the
   [Generator] packages, and the transport along the isomorphism between
   the two objects.  The two vocabularies are bridged in both directions
   by Structure/Generator/Concrete.v's [IsSeparator_of_Separator] and
   [Separator_of_IsSeparator], each a one-line repackaging with no proof
   content, so nothing is proved twice: the class and the [Definition]
   are the same law with different binding forms.  (A first draft of
   this file carried its own copy of that bridge pair and its own
   isomorphism-transport lemma, built in parallel with the theory half;
   integration kept the theory half's [separator_iso] and bridges and
   removed the copies.)

   THE SINGLETON AND THE TERMINAL OBJECT ARE TWO STATEMENTS.  This is a
   measurement, not a caution.  Instance/Sets.v:372's
   [unit_setoid_object] is [{| carrier := poly_unit ; is_setoid :=
   unit_setoid |}], a bare record; Instance/Sets.v:258's [Sets_Terminal]
   is a [Program Instance] whose [terminal_obj] field is
   [{| carrier := poly_unit |}] with the setoid field left to an
   obligation term.  The two records therefore do not convert, and with
   the exact requirement list of this file

     Example term_is_unit :
       @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl.

   is rejected as

     "The term "eq_refl" has type "1 = 1" while it is expected to have
      type "1 = unit_setoid_object"
      (cannot unify "1" and "unit_setoid_object")."

   a CONVERSION refusal — the [1] being the terminal-object notation,
   which is what this file's import list puts in scope for the left-hand
   side, so the message is quoted with its environment.  Consequently
   [Sets_unit_separates] and [Sets_terminal_separates] are separate
   theorems, and the second is NOT obtained from the first by an
   [eq_refl] identification.  Three routes to it are recorded, all cheap
   and all here:

     1. DIRECT, and this is the delivered constant: [sets_elem_term]
        builds the constant map out of the terminal object itself, so the
        proof is the same two lines as for the singleton.
     2. TRANSPORT, [Sets_terminal_separates_by_transport]: the two
        objects ARE isomorphic ([Sets_terminal_unit_iso]), and
        Structure/Generator.v's [separator_iso] carries the property
        across.  This route is recorded because the transport lemma is
        the reusable half — it is what makes "is a separator" an
        invariant of the isomorphism class rather than of the record.
     3. FROM THE PRIOR ART, [Sets_terminal_separates_from_Concrete]:
        unpack Theory/Concrete.v:279's [Sets_Separator] through the
        bridge.  This one exists to make the staleness disclosure above
        machine-checked rather than a claim in prose.

   The three inhabit the same type and no claim is made that they are
   equal terms; [IsSeparator] lands in [Type], where proof irrelevance is
   not available, and comparing two of its inhabitants is not a statement
   this file makes.

   WHAT THE EMPTY SETOID SHOWS, AND WHY IT IS A THEOREM.  Separation is a
   genuine condition, and the witness is the initial object:
   Instance/Sets.v:275's [Sets_Initial] has [False] as carrier, so every
   hypothesis of the separator condition holds vacuously for it, and it
   would identify two arrows that differ.  [Sets_empty_not_separates]
   states this as [IsSeparator … → False].  It is stated positively, and
   NOT as a refusal probe of the kind Test/Probe*.v collects, on purpose:
   such a probe records that the ELABORATOR rejects a command, whereas
   this is a mathematical theorem about a perfectly well-typed statement
   that simply has no inhabitant.  The probe idiom cannot express it, and
   the distinction matters because the two kinds of evidence are not
   interchangeable.  Theory/Concrete.v:299's [Sets_empty_not_Separator]
   proves the same thing about ITS [empty_setoid_object] (:296); the
   statement here is about [@terminal_obj (Sets^op) Sets_Initial] — the
   initial object of [Sets] as Structure/Initial.v:97 defines it, by the
   notation [Initial C := @Terminal (C^op)] — so the two are about
   different terms and neither subsumes the other.

   Two arrows that differ are available from two places, and the choice
   costs a universe.  [Sets_empty_not_separates] uses
   Theory/Concrete.v:259's [Sets_two_arrows] (the identity against
   [Sets_negb] at :253, on that file's [bool_setoid_object] at :244), and
   is polymorphic in the object universe.  [Sets_empty_not_separates_pick]
   uses instead Instance/Sets.v:573's [pick_true] against :579's
   [pick_false], the pair issue #447 named; that route is pinned at
   object universe [Set], and the pin is attributed by [About] rather
   than guessed — [About pick_true] reports [pick_true@{u}] with codomain
   [bool_setoid_object@{Set Set}], so Instance/Sets.v minimized that
   constant's object universe to [Set] at its own definition site (its
   carrier is [bool : Set]) and no annotation here can widen it.  Both
   constants are delivered; they are the same theorem at two universe
   strengths.

   UNIVERSES, MEASURED.  Every statement below is annotated, and the
   annotations are load-bearing.  Without them the elaborator minimizes
   the object universe of [Sets] to [Set]: an earlier revision of this
   file, identical but unannotated, gave
   [Sets_unit_separates@{u} : IsSeparator@{u u Set}
   unit_setoid_object@{Set Set}] under [Set Printing Universes], so the
   theorem held only for setoids whose carriers live in [Set].  As
   written it gives [Sets_unit_separates@{o so} : IsSeparator@{so so o}
   unit_setoid_object@{o o}] with [o < so], matching
   Theory/Concrete.v:279's [Sets_Separator@{o so}].

   One collapse is inherited and cannot be annotated away here:
   [About IsSeparator] reports [IsSeparator@{u u0 u1} : forall {C :
   Category@{u0 u1 u1}}, obj -> Type@{u}] — the hom and proof universes
   of the category are IDENTIFIED, where Theory/Category.v's own
   constraint is only [h <= p].  That is not a defect of the frozen
   interface: its model has it too ([About Cogenerator] gives
   [Cogenerator@{u u0 u1} : Category@{u0 u1 u1} -> Type…] at
   Adjunction/SAFT.v:99), and so does the prior art ([About Separator]
   gives [Separator@{u u0} : forall {C : Category@{u u0 u0}}, …] at
   Theory/Concrete.v:174).  Every statement in this file therefore
   carries [p = h].

   NOT DELIVERED HERE.  The joint-faithfulness characterization of the
   family form (Structure/Generator.v's [JointlyFaithful] against
   [Generator]) is the theory half of #447 and is not restated here; the
   single-object case of it is already Theory/Concrete.v:183 and :197 and
   is only cited.  No claim is made that [Sets_Generator] and
   [Sets_terminal_Generator] are equal, isomorphic, or related as
   [Generator] records — only that each is a [Generator Sets].  Nothing
   here is said about generating SETS of more than one object in [Sets],
   nor about the size conditions (local presentability, Giraud's clause
   (vi)) that make separating sets useful; and the [Sets] subobject
   classifier's separating role is not touched. *)

(** ** The singleton separates *)

(* A global element of [X], as a map out of the singleton setoid.  This is
   the same probe Instance/Sets.v:379's [injectivity_is_monic] uses to
   characterize monos as injections, and the same one
   Theory/Concrete.v:273's [Sets_point] uses out of the terminal object.

   It must stay TRANSPARENT, and that is measured: replacing this
   [Program Definition] by a tactic proof closed with [Qed], everything
   else unchanged, makes the next lemma's [exact] refuse with
   "The term "H (sets_elem x) ttt" has type "(f ∘ sets_elem x) ttt ≈
   (g ∘ sets_elem x) ttt" while it is expected to have type "f x ≈ g x"",
   a CONVERSION refusal: the whole proof is the reduction of the constant
   map at the unique inhabitant.  [sets_elem_term] below measures the
   same way, its message naming [1] where this one names
   [unit_setoid_object]. *)
Program Definition sets_elem@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> X := {| morphism := fun _ => x |}.

(* Global elements distinguish setoid maps.  Two maps agreeing after every
   arrow out of the singleton agree at every element, because the element
   [x] is recovered as [sets_elem x] applied to the unique inhabitant of
   the singleton. *)
Lemma Sets_unit_separates@{o so+} :
  @IsSeparator Sets@{o so} unit_setoid_object@{o o}.
Proof.
  intros X Y f g H x.
  exact (H (sets_elem x) ttt).
Qed.

(* Mac Lane's first example, as the one-object generating family. *)
Definition Sets_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so} unit_setoid_object@{o o}
    Sets_unit_separates.

(** ** The terminal object separates *)

(* The same constant map, but out of [Sets_Terminal]'s object rather than
   out of [unit_setoid_object].  It has to be built separately: the two
   objects do not convert, as the header measures. *)
Program Definition sets_elem_term@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  @terminal_obj Sets@{o so} Sets_Terminal@{so o} ~{Sets@{o so}}~> X :=
  {| morphism := fun _ => x |}.

(* Route 1, the delivered constant: the direct proof.  This is issue
   #447's pinned name. *)
Lemma Sets_terminal_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  intros X Y f g H x.
  exact (H (sets_elem_term x) ttt).
Qed.

Definition Sets_terminal_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    Sets_terminal_separates.

(* The isomorphism the transport route needs.  Both components are the
   constant map at [ttt], and both triangle laws hold by case analysis on
   the unique inhabitant.  Kept [Defined] because it is DATA; closing it
   with [Qed] was measured to compile, nothing in this file needing it
   transparent, but opaque data blocks downstream conversion and
   Instance/Sets.v keeps its own coherence isomorphisms [Defined] for the
   same reason. *)
Definition Sets_terminal_unit_iso@{o so+} :
  @Isomorphism Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    unit_setoid_object@{o o}.
Proof.
  unshelve refine {| to := _; from := _ |}.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - intro u; now destruct u.
  - intro u; now destruct u.
Defined.

(* Route 2: transport along that isomorphism, in the direction
   [unit_setoid_object ≅ terminal_obj], through Structure/Generator.v's
   [separator_iso]. *)
Definition Sets_terminal_separates_by_transport@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  separator_iso Sets_unit_separates (iso_sym Sets_terminal_unit_iso).

(* Route 3: the prior art, unpacked through Structure/Generator/
   Concrete.v's bridge.  This constant exists so that the header's claim
   about Theory/Concrete.v:279 is checked by the compiler rather than
   asserted. *)
Definition Sets_terminal_separates_from_Concrete@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  IsSeparator_of_Separator
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) Sets_Separator@{o so}.

(** ** The initial object does not separate *)

(* A theorem, not a refusal: the statement is well typed and has no
   inhabitant.  There is nothing to probe with out of the empty setoid,
   so the hypothesis is vacuous and would identify the identity of the
   two-element setoid with negation. *)
Lemma Sets_empty_not_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj (Sets@{o so}^op) Sets_Initial@{so o}) → False.
Proof.
  intro Hsep.
  apply Sets_two_arrows@{o so}.
  apply Hsep.
  intros k u; destruct u.
Qed.

(* The same theorem by the route issue #447 named, and pinned at object
   universe [Set] by its donors, as the header attributes. *)
Lemma Sets_empty_not_separates_pick@{so+} :
  @IsSeparator Sets@{Set so}
    (@terminal_obj (Sets@{Set so}^op) Sets_Initial@{so Set}) → False.
Proof.
  intro Hsep.
  apply Bool.diff_true_false.
  refine (Hsep unit_setoid_object@{Set Set} _ pick_true pick_false _ ttt).
  intros k u; destruct u.
Qed.
