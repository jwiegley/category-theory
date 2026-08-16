Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The slice over a terminal object is the ambient category *)

(* Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
              2nd ed., §II.6, p. 47, Exercise 2 [maclane:II.6:ex2] — in the
              catalog's paraphrase (doc/plan/books/maclane/inventory/II.json,
              not the book's wording): if t is a terminal object of C, the
              category (C ↓ t) of objects over t is isomorphic to C.  The same
              statement appears already on p. 45 as the worked example
              accompanying the definition of (C ↓ a) [maclane:II.6:def2]:
              since the one-point set is terminal in Set, the category of sets
              over it is isomorphic to Set.
   nLab:      https://ncatlab.org/nlab/show/over+category
   nLab:      https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   The content is one sentence of mathematics.  An object of the slice C/t is
   an object a of C equipped with a structure morphism a ~> t; when t is
   terminal that morphism carries no information, since [one_unique] says any
   two arrows into t agree.  So "an object over t" is just "an object", and a
   commuting triangle over t is just an arrow: the triangle condition
   `g' ∘ f ≈ g` is automatic.  The forgetful functor (a, g) ↦ a and the section
   a ↦ (a, !) implement the correspondence.

   Dually — [Coslice_Initial] in Block B — the coslice under an initial object
   is again the ambient category, `0/C ≅ C`.

   ** Strength: this is an EQUIVALENCE, and the gap is real

   Mac Lane says "isomorphic", meaning an isomorphism of categories.  What is
   delivered here is [≅[Cat]], and in this library that is *equivalence* of
   categories, not isomorphism: Cat's hom-setoid is [Functor_Setoid]
   (Instance/Cat.v), which identifies functors that are naturally isomorphic.
   The weakening is not an artifact of the proof — the on-the-nose statement is
   FALSE here, for a reason worth naming, and the falsity is MACHINE-CHECKED:
   [slice_terminal_not_strict] (Construction/Comma/Special.v) exhibits a
   category — [Blur], one object, two parallel arrows identified by its
   hom-setoid — with a [Terminal] instance for which
   `Slice Blur ttt ≅[StrictCat] Blur` is refutable outright.

   In a set-based development the object *set* of C/t is in bijection with the
   object set of C, because "there is exactly one arrow a ~> t" is a statement
   about elements.  In this library terminality is stated up to `≈`
   ([one_unique] : f ≈ g), which is weaker than `f = g`.  The objects of
   [Slice] are the dependent pairs `∃ a : C, a ~> t`, so two `≈`-equal but
   distinct structure morphisms g and g' give two *distinct* objects (a; g) and
   (a; g') of the slice.  A strict isomorphism of categories would have to
   identify them, and nothing in the [Terminal] class does.  What is true is
   that they are canonically isomorphic *in the slice*, by the identity of C —
   and that is exactly the natural isomorphism supplied below.  So the honest
   reading is: the slice over a terminal object is equivalent to C, with the
   equivalence exhibited by an explicit adjoint-equivalence-shaped pair, not
   isomorphic to it on the nose.

   The two round trips therefore have DIFFERENT strengths, and both are
   recorded:

   - [Slice_Forget ◯ Slice_Section] is the identity functor on C at STRICT
     strength ([Slice_Terminal_strict_section]): its object map is
     definitionally `fun x => x` and its arrow map definitionally `fun f => f`,
     so the [Functor_StrictEq_Setoid] witness is `fun _ => eq_refl` and the
     coherence clause is `f ≈ f`.  [Slice_Section] is thus a strict section of
     [Slice_Forget], not merely a section up to isomorphism.

   - [Slice_Section ◯ Slice_Forget] is the identity on the slice only up to
     natural isomorphism, by the argument above.  Its components are carried by
     `id` in C ([slice_terminal_unit_carrier]), so the isomorphism is as
     canonical as it can be; it is not, and cannot be, an equality.

   ** Relation to the neighbouring files

   Construction/Slice.v proves the slice IS a comma category,
   `C/c ≅[Cat] (Id ↓ =(c))` ([Comma_Slice]), so this file's statement transports
   to the comma reading at the same strength.  Construction/Comma/Special.v
   handles the other end of Mac Lane's list of specializations, the comma of two
   constant functors. *)

(** ** Block A: the slice over a terminal object *)

Section SliceTerminal.

Context {C : Category}.
Context {T : @Terminal C}.

(* The forgetful functor C/1 ⟶ C: drop the structure morphism.  This is the
   comma projection [comma_proj1] read through [Comma_Slice]; it is spelled out
   directly here so that both its object and arrow maps are the literal first
   projections and hence compute. *)
Program Definition Slice_Forget :
  @Slice C (@terminal_obj C T) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(* The section C ⟶ C/1: equip an object with its unique arrow into 1.  The
   triangle condition for an arrow f is `one ∘ f ≈ one`, discharged by
   [one_unique] (equivalently, it is the corollary [one_comp]) — the only place
   terminality is used in this direction. *)
Program Definition Slice_Section :
  C ⟶ @Slice C (@terminal_obj C T) := {|
  fobj := fun x => (x; one);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply one_unique. Qed.

(* Every slice object is canonically isomorphic to its "renormalised" form
   (a; !).  The carrier of the isomorphism is the identity of C in both
   directions; only the triangle proofs differ, and [one_unique] supplies both.
   This is the natural-isomorphism component of the round trip below, isolated
   so that the strength claim in the header can be read off. *)
Program Definition slice_terminal_unit (x : @Slice C (@terminal_obj C T)) :
  Slice_Section (Slice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(* The component is carried by the identity of C, in both directions. *)
Corollary slice_terminal_unit_carrier
  (x : @Slice C (@terminal_obj C T)) :
  (`1 (to (slice_terminal_unit x)) ≈ id) ∧
  (`1 (from (slice_terminal_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(* Mac Lane, §II.6, Exercise 2 [maclane:II.6:ex2].  Note the strength: `≅[Cat]`
   is EQUIVALENCE of categories in this library (Instance/Cat.v), and the header
   explains why the on-the-nose isomorphism Mac Lane states is unavailable
   here. *)
Program Definition Slice_Terminal :
  @Slice C (@terminal_obj C T) ≅[Cat] C := {|
  to   := Slice_Forget;
  from := Slice_Section
|}.
(* The C-side clause `Slice_Forget ◯ Slice_Section ≈ Id[C]` is discharged by the
   library's default obligation tactic — that composite is the identity on
   objects definitionally, so [iso_id] components suffice; the explicit and
   sharper statement is [Slice_Terminal_strict_section] below.  The clause left
   over is the slice-side one. *)
Next Obligation.
  (* Slice_Section ◯ Slice_Forget ≈ Id[C/1]: the components are the
     renormalisation isomorphisms above; naturality is `id ∘ f ∘ id ≈ f` on the
     underlying C-morphisms, the slice hom-setoid comparing nothing else. *)
  exists slice_terminal_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

(* The C-side round trip at strict strength: [Slice_Section] is a STRICT
   section of [Slice_Forget].  Both maps of the composite are definitionally
   the identity's, so the [Functor_StrictEq_Setoid] object witness is
   `fun _ => eq_refl` and the arrow coherence is `f ≈ f`.  This is strictly
   stronger than the [Cat]-level clause of [Slice_Terminal] and is the precise
   sense in which one half of Mac Lane's isomorphism does survive. *)
Lemma Slice_Terminal_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Slice_Forget ◯ Slice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End SliceTerminal.

(** ** Block B: the coslice under an initial object *)

(* Why this is proved directly rather than transported from Block A.

   `Initial C` is literally `Terminal (C^op)` (Structure/Initial.v), so the
   dual statement OUGHT to be Block A read in the opposite category.  It is
   not, and the obstruction is presentational rather than mathematical.
   Unfolding, the opposite of the slice over C^op has homs

     ∃ f : `1 x ~> `1 y,  f ∘ `2 x ≈ `2 y

   whereas Construction/Slice.v's [Coslice] record has homs

     ∃ f : `1 x ~> `1 y,  `2 y ≈ f ∘ `2 x

   — the same equation written in the other orientation.  Those are distinct
   types, so `Coslice C c` is NOT definitionally `(Slice (C^op) c)^op` and the
   transport would have to be mediated by an explicit comparison isomorphism
   built out of [symmetry] in the hom-setoid, plus the action of the duality
   functor [Op : Cat ⟶ Cat] (Instance/Cat/Opposite.v) on isomorphisms.  That is
   strictly more work, and a heavier dependency, than restating the four short
   definitions with [zero_unique] in place of [one_unique] — which is what
   follows.  Nothing below re-proves any mathematics that Block A proved; the
   two arguments are each two appeals to the uniqueness law. *)

Section CosliceInitial.

Context {C : Category}.
Context {I : @Initial C}.

(* Drop the structure morphism out of 0. *)
Program Definition Coslice_Forget :
  @Coslice C (@initial_obj C I) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(* Equip an object with its unique arrow out of 0; the triangle condition
   `zero ≈ f ∘ zero` is discharged by [zero_unique] (equivalently, the
   corollary [zero_comp]). *)
Program Definition Coslice_Section :
  C ⟶ @Coslice C (@initial_obj C I) := {|
  fobj := fun x => (x; zero);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply zero_unique. Qed.

Program Definition coslice_initial_unit (x : @Coslice C (@initial_obj C I)) :
  Coslice_Section (Coslice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply zero_unique. Qed.
Next Obligation. apply zero_unique. Qed.

Corollary coslice_initial_unit_carrier
  (x : @Coslice C (@initial_obj C I)) :
  (`1 (to (coslice_initial_unit x)) ≈ id) ∧
  (`1 (from (coslice_initial_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(* The dual of [Slice_Terminal], at the same strength and for the same
   reason. *)
Program Definition Coslice_Initial :
  @Coslice C (@initial_obj C I) ≅[Cat] C := {|
  to   := Coslice_Forget;
  from := Coslice_Section
|}.
(* As in Block A the C-side clause is discharged by the default obligation
   tactic — the composite is the identity on objects definitionally — and the
   explicit, sharper form is [Coslice_Initial_strict_section] below. *)
Next Obligation.
  exists coslice_initial_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

Lemma Coslice_Initial_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Coslice_Forget ◯ Coslice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End CosliceInitial.
