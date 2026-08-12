Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Section TerminalSubcategory.

Context {C : Category}.

(* Riehl, CTiC, Lemma 1.6.16: the full subcategory spanned by the terminal
   objects of C.  [sobj] selects exactly the terminal objects (Block A's
   predicate is what makes this expressible -- the bundled class cannot
   span a subcategory, since it carries a choice of object), and [shom]
   retains every C-morphism between them, which is fullness.  Closure
   under composition and identity is then vacuous.

   Written with [Build_Subcategory] rather than [Program]: a Program
   record whose obligations are discharged by [Qed] is opaque to the
   unifier, and the [Replete] witness below needs [shom] to reduce. *)
Definition TerminalObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsTerminalObj c)          (* the terminal objects *)
    (fun _ _ _ _ _ => True)             (* full: every C-morphism is kept *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition *)
    (fun _ _ => I).                     (* closed under identities *)

Notation "'TSub'" := (Sub C TerminalObjects).

Definition TerminalObjects_Full :
  Construction.Subcategory.Full C TerminalObjects := fun _ _ _ _ _ => I.

(* Riehl, CTiC, Exercise 1.6.ii(i) in its subcategory form: the span of
   the terminal objects is replete.  The object half is Block A's
   [Terminal_iso], routed through the bundling pair; the morphism halves
   are trivial because the subcategory is full. *)
Definition TerminalObjects_Replete : Replete C TerminalObjects :=
  fun x ox y f =>
    (IsTerminalObj_from_Terminal
       (Terminal_iso (Terminal_from_IsTerminalObj ox) y f); (I, I)).

(* Each hom-set is INHABITED: the target is terminal, so it receives an
   arrow from the source, and fullness lets it into the subcategory. *)
Definition terminal_sub_hom (a b : TSub) : a ~{TSub}~> b :=
  (@is_terminal_one C (`1 b) (`2 b) (`1 a); I).

(* ... and it is a SINGLETON up to ≈, since the subcategory's hom-setoid
   compares underlying C-morphisms and the target is terminal. *)
Lemma terminal_sub_hom_unique (a b : TSub) (f g : a ~{TSub}~> b) : f ≈ g.
Proof. exact (is_terminal_unique (`2 b) (`1 f) (`1 g)). Qed.

(* The two facts packaged as Lemma 1.6.16's "exactly one morphism in each
   hom-set", in the library's own [Unique] idiom. *)
Definition terminal_sub_hom_contractible (a b : TSub) :
  Unique (fun _ : a ~{TSub}~> b => True) :=
  {| unique_obj       := terminal_sub_hom a b
   ; unique_property  := I
   ; uniqueness       := fun v _ =>
       terminal_sub_hom_unique a b (terminal_sub_hom a b) v |}.

(* It is a GROUPOID: the reverse arrow exists for the same reason, and
   both round trips are arrows into terminal objects, hence identities. *)
Definition terminal_sub_IsIso {a b : TSub} (f : a ~{TSub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

Definition terminal_sub_iso (a b : TSub) : @Isomorphism TSub a b.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom a b).
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

(* A bundled [Terminal] structure is an object of the subcategory; this is
   what makes it non-empty, and it is the hypothesis of the contractibility
   statement in Block E. *)
Definition terminal_sub_obj (T : @Terminal C) : TSub :=
  (@terminal_obj C T; IsTerminalObj_from_Terminal T).

End TerminalSubcategory.

Section InitialSubcategory.

Context {C : Category}.

(* The initial dual.  Unlike Block B this is stated directly rather than
   as [TerminalObjects] at C^op, because [Sub (C^op) (op_subcategory S)]
   and [(Sub C S)^op] are different terms, so duality would buy a
   definition and then cost a translation at every use. *)
Definition InitialObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsInitialObj c)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Notation "'ISub'" := (Sub C InitialObjects).

Definition InitialObjects_Full :
  Construction.Subcategory.Full C InitialObjects := fun _ _ _ _ _ => I.

Definition InitialObjects_Replete : Replete C InitialObjects :=
  fun x ox y f =>
    (IsInitialObj_from_Initial
       (Initial_iso (Initial_from_IsInitialObj ox) y f); (I, I)).

Definition initial_sub_hom (a b : ISub) : a ~{ISub}~> b :=
  (@is_initial_zero C (`1 a) (`2 a) (`1 b); I).

Lemma initial_sub_hom_unique (a b : ISub) (f g : a ~{ISub}~> b) : f ≈ g.
Proof. exact (is_initial_unique (`2 a) (`1 f) (`1 g)). Qed.

Definition initial_sub_hom_contractible (a b : ISub) :
  Unique (fun _ : a ~{ISub}~> b => True) :=
  {| unique_obj      := initial_sub_hom a b
   ; unique_property := I
   ; uniqueness      := fun v _ =>
       initial_sub_hom_unique a b (initial_sub_hom a b) v |}.

Definition initial_sub_IsIso {a b : ISub} (f : a ~{ISub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_iso (a b : ISub) : @Isomorphism ISub a b.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom a b).
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_obj (I0 : @Initial C) : ISub :=
  (@initial_obj C I0; IsInitialObj_from_Initial I0).

End InitialSubcategory.
