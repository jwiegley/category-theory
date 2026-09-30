Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Props.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The modal operator B ⇒ − on propositions *)

(* nLab: https://ncatlab.org/nlab/show/modal+operator
   nLab: https://ncatlab.org/nlab/show/closure+operator
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
         SS 1.4.4, Example 1.123, printed pp. 34-35, and footnote 8,
         printed p. 33
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         SS 10.2, Example 10.4, printed p. 270

   WHAT THE BOOK SAYS.  Seven Sketches Example 1.123 orders propositions
   by entailment ("p ≤ q iff p implies q") and says: "A closure operator
   on it is often called a modal operator.  It is a function j from
   propositions to propositions, for which p ⇒ j(p) and j(j(p)) = j(p).
   An example of a j is 'assuming Bob is in San Diego....'  Think of this
   as a proposition B; so 'assuming Bob is in San Diego, p' means B ⇒ p.
   Let's see why B ⇒ − is a closure operator."  The argument that
   follows is informal.  Awodey's Example 10.4 (p. 270) names a different
   modality, "The 'possibility operator' ⋄p in modal logic is another
   example", which is not stated here.

   WHICH READING IS IMPLEMENTED.  The entailment preorder is
   Instance/Props.v's [Props]: objects [Prop], arrows [Basics.impl], and
   the hom-setoid [True], so [Props] is thin.  [modal_functor B] is
   p ↦ (B → p), [modal_ext] is the first axiom, and the second is
   [modal_idem] as mutual entailment (stdlib [<->]; the library's [↔] is
   [iffT]), which is the isomorphism of [Props].  The book's "=" between
   propositions is [modal_idem_ext], under propositional extensionality
   supplied as a hypothesis; no axiom is assumed.  [modal_monad] is the
   monad: its unit is [modal_ext], its multiplication [modal_mult], the
   transparent term f ↦ (b ↦ f b b), of which [modal_idem] is built, so
   that join computes ([modal_monad_join]); its five laws are [I].
   [modal_monad_is_thin]: it IS Structure/Thin/Monad.v's [thin_monad] at
   [Props] with the witness [fun _ _ _ _ => I], on the whole record by
   [eq_refl].  It is not DEFINED through [thin_monad]: that route is
   refused bare, the sort level of Structure/Thin.v's [Thin] being left
   in the body alone; pinned to u or h it adds h <= u or u <= h
   (measured); with + the thin level stays in the block only (the reason
   Instance/Proset/Monad.v gives for [closure_monad]).  Its algebras are
   the j-closed propositions, (B → p) → p ([modal_talgebra_iff]), and at
   B := False the proposition False is not closed
   ([modal_false_not_closed]).

   THE MONAD OF THE CURRYING ADJUNCTION, at its true strength.  [Props]
   is cartesian closed ([Props_Closed]), and
   Structure/Cartesian/Closed/Adjunction.v's [Curry_Adjunction B] is
   (− ∧ B) ⊣ (B ⇒ −).  Its monad [curry_monad B] has the functor
   p ↦ (B → p ∧ B), by [eq_refl] ([curry_monad_fobj]).  That is a
   different term from B ⇒ −: the equation of the two object maps is
   refused by conversion (measured).  It is NOT a different functor in
   the library's sense: the two are ≈ ([curry_modal_iso], a natural
   isomorphism in [Props]), they have the same closed elements
   ([curry_modal_closed_iff]), and under propositional extensionality,
   taken as a hypothesis, the object maps are equal
   ([curry_modal_fobj_ext]).  So no proof that the object maps differ
   can exist unless that axiom, which is consistent with Coq, is
   refuted (for the functors themselves, functional extensionality as
   well).  The
   modality is obtained from [Props_Closed] up to natural isomorphism,
   and not on the nose.

   THE DUAL.  The same adjunction's comonad [curry_comonad B]
   (Comonad/Duality.v's [Adjunction_Comonad]) has the functor
   p ↦ (B → p) ∧ B ([curry_comonad_fobj]), which is B ∧ − up to mutual
   entailment ([curry_comonad_is_and]): the other composite of footnote 8,
   an interior operator.  Its coalgebras are the p with
   p → (B → p) ∧ B ([curry_wcoalgebra_iff]), that is, the propositions
   that entail B ([curry_open_iff_entails]).

   THE ORDER-LEVEL OPERATOR.  [impl_PreOrder] is [Basics.impl] as a
   stdlib [PreOrder] (the tree declares none, and [Search PreOrder
   Basics.impl] finds none in the loaded stdlib), and [modal_closure B]
   is B ⇒ − as an Instance/Proset/Monad.v [ClosureOperator] on it.  Its
   functor agrees with [modal_functor B] on objects by [eq_refl]
   ([modal_closure_fobj]), and [closure_monad (modal_closure B)] has the
   unit and multiplication of [modal_monad B] by [eq_refl].  The two
   categories are not convertible as the tree stands; the refusal at
   [impl_PreOrder] is the opacity of the two files' Program obligations
   alone: with them transparent (verbatim restatements under Set
   Transparent Obligations), Props = Proset impl_PreOrder is eq_refl on
   the whole record; for a variable P it is refused at [id]
   structurally.  In detail: [Props] is its own [Program Definition]
   (Instance/Proset/Limit.v says it is not [Proset P] for any P, which
   holds by conversion as the tree stands); at [impl_PreOrder] the [obj],
   [hom], [id] and [compose] fields agree by [eq_refl] and the refusal is
   at [homset], each category carrying its own proof that [True] is an
   equivalence (Instance/Props.v's [Props_obligation_1] and
   Instance/Proset.v's [Proset_obligation_1]); for a variable
   [P : PreOrder Basics.impl] the [obj] and [hom] fields agree and [id]
   is refused, with the obligations transparent or not, the identity of
   [Proset P] being the reflexivity proof of the variable P.

   STRENGTHS, measured.  [eq_refl]: [modal_monad_is_thin] (whole record),
   [modal_monad_join] (join computes), [modal_talgebra_round] (structure
   map), [curry_monad_fobj],
   [curry_comonad_fobj], [modal_closure_fobj], [modal_closure_ret],
   [modal_closure_join].  ≈: [curry_modal_iso].  Refused by conversion:
   the object equation of the curry and modal functors (so also the
   functor equation), and [Props = Proset P].  No [Qed] enters the first:
   both sides normalise, to B → p ∧ B and to B → p, distinct [Prop]
   terms, so no flip to [Defined] can change it.  The second is an
   opacity refusal at [impl_PreOrder]: flipped, with verbatim
   restatements of the two [Program Definition]s under [Set Transparent
   Obligations], [Props = Proset impl_PreOrder] is [eq_refl] on the whole
   record; for a variable P the same flip leaves it refused at [id],
   structurally.

   UNIVERSES, read off [About] with all instances printed.  No constant
   has a level that occurs in its body only.  [Set < u] is [Props]'s own
   (its objects are [Prop]), first carried by Instance/Props.v's [Props].
   [h < e] in the curry constants is first carried by
   Structure/Cartesian/Closed.v's [Closed] (its [u0 < u1], the level of
   the [Sets] isomorphism of [exp_iso]), which [curry_functor] and
   [curry_cofunctor] take as an argument for that reason: [Exp_Functor]
   and [Prod_Functor] each carry a level absent from their own types, so
   with [Props_Closed] inlined the level e would occur in the body only.
   Those levels, the last level of [Curry_Adjunction]'s [Adjunction] and
   the level u4 of [Adjunction_Comonad], sixth in its binder (free in
   their blocks), are pinned to e or h.  The caps [h <= compose.u0,
   compose.u1, compose.u2, ID.u0, prod_rect.u0, prod_rect.u1,
   prod_rect.u2] are global stdlib
   universes already in the blocks of [Closed] and [Curry_Adjunction].
   [impl_PreOrder] carries the global [Set < Defs.u0] (stdlib's
   [PreOrder] at a relation on [Prop]).  The biconditionals [@{u h +}]
   add the free [iffT] level of their [Prop] side.  This file loads both
   declarations of [Thin] and of [proset_thin] (Structure/Thin.v with
   Instance/Proset/Order.v, and Instance/Proset/Galois.v, through
   Instance/Proset/Monad.v; measured by [Locate]) and names neither: the
   witness is the term [fun _ _ _ _ => I].

   NOT DELIVERED.  No Lawvere-Tierney topology or nucleus (B ⇒ −
   preserves meets, which is not stated); no other modality (Awodey's ⋄);
   no functoriality in B; nothing over a Heyting algebra other than
   [Props]. *)

(** ** The operator and its two axioms *)

(* j p := B → p, an endofunctor of the entailment preorder [Props]; its
   law fields are [I], the hom-setoid of [Props] being [True]. *)
Definition modal_functor@{u h} (B : Prop) : Props@{u h} ⟶ Props@{u h} :=
  @Build_Functor Props@{u h} Props@{u h} (fun p => B → p)
    (fun p q (f : Basics.impl p q) (g : B → p) (b : B) => f (g b))
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

(* Seven Sketches Example 1.123's two axioms: p ⇒ j(p), and
   j(j(p)) = j(p), read as mutual entailment. *)
Definition modal_ext@{} (B p : Prop) : p → (B → p) := fun x _ => x.

(* The multiplication, a transparent term: the assumption used twice. *)
Definition modal_mult@{} (B p : Prop) : (B → (B → p)) → (B → p) :=
  fun f b => f b b.

Definition modal_idem@{} (B p : Prop) : (B → (B → p)) <-> (B → p) :=
  conj (modal_mult B p) (modal_ext B (B → p)).

(* The book's equation itself, under propositional extensionality taken
   as a hypothesis. *)
Lemma modal_idem_ext@{} (propext : ∀ P Q : Prop, (P <-> Q) → P = Q)
  (B p : Prop) : (B → (B → p)) = (B → p).
Proof. exact (propext _ _ (modal_idem B p)). Qed.

(* The monad: unit the first axiom, multiplication the forward half of
   the second, every law [I]. *)
Definition modal_monad@{u h} (B : Prop) :
  @Monad Props@{u h} (modal_functor@{u h} B) :=
  @Build_Monad Props@{u h} (modal_functor@{u h} B)
    (modal_ext B) (modal_mult B)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Its join computes: it is the term f ↦ (b ↦ f b b). *)
Example modal_monad_join@{u h} (B p : Prop) (f : B → (B → p)) (b : B) :
  @join _ _ (modal_monad@{u h} B) p f b = f b b := eq_refl.

(* It IS Structure/Thin/Monad.v's [thin_monad] at [Props] with the
   witness [fun _ _ _ _ => I], on the WHOLE record: that constructor's
   law fields reduce to [I] by beta. *)
Example modal_monad_is_thin@{u h t} (B : Prop) :
  modal_monad@{u h} B
    = @thin_monad@{t u h} Props@{u h} (fun _ _ _ _ => I)
        (modal_functor@{u h} B) (modal_ext B) (modal_mult B) := eq_refl.

(* Its algebras are the j-closed propositions, (B → p) → p. *)
Definition modal_talgebra_iff@{u h +} (B p : Prop) :
  @TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
    ↔ ((B → p) → p) :=
  (fun a => @t_alg Props@{u h} (modal_functor B) (modal_monad B) p a,
   fun h => @Build_TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
              h I I).

Example modal_talgebra_round@{u h p} (B p : Prop) (h : (B → p) → p) :
  match modal_talgebra_iff@{u h p} B p with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* Non-vacuity: at B := False the proposition False is not closed. *)
Lemma modal_false_not_closed@{u h} :
  @TAlgebra Props@{u h} (modal_functor False) (modal_monad False) False
    → False.
Proof.
  intro a. destruct (modal_talgebra_iff False False) as [to_closed _].
  exact (to_closed a (fun x => x)).
Qed.

(** ** The monad of the currying adjunction (− ∧ B) ⊣ (B ⇒ −) *)

(* The two composites of Structure/Cartesian/Closed/Adjunction.v's
   [Prod_Functor B] and [Exp_Functor B] at [Props], for a closed
   structure [CL] (in use, always [Props_Closed]).  Taking [CL] as an
   argument keeps its exponential level e in the type: [Exp_Functor] and
   [Prod_Functor] each carry a level absent from their own types, pinned
   here to e. *)
Definition curry_functor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B)
    (@Prod_Functor@{u h e e} Props@{u h} _ B).

Definition curry_cofunctor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Prod_Functor@{u h e e} Props@{u h} _ B)
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B).

(* The monad of [Curry_Adjunction B].  The adjunction's last level is
   free in its block and is pinned to h. *)
Definition curry_monad@{u h e | h < e +} (B : Prop) :
  @Monad Props@{u h} (curry_functor@{u h e} Props_Closed B) :=
  @Adjunction_Monad@{u h u h e h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

(* Its functor is B ⇒ (− ∧ B), on the nose. *)
Example curry_monad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = (B → p /\ B) := eq_refl.

(* It is not B ⇒ − by conversion (the equation of objects is refused),
   but the two functors are naturally isomorphic. *)
Lemma curry_modal_iso@{u h e + | h < e +} (B : Prop) :
  curry_functor@{u h e} Props_Closed B ≈ modal_functor@{u h} B.
Proof.
  unshelve eexists.
  - intro p. unshelve refine (@Build_Isomorphism Props _ _ _ _ I I).
    + exact (fun f b => proj1 (f b)).
    + exact (fun f b => conj (f b) b).
  - intros; exact I.
Qed.

(* Under propositional extensionality, taken as a hypothesis, the two
   object maps agree, so no proof of their difference can exist unless
   that axiom is refuted. *)
Lemma curry_modal_fobj_ext@{u h e | h < e +}
  (propext : ∀ P Q : Prop, (P <-> Q) → P = Q) (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = fobj[modal_functor@{u h} B] p.
Proof.
  apply propext. split.
  - exact (fun f b => proj1 (f b)).
  - exact (fun f b => conj (f b) b).
Qed.

Definition curry_talgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
    ↔ ((B → p /\ B) → p) :=
  (fun a => @t_alg Props@{u h} _ (curry_monad@{u h e} B) p a,
   fun h => @Build_TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
              h I I).

(* The two monads have the same closed elements. *)
Definition curry_modal_closed_iff@{} (B p : Prop) :
  ((B → p /\ B) → p) <-> ((B → p) → p) :=
  conj (fun h f => h (fun b => conj (f b) b))
       (fun h f => h (fun b => proj1 (f b))).

(** ** The dual: the comonad of the same adjunction, B ∧ − *)

(* [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in neither
   its type nor its block; it is pinned to h, as is the adjunction's last
   level. *)
Definition curry_comonad@{u h e | h < e +} (B : Prop) :
  @Comonad Props@{u h} (curry_cofunctor@{u h e} Props_Closed B) :=
  @Adjunction_Comonad@{u h u h e h h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

Example curry_comonad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_cofunctor@{u h e} Props_Closed B] p = ((B → p) /\ B) := eq_refl.

(* The interior operator it defines is B ∧ −, up to mutual entailment. *)
Definition curry_comonad_is_and@{} (B p : Prop) :
  ((B → p) /\ B) <-> (B /\ p) :=
  conj (fun '(conj f b) => conj b (f b))
       (fun '(conj b x) => conj (fun _ => x) b).

Definition curry_wcoalgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
    ↔ (p → (B → p) /\ B) :=
  (fun c => @w_coalg Props@{u h} _ (curry_comonad@{u h e} B) p c,
   fun h => @Build_WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
              h I I).

(* Its open elements are the propositions that entail B. *)
Definition curry_open_iff_entails@{} (B p : Prop) :
  (p → (B → p) /\ B) <-> (p → B) :=
  conj (fun h x => proj2 (h x)) (fun h x => conj (fun _ => x) (h x)).

(** ** The same operator on the preorder of propositions *)

Definition impl_PreOrder@{} : PreOrder Basics.impl :=
  {| PreOrder_Reflexive := fun _ x => x
   ; PreOrder_Transitive := fun _ _ _ f g x => g (f x) |}.

Definition modal_mono@{u} (B : Prop) :
  @MonotoneFun@{u u} Prop Basics.impl Prop Basics.impl :=
  {| mono_map := fun p => B → p
   ; mono_pres := fun p q (f : Basics.impl p q) =>
       (fun g b => f (g b)) : Basics.impl (B → p) (B → q) |}.

Definition modal_closure@{u} (B : Prop) : ClosureOperator@{u} impl_PreOrder :=
  {| cl_fun  := modal_mono B
   ; cl_ext  := modal_ext B
   ; cl_mult := modal_mult B |}.

(* [Props] is not [Proset impl_PreOrder] by conversion, so the two
   presentations are distinct terms; their functors agree on objects. *)
Example modal_closure_fobj@{u h} (B p : Prop) :
  fobj[closure_functor@{u h} (modal_closure@{u} B)] p
    = fobj[modal_functor@{u h} B] p := eq_refl.

(* And the two monads have the same unit and multiplication. *)
Example modal_closure_ret@{u h} (B p : Prop) :
  @ret _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @ret _ _ (modal_monad@{u h} B) p := eq_refl.

Example modal_closure_join@{u h} (B p : Prop) :
  @join _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @join _ _ (modal_monad@{u h} B) p := eq_refl.
