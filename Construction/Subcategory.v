Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Subcategory.

Context (C : Category).

(** A subcategory D of a category C. *)

(* nLab: https://ncatlab.org/nlab/show/subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Subcategory

   A subcategory D of C is given by a subcollection [sobj] of the objects of C
   together with, for each pair of selected objects, a subcollection [shom] of
   the C-morphisms between them, closed under identity ([sid]) and composition
   ([scomp]). The source/target closure condition (if f : x ~> y is in D then
   so are x and y) holds here by construction: [shom] is only indexed by
   objects ox, oy already selected from [sobj].

   These conditions make D a category in its own right ([Sub] below) for which
   the inclusion D ⟶ C ([Incl]) is a functor; that inclusion is always
   faithful, since on each hom-set it is the first projection out of a sigma
   type — proved as [Incl_Faithful] below. A subcategory is full when [shom]
   retains every C-morphism between selected objects ([Full]), and wide (lluf)
   when [sobj] selects every object of C ([Wide]). *)

Record Subcategory := {
  sobj : C → Type;                  (* sub-collection of the objects of C *)

  (* sub-collection of the C-morphisms between selected objects *)
  shom {x y : C} : sobj x → sobj y → (x ~> y) → Type;

  (* closed under composition: if f : y ~> z and g : x ~> y are in D, then so
     is the composite f ∘ g : x ~> z *)
  scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
        {f : y ~> z} {g : x ~> y} :
    shom oy oz f → shom ox oy g → shom ox oz (f ∘ g);

  (* closed under identity: if x is in D then so is the identity 1ₓ *)
  sid {x : C} (ox : sobj x) : shom ox ox (@id C x)
}.

Variable S : Subcategory.

(* These conditions ensure that D is a category in its own right... *)
Program Definition Sub : Category := {|
  obj     := { x : C & sobj S x };
  hom     := fun x y => { f : `1 x ~> `1 y & shom S `2 x `2 y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; sid S `2 x);
  compose := fun x y z f g  => (`1 f ∘ `1 g; scomp S `2 x `2 y `2 z `2 f `2 g)
|}.

(* ... and the inclusion D ⟶ C is a functor. *)
Program Instance Incl : Sub ⟶ C := {
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
}.

(* The inclusion is faithful, for every [S] whatsoever.

   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5, Remark 1.5.8,
         printed p. 33

   This lemma is as shallow as it looks, and it is worth saying so plainly
   rather than dressing it up: [Sub]'s hom-setoid is DEFINITIONALLY `≈` of
   first projections (`equiv := fun f g => `1 f ≈ `1 g` in [Sub] above), and
   [Incl]'s action on morphisms is that same first projection, so the
   hypothesis and the conclusion are literally the same statement and the
   proof is [exact]. Nothing about [S] is used — neither closure field, nor
   even that [shom] is inhabited. What the lemma buys is that the argument is
   now made once, generically, instead of per subcategory: it is exactly the
   proof re-derived for one particular subcategory at
   Theory/Sheaf/Category.v:103.

   The substance of a faithfulness claim sits in the hom-setoid being injected
   out of, not in the injection; see Construction/Subcategory/Finite.v for an
   instance of [Sub] carrying two parallel morphisms shown distinct. *)

Lemma Incl_Faithful : Functor.Faithful Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(* Additionally, we say that D is...

   A full subcategory if for any x and y in D, every morphism f : x → y in C
   is also in D... *)

Definition Full : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y), shom S ox oy f.

(* ... (that is, the inclusion functor D ⟶ C is full) *)

Lemma Full_Implies_Full_Functor : Full → Functor.Full Incl.
Proof.
  unfold Full; intros.
  construct.
  - exists g.
    destruct x, y.
    apply X; auto.
  - reflexivity.
Qed.

(* ... and back again.

   Reading the previous lemma in reverse runs into the setoid discipline.
   [Functor.Full Incl] returns, for a C-morphism f between selected objects, a
   morphism OF THE SUBCATEGORY, and [fmap_sur] compares it to f in the
   hom-setoid: what comes back is some g with g ≈ f carrying a [shom] witness,
   not a witness for f itself. That up-to-≈ statement is what fullness of the
   inclusion yields on its own, and it is recorded first. *)

Lemma Full_Functor_Implies_Full_upto (HF : Functor.Full Incl) :
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y),
    { g : x ~> y & (g ≈ f) ∧ shom S ox oy g }.
Proof.
  intros x y ox oy f.
  pose (p := @prefmap _ _ Incl HF (x; ox) (y; oy) f).
  exists (`1 p).
  split.
  - exact (@fmap_sur _ _ Incl HF (x; ox) (y; oy) f).
  - exact (`2 p).
Qed.

(* To close the gap and land on [Full] as stated, one needs [shom] to be
   closed under the hom-setoid equivalence. The [Subcategory] record above has
   no such field — its two closure conditions are for composition and
   identities — so the property is named here and taken as a hypothesis rather
   than derived. It holds trivially for the usual case of a full subcategory
   cut out by a predicate on objects alone, where [shom] ignores its morphism
   argument: Theory/Sheaf/Category.v:77 and Construction/Subcategory/Finite.v
   are both of that shape, and the latter discharges it. *)

Definition ShomRespects : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f g : x ~> y),
    f ≈ g → shom S ox oy f → shom S ox oy g.

(* The converse of [Full_Implies_Full_Functor] under that hypothesis, which
   with it completes the "full subcategory iff full inclusion" biconditional.
   Only the hypothesis's transport along ≈ is used; the two directions are
   otherwise independent.

   The hypothesis is NECESSARY, not merely convenient:
   Construction/Subcategory/FullConverse.v exhibits a subcategory whose
   inclusion is full as a functor while the subcategory is not full as data,
   over a hom-setoid with two classes, refuting the unhypothesised converse
   outright. *)

Lemma Full_Functor_Implies_Full : ShomRespects → Functor.Full Incl → Full.
Proof.
  intros HR HF x y ox oy f.
  destruct (Full_Functor_Implies_Full_upto HF x y ox oy f) as [g [Hgf Hg]].
  exact (HR _ _ _ _ _ _ Hgf Hg).
Qed.

(* A replete subcategory if for any x in D and any isomorphism f : x ≅ y in C,
   both y and f are also in D. *)

Definition Replete : Type :=
  ∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
    { oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.

(* A wide subcategory if every object of C is also an object of D. *)

Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.

#[export] Existing Instance Incl_Faithful.
