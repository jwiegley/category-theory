Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The category of setoids *)

(* nLab: https://ncatlab.org/nlab/show/category+of+sets
   nLab: https://ncatlab.org/nlab/show/setoid
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets
   Wikipedia: https://en.wikipedia.org/wiki/Setoid

   This is the category [Sets], the constructive analogue of the classical
   category Set. To model "sets" without quotient types and without the
   function-extensionality axiom, objects are not bare types but setoids
   (Bishop sets): a carrier type together with an equivalence relation `≈`.
   Morphisms are setoid maps, i.e. functions that respect `≈` (proper
   functions), and the hom-setoid identifies two such maps when they agree
   pointwise up to the codomain's `≈` (extensional equality of setoid maps,
   realised without [funext]).

      objects: setoids        (carrier type + equivalence relation `≈`)
       arrows: setoid maps    (functions f with x ≈ y → f x ≈ f y)
     hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (pointwise, up to codomain `≈`)
     identity: the identity function
   composition: composition of functions, again respecting `≈`

   This file builds the category and its first structural instances:
   [Sets_Terminal] (singleton), [Sets_Initial] (empty), the cartesian
   [Sets_Product_Monoidal], and the characterizations of monos as injections
   and epis as surjections. The cartesian / closed structure proper lives in
   the companion files Instance/Sets/Cartesian.v and
   Instance/Sets/Cartesian/Closed.v. *)

(* Bishop sets, the zero-axiom regime, and the universal codomain

   nLab:   https://ncatlab.org/nlab/show/Bishop+set
   nLab:   https://ncatlab.org/nlab/show/E-category
   nLab:   https://ncatlab.org/nlab/show/predicative+topos
   Book:   Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967
   Thesis: Hofmann, "Extensional Concepts in Intensional Type Theory",
           University of Edinburgh, LFCS report ECS-LFCS-95-327, 1995

   The two records below transcribe definitions Bishop set down in 1967.
   A set, for Bishop, is not an entity with an ideal existence: to define
   one is to prescribe what must be done to construct an element and what
   must be done to show two elements equal (Bishop 1967, chapter one, "A
   constructivist manifesto"); a function is a finite routine on elements
   that respects the two equalities.  [SetoidObject] and [SetoidMorphism]
   are those definitions as records — carrier plus equivalence, program
   plus congruence certificate.  The name "setoid" entered type theory
   with Hofmann's 1995 thesis (per the nLab), which also supplies the
   strategy's mathematical warrant: Hofmann built models of intensional
   type theory out of types with equivalence relations, models in which
   functional extensionality and quotients hold, so working with setoids
   is not a stopgap but a model construction.  The design space — total
   versus partial setoids, four notions of setoid map — is surveyed in
   (Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003);
   this file sits in the total-setoid column with a Type-valued relation.

   Two problems meet here.  First, Coq's intensional equality identifies
   only terms with the same definition: quotient types are absent, and
   pointwise-equal functions need not be provably equal.  Bishop's move
   is to never separate a carrier from its equality — a quotient is just
   another choice of `≈` on the same carrier (Construction/Quotient.v is
   the hom-level version) — and [SetoidMorphism_equiv] makes equality of
   maps extensional by definition rather than by axiom.  This is the
   decision Theory/Category.v credits with the library's zero-axiom
   regime.  Second, category theory needs a Set to land in.  The debt to
   Theory/Category.v runs both ways: a [Category] there is what the nLab
   calls an E-category — enriched in setoids, terminology in active use
   in Palmgren's school (Palmgren, Wilander, "Constructing categories
   and setoids of setoids in type theory", LMCS 10(3) 2014) — so its
   hom-functor can only land in a category whose objects are setoids.
   [Sets] is that category: the codomain of Functor/Hom.v and the Yoneda
   embedding (Functor/Hom/Yoneda.v), of presheaves, of the ends and
   coends of Instance/Sets/End.v and Instance/Sets/Coend.v, and of the
   weights of Structure/Limit/Weighted.v.  Instance/Coq.v is the
   contrast object: bare types under pointwise Leibniz equality, with no
   chosen `≈`.

   The cost has a name.  Altenkirch calls it setoid hell (Altenkirch,
   "From setoid hell to homotopy heaven? The role of extensionality in
   Type Theory", TYPES 2017): every type-level construction must be
   lifted to setoids by hand, the lifting is boilerplate, and the
   implementation is never actually hidden.  The Type-valued [Proper]
   machinery assembled in Lib/Foundation.v exists to make that
   discipline bearable; and the same talk concedes the other side of the
   ledger — most constructions need no higher dimensions, and setoids
   or groupoids suffice.  The successor programme is (Altenkirch,
   Boulier, Kaposi, Tabareau, "Setoid Type Theory — A Syntactic
   Translation", MPC 2019).

   How much of the classical Set survives?  In Martin-Löf type theory
   the category of setoids is a ΠW-pretopos, a locally cartesian closed
   pretopos with W-types and a predicative analogue of a topos (van den
   Berg, "Predicative toposes", arXiv:1207.0959 (2012), after Moerdijk
   and Palmgren 1999/2000).  Predicativity is visible in the subobject
   classifier: its characteristic maps must receive a [Type]-valued
   truth value, so the classifier for [Sets] lives one universe up and
   Instance/Sets/Classifier.v states it as cross-universe theorems
   rather than as an instance — a theorem-shaped fact about size, not a
   gap in the formalization.  That obstruction is genuinely about the
   classifier and does not spread: [surjectivity_is_epic] at the end of
   this file was long believed to inherit it, but the classical
   truth-value probe is not the only one available, and the cokernel
   pair used below stays at the universe of the carriers.  Because `≈`
   is Type-valued,
   its proofs carry data: [bijective_is_iso] turns a surjectivity
   witness into an honest inverse function with no appeal to choice,
   the choice having been data all along.  The remaining working
   completeness of [Sets] is built piecewise under Instance/Sets/ —
   products and exponentials, pushouts, and Cauchy completeness through
   the splitting of idempotents in Instance/Sets/Karoubi.v. *)

Record SetoidObject@{o p} : Type@{max(o+1,p+1)} := {
  carrier :> Type@{o};               (* the underlying type (Bishop carrier) *)
  is_setoid :> Setoid@{o p} carrier   (* its equivalence relation `≈` *)
}.
#[export] Existing Instance is_setoid.

(* A setoid map: a function on carriers together with a proof that it respects
   the two equivalences. This is the morphism part of [Sets]. *)
Record SetoidMorphism@{o h p} `{Setoid@{o p} x} `{Setoid@{o p} y} := {
  morphism :> x → y;                  (* the underlying function on carriers *)
  proper_morphism :>                  (* it sends `≈`-related inputs to `≈`-related outputs *)
    Proper@{h p} (respectful@{h p h p h p} equiv equiv) morphism
}.
#[export] Existing Instance proper_morphism.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.

(* Extensional equality of setoid maps: two maps are equivalent when they
   agree pointwise, judged up to the codomain's `≈`. This is the hom-setoid's
   underlying relation; [funext] is not needed because we compare up to `≈`. *)
Definition SetoidMorphism_equiv@{o h p} {x y : SetoidObject@{o p}} :
  crelation@{h p} (SetoidMorphism@{o h p} x y) :=
  fun f g => ∀ x, @equiv@{o p} _ y (f x) (g x).

Arguments SetoidMorphism_equiv {x y} _ _ /.

#[export]
Program Instance SetoidMorphism_Setoid@{o h p} {x y : SetoidObject@{o p}} :
  Setoid@{h p} (SetoidMorphism@{o h p} x y) := {|
  equiv := SetoidMorphism_equiv@{o h p};
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y0 x1).
    + apply X.
    + apply X0.
Qed.

Definition setoid_morphism_id@{o h p} {x : SetoidObject@{o p}} :
  SetoidMorphism@{o h p} x x := {|
  morphism := Datatypes.id
|}.

#[export] Hint Unfold setoid_morphism_id : core.

Program Definition setoid_morphism_compose@{o h p} {x y z : SetoidObject@{o p}}
        (g : SetoidMorphism@{o h p} y z)
        (f : SetoidMorphism@{o h p} x y) : SetoidMorphism@{o h p} x z := {|
  morphism := Basics.compose g f
|}.

#[export] Hint Unfold setoid_morphism_compose : core.

Program Definition setoid_morphism_compose_respects@{o h p}
  {x y z : SetoidObject@{o p}} :
  Proper@{h p} (equiv@{h p} ==> equiv@{h p} ==> equiv@{h p})
    (@setoid_morphism_compose x y z).
Proof.
  unfold Proper, respectful.
  simpl; intros.
  rewrite X.
  apply proper_morphism, X0.
Qed.

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Definition Sets@{o so} : Category@{so o o} := {|
  obj     := SetoidObject@{o o} : Type@{so};
  hom     := λ x y, SetoidMorphism@{o o o} x y : Type@{o};
  homset  := @SetoidMorphism_Setoid@{o o o};
  id      := @setoid_morphism_id@{o o o};
  compose := @setoid_morphism_compose@{o o o};

  compose_respects := @setoid_morphism_compose_respects@{o o o}
|}.

Require Import Category.Theory.Isomorphism.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "x ≊ y" := ({| carrier := x |} ≅[Sets] {| carrier := y |})
  (at level 99) : category_scope.

#[export]
Program Instance isomorphism_to_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (to iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct to; simpl in *.
  rewrite X; reflexivity.
Qed.

#[export]
Program Instance isomorphism_from_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (from iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct from; simpl in *.
  rewrite X; reflexivity.
Qed.

(* Build a [SetoidMorphism] by giving its underlying function and leaving the
   [proper_morphism] obligation as a fresh goal. *)
Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

(* The singleton setoid: [poly_unit] under `=`, used as the terminal object. *)
#[export]
Program Instance Unit_Setoid@{u} : Setoid@{u u} poly_unit@{u} := {
  equiv := fun x y => x = y
}.

(* Terminal object: the singleton. There is exactly one map into it (every
   element maps to [ttt]), unique up to `≈`. *)
#[export]
Program Instance Sets_Terminal : @Terminal Sets := {
  terminal_obj := {| carrier := poly_unit |};
  one := fun _ => {| morphism := fun _ => ttt |};
  one_unique := fun x f g => _
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Require Import Category.Structure.Initial.

(* The empty setoid: [False] as carrier; equivalence is vacuous. *)
#[export]
Program Instance False_Setoid@{u} : Setoid@{u u} False.
Next Obligation. proper. Qed.

(* Initial object: the empty setoid. The unique map out of it is the empty
   function (by [False] elimination). *)
#[export]
Program Instance Sets_Initial : @Initial Sets := {
  terminal_obj := {| carrier := False |};
  one := _
}.
Next Obligation.
  construct.
  - contradiction.
  - proper.
Qed.
Next Obligation. contradiction. Qed.

Require Import Category.Structure.Monoidal.

(* Cartesian monoidal structure on [Sets]: the tensor is the product of
   setoids (carrier = product of carriers, `≈` componentwise) and the unit is
   the singleton setoid. The unitor/associator obligations below supply the
   coherence isomorphisms. *)
#[export]
Program Instance Sets_Product_Monoidal : @Monoidal Sets := {
  I      := {| carrier := poly_unit |};
  tensor := {|
    fobj := fun p =>
      {| carrier := carrier (fst p) * carrier (snd p)
       ; is_setoid := _
       |};
    fmap := fun x y f =>
      {| morphism := fun p => (fst f (fst p), snd f (snd p))
       ; proper_morphism := _ |}
  |}
}.
Next Obligation.
  construct.
  - repeat intro.
    destruct s, s0.
    try rename X into H.
    try rename X0 into H0.
    exact (fst H ≈ fst H0 ∧ snd H ≈ snd H0).
  - simpl.
    equivalence.
Defined.
Next Obligation.
  proper; simpl in *.
  - destruct s.
    now rewrites.
  - destruct s0.
    now rewrites.
Qed.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ exact ttt | assumption ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ assumption | exact ttt ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + simplify; auto.
    + proper.
  - construct.
    + simplify; auto.
    + proper.
  - simpl.
    simplify; simpl; cat.
  - simpl.
    simplify; simpl; cat.
Defined.

(* The singleton as a [SetoidObject], packaging [unit_setoid] for use as a
   probe object below (a map out of it picks an element up to `≈`). *)
Definition unit_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := poly_unit@{t}
   ; is_setoid := unit_setoid@{t u} |}.

(* In [Sets] the monomorphisms are exactly the injections (up to `≈`). The
   non-trivial direction probes [f] with two constant maps out of the singleton
   [unit_setoid_object]. *)
Lemma injectivity_is_monic {X Y : SetoidObject} (f : X ~{Sets}~> Y) :
  (∀ x y : X, f x ≈ f y → x ≈ y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    given (const_x : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply x.
      - proper.
    }
    given (const_y : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply y.
      - proper.
    }
    destruct HA.
    specialize (monic unit_setoid_object const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    simpl in *.
    eapply monic; eauto.
    constructor.
Qed.

(* In [Sets] a bijection (injective and split-surjective up to `≈`) is an
   isomorphism: the chosen preimage assembles a two-sided inverse. *)
Lemma bijective_is_iso {A B : SetoidObject} (h : A ~{Sets}~> B) :
  injective h -> surjective h -> IsIsomorphism h.
Proof.
  intros [i] [lift] ; unshelve econstructor.
  - exists (fun b => `1 (lift b)).
    abstract(intros a b eq; simpl;
    apply i; now rewrite `2 (lift a), `2 (lift b)).
  - abstract(intro x; now rewrite `2 (lift x)).
  - abstract(intro x; apply i; now rewrite `2 (lift (h x))).
Defined.


(* In Set the epimorphisms are exactly the surjections (see the Wikipedia and
   nLab pages cited in the file header).  This file used to state the
   biconditional and abandon the proof, so NEITHER direction entered the
   environment -- not even the forward one, whose script was complete but
   stranded inside the abandoned block.  Both directions are proved below, at
   the universe of A and B.

   The abandoned attempt (and the header note that went with it) reached for
   the classical probe: distinguish a point outside the image using the
   characteristic map of the image against a constant map into a truth-value
   object.  THAT probe genuinely does not fit here -- its object has carrier
   [Type] with `≈` taken to be `↔`, and no such object is an [obj[Sets]] at the
   universe of A and B, since Set's subobject classifier lives one level up
   (Instance/Sets/Classifier.v).

   But epis-are-surjections does not inherit that obstruction, because the
   truth-value object is not the only available probe.  The COKERNEL PAIR of h
   with itself does the same work and stays at the universe of B: take two
   copies of B glued exactly along the image of h, i.e. `carrier B + carrier B`
   under [ckrel] below.  The predicate [Im b := ∃ a, h a ≈ b] is
   [Type]-valued at the SAME level as the carriers -- `carrier A` is there
   already, and `equiv` on a [SetoidObject@{p p}] is a [crelation] at that
   level -- so nothing ever needs [Type@{p} : Type@{p}].  The two inclusions
   agree after h (each `h a` is in the image, witnessed by `a`), so right
   cancellation identifies them on all of B, and the [Im] component of the
   resulting equivalence at b IS the preimage.

   The argument is constructive: `∃` is [sigT] here (Lib/Foundation.v), so the
   preimage is genuinely extracted rather than merely asserted, and no choice
   principle is used. *)

Section CokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(* Membership in the image of f, at the level of the carriers. *)
Definition Im (b : carrier B) : Type@{p} := ∃ a : carrier A, f a ≈ b.

Lemma Im_resp (x y : carrier B) : x ≈ y → Im x → Im y.
Proof. intros E [a Ha]; exists a; transitivity x; assumption. Qed.

(* Two copies of B, identified across the copies exactly on the image. *)
Definition ckrel (u v : (carrier B + carrier B)%type) : Type@{p} :=
  match u, v with
  | inl x, inl y => x ≈ y
  | inr x, inr y => x ≈ y
  | inl x, inr y => prod (x ≈ y) (Im x)
  | inr x, inl y => prod (x ≈ y) (Im x)
  end.

Lemma ckrel_equiv : Equivalence ckrel.
Proof.
  constructor.
  - intro u; destruct u; simpl; reflexivity.
  - intros u v; destruct u, v; simpl; intro H;
      try (symmetry; assumption);
      destruct H as [E I]; split;
      [ symmetry; assumption | eapply Im_resp; eassumption
      | symmetry; assumption | eapply Im_resp; eassumption ].
  - intros u v w; destruct u, v, w; simpl; intros H1 H2;
      repeat match goal with [ X : prod _ _ |- _ ] => destruct X end;
      try (etransitivity; eassumption);
      split; try (etransitivity; eassumption); try assumption;
      try (eapply Im_resp; [ symmetry; eassumption | assumption ]).
Qed.

Definition CKSetoid : SetoidObject@{p p} :=
  {| carrier := (carrier B + carrier B)%type;
     is_setoid := {| equiv := ckrel; setoid_equiv := ckrel_equiv |} |}.

Definition ck_left : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inl b |}; repeat intro; simpl; assumption.
Defined.

Definition ck_right : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inr b |}; repeat intro; simpl; assumption.
Defined.

(* The two inclusions agree after f: every f a lies in the image, by a. *)
Lemma ck_agree : ck_left ∘[Sets@{p h}] f ≈ ck_right ∘[Sets@{p h}] f.
Proof.
  intro a; simpl; split; [ reflexivity | exists a; reflexivity ].
Qed.

End CokernelPair.

(* Mac Lane, CWM 2nd ed., §I.5, printed p. 19: in Set the epis are exactly the
   surjections.  Both directions, at one universe. *)
Lemma surjectivity_is_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) :
  (∀ b, ∃ a, h a ≈ b)%type ↔ Epic@{h p} h.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros E b.
    exact (snd (@epic _ _ _ _ E (CKSetoid h)
                  (ck_left h) (ck_right h) (ck_agree h) b)).
Defined.

(* The two halves under their own names, for callers that want just one. *)
Definition surjective_implies_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : (∀ b, ∃ a, h a ≈ b)%type → Epic@{h p} h :=
  fst (surjectivity_is_epic@{h p} h).

Definition epic_implies_surjective@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : Epic@{h p} h → (∀ b, ∃ a, h a ≈ b)%type :=
  snd (surjectivity_is_epic@{h p} h).

(* Sets is balanced: a map that is both monic and epic is an isomorphism.
   Monicity gives injectivity ([injectivity_is_monic]), epicness gives the
   preimages, and [bijective_is_iso] assembles a two-sided inverse -- with no
   appeal to choice, the preimages having been data all along. *)
Definition Sets_balanced@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets@{p h}}~> B)
  (Hm : @Monic Sets@{p h} A B h) (He : @Epic@{h p} Sets@{p h} A B h) :
  @IsIsomorphism Sets@{p h} A B h :=
  bijective_is_iso h
    {| inj := λ x y, snd (injectivity_is_monic h) Hm x y |}
    {| surj := λ b, epic_implies_surjective@{h p} h He b |}.

(* ------------------------------------------------------------------------ *)
(** ** The cancellation lemmas do not cancel the other factor *)

(* Mac Lane, CWM 2nd ed., §I.5 Exercise 1 asks about BOTH factors, and
   Awodey §2.9 Exercise 2(d) asks for the counterexample outright.
   [monic_cancel] and [epic_cancel] (Theory/Morphisms.v) each cancel one
   factor; nothing follows about the other, and a single pair of setoid maps
   refutes both converses at once.

   Take the two-element setoid [bool_setoid_object], the map [pick_true] out
   of the singleton, and the map [collapse] back onto it.  Their composite is
   the identity of the singleton, hence monic and epic; but [collapse] is not
   monic (it identifies the two booleans) and [pick_true] is not epic (it
   misses [false]). *)

Definition bool_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := eq ; setoid_equiv := eq_equivalence |} |}.

Program Definition pick_true : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => true |}.

Program Definition collapse : bool_setoid_object ~{Sets}~> unit_setoid_object :=
  {| morphism := fun _ => ttt |}.

Program Definition pick_false : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => false |}.

(* The composite is the identity on the singleton, up to `≈`. *)
Lemma collapse_pick : collapse ∘[Sets] pick_true ≈ id{Sets}.
Proof. intro u; now destruct u. Qed.

(* Hence it is both monic and epic: everything into or out of the singleton is
   forced, the singleton being terminal. *)
Lemma collapse_pick_monic : Monic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 _ u; now destruct (g1 u), (g2 u). Qed.

Lemma collapse_pick_epic : Epic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 H u; destruct u; apply (H ttt). Qed.

(* ... while the OTHER factor need not be, in either case.  [collapse] identifies the
   two booleans, so it is not monic: probe it with [pick_true] against
   [pick_false], which it cannot tell apart. *)
Lemma collapse_not_monic : Monic collapse → False.
Proof.
  intro M.
  assert (E : collapse ∘[Sets] pick_true ≈ collapse ∘[Sets] pick_false)
    by (intro u; now destruct u).
  exact (Bool.diff_true_false
           (@monic Sets _ _ collapse M unit_setoid_object
              pick_true pick_false E ttt)).
Qed.

(* And [pick_true] misses [false], so it is not epic: probe it with the
   identity against the constantly-true map, which agree on [true] alone. *)
Lemma pick_true_not_epic : Epic pick_true → False.
Proof.
  intro E.
  assert (H : id{Sets} ∘[Sets] pick_true
                ≈ (pick_true ∘[Sets] collapse) ∘[Sets] pick_true)
    by (intro u; now destruct u).
  exact (Bool.diff_false_true
           (@epic Sets _ _ pick_true E bool_setoid_object
              id{Sets} (pick_true ∘[Sets] collapse) H false)).
Qed.

(* The two asymmetries, packaged under the names Theory/Morphisms.v cites. *)
Definition sets_epic_left_factor_only :
  Epic (collapse ∘[Sets] pick_true) * (Epic pick_true → False) :=
  (collapse_pick_epic, pick_true_not_epic).

Definition sets_monic_right_factor_only :
  Monic (collapse ∘[Sets] pick_true) * (Monic collapse → False) :=
  (collapse_pick_monic, collapse_not_monic).

