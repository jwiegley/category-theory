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
   nLab pages cited in the file header), so the statement below is correct.
   The forward direction (surjective → epic) is proved; the reverse direction
   is abandoned (this lemma ends in a non-completing tactic), so
   [surjectivity_is_epic] does NOT enter the environment and nothing downstream
   relies on it.

   The classical argument distinguishes a point not in the image with the
   characteristic map of the image versus the constant map into a truth-value
   object. Realising that truth-value object here runs into a size obstruction:
   the natural choice has carrier [Type] (or [Prop]) with `≈` taken to be `↔`,
   but such an object does not fit as an [obj[Sets]] at the same universe as
   [A] and [B] — Set's subobject classifier lives one universe up. Closing
   this would require universe-polymorphic re-engineering of [Sets] and is left
   as future work. Companion results [injectivity_is_monic] and
   [bijective_is_iso] above are fully proved. *)
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
  - (* This constructive proof was given by
       aws (https://mathoverflow.net/users/30790/aws)
       In the category of sets epimorphisms are surjective - Constructive Proof?
       URL (version: 2014-08-18): https://mathoverflow.net/q/178786 *)
    intros [epic] ?.
    given (C : SetoidObject). {
      refine {|
        carrier := Type;
        is_setoid := {|
          equiv p q := p ↔ q
        |}
      |}.
      equivalence.
    }

    (* given (f : B ~{Sets}~> C). { *)
    (*   refine {| *)
    (*     morphism := λ b, ∃ a, h a ≈ b *)
    (*   |}. *)
    (* } *)
    (* given (g : B ~{Sets}~> C). { *)
    (*   refine {| *)
    (*     morphism := λ _, True *)
    (*   |}. *)
    (* } *)
    (* specialize (epic C f g). *)
    (* enough ((f ∘[Sets] h) ≈ (g ∘[Sets] h)). { *)
    (*   specialize (epic X b); clear X. *)
    (*   unfold f, g in epic. *)
    (*   simpl in *. *)
    (*   now rewrite epic. *)
    (* } *)
    (* intro. *)
    (* unfold f, g; simpl. *)
Abort.
