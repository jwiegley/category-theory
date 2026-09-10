(** * Probe for Structure/Limit/Diagrams.v (issue #420)

    Pins the measured boundaries of the category of diagrams and its limit
    functor: the two record-level walls that force identity and composition
    to be built componentwise, the hypothesis mismatch behind the colimit
    dual, and — as a compiled countermodel rather than an argument — why the
    comma category over Cat cannot carry the limit's arrow part.  Every
    refutation command below was stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read, so each refusal is
    of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [W ◯ Id = W] is refused at [eq_refl] ("cannot unify
                     W ◯ Id[A] and W"): functor composition is not strictly
                     unital as a record; the object actions agree (control).
     N2 CONVERSION   [F ◯ (U ◯ W) = (F ◯ U) ◯ W] is refused at [eq_refl]:
                     nor strictly associative; object AND arrow actions
                     agree (controls).
     N3 TYPING       [nat_id] has type [ddiag X ◯ Id ⟹ ddiag X ◯ Id], not
                     [ddiag X ◯ Id ⟹ ddiag X] — the unit wall behind
                     [Did]'s componentwise identity (control).
     N4 TYPING       [nat_compose (dtau g) (dtau f ⊲ dW g)] lands at
                     [(ddiag Z ◯ dW f) ◯ dW g ⟹ ddiag X] where [DHom] wants
                     [ddiag Z ◯ (dW f ◯ dW g) ⟹ ddiag X] — the bracketing
                     wall behind [Dcomp] (control).
     N5 CONVERSION   [@Cocomplete C = @Complete (C^op)] is refused at
                     [eq_refl] ("cannot unify Cocomplete and Complete");
                     the two bridges round-trip at [eq_refl] (controls).
     N6 TYPING       the naive bridge [fun D G => L D G] is refused:
                     [G : D ⟶ C^op] where [D ⟶ C] is expected; the bridge
                     through [Opposite D] and [Opposite_Functor G] is the
                     control.

    Countermodel (positive, compiled): in [CommaDiagrams Sets] the two
    arrows [p420_f_id] and [p420_f_negb] on the one-object diagram constant
    at the two-element setoid share their functor components and differ
    only in their squares (the identity and the swap [negb_iso]);
    [p420_squares_forgotten] proves them equivalent in the comma setoid,
    [p420_id_not_negb] that the squares' components are not, and
    [p420_no_respectful_arrow_part] that no [Proper] assignment of arrows
    can return the square's component on both — so the issue's "comma form
    over Cat" cannot carry a limit functor's arrow part.

    Readbacks: the object and hom types of [Diagrams C], the object and
    arrow parts of [LimDiagrams] and [ColimDiagrams], the apex of the
    reindexed-and-pushed cone, and [CommaDiagrams_equiv].

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the
    binder names [G] and [L] of N5/N6, the six names the refuted
    declarations would introduce, and the instrument's absent name — so a
    renamed or removed constant breaks the build on a positive line rather
    than letting a refutation pass for the wrong reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.Limit.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Structure.Limit.Diagrams.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe420_absent_name.

(** ** A: functor composition is neither strictly unital nor associative *)

Section Bracketing.

Context {A B C D : Category}.

(* N1 CONVERSION: the unit law of [◯] is not an identity of records *)
Fail Example p420_unit (W : A ⟶ B) : W ◯ Id[A] = W := eq_refl.

(* control: the object action agrees *)
Example p420_unit_fobj (W : A ⟶ B) : fobj[W ◯ Id[A]] = fobj[W] := eq_refl.

(* N2 CONVERSION: nor is associativity *)
Fail Example p420_assoc (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) :
  F ◯ (U ◯ W) = (F ◯ U) ◯ W := eq_refl.

(* controls: object and arrow actions agree *)
Example p420_assoc_fobj (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) :
  fobj[F ◯ (U ◯ W)] = fobj[(F ◯ U) ◯ W] := eq_refl.

Example p420_assoc_fmap (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) {x y : A} (f : x ~> y) :
  fmap[F ◯ (U ◯ W)] f = fmap[(F ◯ U) ◯ W] f := eq_refl.

End Bracketing.

(** ** B: why identity and composition of [Diagrams] are built componentwise *)

Section Componentwise.

Context {C : Category} {X Y Z : DObj C}.

(* N3 TYPING: the identity transformation lands at [ddiag X ◯ Id ⟹ ddiag X ◯ Id] *)
Fail Definition p420_Did : DHom X X :=
  {| dW := Id[didx X]; dtau := nat_id |}.

(* control: the componentwise identity *)
Check (Did X).

(* N4 TYPING: whiskering then composing lands at the other bracketing *)
Fail Definition p420_Dcomp (f : DHom Y Z) (g : DHom X Y) : DHom X Z :=
  {| dW := dW f ◯ dW g; dtau := nat_compose (dtau g) (dtau f ⊲ (dW g)) |}.

(* control: the componentwise composite *)
Check (fun (f : DHom Y Z) (g : DHom X Y) => Dcomp f g).

End Componentwise.

(** ** C: the colimit dual's hypothesis *)

Section Dual.

Context {C : Category}.

(* N5 CONVERSION: [Cocomplete C] is not [Complete (C^op)] by conversion *)
Fail Example p420_cocomplete (L : @Cocomplete C) :
  @Cocomplete C = @Complete (Opposite C) := eq_refl.

(* N6 TYPING: nor is the naive bridge well-typed *)
Fail Definition p420_bridge (L : @Cocomplete C) : @Complete (Opposite C) :=
  fun D G => L D G.

(* controls: the bridges through [(F^op)^op = F], round-tripping at [eq_refl] *)
Check (@Complete_op_of_Cocomplete C).
Check (@cocomplete_roundtrip C).
Check (@complete_op_roundtrip C).

End Dual.

(** ** D: the comma form over Cat forgets the square — a concrete countermodel *)

Section Countermodel.

(* the one-object diagram in Sets constant at the two-element setoid *)
Definition p420_F : _1 ⟶ Sets := fobj[@Diagonal Sets _1] bool_setoid_object.

Definition p420_X : CommaDiagrams Sets := ((_1, ttt); p420_F).

Program Definition negb_mor : bool_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := negb |}.

Program Definition negb_iso : bool_setoid_object ≅[Sets] bool_setoid_object :=
  {| to := negb_mor; from := negb_mor |}.
Next Obligation.
  intros; simpl in *; repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.
Next Obligation.
  intros; simpl in *; repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.

(* two comma arrows X → X with the same shape functor and different squares *)
Definition p420_square (i : bool_setoid_object ≅[Sets] bool_setoid_object) :
  p420_F ∘[Cat] Id[_1] ≈ fmap[@Diagonal Cat _1 Sets] ((@id _1 ttt)) ∘[Cat] p420_F.
Proof.
  exists (fun _ => i).
  intros a b h; simpl.
  intro x; symmetry; exact (iso_from_to i x).
Defined.

Definition p420_f_id : p420_X ~{CommaDiagrams Sets}~> p420_X :=
  ((Id[_1], (@id _1 ttt)); p420_square iso_id).

Definition p420_f_negb : p420_X ~{CommaDiagrams Sets}~> p420_X :=
  ((Id[_1], (@id _1 ttt)); p420_square negb_iso).

(* the comma setoid identifies them *)
Lemma p420_squares_forgotten : p420_f_id ≈ p420_f_negb.
Proof. split; reflexivity. Qed.

(* ... but their squares' components differ *)
Lemma p420_id_not_negb : (@id Sets bool_setoid_object ≈ negb_mor) → False.
Proof. intro H. specialize (H true). simpl in H. discriminate H. Qed.

(* so no respectful assignment of arrows can read the square back: any
   [m] that sends the two arrows to their square components is refuted *)
Lemma p420_no_respectful_arrow_part
  (m : (p420_X ~{CommaDiagrams Sets}~> p420_X) →
       (bool_setoid_object ~{Sets}~> bool_setoid_object))
  (Hm : Proper (equiv ==> equiv) m)
  (H1 : m p420_f_id ≈ id) (H2 : m p420_f_negb ≈ negb_mor) : False.
Proof.
  apply p420_id_not_negb.
  rewrite <- H1, <- H2.
  apply Hm.
  exact p420_squares_forgotten.
Qed.

End Countermodel.

(** ** E: readbacks *)

Check (@Diagrams_obj).
Check (@Diagrams_hom).
Check (@LimDiagrams_fobj).
Check (@LimDiagrams_fmap).
Check (@dlim_cone_apex).
Check (@ColimDiagrams_fobj).
Check (@dcolim_is_colimit_apex).
Check (@CommaDiagrams_equiv).

(** ** Guard block *)

Check @DObj.
Check @didx.
Check @ddiag.
Check @DHom.
Check @dW.
Check @dtau.
Check @DHom_equiv.
Check @DHom_Setoid.
Check @Did.
Check @Dcomp.
Check @Dcomp_respects.
Check @Diagrams.
Check @dlim.
Check @dlim_is.
Check @dlim_cone.
Check @dlim_map.
Check @dlim_map_commutes.
Check @dlim_map_unique.
Check @LimDiagrams.
Check @Complete_op_of_Cocomplete.
Check @cocomplete_of_complete_op.
Check @ColimDiagrams.
Check @dcolim.
Check @CommaDiagrams.
Check @nat_id.
Check @nat_compose.
Check @Cocomplete.
Check @Complete.
Check @Opposite.
Check @Id.
Check @Compose.
Check @fobj.
Check @fmap.
Check @bool_setoid_object.
Check @Diagonal.
Check @Comma.
Check @_1.
Check @ttt.
