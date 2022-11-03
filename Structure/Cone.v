Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Class ACone `(c : obj[C]) `(F : J ⟶ C) := {
    vertex_map (x : J) : c ~{C}~> F x;
    cone_coherence {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ vertex_map x ≈ vertex_map y
  }.

#[export] Program Instance AConeEquiv {C J: Category}
  c (F : C ⟶ J) : Setoid (ACone c F) :=
  {| equiv := fun cone1 cone2 =>
                forall j, @vertex_map _ _ _ _ cone1 j ≈ @vertex_map _ _ _ _ cone2 j |}.
Next Obligation.
  equivalence.
  specialize X with j. specialize X0 with j.
  exact (Equivalence_Transitive _ _ _ X X0).
Qed.  

Class Cone `(F : J ⟶ C) := {
  vertex_obj : C;
  coneFrom : ACone vertex_obj F
}.

Coercion vertex_obj : Cone >-> obj.
#[export] Existing Instance coneFrom.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ L ]" := (@vertex_map _ _ _ _ (@coneFrom _ _ _ L) _)
  (at level 9, format "vertex_map[ L ]") : category_scope.

Notation "Cone[ N ] F" := (ACone N F)(* . { ψ : Cone F | vertex_obj[ψ] = N } *)
  (at level 9, format "Cone[ N ] F") : category_scope.

Definition Cocone `(F : J ⟶ C) := Cone (F^op).

#[export]
Instance ConePresheaf `(F : J ⟶ C) : C^op ⟶ Sets.
Proof.
  unshelve eapply Build_Functor.
  - change obj[C^op] with obj[C]. 
    exact (fun c => {| carrier := Cone[c]F ; is_setoid := AConeEquiv _ _ |}).
  - change obj[C^op] with obj[C] in *; intros c c'.
    intro f; simpl in f.
    unshelve eapply Build_SetoidMorphism.
    + simpl; intro λ1. unshelve eapply Build_ACone.
      * exact (fun x => compose (@vertex_map _ _ _ _ λ1 x) f).
      * abstract(simpl; intros x y g; now rewrite comp_assoc, (cone_coherence g)).
    + abstract(simpl; intros a b t j; specialize t with j; cbn;
      rewrite t; reflexivity).
  - abstract(proper).
  - abstract(intro x; cbn; intros y j; now apply id_right).
  - abstract(cbn; intros; now apply comp_assoc).
Defined.


