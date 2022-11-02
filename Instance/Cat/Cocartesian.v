Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Coproduct.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* Another way of reading this is that we're proving Cat^op is Cartesian. *)
Local Open Scope morphism_scope.
#[export]
Program Instance Cat_Cocartesian : @Cocartesian Cat := {
  product_obj := @Coproduct;
  isCartesianProduct C D := {|
   fork := fun _ F G =>
     {| fobj := fun x =>
                 match x with
                 | Datatypes.inl x => F x
                 | Datatypes.inr x => G x
                 end
     ; fmap := fun x y f =>
                 match x with
                 | Datatypes.inl x =>
                   match y with
                   | Datatypes.inl y => _
                   | Datatypes.inr y => False_rect _ _
                   end
                 | Datatypes.inr x =>
                   match y with
                   | Datatypes.inl y => False_rect _ _
                   | Datatypes.inr y => _
                   end
                 end |};
  exl := 
            {| fobj := Datatypes.inl
             ; fmap := fun _ _ => _ |};
  exr := 
            {| fobj := Datatypes.inr
             ; fmap := fun _ _ => _ |};     
   |}
}.                                                         
Next Obligation. exact (fmap f). Defined.
Next Obligation. exact (fmap f). Defined.
Next Obligation.
  proper.
  destruct x, y; simpl in *;
  solve [ apply fmap_respects; auto | contradiction ].
Qed.
Next Obligation.
  destruct x; simpl in *; cat.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  proper.
  destruct x3, y1; simpl; auto; tauto.
Qed.
Next Obligation.
  split; intros; simplify.
  - apply (e (Datatypes.inl x0) (Datatypes.inl y)).
  - apply (e (Datatypes.inr x0) (Datatypes.inr y)).
  - destruct x1; auto.
  - destruct x1, y.
    + apply e0; tauto.
    + tauto.
    + tauto.
    + apply e; tauto.
Qed.
