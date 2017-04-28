Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Closed.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

(*
Program Instance Cat_Closed : @Closed Cat _ := {
  Exp     := @Nat;
  exp_iso := fun X Y Z =>
    {| to :=
         {| morphism := fun f =>
              {| fobj := fun x =>
                   {| fobj := fun y => f (x, y)
                    ; fmap := fun _ _ k => fmap[f] (@id X x, k) |}
               ; fmap := _ |} |}
     ; from :=
         {| morphism := fun f =>
              {| fobj := fun x => f (fst x) (snd x)
               ; fmap := fun x y k =>
                   fmap[f (fst y)] (snd k)
                     ∘ transform[fmap[f] (fst k)] (snd y) |} |} |}
}.
Next Obligation.
  proper; apply fmap_respects.
  split; simpl; cat.
Qed.
Next Obligation.
  rewrite <- fmap_comp; simpl.
  apply fmap_respects; split; simpl; cat.
Qed.
Next Obligation.
  refine {| transform := fun X => _ |}; simpl; intros.
  Unshelve. all:swap 1 2.
    exact (@fmap _ _ f (X0, X) (Y0, X) (f0, @id Y X)).
  rewrite <- !fmap_comp.
  apply fmap_respects; simpl; cat.
Defined.
Next Obligation.
  proper.
  apply fmap_respects; simpl; cat.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- fmap_comp.
  apply fmap_respects; simpl; cat.
Qed.
(*
Next Obligation.
  proper.
  eexists; simpl; autounfold; simpl.
  eexists; simpl.
  Unshelve. all:swap 1 2.
    simpl.
    refine {| transform := fun X => _ |}; simpl; intros.
    Unshelve. all:swap 1 4.
      simpl.
      specialize (H (X0, X)).
      admit.
    eexists.
    Unshelve. all:swap 1 3.
      simpl.
      refine {| transform := fun X => _ |}; simpl; intros.
      Unshelve. all:swap 1 4.
        simpl.
        admit.
      admit.
    simpl; autounfold; simpl.
    admit.
Admitted.
Next Obligation.
  simpl in *.
  exact (fmap[f o] h0 ∘ transform[fmap[f] h] o2).
  apply (transform[h1]).
  apply h1.
Admitted.
Next Obligation.
  proper.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  proper.
Admitted.
Next Obligation.
  simpl.
Admitted.
*)
*)
