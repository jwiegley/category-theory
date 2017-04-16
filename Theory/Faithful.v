(* jww (2017-04-13): TODO
Class FullyFaithful `(F : @Functor C D) :=
{ unfmap : ∀ {X Y : C}, (F X ~> F Y) → (X ~> Y)
}.

Program Instance Hom_Faithful (C : Category) : FullyFaithful C :=
{ unfmap := fun _ _ f => (transport/f) id
}.

Program Instance Hom_Faithful_Co (C : Category) {A : C} : FullyFaithful (C A).
Obligation 1.
  destruct C. crush.
  clear left_identity.
  clear right_identity.
  clear comp_assoc.
  specialize (compose X A Y).
  apply compose in X0.
    assumption.
  (* jww (2014-08-12): Is this even provable?  Ed thinks no. *)
*)