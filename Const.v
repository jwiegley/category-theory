(* jww (2017-04-13): TODO
(* Inductive Const := Const_ : Type → Const. *)

(* Definition getConst `{C : Category} (c : @Const C) : C := *)
(*   match c with *)
(*   | Const_ x => x *)
(*   end. *)

Program Instance Const `{C : Category} `{J : Category} (x : C) : J ⟶ C := {
    fobj := fun _ => x;
    fmap := fun _ _ _ => id
}.

Lemma Const_Iso `{C : Category} : ∀ a b, Const a b ≅ a.
Proof. intros. crush. Qed.

Definition Sets_getConst `{J : Category} (a : Type) (b : J)
  (c : @Const Sets J a b) : Type := @fobj J Sets (@Const Sets J a) b.

Program Instance Const_Transport `(C : Category) `(J : Category)
    `(x ~{C}~> y) : @Natural J C (@Const C J x) (@Const C J y).
Obligation 2.
  rewrite left_identity.
  rewrite right_identity.
  unfold Const_Transport_obligation_1.
  reflexivity.
Defined.

Program Instance Delta `{C : Category} `{J : Category} : C ⟶ [J, C] := {
    fobj := @Const C J
}.
Obligation 1.
  apply Const_Transport.
  assumption.
Defined.
Obligation 2.
  unfold Delta_obligation_1.
  unfold Const_Transport.
  unfold Const_Transport_obligation_1.
  unfold Const_Transport_obligation_2.
  apply nat_irrelevance.
  extensionality e.
  reflexivity.
Qed.
Obligation 3.
  unfold Delta_obligation_1.
  unfold Const_Transport.
  unfold Const_Transport_obligation_1.
  unfold Const_Transport_obligation_2.
  apply nat_irrelevance.
  extensionality e.
  reflexivity.
Qed.

Class Complete `(C : Category) := {
    complete : ∀ (J : Category), { Lim : [J, C] ⟶ C & @Delta C J ⊣ Lim }
}.
*)