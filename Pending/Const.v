Set Warnings "-notation-overridden".

(* jww (2017-04-13): TODO
Program Instance Const_Transport `(C : Category) `(J : Category)
    `(x ~{C}~> y) : @Natural J C (@Const C J x) (@Const C J y).
Obligation 2.
  rewrite left_identity.
  rewrite right_identity.
  unfold Const_Transport_obligation_1.
  reflexivity.
Qed.

Program Instance Delta {C : Category} {J : Category} : C ⟶ [J, C] := {
    fobj := @Const C J
}.
Obligation 1.
  apply Const_Transport.
  assumption.
Qed.
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
    complete : ∀ (J : Category), ∃ Lim : [J, C] ⟶ C, @Delta C J ⊣ Lim
}.
*)
