(* jww (2017-04-13): TODO
Class Adjunction `{C : Category} `{D : Category}
    `(F : @Functor D C) `(U : @Functor C D) := {
    adj : ∀ (a : D) (b : C), (C (F a) b) ≅ (D a (U b))
}.

Notation "F ⊣ G" := (Adjunction F G) (at level 70) : category_scope.

Program Instance adj_identity `{C : Category} : Id ⊣ Id.

(* Definition adj' `{C : Category} `{D : Category} `{E : Category} *)
(*    (F : Functor D C) (U : Functor C D) *)
(*    (F' : Functor E D) (U' : Functor D E)  (a : E) (b : C) *)
(*    : (C (fun_compose F F' a) b) ≅ (E a (fun_compose U' U b)). *)

Definition adj_compose `{C : Category} `{D : Category} `{E : Category}
   (F : Functor D C) (U : Functor C D)
   (F' : Functor E D) (U' : Functor D E)
   (X : F ⊣ U) (Y : F' ⊣ U')
   : @fun_compose E D C F F' ⊣ @fun_compose C D E U' U.
Proof.
  destruct X.
  destruct Y.
  apply (@Build_Adjunction C E (@fun_compose E D C F F') (@fun_compose C D E U' U)).
  intros.
  specialize (adj0 (F' a) b).
  specialize (adj1 a (U b)).
  replace ((E a) ((fun_compose U' U) b)) with ((E a) ((U' (U b)))).
  replace ((C ((fun_compose F F') a)) b) with ((C (F (F' a))) b).
  apply (@iso_compose Sets ((C (F (F' a))) b) ((D (F' a)) (U b)) ((E a) (U' (U b)))).
  assumption.
  assumption.
  crush.
  crush.
Qed.

Record Adj_Morphism `{C : Category} `{D : Category} := {
    free_functor : Functor D C;
    forgetful_functor : Functor C D;
    adjunction : free_functor ⊣ forgetful_functor
}.

(* Lemma adj_left_identity `(F : @Functor D C) `(U : @Functor C D) *)
(*   : adj_compose Id Id F U adj_identity (F ⊣ U) = F ⊣ U. *)
(* Proof. *)
(*   destruct F. *)
(*   unfold fun_compose. *)
(*   simpl. *)
(*   apply fun_irrelevance. *)
(*   extensionality e. *)
(*   extensionality f. *)
(*   extensionality g. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma adj_right_identity `(F : @Functor C D) : fun_compose F Id = F. *)
(* Proof. *)
(*   destruct F. *)
(*   unfold fun_compose. *)
(*   simpl. *)
(*   apply fun_irrelevance. *)
(*   extensionality e. *)
(*   extensionality f. *)
(*   extensionality g. *)
(*   reflexivity. *)
(* Qed. *)

Lemma adj_irrelevance
   `{C : Category} `{D : Category} `{E : Category}
   (F F' : Functor D C) (U U' : Functor C D)
  : ∀ (X : F ⊣ U) (X' : F' ⊣ U'),
  @F = @F' →
  @U = @U' →
  {| free_functor      := @F
   ; forgetful_functor := @U
   ; adjunction        := @X
   |} =
  {| free_functor      := @F'
   ; forgetful_functor := @U'
   ; adjunction        := @X'
   |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

Program Instance Adj : Category := {
    ob := Category;
    hom := @Adj_Morphism
}.
Obligation 1.
  apply Build_Adj_Morphism
    with (free_functor      := Id)
         (forgetful_functor := Id).
  apply adj_identity.
Defined.
Obligation 2.
  destruct X.
  destruct X0.
  apply Build_Adj_Morphism
    with (free_functor      := fun_compose free_functor1 free_functor0)
         (forgetful_functor := fun_compose forgetful_functor0 forgetful_functor1).
  apply adj_compose.
  assumption.
  assumption.
Defined.
Obligation 3.
  unfold Adj_obligation_2.
  unfold Adj_obligation_1.
  destruct f.
  destruct adjunction0.
  simpl.
  pose (fun_left_identity free_functor0).
  pose (fun_right_identity forgetful_functor0).
  apply adj_irrelevance.
  rewrite e. reflexivity.
  rewrite e0. reflexivity.
Qed.
Obligation 4.
  unfold Adj_obligation_2.
  unfold Adj_obligation_1.
  destruct f.
  destruct adjunction0.
  simpl.
  pose (fun_left_identity forgetful_functor0).
  pose (fun_right_identity free_functor0).
  apply adj_irrelevance.
  rewrite e0. reflexivity.
  rewrite e. reflexivity.
Qed.
Obligation 5.
  admit.
Qed.
*)