(* jww (2017-04-13): TODO
(* Here F is a diagram of type J in C. *)
Record Cone `{C : Category} `{J : Category} (n : C) `(F : @Functor J C) := {
    cone_mor : ∀ j : J, n ~> F j;
    cone_law : ∀ i j (f : i ~{J}~> j), (@fmap J C F i j f) ∘ cone_mor i = cone_mor j
}.

Lemma Const_Cone_Iso `(F : @Functor J C)
  : ∀ a, @Isomorphism Sets (Const a ⟾ F) (Cone a F).
Proof.
  intros.
  refine (Build_Isomorphism _ _ _ _ _ _ _); simpl.
  - (* to *)
    crush.
    refine (Build_Cone _ _ _ _ _ _); intros; simpl; destruct X.
    + (* cone_mor *)
      apply transport0.
    + (* cone_law *)
      destruct F.
      simpl in naturality0.
      specialize (naturality0 i j f).
      rewrite right_identity in naturality0.
      apply naturality0.
  - (* from *)
    crush.
    unfold Const.
    destruct X.
    refine (Build_Natural _ _ _ _ _ _); intros; simpl.
    + (* transport *)
      apply cone_mor0.
    + (* naturality *)
      rewrite right_identity.
      destruct F.
      simpl in cone_law0.
      apply cone_law0.
  - (* iso_to *)
    extensionality e.
    destruct e.
    apply proof_irrelevance.
  - (* iso_from *)
    extensionality e.
    destruct e.
    apply proof_irrelevance.
Qed.
*)