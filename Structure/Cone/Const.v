(* jww (2017-04-13): TODO
Lemma Const_Cone_Iso `(F : @Functor J C)
  : ∀ a, @Isomorphism Sets (Const a ⟾ F) (Cone a F).
Proof.
  intros.
  isomorphism.
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
    transform.
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
