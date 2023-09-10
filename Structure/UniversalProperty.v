Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Groupoid.
(* A predicate on objects of a category can be called a "universal property" *)
(* if satisfying the predicate is equivalent to representing a certain functor. *)
(* This definition of a universal property contains all examples that I am aware of
   but I do not claim it is completely exhaustive. *)
Class IsUniversalProperty (C : Category) (P : C → Type) (eqP : forall c, Setoid (P c)) :=
  {
    repr_functor : C ⟶ Sets ;
    repr_equivalence : forall c : C,
      @Isomorphism Sets 
        (Build_SetoidObject (P c) (eqP c))
        (Build_SetoidObject (Isomorphism [Hom c,─] repr_functor) _)
  }.

Lemma preyoneda {C : Category} {c d: C} {P : C^op ⟶ Sets} (τ : [Hom ─ , c] ⟹ P) :
  forall f : d ~> c,
    transform τ d f ≈ fmap[P] f (transform τ c id{C}).
Proof.
  intro f. rewrite <- (id_left f) at 1.
  exact (symmetry (naturality τ _ d f) id{C}).
Qed.
 
#[local] Program Instance exists_setoid (A : Type) (B : Setoid A) (C : A -> Type) :
  Setoid { x : A & C x } :=
  { equiv := fun a b => `1 a ≈ `1 b }.
Local Arguments morphism {x H y H0} s.
Proposition representability_by_yoneda (C : Category) (F : C^op ⟶ Sets) (c : C):
  @Isomorphism Sets
    {| carrier := { x : F c & IsIsomorphism (from (Yoneda_Lemma C F c ) x) } |}
                              
    (Build_SetoidObject (Isomorphism [Hom ─,c] F) _) .
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + intros [elt yoneda_is_iso]. unshelve econstructor.
      * exact (from (Yoneda_Lemma C F c) elt).
      * exact (from (IsIsoToIso _ yoneda_is_iso)).
      * apply is_right_inverse.
      * apply is_left_inverse.
    + abstract(intros [eltx x_is_iso] [elty y_is_iso] eltx_eq_elty;
      simpl in eltx_eq_elty;
      apply to_equiv_implies_iso_equiv; simpl;
      intros; rewrite eltx_eq_elty; reflexivity).
  - unshelve econstructor.
    + simpl. intro X; simpl in X. destruct X as [Xto Xfrom tofromid fromtoid]; simpl in *.
      exists (morphism (to (Yoneda_Lemma C F c)) Xto).
      simpl. 
      unshelve econstructor.
      * exact Xfrom.
      * abstract(simpl; intros; rewrite <- tofromid; symmetry; apply preyoneda).
      * abstract(simpl; intros; rewrite <- preyoneda; apply fromtoid).
    + abstract(intros x y eq; simpl; destruct eq as [e ?]; simpl in e; apply e).
  - abstract(unshelve econstructor; simpl; intros ? ?;
                   [ symmetry; apply preyoneda | reflexivity ]  ).
  - abstract(simpl; intros [x f]; simpl; set (k := @fmap_id _ _ F);
             simpl in k; apply k).
Defined.

Section UniversalProperty.
  Context (C : Category) (P : obj[C] -> Type) (eqP : forall c, Setoid (P c))
    (H : IsUniversalProperty C P eqP).

  Proposition univ_property_unique (c : C) (t : P c) : @Unique obj[C] (ob_setoid) P.
  Proof using eqP H.
    exists c ; [exact t |].
    intros v Pv.
    set (a1 := to (repr_equivalence c)). set (a2 := to(repr_equivalence v)).
    set (b1 := a1 t). set (b2 := a2 Pv). unfold a1, a2 in *. clear a1 a2;
      unfold carrier in b1, b2.
    unshelve econstructor. 
    - exact (@two_sided_inverse _ _ _ _  (Yoneda_Embedding' C v c) (from b1 ∘ to b2)). 
    - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ to b1)). 
    - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
      set (j := ( _ ( compose  _ _)));
      set (j' := ( _ ( compose  _ _)));
      change j with (op j);
      change j' with (op j');
      set (m := @fmap_comp _ _ C v c v (op j') (op j));
      rewrite m;
      unfold op, j, j';
      rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
      rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
      simpl; intros x f; unfold op; rewrite id_right;
      set (ab := (iso_to_from b1));
      simpl in ab; rewrite ab;
      rewrite (@fmap_id _ _ repr_functor x (to b2 x f));
      simpl; clear ab;
      set (ab' := (iso_from_to b2));
      simpl in ab'; rewrite ab'; rewrite id_left;
      reflexivity). 
    - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
      set (j := ( _ ( compose  _ _)));
      set (j' := ( _ ( compose  _ _)));
      change j with (op j);
      change j' with (op j');
      set (m := @fmap_comp _ _ C c v c (op j') (op j));
      rewrite m;
      unfold op, j, j';
      rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
      rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
      simpl; intros x f; unfold op; rewrite id_right;
      set (ab := (iso_to_from b2));
      simpl in ab; rewrite ab;
      rewrite (@fmap_id _ _ repr_functor x (to b1 x f));
      simpl; clear ab;
      set (ab' := (iso_from_to b1));
      simpl in ab'; rewrite ab'; rewrite id_left;
      reflexivity).
  Defined.

  Proposition univ_property_respects_iso (c d : C) (iso : c ≅ d) : P c -> P d.
  Proof using eqP H.
    intro t.
    rapply (from (repr_equivalence d)).
    apply (Equivalence_Transitive (fobj[C] d) (fobj[C] c)).
    - exact (fobj_iso _ _ _ (iso_sym (Isomorphism_Opposite iso))).
    - apply (to (repr_equivalence c)). exact t.
  Defined.

  (* Let c, d be objects in C, and t : P c, s : P d.
     Then there is a unique isomorphism p : c ≈ d 
     such that the transport of p along t is equivalent to s. *)
  Proposition univ_property_unique_up_to_unique_iso
    (c d : C) (t : P c) (s : P d) :
    Unique (fun p : (c ≅ d) => univ_property_respects_iso c d p t ≈ s).
  Proof.
    (* We have already constructed the isomorphism p.*)
    (* We have isomorphisms Hom(c, -) ≅ repr_functor ≅ Hom(d,-)
       corresponding to the choice of t and s, and we 
       pull back this isomorphism Hom(c,-) ≅ Hom(d,-) along the
       Yoneda embedding. *)
    exists (uniqueness (univ_property_unique c t) d s).
    - (* Why does this isomorphism respect the structure of P? *)
      abstract(simpl; unfold univ_property_respects_iso; simpl;
      (* Proofs of P d are in one to one correspondence 
         with natural isomorphisms
         Hom(d, - ) ≅ repr_functor. *)
      (* So it suffices to show that these determine the same natural isomorphism. *)
      rapply (snd (injectivity_is_monic _) (iso_to_monic (repr_equivalence d)));
      set (M := (iso_to_from (repr_equivalence d)));
        simpl in M; rewrite M; clear M;
      apply to_equiv_implies_iso_equiv;
      intros j u; simpl in u;
      simpl;
      set (ab :=  (to (repr_equivalence c )) );
      assert (K := @naturality _ _ _ _ (to (ab t)) _ _ u);
      simpl in K;
      rewrite <- K;
      clear K;
      set (A := iso_to_from (ab t) d); simpl in A; unfold op; rewrite A; clear A;
      set (aj := to (repr_equivalence d ));
      set (aj' := to (aj s));
      change (@id C d) with (@id (C^op) d);
      rewrite <- 2 (@preyoneda (C^op) _ _ repr_functor aj');
               reflexivity).
    - (* The isomorphism is unique. *)
      (* The canonical isomorphism c ≌ d "carrying" t to s is defined as follows: *)
      (* rep_c : Hom(c, -) ≌ repr_functor *)
      (* rep_d : Hom(d, -) ≌ repr_functor *)
      (* rep_c ^-1 ∘ rep_d : Hom(d,-) -> repr_functor -> Hom(c, -) *)
      (* " ... " d id_d : Hom(c, d) *)
      (* p := rep_c^-1 ∘ rep_d d id_d. *)
      (* OTOH, by assumption, we have - 
         y(v) : Hom(d, -) ≌ Hom(c, -)
         rep_c : Hom(c, -) ≌ repr_functor
         rep_d : Hom(d, -) ≌ repr_functor *)
      (* and the natural isomorphism Hom(d, -) ≌ repr_functor given by *)
      (* rep_c ∘ y(v) : Hom(d, -)  ≌ Hom(c, -) ≌ repr_functor *)
      (* corresonds to s across the bijection. *)
      (* Of couse since by construction, s also corresponds to rep_d, *)
      (* this means that  rep_c ∘ y(v) ≈ rep_d as isomorphisms Hom(d,-) ≈ repr_functor. *)
      (* Thus y(v) ≈ rep_c^-1 ∘ rep_d : Hom(d,-) ≅ Hom(c,-) and in particular 
         they agree at (d, id{C} d).  *)
      abstract(intros v respects_iso;
      simpl uniqueness;
      apply to_equiv_implies_iso_equiv; simpl;
      unfold univ_property_respects_iso, Equivalence_Transitive in respects_iso;
        simpl in respects_iso;
      set (v' := iso_sym (Isomorphism_Opposite v)) in *;
      set (yv := fobj_iso C d c v') in *;
      rewrite <- (id_left (to v));
      change (id{C} ∘ to v) with (to yv d id{C});
      change (from (to (repr_equivalence c) t) d (to (to (repr_equivalence d) s) d id)) with
        (((from (to (repr_equivalence c) t)) ∘ (to (to (repr_equivalence d) s))) d id);
      cut ((iso_sym (to (repr_equivalence c) t)) ⊙ ( (to (repr_equivalence d) s)) ≈ yv);
               [ intro a; destruct a as [a _]; simpl in a; apply a |];
      apply (@proper_morphism _ _ _ _ (to (repr_equivalence d))) in respects_iso;
      assert (K := (iso_to_from (repr_equivalence d)));
      simpl in K; rewrite K in respects_iso; clear K;
      apply (@compose_respects (Groupoid (@Fun.Fun C Sets)) _ _ _
               (iso_sym (to (repr_equivalence c) t)) (iso_sym (to (repr_equivalence c) t))
               (Equivalence_Reflexive _ ))
              in respects_iso;
      rewrite comp_assoc in respects_iso; simpl in respects_iso;
      rewrite iso_sym_left_inverse in respects_iso;
      change iso_id with (@id (Groupoid (@Fun.Fun C Sets)) (fobj[C] c)) in respects_iso;
      rewrite (@id_left (Groupoid (@Fun.Fun C Sets))) in respects_iso;
      symmetry in respects_iso;
      exact respects_iso).
  Defined.      
End UniversalProperty.
