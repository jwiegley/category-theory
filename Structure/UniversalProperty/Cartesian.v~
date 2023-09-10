Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.UniversalProperty.

Local Hint Extern 5 (hom ?z ?x) => apply (@exl' _ x _ z (ltac:(typeclasses eauto))) : cat.
Local Hint Extern 5 (hom ?z ?y) => apply (@exr' _ _ y z (ltac:(typeclasses eauto))) : cat.
Local Hint Extern 5 (Proper _ _ ) => progress(repeat(intro)) : cat.
    
#[local] Hint Rewrite @exl_fork : categories.
#[local] Hint Rewrite @exr_fork : categories.


Section ACartesianProduct.
  Lemma exl'_fork_comp {C : Category} {w x y z p} (f : x ~> y) (g : x ~> z) (h : w ~> x)
    (H : IsCartesianProduct y z p) :
    exl' ∘ (fork' f g ∘ h) ≈ f ∘ h.
  Proof.
    rewrite comp_assoc.
    rewrite exl'_fork.
    reflexivity.
  Qed.
  Lemma exr'_fork_comp {C : Category} {w x y z p} (f : x ~> y) (g : x ~> z) (h : w ~> x)
    (H : IsCartesianProduct y z p) :
    exr' ∘ (fork' f g ∘ h) ≈ g ∘ h.
  Proof.
    rewrite comp_assoc.
    rewrite exr'_fork.
    reflexivity.
  Qed.
End ACartesianProduct.

Lemma preyoneda {C : Category} {c d: C} {P : C^op ⟶ Sets} (τ : [Hom ─ , c] ⟹ P) :
  forall f : d ~> c,
    transform τ d f ≈ fmap[P] f (transform τ c id{C}).
Proof.
  intro f. rewrite <- (id_left f) at 1.
  exact (symmetry (naturality τ _ d f) id{C}).
Qed.

Section CartesianProductUniversalProperty.
  Context (C : Category).
  Context (x y : C).
  
  Set Warnings "-non-reversible-notation".
  Notation next_field X
    := ltac:(let c := type of X in match c with forall _ : ?A, _  => exact A end).
  Set Warnings "non-reversible-notation".
  
  Let prod_is_univ_property :=
      Build_IsUniversalProperty C^op
       (fun z => IsCartesianProduct x y z)
       (fun z => CartesianProductStructuresEquiv x y z)
       ([Hom ─ , x ] × [Hom ─ , y ]).
  Section allC.
    Context (z : C).
     (* IsCartesianProduct x y z
       ≊ fobj[C^op] z ≅ fobj[Curried_CoHom C] x × fobj[Curried_CoHom C] y : Type] *)
    Let master_iso := Eval hnf in ltac:(
                      (let A := (eval hnf in (next_field prod_is_univ_property)) in
                       match A with
                       | forall a : _, @?B a => exact(B z)
                       end)).
    Let Build_Iso := Eval hnf in ltac:(let A := (eval hnf in master_iso) in
                           match A with
                           | @Isomorphism ?a ?b ?c => exact(@Build_Isomorphism a b c)
                           end).
    Let master_iso_to := next_field Build_Iso.

    Let Build_to := Eval hnf in ltac:(let A := (eval hnf in master_iso_to) in
                           match A with
                           | @SetoidMorphism ?x ?sx ?y ?sy =>
                               exact(@Build_SetoidMorphism x sx y sy)
                           end).
    Let master_iso_to_underlying := next_field Build_to.
    Proposition cartesian_prod_struct_to_representable : master_iso_to_underlying.
    Proof using Type.
      clear prod_is_univ_property Build_Iso Build_to master_iso master_iso_to.
      unfold master_iso_to_underlying; clear master_iso_to_underlying.
      intro A; simpl in A.
      cbn . 
      unshelve econstructor.
      - simpl. unshelve econstructor.
        + intro a. simpl. unshelve econstructor.
          * auto with cat. 
          * abstract(auto with cat).
        + abstract(simpl; intros; auto with cat).
        + abstract(simpl; intros; auto with cat).
      - simpl. unshelve econstructor.
        + intro a. simpl. unshelve econstructor.
          * intros [m n]. now apply fork'.
          * abstract(eintros [? ?] [? ?] [eqm eqn]; now apply fork'_respects).
        + abstract(simpl; intros ? ? ? [? ?]; simpl;
          apply ump_product; split; 
            [ exact (exl'_fork_comp _ _ _ _) | exact (exr'_fork_comp _ _ _ _) ]).
        + abstract(simpl; intros ? ? ? [? ?]; simpl; symmetry; apply ump_product; split;
                   [ exact (exl'_fork_comp _ _ _ _) | exact (exr'_fork_comp _ _ _ _) ]).
      - abstract(simpl; intros t [p q]; split; 
                 [ rewrite exl'_fork; now autorewrite with categories |
                   rewrite exr'_fork; now autorewrite with categories ] ).
      - abstract(simpl; intros a f; symmetry;
                 apply ump_product; split; now autorewrite with categories).
    Defined.

    Let prod_to_representable_proper :=
          next_field (Build_to cartesian_prod_struct_to_representable).
    Proposition to_is_proper : prod_to_representable_proper.
    Proof using Type.
      unfold prod_to_representable_proper, cartesian_prod_struct_to_representable.
      clear prod_to_representable_proper.
      clear prod_is_univ_property Build_Iso Build_to master_iso master_iso_to
        master_iso_to_underlying.
      simpl. intros X Y [eq1 eq2]. unshelve econstructor.
      + simpl; intros c f; split; auto with cat.
      + simpl. intros c [f1 f2]. apply ump_product; split.
        * rewrite <- eq1; apply exl'_fork.
        * rewrite <- eq2; apply exr'_fork.
    Qed.

    Let to := Build_to cartesian_prod_struct_to_representable to_is_proper.
    Let master_iso_from := Eval hnf in (next_field (Build_Iso to)).
    Let Build_from := Eval hnf in ltac:(let A := (eval hnf in master_iso_from) in
                           match A with
                           | @SetoidMorphism ?x ?sx ?y ?sy =>
                               exact(@Build_SetoidMorphism x sx y sy)
                           end).
    Let master_iso_from_underlying := next_field Build_from.
    Proposition representable_to_cartesian_prod_struct : master_iso_from_underlying.
    Proof using Type.
      unfold master_iso_from_underlying; clear master_iso_from_underlying.
      clear Build_from master_iso_from to prod_to_representable_proper
        master_iso_to_underlying Build_to master_iso_to Build_Iso master_iso
        prod_is_univ_property.
      
      intros [[to_trans to_nat ?] [from_trans from_nat ?] c d]. 
              simpl in c, d.
      simpl. (* set (j := trans z (@id _ z)). simpl in j; destruct j as [ll rr]. *)
      unshelve econstructor.
      - exact (fun a f g => from_trans a (f, g)).
      - exact (fst (to_trans z (@id _ z))).
      - exact (snd (to_trans z (@id _ z))).
      - abstract(intro a; repeat(intro); now apply (proper_morphism (from_trans a))).
      - intros a f g h; split; clear naturality_sym naturality_sym0; simpl in to_nat, from_nat. 
        + abstract(
            intro m; split; rewrite m; specialize c with a (f,g); destruct c as [feq geq];
            simpl in feq, geq; rewrite id_right in feq; rewrite id_right in geq;
            destruct (to_nat z a (from_trans a (f, g)) id{C}) as [fst_eq snd_eq];
            symmetry; [ rewrite <- feq at 1 | rewrite <- geq at 1] ; symmetry;
            rewrite id_left in fst_eq; rewrite id_left in snd_eq;
            [ now apply fst_eq | now apply snd_eq ]).
        + abstract(intros [t s];
          rewrite <- id_right; symmetry; rewrite <- (d a h);
          destruct (to_nat z a h id{C}) as [fst_eq snd_eq];
          apply (proper_morphism (from_trans a)); split; simpl; symmetry;
            rewrite <- (id_left h); [ now rewrite <- fst_eq | now rewrite <- snd_eq ]).
    Defined.

    Let representable_to_prod_proper :=
          next_field (Build_from representable_to_cartesian_prod_struct).

    (* Proper (equiv ==> equiv) representable_to_cartesian_prod_struct *)
    Proposition from_is_proper : representable_to_prod_proper.
    Proof using Type.
      unfold representable_to_prod_proper; clear representable_to_prod_proper.
      unfold representable_to_cartesian_prod_struct.
      clear master_iso_from_underlying
        Build_from
        master_iso_from
        to
        prod_to_representable_proper
        master_iso_to_underlying
        Build_Iso
        Build_to
        master_iso_to
        master_iso
        prod_is_univ_property.
      
      intros a b eq; simpl; split; simpl in eq; unfold iso_equiv in eq;
        destruct eq as [to_eq from_eq]; simpl in to_eq.
      - exact (fst (to_eq z id{C})).
      - exact (snd (to_eq z id{C})).
    Qed.
    Let from := Build_SetoidMorphism _ _ _ _ _ from_is_proper.

    (* This proves that a Cartesian product structure is _logically_ equivalent
       to the object representing a certain functor, but we need to construct the isomorphism. *)
    (* Let tofrom_id := next_field (@Build_Isomorphism Sets _ _ to from). *)

    Local Arguments transform {C D F G}.
    
    Proposition tofrom_id : @compose Sets _ _ _ to from ≈ id{Sets}.
    Proof.
      unfold to, from, representable_to_cartesian_prod_struct, Build_to,
        cartesian_prod_struct_to_representable.
      clear from.
      intro T. simpl.
      apply to_equiv_implies_iso_equiv; simpl.
      intros c x1.
      clear representable_to_prod_proper
        master_iso_from_underlying
        Build_from
        master_iso_from
        to
        prod_to_representable_proper
        master_iso_to_underlying
        Build_to
        master_iso_to
        Build_Iso
        master_iso
        prod_is_univ_property.
      split; destruct T as [Tto Tfrom T_tofromiso T_fromtoiso]; simpl;
        rewrite (preyoneda _ x1);
        set (X := fobj[Curried_CoHom C] x); set (Y := fobj[Curried_CoHom C] y).
      - set (l := (@exl (@Fun.Fun C^op Sets) _ X Y)).
        change (fst (fmap[X × Y] x1 (Tto z id{C}))) with
          ((transform l _ ∘ (fmap[X × Y] x1)) (Tto z id{C})).
        now rewrite <- (naturality l _ c x1 (Tto z id{C})).
      - set (r := (@exr (@Fun.Fun C^op Sets) _ X Y)).
        change (snd (fmap[X × Y] x1 (Tto z id{C}))) with
          ((transform r _ ∘ (fmap[X × Y] x1)) (Tto z id{C})).
        now rewrite <- (naturality r _ c x1 (Tto z id{C})).
    Qed.

    Proposition fromto_id : @compose Sets _ _ _ from to ≈ id{Sets}.
    Proof using Type.
      unfold to, from, representable_to_cartesian_prod_struct, Build_to,
        cartesian_prod_struct_to_representable.
      clear from.
      intro T. simpl.
      clear representable_to_prod_proper
        master_iso_from_underlying
        Build_from
        master_iso_from
        to
        prod_to_representable_proper
        master_iso_to_underlying
        Build_to
        master_iso_to
        Build_Iso
        master_iso
        prod_is_univ_property.

      split; rewrite id_right; reflexivity.
      Qed.

    Definition allC := Build_Iso to from tofrom_id fromto_id.
  End allC.

  Definition CartesianProductUniversalProperty := Eval hnf in prod_is_univ_property allC.
End CartesianProductUniversalProperty.
