Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
(* Require Import Category.Instance.Two.Discrete.*)
Require Import Category.Instance.Fun.Cartesian.
(* A predicate on objects of a category can be called a "universal property" *)
(* if satisfying the predicate is equivalent to representing a certain functor. *)
(* This definition of a universal property contains all examples that I am aware of
   but I do not claim it is completely exhaustive. *)
Check @Isomorphism Sets.

Class IsUniversalProperty (C : Category) (P : C → Type) (eqP : forall c, Setoid (P c)) :=
  {
    repr_functor : C ⟶ Sets ;
    repr_equivalence : forall c : C,
      @Isomorphism Sets 
        (Build_SetoidObject (P c) (eqP c))
        (Build_SetoidObject (Isomorphism [Hom c,─] repr_functor) _)
  }.

Ltac simpl_obj_in_hypotheses :=
  repeat(match goal with
         | [H : obj[?C] |- _ ] => progress(simpl obj in H)
         end).
Ltac simpl_fobj_in_hypotheses :=
  repeat(match goal with
        | [H : context[fobj[?C]] |- _ ] => progress(simpl fobj in H)
         end).
Ltac simpl_fmap_in_hypotheses :=
  repeat(match goal with
        | [H : context[fmap[?C]] |- _ ] => progress(simpl fmap in H)
         end).
Ltac simpl_hom_in_hypotheses :=
  repeat(match goal with
        | [H : context[hom[?C]] |- _ ] => progress(simpl hom in H)
         end).

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

Section CartesianProductUniversalProperty.
  Context (C : Category).
  Context (x y : C).

  Notation next_field X
    := ltac:(let c := type of X in match c with forall _ : ?A, _  => exact A end).

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
    Proof.
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
    Proof.
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
    Proof.
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
    Print representable_to_prod_proper.
    (* Proper (equiv ==> equiv) representable_to_cartesian_prod_struct *)
    Proposition from_is_proper : representable_to_prod_proper.
    Proof.
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
    Let tofrom_id := next_field (@Build_Isomorphism Sets _ _ to from).
    (* tofrom_id := to ∘ from ≈ id{Sets} : Type *)
    Print tofrom_id.
    

    
(* Maybe easier for limits ?*)
Section LimitUniversalProperty.
  (* Context (C : Category). *)
  (* Context (x y : C). *)

  Notation next_field X
    := ltac:(let c := type of X in match c with forall _ : ?A, _  => exact A end).
  Let prod_is_univ_property :=
        Build_IsUniversalProperty C^op
         (fun z => IsCartesianProduct x y z)
         (fun z => CartesianProductStructuresEquiv x y z)
         (@ConePresheaf Two_Discrete C (Pick_Two x y)).
  Section allC.
    Context (z : C).
    Check prod_is_univ_property.
    Let master_iso := Eval hnf in ltac:(
                      (let A := (eval hnf in (next_field prod_is_univ_property)) in
                       match A with
                       | forall a : _, @?B a => exact(B z)
                       end)).w
    Print master_iso.
    (* Suppose that X is a _constant_ of type :
       forall (a : A) (b : B a) (c : C a b), D a. *)
    (* I want a. *)
    (* I know I can get a from D a. *)
    Check Build_Isomorphism.
    (* I claim I can get a if I know D a b c. How? *)
    
    (* How can I get A? *)
    Print Isomorphism.
    
    Let Build_Iso := Eval hnf in ltac:(let A := (eval hnf in master_iso) in
                           match A with
                           | @Isomorphism ?a ?b ?c => exact(@Build_Isomorphism a b c)
                           end).
    Let master_iso_to := next_field Build_Iso.
    Print master_iso_to.
    Check @SetoidMorphism.
    Let Build_to := Eval hnf in ltac:(let A := (eval hnf in master_iso_to) in
                           match A with
                           | @SetoidMorphism ?x ?sx ?y ?sy =>
                               exact(@Build_SetoidMorphism x sx y sy)
                           end).
    Let master_iso_to_underlying := next_field Build_to.
    Proposition cartesian_prod_struct_to_representable : master_iso_to_underlying.
    Proof.
      clear prod_is_univ_property master_iso Build_Iso Build_to master_iso_to.
      unfold master_iso_to_underlying; clear master_iso_to_underlying.
      simpl. intro H.
      unshelve econstructor.
      - simpl. unshelve econstructor.
        + intro x0. unshelve econstructor.
          * simpl. intro f. unshelve econstructor.
            -- intro x1. destruct x1; auto with cat.
            -- intros ? ? f0. destruct f0; auto with cat.
          * repeat(intro). destruct j; apply compose_respects; auto with cat.
        + simpl. intros ? ? ? ? j; destruct j; try(apply compose_respects); auto with cat.
        + simpl. intros ? ? ? ? j; destruct j; try(apply compose_respects); auto with cat.
      - unshelve econstructor.
        + intro a. unshelve econstructor.
          * simpl. intro Co. 
               
               
               

      
      
    

    Let master_iso_to_underlying := next_field master_iso_to.
    Print master_iso_to. 
    Proposition to : iso_to.
    Proof.
      clear Build_Iso master_iso prod_is_univ_property.
      unfold iso_to; clear iso_to; simpl.
      unshelve econstructor.
      - 
      
    
    Check Build_Isomorphism.
    
    
    Proposition have_master_iso : master_iso.
    Proof.
      unshelve refine (Build_Isomorphism _ _ _ _ _ _).
      

    


                  eval hnf in(
                let A := next_field prod_is_univ_property in
                match A with
                | forall a : _, @?B a => B z
                end)).
            let A := (eval hnf in ()) in
          match A with
          | 
          end).
    Print master_iso.
               .
    
                 
                
    


  
  Let master_iso := Eval hnf in (next_field prod_is_univ_property).
  (*  ∀ c : obj[C^op], IsCartesianProduct x y c *)
  (*         ≊ fobj[C^op] c ≅ ConePresheaf (Pick_Two x y) : Type] *)
  Print master_iso.
  Print master_iso.
  (* Eval cbv delta in master_iso. *) (* This works but unfolds too much. *)
  Goal True.
    match (eval hnf in master_iso) with
    | forall z : _ , @?B z =>
        match eval hnf in (B x) with
        | ?a => set (j := a)
        end
    end.

    
    set (z := match type of (f x) with
              | ?a => a
              end).
  set (Z := ltac:(match type of (f x) with
            | ?a => a
            end)).
      
  Let abc := ltac:(
                     match mas with
                   | forall x : _ , _ => idtac 
                   end).
  Check (forall a : C, Prop) x.
  Variable c : C^op.
  Let s := match master_iso with
           | forall _ : _, B => exact
  Check master_iso c.
  Goal master_iso.
  Proof. 
    intro z.
    unshelve econstructor. {
    (* SetoidMorphism (IsCartesianProduct x y z) 
       (NatIso(Hom(-,z),ConePresheaf(Pick_Two x y)  *) 
    simpl. unshelve econstructor. { 
    (* Underlying map IsCartesianProduct x y z)  -> 
        NatIso(Hom(-,z),ConePresheaf(Pick_Two x y) *)
    unshelve econstructor. {
     (* Given that z is Cartesian product of x, y, 
       give a natural transformation Hom(-,z) => Cone(-, Pick_Two x y) *)
    simpl. unshelve econstructor. {
    (* Morphisms of natural transformation *)
    intro a. simpl. simpl_obj_in_hypotheses. unshelve econstructor. {
    (* Hom(a,z) -> Cone[a](Pick_Two x y) *)
    intro f. unshelve econstructor. {
    (* Morphisms of the cone, forall j : Two_Discrete, Hom(a, Pick_Two x y j) *)
      intro j. simpl_obj_in_hypotheses. simpl. destruct j; auto with cat.
    }
    {  (* Cone satisfies cone_coherence *)
      intros j1 j2 g. simpl_obj_in_hypotheses. simpl_fobj_in_hypotheses.
      simpl_hom_in_hypotheses. destruct j1, j2; now autorewrite with categories.
    } (* Cone built. *) }
    { (* Prove that the map Hom(a,z) -> Cone(a)(Pick_Two x y) is proper. *)
      repeat(intro). simpl equiv. destruct j; apply compose_respects; auto.
      + time(
        exact ((@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C _ x))) (@exl' _ _ _ _ X))).
    
    repeat(unshelve econstructor; intros).
    
    
    - simpl_obj_in_hypotheses. simpl. destruct x1; auto with cat.
    - simpl_obj_in_hypotheses. simpl_fobj_in_hypotheses. simpl_hom_in_hypotheses.
      destruct y0, x1; now autorewrite with categories.
    - repeat(intro). simpl equiv. destruct j; apply compose_respects; auto.
      + Set Printing All.
        simpl in X. simpl in x1, y0. simpl in X0.
        simpl in c, x0.
        Check ((@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C c x))) (@exl' _ _ _ _ X)).
        time(
        exact ((@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C c x))) (@exl' _ _ _ _ X))).
        
      
    
  Print to.

  
  
Proposition IsCartesianProductIsUniversalProperty (C : Category) (x y : C) :
  IsUniversalProperty C^op (fun z => IsCartesianProduct x y z)
    (fun z => CartesianProductStructuresEquiv x y z).
Proof.  
unshelve eapply Build_IsUniversalProperty; 
 [ exact (@ConePresheaf Two_Discrete C (Pick_Two x y)) |].
repeat( unshelve econstructor; intros ).
- simpl_obj_in_hypotheses; simpl_fobj_in_hypotheses. simpl.
  destruct x1; auto with cat.
- simpl_obj_in_hypotheses. simpl_fobj_in_hypotheses. 
  simpl_hom_in_hypotheses.
  destruct y0, x1; now autorewrite with categories.
- repeat(intro). simpl equiv. destruct j; apply compose_respects; auto.
  + Set Printing All.
    apply ((@Equivalence_Reflexive _ _ (@setoid_equiv _ (@homset C c x))) (@exl' _ _ _ _ X)).
    
    apply Equivalence_Reflexive .
    reflexivity.
    progress autorewrite with categorries
    
For any goal ->   (*external*) (progress simplify)(level 5, id 0)
                  (*external*) (progress autorewrite with categories)(level 10, id 0)
                  (*external*) apply_setoid_morphism(level 20, id 0)
                  (*external*) functor_simpl(level 10, id 0)
                  (*external*) (progress cbn in *)(level 40, id 0) 
For equiv ->   (*external*) (simple apply (@compose_respects _ _ _ _))(level 1, pattern 
               @equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _), id 0)
               (*external*) reflexivity(level 1, pattern @equiv _ _ _ _, id 0)
               (*external*) unfold_proper(level 4, pattern @equiv _ _ (?f _) (?f _), id 0)
               (*external*) compose_respects_script(level 20, pattern 
               @equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _), id 0) 
For hom ->   simple apply @id ; trivial(level 1, pattern (@hom ?META1226) ?META1227 ?META1227, id 0)
             (*external*) compose_reduce(level 1, pattern @hom _ _ _, id 0)
             (*external*) (apply (@fork _ _ _ _ _))(level 4, pattern 
             @hom _ _ (@product_obj _ _ _ _), id 0)
             (*external*) (apply (@exr' _ _ y z _))(level 5, pattern 
             @hom _ ?z ?y, id 0)
             (*external*) (apply (@exl' _ x _ z _))(level 5, pattern 
             @hom _ ?z ?x, id 0)
             (*external*) (progress simpl hom)(level 10, pattern @hom _ _ _ _, id 0) 
For forall_relation ->   unfold forall_relation(level 4, id 0) 
For SetoidMorphism ->   (*external*) unshelve
                        (eapply Build_SetoidMorphism)(level 4, pattern 
                        @SetoidMorphism _ _ _ _, id 0) 
For sigT ->   (*external*) split_exists(level 1, pattern @sigT _ _, id 0) 
  + 
    
  
                                                  
  
  abstract(proper; simpl_obj_in_hypotheses; destruct j; auto with cat).
- simpl.
  
  

intro c; unshelve eapply Build_Isomorphism.



- unshelve econstructor.
  + cbn; intro IsProduct. unshelve econstructor.
    * simpl. unshelve econstructor.
      -- simpl. intro. unshelve econstructor.
         ++ intro. unshelve econstructor.
            ** simpl. intro x1; destruct x1.
