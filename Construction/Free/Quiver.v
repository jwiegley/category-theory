Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Quiver.
  Class Quiver@{o h p} := {
      nodes : Type@{o};
      uedges := Type@{h} : Type@{h+1};
      edges : nodes → nodes → uedges;
      edgeset : ∀ X Y, Setoid@{h p} (edges X Y)
    }.
  Coercion nodes : Quiver >-> Sortclass.
  Context (G : Quiver).
  Existing Instance edgeset.

  Fixpoint tlist'_quiver_equiv (k i j : G) 
    (f : @tlist' _ edges k i) (g : @tlist' _ edges k j) ( p : i = j ) : Type :=
    match f in (tlist' _ i_t) return (tlist' _ j) -> i_t = j -> Type with
    | tnil => fun g' q => tnil = Logic.transport_r (fun z => @tlist' _ edges k z) q g'
    | @tcons _ _ _ i0 i1 fhead ftail =>
        fun g' : tlist' _ j  => 
          match g' in tlist' _ j return @tlist' _ edges k i1 -> i0 = j -> Type with
          | tnil => fun _ _ => False
           | @tcons _ _ _ j0 j1 ghead gtail =>
               fun ftail' p' =>
                 { q : i1 = j1 &
                      (Logic.transport (fun t => edges i0 t) q fhead ≈
                         Logic.transport_r (fun t => edges t j1) p' ghead) &
                      tlist'_quiver_equiv k i1 j1 ftail' gtail q }
          end ftail
    end g p.

  Inductive tlist'_quiver_inductive (i : G) :
    forall (j : G), (@tlist' _ edges i j) -> (@tlist' _ edges i j) -> Type :=
  | tlist_both_empty : tlist'_quiver_inductive i tnil tnil
  | tlist_both_cons (k : G) :
    forall (j : G) (ftail gtail : @tlist' _ edges i j) (fhead ghead : edges k j),
           (tlist'_quiver_inductive j ftail gtail) ->
           fhead ≈ ghead ->
           tlist'_quiver_inductive k (tcons _ fhead ftail)
                                   (tcons _ ghead gtail).

  Proposition fixpoint_implies_inductive (i j : G) (f g : tlist edges i j) :
    tlist'_quiver_equiv _ _ _ f g eq_refl -> (tlist'_quiver_inductive _ _ f g).
  Proof.
    revert g; induction f.
    - intros g H. simpl in H; unfold Logic.transport_r in H; simpl in H; destruct H.
      constructor.
    - intro g; destruct g; [ now apply False_rect |].
      intro H. simpl in H; destruct H as [q t t0].
      destruct q.
      constructor.
      + apply IHf. assumption.
      + unfold Logic.transport_r in t. simpl in t. exact t.
  Defined.

  Proposition inductive_implies_fixpoint (i j : G) (f g : tlist edges i j) :
    (tlist'_quiver_inductive _ _ f g) -> tlist'_quiver_equiv _ _ _ f g eq_refl.
  Proof.
    intro H.
    induction H; [ now simpl | simpl ].
    exists eq_refl; assumption.
  Defined.
  
  Lemma tlist'_equiv_lengths (i j k : G) (f : tlist' k i) (g : tlist' k j) (p : i = j) :
    tlist'_quiver_equiv _ _ _ f g p -> tlist_length f = tlist_length g.
    revert j g p; induction f.
    - intros j g p H. destruct g; [ reflexivity | ].
      simpl in H. destruct p. unfold Logic.transport_r in H; simpl in H;
        now inversion H.
    - intros j' g p; destruct g; [ now apply False_rect | simpl ].
      intros [j_eq_j0 X]; apply eq_S; unshelve eapply IHf; [ exact j_eq_j0 | assumption ].
  Defined.
  
  Proposition tlist'_quiver_equiv_reflexive (k i: G) :
    forall f : tlist edges i k, tlist'_quiver_equiv k i i f f eq_refl.
  Proof.
    intro f; induction f; [ now constructor |].
    unshelve econstructor; easy.
  Defined.

  Arguments Logic.transport_r /.

  Proposition tlist'_quiver_equiv_transitive (k i1 i2 i3: G) :
      forall (f : tlist edges i1 k) (g : tlist edges i2 k) (h : tlist edges i3 k)
             (p : i1 = i2) (q : i2 = i3),
        tlist'_quiver_equiv k i1 i2 f g p ->
        tlist'_quiver_equiv k i2 i3 g h q->
        tlist'_quiver_equiv k i1 i3 f h (eq_trans p q).
  Proof.
    intro f; revert i2 i3.
    induction f as [ | i0 i1 fhead ftail ]; 
      [ intros i2 i3 g h p q equiv1 equiv2;
        destruct p, q;
        simpl in *; destruct equiv1; now simpl in equiv2 |].
 
      (* [ intros; destruct g; [ easy | now apply False_rect ] |]. *)
    intros i2 i3 g h p q equiv1 equiv2.
    destruct g as [ | j0 j1 ghead gtail ]; [ now apply False_rect |]. 
    simpl in equiv1. destruct equiv1 as [j_eq_j0 fhead_eq_ghead].
    destruct h as [ | k0 k1 hhead htail]; [ now apply False_rect |].
    simpl; simpl in equiv2; destruct equiv2 as [j1_eq_k1 gtail_eq_htail].
    unshelve esplit; [ exact (eq_trans j_eq_j0 j1_eq_k1) | |].
    - destruct j1_eq_k1, p, q, j_eq_j0.
      unfold Logic.transport_r in *.
      simpl Logic.transport in *. now apply (@Equivalence_Transitive _ _ _ _ ghead).
    - unshelve eapply IHftail; [ exact gtail | assumption | assumption ].
  Defined.

  Proposition tlist'_quiver_equiv_symmetric (k i j: G) (p : i = j) : 
    forall (f : tlist edges i k) (g: tlist edges j k),
      tlist'_quiver_equiv k i j f g p -> tlist'_quiver_equiv k j i g f (eq_sym p).
  Proof.
    intro f; revert j p; induction f as [| i0 i1 fhead ftail];
      intros j p g; destruct g as [|j0 j1 ghead gtail].
    - unfold tlist'_quiver_equiv. intro H.
      rewrite H at 2. unfold Logic.transport_r. simpl.
      clear H. destruct p. reflexivity.
    - intro H; simpl in H. apply False_rect. destruct p; simpl in H.
      inversion H.
    - now apply False_rect.
    - simpl. intros [q e t].
      exists (eq_sym q).
      + simpl. apply Equivalence_Symmetric. destruct p, q. simpl in *.
        assumption.
      + now apply IHftail, t.
  Defined.

  Definition tlist_quiver_equiv (i k : G) : crelation (tlist edges i k) :=
    fun f g => tlist'_quiver_equiv _ _ _ f g eq_refl.

#[export]
  Instance tlist_quiver_equiv_is_equiv (i k : G) : Equivalence (tlist_quiver_equiv i k).
  Proof.
    unshelve eapply Build_Equivalence.
    + intro; apply tlist'_quiver_equiv_reflexive.
    + intros f g H;
      unfold tlist_quiver_equiv; change (@eq_refl _ i) with (eq_sym (@eq_refl _ i));
      apply tlist'_quiver_equiv_symmetric; exact H.
    + intros f g h equiv1 equiv2. unfold tlist_quiver_equiv.
      change (@eq_refl _ i) with (eq_trans (@eq_refl _ i) (@eq_refl _ i)).
      unshelve eapply tlist'_quiver_equiv_transitive; [ exact g | |]; assumption.
  Defined.
End Quiver.

Definition Build_Quiver_Standard_Eq ( node_type : Type )
  ( edge_type : node_type -> node_type -> Type ) : Quiver :=
  {|
    nodes := node_type ;
    edges := edge_type;
    edgeset := fun _ _ => {| equiv := eq; setoid_equiv := eq_equivalence |}                       
  |}.

Class QuiverHomomorphism@{o1 h1 p1 o2 h2 p2}
  (G : Quiver@{o1 h1 p1}) (G' : Quiver@{o2 h2 p2}) := {
    fnodes : @nodes G -> @nodes G';
    fedgemap : ∀ x y : @nodes G, edges x y -> edges (fnodes x) (fnodes y);
    fedgemap_respects : ∀ x y,
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      (@equiv@{h1 p1} _ (edgeset _ _))
                      (@equiv@{h2 p2} _ (edgeset _ _))) (@fedgemap x y)
  }.

Coercion fnodes : QuiverHomomorphism >-> Funclass.
Local Existing Instance edgeset.

Section QuiverCategory.
Definition QuiverHomomorphismEquivalence
  (Q : Quiver) (Q' : Quiver) (F G : QuiverHomomorphism Q Q') : Type :=
  { node_equiv : forall x : Q, (@fnodes _ _ F x) = (@fnodes _ _ G x)
        & forall (x y : Q) (f : edges x y),
          let eqx := node_equiv x in
          let eqy := node_equiv y in
          let Ff := @fedgemap _ _ F x y f in
          let Gf := @fedgemap _ _ G x y f in
          (Logic.transport (fun t => edges (F x) t) eqy Ff ≈
             Logic.transport_r (fun t => edges t (G y)) eqx Gf) }.

Proposition QuiverHomomorphismEquivalence_Reflexive (Q Q' : Quiver)
  : Reflexive (QuiverHomomorphismEquivalence Q Q').
Proof.
  intro F. unfold QuiverHomomorphismEquivalence.
  exists (fun _ => eq_refl). reflexivity.
Qed.

Proposition transport_id (C : Category) (c c' : C) (p : c = c') :
  Logic.transport (hom c) p (@id C c) = Logic.transport_r (fun z => hom z c') p (@id C c').
Proof.
  now destruct p.
Defined.

Proposition transport_comp (C : Category) (c d e e' : C) (p : e = e')
  (f : hom c d) (g : hom d e)
  : Logic.transport (hom c) p (g ∘ f) = (Logic.transport (hom d) p g) ∘ f.
Proof.
  now destruct p.
Defined.

Proposition transport_r_comp (C : Category) (c c' d e : C) (p : c = c')
  (f : hom c' d) (g : hom d e)
  : Logic.transport_r (fun z => hom z e) p (g ∘ f) =
      g ∘ (Logic.transport_r (fun z => hom z d) p f).
Proof.
  now destruct p.
Defined.

Proposition transport_comp_mid (C : Category) (c d d' e : C) (p : d = d')
  (f : hom c d) (g : hom d' e)
  : g ∘ (Logic.transport (hom c) p f) =
      (Logic.transport_r (fun z => hom z e) p g) ∘ f.
Proof.
  now destruct p.
Defined.

Proposition QuiverHomomorphismEquivalence_Transitive (Q Q' : Quiver)
  : Transitive (QuiverHomomorphismEquivalence Q Q').
Proof.
  intros F G H
    [F_eq_G_on_obj FG_coherent_transport]
    [G_eq_H_on_obj GH_coherent_transport].
  unfold QuiverHomomorphismEquivalence in *.
  exists (fun x => eq_trans (F_eq_G_on_obj x) (G_eq_H_on_obj x)).
  intros c c' f.
  unfold Logic.transport_r.
  rewrite eq_trans_sym_distr.
  rewrite <- 2! transport_trans.
  rewrite (FG_coherent_transport c c' f).
  unfold Logic.transport_r in *.
  rewrite <- (GH_coherent_transport c c' f).
  rewrite transport_relation_exchange.
  reflexivity.
Qed.

Proposition QuiverHomomorphismEquivalence_Symmetric (Q Q' : Quiver)
  : Symmetric (QuiverHomomorphismEquivalence Q Q').
Proof.
  intros F G [F_eq_G_on_obj FG_coherent_transport].
  simpl in FG_coherent_transport.
  exists (fun x => eq_sym (F_eq_G_on_obj x)).
  simpl.
  intros c c' f. unfold Logic.transport_r in *.
  rewrite eq_sym_involutive.
  specialize FG_coherent_transport with c c' f.
  apply (proper_transport_dom Q' edges _ (F c) (G c) (G c') (F_eq_G_on_obj c)) in
    FG_coherent_transport.
  rewrite transport_trans, eq_trans_sym_inv_l
    in FG_coherent_transport;
    simpl in FG_coherent_transport.
  apply (proper_transport_cod Q' edges _ (G c) (G c') (F c') (eq_sym (F_eq_G_on_obj c'))) in
    FG_coherent_transport.
  rewrite transport_relation_exchange, transport_trans,
    eq_trans_sym_inv_r in FG_coherent_transport;
    simpl in FG_coherent_transport.
  symmetry; exact FG_coherent_transport.
Defined.

Program Definition QuiverId (Q : Quiver) : QuiverHomomorphism Q Q :=
  {|
    fnodes := Datatypes.id;
    fedgemap := fun _ _ => Datatypes.id;
    fedgemap_respects := _
  |}.

Arguments fedgemap {G G' QuiverHomomorphism x y}.

Lemma transport_quiver_dom
  (C D: Type) (ArrC : forall c c' : C, Type) (ArrD : forall d d' : D, Type)
  (Fobj : C -> D) (Fmap : forall c c' : C, (ArrC c c') -> (ArrD (Fobj c) (Fobj c')))
  (c c' d: C) (p : c = c') (f : ArrC c d)
  : Fmap _ _ (Logic.transport (fun z => ArrC z d) p f) =
      Logic.transport (fun z => ArrD z (Fobj d)) (f_equal (Fobj) p) (Fmap _ _ f).
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_quiver_cod
  (C D: Type) (ArrC : forall c c' : C, Type) (ArrD : forall d d' : D, Type)
  (Fobj : C -> D) (Fmap : forall c c' : C, (ArrC c c') -> (ArrD (Fobj c) (Fobj c')))
  (c d d': C) (p : d = d') (f : ArrC c d)
  : Fmap _ _ (Logic.transport (fun z => ArrC c z) p f) =
      Logic.transport (fun z => ArrD (Fobj c) z) (f_equal (Fobj) p) (Fmap _ _ f).
Proof.
  destruct p. reflexivity.
Defined.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Definition QuiverComp {Q1 Q2 Q3: Quiver} (F : Q1 ⇨ Q2) (G : Q2 ⇨ Q3) : Q1 ⇨ Q3.
Proof.
  unshelve refine
    (Build_QuiverHomomorphism Q1 Q3 (Basics.compose (@fnodes _ _ G) (@fnodes _ _ F)) _ _).
  unshelve eapply Build_SetoidMorphism.
  + exact (fun f => (fedgemap (fedgemap f))).
  + cat_simpl.
Defined.

#[export] Instance QuiverHomomorphismEquivalence_IsEquivalence (Q Q': Quiver)
  : @Equivalence (QuiverHomomorphism Q Q') (QuiverHomomorphismEquivalence Q Q') :=
  {|
    Equivalence_Reflexive := QuiverHomomorphismEquivalence_Reflexive Q Q';
    Equivalence_Symmetric := QuiverHomomorphismEquivalence_Symmetric Q Q';
    Equivalence_Transitive := QuiverHomomorphismEquivalence_Transitive Q Q'
  |}.
Local Existing Instance fedgemap_respects.
#[export] Instance QuiverCategory : Category.
Proof.
  unshelve eapply
    (Build_Category'
       QuiverHomomorphism
       QuiverId
       (fun Q1 Q2 Q3 F G => @QuiverComp Q1 Q2 Q3 G F) ).
  + exact (fun Q Q' =>
             {| equiv := QuiverHomomorphismEquivalence Q Q';
               setoid_equiv := QuiverHomomorphismEquivalence_IsEquivalence Q Q'
             |}).
  + intros Q1 Q2 Q3 G1 G2 [G_equiv_on_obj G_arrow_coher]
      F1 F2 [F_equiv_on_obj F_arrow_coher].
    exists (fun x => eq_trans (f_equal (@fnodes _ _ G1) (F_equiv_on_obj x))
                       (G_equiv_on_obj (F2 x))).
    intros x y f; simpl in *.
    unfold Logic.transport_r in *.
    rewrite eq_trans_sym_distr.
    rewrite <- 2! transport_trans.
    rewrite <- (G_arrow_coher _ _ (fedgemap f)).
    rewrite <- transport_relation_exchange.
    rewrite eq_sym_map_distr.
    rewrite <- 2! transport_f_equal.
    apply (proper_transport_cod _ edges _ (G1 (F1 x)) _ _ (G_equiv_on_obj (F2 y))).
    rewrite transport_f_equal.
    rewrite <- transport_quiver_cod.
    rewrite (F_arrow_coher _ _ f).
    rewrite (transport_f_equal _ _ (fun b => edges b (G1 (F2 y)))).
    rewrite <- transport_quiver_dom.
    apply fedgemap_respects.
    reflexivity.
  + intros x y f; now exists (fun x =>  eq_refl). 
  + intros x y f; now exists (fun x =>  eq_refl). 
  + intros w x y z f g h; now exists (fun x => eq_refl). 
Defined.
End QuiverCategory.

Section Underlying.
  Universes o h p.

  Program Definition QuiverOfCat (C : Category@{o h p}) : Quiver@{o h p} :=
    {|
      nodes     := obj;
      edges     := hom
    |}.
  Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
  Program Definition QuiverHomomorphismOfFunctor
    (C D: Category) (F : @Functor C D) : (QuiverOfCat C) ⇨ (QuiverOfCat D).
  unshelve eapply Build_QuiverHomomorphism.
  - exact fobj.
  - exact (@fmap C D F).
  - exact fmap_respects.
  Defined.

  Definition Forgetful : @Functor StrictCat QuiverCategory.
  Proof.
    unshelve eapply Build_Functor.
    + exact QuiverOfCat.
    + exact QuiverHomomorphismOfFunctor.
    + intros x y f g f_eq_g. destruct f_eq_g as [fg_eq_on_obj arrow_coherence].
      exists fg_eq_on_obj. simpl; intros c c' k.
      apply arrow_coherence.
    + intro C. exists (fun x => eq_refl). now trivial.
    + intros x y z f g. exists (fun x => eq_refl). now trivial.
  Defined.

End Underlying.

Section Free.
  Universes o h p.
  Context (G : Quiver@{o h p}).

  Arguments Logic.transport_r /.
  Program Definition FreeOnQuiver : Category@{o h p} :=
    {|
      obj     := @nodes G;
      hom     := tlist edges;
      homset  := fun i j => {| equiv := tlist_quiver_equiv _ _ _  ;
                              setoid_equiv := tlist_quiver_equiv_is_equiv _ _ _ |};
      id      := fun _ => tnil;
      compose := fun _ _ _ f g => g +++ f
|}.
Next Obligation.
  revert z x0 y0 X y1 X0.
  induction x1.
  - intros z f g f_eq_g ghead H.
    unfold tlist_quiver_equiv in H.
    unfold tlist'_quiver_equiv in H. simpl in H. destruct H.
    destruct (eq_sym (tlist_app_tnil_l f)).
    destruct (eq_sym (tlist_app_tnil_l g)).
    assumption.
  - intros z f g f_eq_g ghead H.
    destruct (tlist_app_comm_cons b x1 f).
    unfold tlist_quiver_equiv.
    destruct ghead as [| i k e ghead]; [ now apply False_rect| ].
    destruct (tlist_app_comm_cons e ghead g).
    simpl tlist'_quiver_equiv. unfold tlist_quiver_equiv in H.
    simpl in H. destruct H as [q tr t]; exists q; [ exact tr |].
    unfold tlist_quiver_equiv in IHx1. destruct q.
    apply IHx1; [ exact f_eq_g | exact t ].
  Defined. 
  Next Obligation. rewrite tlist_app_tnil_r. apply Equivalence_Reflexive. Qed.
  Next Obligation. rewrite tlist_app_tnil_l. apply Equivalence_Reflexive. Qed.
  Next Obligation. rewrite tlist_app_assoc. apply Equivalence_Reflexive.  Qed.
  Next Obligation. rewrite tlist_app_assoc. apply Equivalence_Reflexive.  Qed.
  
  Definition InducedFunctor {C : Category} 
    (F : QuiverHomomorphism G (QuiverOfCat C)) : @Functor (FreeOnQuiver) C.
  Proof.
    unshelve eapply Build_Functor. 
    { change obj[C] with (@nodes (QuiverOfCat C)). exact fnodes. }
    { intros c c'; simpl; intro f; unfold tlist in f.
      induction f as [| c c_mid fhead ftail IHftail] ; [ exact id | ].
      refine (compose IHftail _).
      change _ with (@edges (QuiverOfCat C) (fnodes c) (fnodes c_mid)).
      exact (fedgemap _ _ fhead). }
    { intros c1 c2; simpl; intro f; induction f as [| c1 c_mid fhead ftail IHf].
      - intros a H; simpl in H; unfold tlist_quiver_equiv, tlist'_quiver_equiv in H. 
        simpl in H; destruct H; reflexivity.
      - intros g H. unfold tlist_quiver_equiv in H.
        destruct g; [ now apply False_rect |].
        simpl in H. destruct H as [q t t0]. simpl.
        set (zm := tlist'_rect G edges c2 _ _ _) in *; clearbody zm.
        destruct q.
        refine (@compose_respects C
                  (@fnodes _ _ F i)
                  (@fnodes _ _ F c_mid)
                  (@fnodes _ _ F c2)
                  (zm c_mid ftail)
                  (zm c_mid g)
                  _
                  ((@fedgemap _ _ F) i c_mid fhead)
                  ((@fedgemap _ _ F) i c_mid e)
                  _   ).
        + apply IHf. assumption.
        + apply (@fedgemap_respects _ _ F). exact t.
    }
    { reflexivity. }
    { intros c1 c2 c3 f g. simpl.
      induction g.
      + simpl. destruct (eq_sym (tlist_app_tnil_l f)).
        apply Equivalence_Symmetric, id_right.
      + destruct (tlist_app_comm_cons b g f); simpl.
        set (zm := tlist'_rect _ _ _ _ _ _) in *.
        rewrite comp_assoc; set (k := fedgemap _ _ _).
        change (edges _  _ ) with (@hom _ ((@fnodes _ _ F) i) ((@fnodes _ _ F) j)) in k.
        refine  (compose_respects _ _ _ k k _); [ apply IHg | reflexivity]. }
  Defined.

  Definition UnitQuiverCatAdjunction :
    QuiverHomomorphism G (QuiverOfCat (FreeOnQuiver)).
  Proof.
    unshelve eapply Build_QuiverHomomorphism.
    { exact Datatypes.id. }
    { exact (fun x y f => tlist_singleton f). }
    { intros x y p q; unfold tlist_singleton;
        simpl; unfold tlist_quiver_equiv, tlist'_quiver_equiv;
        intros ?; exists eq_refl; [assumption | reflexivity]. }
  Defined.
  
  Definition UniversalArrowQuiverCat : @UniversalArrow QuiverCategory StrictCat  G Forgetful.
    unshelve eapply universal_arrow_from_UMP.
    - exact FreeOnQuiver.
    - exact UnitQuiverCatAdjunction.
    - intros C F; unshelve esplit.
      + exact (InducedFunctor F).
      + simpl. exists (fun z => eq_refl). simpl. intros; now rewrite id_left.
      + intros S [FS_eq_on_obj FS_arrow_coherence]; simpl in FS_arrow_coherence.
        exists FS_eq_on_obj.
        intros x y f. induction f.
        * change (@tnil _ _ y) with (@id FreeOnQuiver y).
          simpl; rewrite fmap_id. rewrite transport_id; reflexivity.
        * change (fmap[InducedFunctor F] (b ::: f)) with
            ((fmap[InducedFunctor F] f) ∘ (@fedgemap _ _ F _ _ b)).
          assert (RW : @equiv (@hom FreeOnQuiver i y) _ (b ::: f)
                         (@compose FreeOnQuiver _ _ _ f (tlist_singleton b)))
                   by 
                   (unfold tlist_singleton; simpl; now rewrite <- tlist_app_cons);
          rewrite RW, fmap_comp.
          rewrite transport_comp.
          rewrite IHf.
          rewrite <- transport_comp_mid.
          rewrite transport_r_comp.
          apply compose_respects; [ reflexivity |].
          apply FS_arrow_coherence.
  Defined.
End Free.

Definition FreeCatFunctor : @Functor QuiverCategory StrictCat :=
  (LeftAdjointFunctorFromUniversalArrows Forgetful
     (fun _ => @UniversalArrowQuiverCat _ )).

Definition FreeForgetfulAdjunction : Adjunction FreeCatFunctor Forgetful :=
  AdjunctionFromUniversalArrows _ _ .

Section FreeQuiverSyntax.
Context {G : Quiver}.

Inductive Mor : nodes → nodes → Type :=
  | Ident {x} : Mor x x
  | Morph {x y} (f : edges x y) : Mor x y
  | Comp  {x y z} (f : Mor y z) (g : Mor x y) : Mor x z.

Fixpoint morDA `(t : Mor x y) : tlist edges x y :=
  match t with
  | Ident => tnil
  | Morph f => tcons _ f tnil
  | Comp f g => morDA g +++ morDA f
  end.

Program Instance Mor_Setoid {x y} : Setoid (Mor x y) := {
  equiv f g := morDA f = morDA g
  }.
Next Obligation. equivalence; congruence. Qed.

Fixpoint tlistDA `(t : tlist edges x y) : Mor x y :=
  match t with
  | tnil => Ident
  | tcons _ f fs => Comp (tlistDA fs) (Morph f)
  end.

Lemma morDA_tlistDA `{f : tlist edges x y} :
  morDA (tlistDA f) = f.
Proof.
  induction f; simpl; auto.
  rewrite <- tlist_app_cons.
  now rewrite IHf.
Qed.

(* While this is merely an equivalence. Such is the essence of adjointness
   between pseudocategories. *)
Lemma tlistDA_morDA `{f : Mor x y} :
  tlistDA (morDA f) ≈ f.
Proof.
  induction f; simpl; auto.
  rewrite <- IHf1, <- IHf2.
  now rewrite morDA_tlistDA.
Qed.

Program Definition FreeSyntax : Category := {|
  obj     := nodes ;
  hom     := Mor;
  homset  := @Mor_Setoid;
  id      := fun _ => Ident;
  compose := fun _ _ _ => Comp
|}.
Next Obligation. simpl. congruence. Qed.
Next Obligation. now apply tlist_app_tnil_r. Qed.
Next Obligation. now apply tlist_app_assoc. Qed.
Next Obligation. now symmetry; apply tlist_app_assoc. Qed.

End FreeQuiverSyntax.
