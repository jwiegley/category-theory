Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Let C be a category, let x, y : Obj(C), and let x -> [f0 ; f1 ; f2 ... fn] -> y and 
   x -> [g0 ; g1 ; ... ; gm] -> y be two chains of composable paths in C. 
   When are these paths equivalent?

   There are two answers that seem reasonable to me: 
   1. n = m; cod f0 = cod g0; cod f1 = cod g1, ..., dom fn = dom gn, and f0 = g0, f1 = g1, ...
   2. n = m, and there is a system of isomorphisms cod f0 ≅ cod g0, cod f1 ≅ cod g1,... 
   dom fn = dom gn, such that everything in sight commutes. *)

(** The first answer is simpler but is also categorically "evil" in the sense that one
   must compare objects up to equality.  The second answer seems more compatible with the
   general paradigm that isomorphic objects in a category should be identified.*)

(** In (1.) and (2.) different amounts of structure on the objects and arrows are
   necessary to define these notions.
   In (1.), one only needs the type of objects and the
   type of arrows, where the arrow types are perhaps setoids, in other words a directed
   graph or quiver. *)

(** In (2.), one needs in addition a distinguished notion of an isomorphism between
   objects, so that one can talk about transporting the arrows along the isomorphism.
   Thus the structure required in order for the equivalence in (2.) to make sense is that
   we have a groupoid A and a functor A^op x A -> Sets.  One could call this structure an
   "endoprofunctor on a groupoid."  I will call it a "groupoid quiver."  One can regard a
   groupoid as simply a well-behaved setoid, i.e. it is a setoid with additional properties.
*)

Section Quiver.
  Class Quiver@{o h p} := {
      nodes :> Type@{o};
      uedges := Type@{h} : Type@{h+1};
      edges : nodes → nodes → uedges;
      edgeset : ∀ X Y, Setoid@{h p} (edges X Y)
    }.
  Coercion nodes : Quiver >-> Sortclass.
  Context (G : Quiver).
  Existing Instance edgeset.
  Check tlist'.

  Fixpoint tlist'_quiver_equiv (k i j : G) 
    (f : @tlist' _ edges k i) (g : @tlist' _ edges k j) ( p : i = j ) : Type :=
    match f in (tlist' _ i_t) return (tlist' _ j) -> i_t = j -> Type with
    | tnil => fun g' _ => match g' with
                          | tnil => True
                          | _ => False
                          end
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
  
  Proposition tlist'_quiver_equiv_reflexive (k i: G) :
    forall f : tlist edges i k, tlist'_quiver_equiv k i i f f eq_refl.
  Proof.
    intro f; induction f; [ now constructor |].
    unshelve econstructor; easy.
  Defined.

  Proposition tlist_quiver_equiv'_transitive (k i1 i2 i3: G) :
      forall (f : tlist edges i1 k) (g : tlist edges i2 k) (h : tlist edges i3 k)
             (p : i1 = i2) (q : i2 = i3),
        tlist'_quiver_equiv k i1 i2 f g p ->
        tlist'_quiver_equiv k i2 i3 g h q->
        tlist'_quiver_equiv k i1 i3 f h (eq_trans p q).
  Proof.
    intro f; revert i2 i3.
    induction f as [ | i0 i1 fhead ftail ]; 
      [ intros; destruct g; [ easy | now apply False_rect ] |].
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
  
End Quiver.

Section GroupoidQuiver.
  (* Coercion catOfGroupoid : Groupoid >-> Category. *)
  (* Class GroupoidQuiver (C : Groupoid) := { gq_edges : @Functor (C^op ∏ C) Sets }. *)
  (* Existing Instance all_are_iso. *)
  (* Context (C : Groupoid). *)
  (* Context (GC : GroupoidQuiver C). *)
  (* Let gq_edges' := fun i j : C => gq_edges (i,j). *)
  (* (*     transport_head {X Y Z} : X ≈ Z -> edges X Y -> edges Z Y; *) *)
  (* Let transport_head {X Y Z} : X ≈ Z -> gq_edges' X Y -> gq_edges' Z Y. *)
  (* Proof. *)
  (*   intros f; simpl; unfold gq_edges'; intro g.  *)
  (*   unshelve eapply (fmap[gq_edges]). *)
  (*   { apply (X,Y). } *)
  (*   { split; simpl; [apply (@two_sided_inverse _ _ _ f _) | apply id]. } *)
  (*   exact g. *)
  (* Defined. *)
      
(* Class GroupoidQuiver (G : Groupoid) := { edges : @Functor (G^op ∏ G) Sets }. *)

Definition Build_Quiver_Standard_Eq ( node_type : Type )
  ( edge_type : node_type -> node_type -> Sets ) : Quiver (path_groupoid node_type).
Proof.
  unshelve eapply Build_Quiver.
  unshelve eapply Build_Functor.
  { intro xy; destruct xy as [x y]; exact (edge_type x y). }
  { intros [x1 x2] [y1 y2]; simpl in *. intros [eq1 eq2]; destruct eq1, eq2.
    unshelve econstructor; [ exact (fun x => x) | easy]. }
  { intros [x1 x2] [y1 y2] [eq1 eq2]; simpl in *; destruct eq1, eq2.
    intros [? ?]; simpl; intros [eq1 eq2]; simpl.
    rewrite <- eq1, <- eq2. intro x; reflexivity. }
  { intros [x1 x2]. simpl in *. reflexivity. }
  { intros [x1 x2] [y1 y2] [z1 z2] [eq1 eq2] [eq3 eq4] f. simpl in *.
    destruct eq1, eq2, eq3, eq4; reflexivity. }
Defined.

(* {| *)
  (*   nodes := node_type ; *)
  (*   nodeset := {| equiv := eq ; setoid_equiv := eq_equivalence |}; *)
  (*   edges := edge_type; *)
  (*   edgeset := fun _ _ => {| equiv := eq; setoid_equiv := eq_equivalence |}                        *)
  (* |}. *)
Print Build_Quiver_Standard_Eq.

(* Class Quiver@{o h p} : Type@{max(o+1,h+1,p+1)} := { 
(*     nodes : Type@{o}; *)
(*     nodeset : Setoid@{o p} nodes; *)
(*     uedges := Type@{h} : Type@{h+1}; *)
(*     edges : nodes → nodes → uedges; *)
(*     edgeset : ∀ X Y, Setoid@{h p} (edges X Y); *)
(*     transport_head {X Y Z} : X ≈ Z -> edges X Y -> edges Z Y; *)
(*     transport_tail {X Y Z} : Y ≈ Z -> edges X Y -> edges X Z; *)
(*     transport_head_respects_equiv : *)
(*     ∀ Y : nodes, equiv_transport nodes nodeset (fun X => edges X Y) _ *)
(*                    (fun X => @transport_head X Y); *)
(*     transport_tail_respects_equiv : *)
(*     ∀ X : nodes, equiv_transport nodes nodeset (edges X) _ *)
(*                    (@transport_tail X); *)
(*     transport_coherent : *)
(*     ∀ X1 Y1 X2 Y2, ∀ f : edges X1 Y1, *)
(*     ∀ equivX : X1 ≈ X2, ∀ equivY : Y1 ≈ Y2, *)
(*       transport_tail equivY (transport_head equivX f) ≈ *)
(*         transport_head equivX (transport_tail equivY f) *)
(*   }. *)

Local Existing Instance nodeset.
Local Existing Instance edgeset.
(* A constructor for quivers when equality is the standard equality everywhere.  *)
  
Program Definition Build_Quiver_Standard_Eq ( node_type : Type )
  ( edge_type : node_type -> node_type -> Type ) : Quiver :=
  {|
    nodes := node_type ;
    nodeset := {| equiv := eq ; setoid_equiv := eq_equivalence |};
    edges := edge_type;
    edgeset := fun _ _ => {| equiv := eq; setoid_equiv := eq_equivalence |}                       
  |}.
Print Build_Quiver_Standard_Eq.

Coercion nodes : Quiver >-> Sortclass.

Class QuiverHomomorphism@{o1 h1 p1 o2 h2 p2}
  (G : Quiver@{o1 h1 p1}) (G' : Quiver@{o2 h2 p2}) := {
    fnodes : @nodes G -> @nodes G';
    nodemap_respects :
    Proper@{o1 o2} (respectful@{o1 _ _ o2 _ _ } (@equiv@{o1 o1} _ (nodeset))
                           (@equiv@{o2 o2} _ (nodeset))) fnodes;
    fedgemap : ∀ x y : @nodes G, edges x y -> edges (fnodes x) (fnodes y);
    fedgemap_respects : ∀ x y,
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      (@equiv@{h1 p1} _ (edgeset _ _))
                      (@equiv@{h2 p2} _ (edgeset _ _))) (@fedgemap x y)
  }.

Section Free.
  Universes o h p.
  Context (G : Quiver@{o h p}).
  Check (@equiv _ nodeset).

    (*   transport_head {X Y Z} : X ≈ Z -> edges X Y -> edges Z Y; *)
    (* transport_tail {X Y Z} : Y ≈ Z -> edges X Y -> edges X Z; *)

  Inductive tlist_quiver_equiv' (k : G) : forall i j : G,
      i ≈ j -> (tlist edges i k) -> (tlist edges j k) -> Type :=
  | tlist_equiv_nil : tlist_quiver_equiv' k k
                        (Equivalence_Reflexive k) tnil tnil
  | tlist_equiv_cons :
    forall (i i' j j' : G) (p : i ≈ j) (q : i' ≈ j')
           (fhead : edges i i') (ftail : tlist edges i' k)
           (ghead : edges j j') (gtail : tlist edges j' k),
      transport_head p (transport_tail q fhead) ≈ ghead ->
      (tlist_quiver_equiv' i' j' q ftail gtail) ->
      tlist_quiver_equiv' i j p (tcons _ fhead ftail) (tcons _ ghead gtail).

  Definition tlist_quiver_equiv (i k : G) :=
    tlist_quiver_equiv' k i i (Equivalence_Reflexive i).

  Proposition tlist_quiver_equiv'_reflexive (i j k : G)
    (p : i ≈ j) (f : tlist edges i k) (g : tlist edges j k) :
    (tlist_quiver_equiv' k) i j p f g ->
    (tlist_quiver_equiv' k) j i (Equivalence_Symmetric _ _ p) g f.
  Proof.
    intro H. induction H.
    {
      
      unshelve eapply (@tlist_equiv_nil k).
        
  
  Program Definition FreeOnQuiver@{fo fh fp} : Category@{fo fh fp} :=
    {|
      obj     := @nodes G;
      hom     := tlist edges;
      homset  := fun i j => {| equiv := tlist_quiver_equiv  |};
      id      := fun _ => tnil;
      compose := fun _ _ _ f g => g +++ f
|}.
  
Next Obligation. equivalence; congruence. Qed.
Next Obligation. now apply tlist_app_tnil_r. Qed.
Next Obligation. now apply tlist_app_assoc. Qed.  
Next Obligation. symmetry; now apply tlist_app_assoc. Qed.  
End Free.

Section Underlying.
  Universes o h p.
  Context (C : Category@{o h p}).
  Program Definition QuiverOfCat@{fo fh} : Quiver@{fo fh} := {|
  nodes     := obj;
  edges     := hom
                                                            |}.
End Underlying.

Definition InducedFunctor {G : Quiver} {C : Category} 
  (F : QuiverHomomorphism G (QuiverOfCat C)) :   @Functor (FreeOnQuiver G) C.
Proof.
  unshelve eapply Build_Functor.
  { change obj[C] with (@nodes (QuiverOfCat C)). exact fnodes. }
  { intros x y; simpl; intro f; induction f as [nil | i j k f g IHg];
      [ exact id | refine (compose IHg _); exact (fedges i j f)]. }
  { cat_simpl. }
  { reflexivity. }
  { intros ? ? ? ? g; simpl; induction g;
      [ now cat | rewrite <- tlist_app_comm_cons; simpl;
                  rewrite comp_assoc, <- IHg; reflexivity ]. }
Defined.

Definition UnitQuiverCatAdjunction (Q : Quiver) :
  QuiverHomomorphism Q (QuiverOfCat (FreeOnQuiver Q)).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  { exact Datatypes.id. }
  { exact (fun x y f => @tcons _ _ x y y f (tnil)). }
Defined.
                                 
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
