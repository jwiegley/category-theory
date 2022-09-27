Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Class Quiver@{o h} : Type@{max(o+1,h+1)} := {
    nodes : Type@{o};
    uedges := Type@{h} : Type@{h+1};
    edges : nodes → nodes → uedges
  }.

Coercion nodes : Quiver >-> Sortclass.


Class QuiverHomomorphism (G G' : Quiver) := {
    fnodes : @nodes G -> @nodes G';
    fedges : ∀ x y : @nodes G, edges x y -> edges (fnodes x) (fnodes y)
  }.

Section Free.
  Universes o h.
  Context (G : Quiver@{o h}).
  
  Program Definition FreeOnQuiver@{fo fh} : Category@{fo fh fh} := {|
  obj     := nodes;
  hom     := tlist edges;
  homset  := fun _ _=> {| equiv := eq |};
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

Definition InducedFunctor (G : Quiver) (C : Category)
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
