Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.

#[export] Hint Extern 1 => reflexivity : core.

Ltac compose_reduce :=
  multimatch goal with
  | [ f : @hom ?C ?x ?y  |- @hom ?C ?x ?z ] => refine (@compose C x y z _ f)
  | [ f : @hom ?C ?y ?z  |- @hom ?C ?x ?z ] => apply (@compose C x y z f)
  end.

Create HintDb cat discriminated.

#[export]
Hint Extern 1 (@hom _ _ _) => compose_reduce : cat.

Ltac apply_setoid_morphism := 
  match goal with
  | [ H : context[SetoidMorphism ] |- _ ] =>  apply H
  end.

#[export]
Hint Extern 20 => apply_setoid_morphism : cat.

(* This is tempting but the "proper" script calls
   intuition, which calls auto with *, so "proper" 
   should probably be a top-level command only. *)
(* Hint Extern 1 (Proper _ _) => proper : cat. *)
(* Similarly with cat_simpl. *)
(* Hint Extern 20 => progress(cat_simpl) : cat. *)
(* Hint Extern 40 (@hom _ _ _) => hom_to_homset : cat. *)
#[export] Hint Immediate id : cat.

Ltac split_exists := unshelve eapply existT.
#[export] Hint Extern 1 (@sigT _ _) => split_exists : cat.

Ltac functor_simpl :=
  match goal with
  | [ |- context[@fobj _ _ (Build_Functor _ _ _ _ _ _ _)]] => unfold fobj
  | [ |- context[@fmap _ _ (Build_Functor _ _ _ _ _ _ _)]] => unfold fmap
  end.
#[export] Hint Extern 10 => functor_simpl : cat.
#[export] Hint Extern 10 (hom _ _ _) => progress(simpl hom) : cat.
#[export] Hint Extern 40 => progress(cbn in *) : cat.
#[export] Hint Extern 4 (SetoidMorphism _ _) => unshelve eapply Build_SetoidMorphism : cat.
#[export] Hint Extern 4 (hom _ (_ × _)) => apply fork : cat.
#[export] Hint Unfold forall_relation : cat.
#[export] Hint Extern 1 (@equiv _ _ _ _) => reflexivity : cat.
#[export] Hint Extern 1 (@equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _))
     => simple apply compose_respects : cat.

Ltac compose_respects_script :=
first [repeat(rewrite <- comp_assoc);
       apply compose_respects; try(reflexivity)
      |repeat(rewrite -> comp_assoc);
       apply compose_respects; try(reflexivity)].

#[export] Hint Extern 20 (@equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _))
     => compose_respects_script : cat.    

#[export] Hint Extern 10 => progress(autorewrite with categories) : cat.
#[export] Hint Extern 5 => (progress(simplify)) : cat.
#[export] Hint Rewrite <- @comp_assoc : categories.
Ltac unfold_proper :=
  match goal with
  | [ H : Proper _ ?f |- ?f _ ≈ ?f _ ] => unfold Proper, "==>" in H; simpl in H; assert (QQ:= H)
  | [ H : Proper _ ?f |- ?f _ _ ≈ ?f _ _ ] => unfold Proper, "==>", forall_relation in H;
                                              simpl in H; assert (QQ:= H)
  end; solve [auto with cat].
#[export] Hint Extern 4 (@equiv _ _ (?f _) (?f _)) => unfold_proper : cat.

