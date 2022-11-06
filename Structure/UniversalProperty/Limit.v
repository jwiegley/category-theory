Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Hom.Yoneda.

Section LimitUniversalProperty.
  Context (J C : Category).
  Context (F : J ⟶ C).

  Definition ump_limit_construct (a z : C) (H : IsALimit F z) :
      ACone a F -> a ~> z.
  Proof.
    destruct H.
    intro m; specialize ump_limit with {| vertex_obj := a ; coneFrom := m |}.
    destruct ump_limit as [unique_obj ? ?].
    exact unique_obj.
  Defined.

  Proposition ump_limit_construct_proper (a z : C) (H : IsALimit F z) :
    Proper (equiv ==> equiv) (ump_limit_construct a z H).
  Proof.
    repeat(intro).
    unfold ump_limit_construct.
    apply uniqueness. simpl.
    intro j.
    set (k := (unique_property (ump_limit {| vertex_obj := a ; coneFrom := y |}))).
    destruct x, y; simpl in X.
    simpl in *; rewrite X; apply k.
  Qed.

  Local Arguments vertex_map {J C c F}.
  Proposition ump_limit_construct_recover (w z : C) (H : IsALimit F z) (m : obj[J])
     (a : ACone w F) : vertex_map limit_acone m ∘ (ump_limit_construct w z _ a) ≈ vertex_map a m.
  Proof.
    unfold ump_limit_construct. simpl. 
    exact (unique_property (ump_limit {| vertex_obj := w; coneFrom :=a |} ) _).
  Qed.

  Create HintDb limit discriminated.
  Hint Resolve ump_limit_construct : limit.
  Hint Resolve ump_limit_construct_proper : limit.
    
  Notation next_field X
    := ltac:(let c := type of X in match c with forall _ : ?A, _  => exact A end).

  Let limit_is_univ_property :=
        Build_IsUniversalProperty C^op
         (fun c => IsALimit F c)
         (fun c => @LimitSetoid J C F c)
         (@ConePresheaf J C F).
  Section allC.
    Context (z : C).
    Let master_iso := Eval hnf in ltac:(
                      (let A := (eval hnf in (next_field limit_is_univ_property)) in
                       match A with
                       | forall a : _, @?B a => exact(B z)
                       end)).
    (* master_iso := IsALimit F z ≊ fobj[C^op] z ≅ ConePresheaf F *)

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
    
    (* Ltac by_limit_ump := *)
    (*   match goal with *)
    (*   | [ H : IsALimit ?F ?c |- hom ?a ?c ] => *)
    (*       apply  *)
    Print vertex_map.
    Local Arguments vertex_map {J C c F}.
    Proposition limit_to_representable : master_iso_to_underlying.
    Proof using Type.
      unfold master_iso_to_underlying; clear master_iso_to_underlying.
      clear Build_to master_iso_to master_iso Build_Iso limit_is_univ_property.
      simpl. intro A.
      unshelve econstructor.
      - apply (from (Yoneda_Lemma C (ConePresheaf F) z)).
        exact limit_acone.
      - simpl; unshelve econstructor.
        + simpl; intro c; unshelve econstructor; auto with limit.
        + simpl. intros c' c f L.
          symmetry; apply uniqueness.
          intro m; simpl.
          (* If L is a cone c' -> F, and I pull it back along f : c -> c',
             
          
          Locate Unique.
            
