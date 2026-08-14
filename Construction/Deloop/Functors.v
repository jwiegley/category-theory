Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Functors out of a delooping: homomorphisms, actions, representations

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.3
    (printed p. 15), Exercise 3(b,c) [maclane:I.3:ex3]: a functor between
    two groups regarded as one-object categories is a group homomorphism;
    a functor from a group to Set is a permutation representation, and to
    [Matr_K] a matrix representation.
    Awodey, "Category Theory", §4.3 (printed p. 86)
    [awodey:4.3:remark-functor-group-hom, awodey:4.3:def-representation]:
    the same identification, and representations as functors out of the
    delooping; §7.1 (printed p. 154)
    [awodey:7.1:construction-poset-to-group]: a functor from a poset to a
    group is exactly a unit-and-composition-respecting family g_{p,q} —
    a cocycle.
    Riehl, "Category Theory in Context", §1.3: Example 1.3.9
    [riehl:1.3:example9] (actions as functors, with the left/right
    convention), Corollary 1.3.10 [riehl:1.3:cor10] (each group element
    acts by an automorphism, inverses mapping to inverses), Exercise
    1.3.i [riehl:1.3:exi] (functors between groups).

    Everything is developed over Construction/Deloop.v's [MonObject] and
    [GrpObject] and its delooping [Deloop M].  The homomorphism record
    is Structure/Groupoid.v's [MonHom] (with [MonIso] for isomorphisms),
    and group statements are the monoid statements read at a
    [GrpObject]: the extra content — homomorphisms preserve inverses —
    is that file's THEOREM [MonHom_grp_inv], by uniqueness of inverses,
    the same derivation pattern as Instance/Ab.v's and
    Theory/Algebra/Rig.v's negation-preservations.  Part (b) itself is
    likewise already in tree: Construction/Deloop/Transform.v's
    [Deloop_map]/[Deloop_unmap], whose homomorphism-side round trip
    [Deloop_unmap_map] holds as an EQUALITY OF RECORDS — nothing here
    re-proves either.

    THE SPINE is one general correspondence: functors [Deloop M ⟶ C]
    are the same as a choice of object c : C together with a monoid
    homomorphism [M → hom_monoid C c] into Deloop.v's endomorphism
    monoid ([functor_of_hom_monoid] / [hom_monoid_of_functor], with
    round trips).  Every part of the exercise specializes it:

      - C := Deloop N (part b): the object choice is forced, and
        Transform.v's [Deloop_map] IS the spine at that single object
        ([Deloop_map_spine]; the types agree definitionally by
        Deloop.v's [hom_monoid_Deloop]); what Transform.v states only
        pointwise — its functor-side round trip is [eq_refl] on [fmap]
        and propositional on [fobj] — is completed here to a full
        [Functor_Setoid] natural isomorphism ([Deloop_functor_round]);
      - C := Sets (part c, permutation representations): unfolded into
        the friendlier [MSetoidAction] record — a monoid acting on a
        setoid — with the correspondence both ways
        ([action_of_functor] / [functor_of_action]); at a [GrpObject]
        this is Riehl's Example 1.3.9, the LEFT-action convention (a
        left action is a functor out of B G);
      - C := Matr R (part c, matrix representations): [MatrixRep], a
        dimension n together with a homomorphism into the multiplicative
        monoid of n × n matrices — the dimension IS the chosen object
        ([matrix_rep_of_functor] / [functor_of_matrix_rep]).

    RIGHT ACTIONS (Riehl's convention note): a right action is a functor
    out of [(Deloop G)^op], and Construction/Deloop/Opposite.v's
    [Deloop_op] identifies that source with [Deloop (MonObject_op G)],
    so the two translations [right_action_of_op_functor] and
    [op_functor_of_right_action] carry right actions to and from LEFT
    actions of the opposite monoid — the classical statement.  Their
    mutual inversion is NOT stated here: it would combine
    [action_functor_round] with [Deloop_op]'s isomorphism laws and the
    functoriality of [◯] over [Functor_Setoid].

    THE AUTOMORPHISM COROLLARY (Riehl 1.3.10): at a [GrpObject] every
    [fmap] lands in isomorphisms.  Per the issue this is delivered as a
    NAMED INSTANTIATION of Theory/Functor.v's [fobj_iso] at
    [Deloop_group_iso] ([action_automorphism]), with the inverse of the
    action of g being the action of the inverse of g, recorded
    definitionally ([action_automorphism_from]).  As with Deloop.v's
    [Deloop_group_iso], the TYPE [F ttt ≅ F ttt] is inhabited by
    [iso_id] alone; the corollary's content is WHICH isomorphism, i.e.
    the two definitional readings [action_automorphism_to]/[_from].

    THE COCYCLE CHARACTERIZATION (Awodey §7.1): functors from a proset
    into a delooping are exactly proof-irrelevant families g_{p,q}
    satisfying the unit and composition conditions ([Cocycle],
    [cocycle_of_functor] / [functor_of_cocycle], with round trips on
    BOTH sides — [cocycle_round] pointwise, [cocycle_functor_round] up
    to [Functor_Setoid] isomorphism).  The worked witness is
    Awodey's, transposed from ℝ to ℤ to keep the instance layer
    axiom-free (the same substitution Theory/Algebra/Rig.v makes for its
    ring witness): P = (ℤ, ≤), G = (ℤ, +), g_{x,y} = y − x
    ([translation_cocycle]). *)

(** ** Monoid homomorphisms: Structure/Groupoid.v's [MonHom]

    The homomorphism record and its inverse-preservation theorem are
    imported, not redefined: Structure/Groupoid.v's [MonHom_grp_inv]
    already proves (via [mon_inverse_unique]) that a monoid
    homomorphism between groups preserves inverses, which is why
    neither that file nor this one defines a separate class of group
    homomorphisms. *)

(** ** The spine: functors out of a delooping pick an endomorphism
    monoid *)

Section Spine.

Context {M : MonObject}.
Context {C : Category}.

Program Definition functor_of_hom_monoid (c : C)
  (h : MonHom M (hom_monoid C c)) : Deloop M ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ (g : carrier M) => mon_map h g
|}.
Next Obligation.
  intros c h x y f g Hfg; exact (mon_map_respects h _ _ Hfg).
Qed.
Next Obligation. intros c h x; exact (mon_map_unit h). Qed.
Next Obligation. intros c h x y z f g; exact (mon_map_op h f g). Qed.

(* The reverse leg needs no obligations: every homomorphism law is a
   functor law by projection, exactly as in Transform.v's
   [Deloop_unmap] (of which this is the general-codomain form).
   ([Build_MonHom] is applied to explicit arguments for the same reason
   Transform.v's [Deloop_map] applies [Build_Functor] so: the fields
   alone do not determine the record's parameters.) *)
Definition hom_monoid_of_functor (F : Deloop M ⟶ C) :
  MonHom M (hom_monoid C (F ttt)) :=
  @Build_MonHom M (hom_monoid C (F ttt))
    (fun g : carrier M => @fmap _ _ F ttt ttt g)
    (@fmap_respects _ _ F ttt ttt)
    (@fmap_id _ _ F ttt)
    (fun a b => @fmap_comp _ _ F ttt ttt ttt a b).

(* Round trip on the homomorphism side: the same map, pointwise. *)
Lemma hom_monoid_round (c : C) (h : MonHom M (hom_monoid C c))
  (g : carrier M) :
  mon_map (hom_monoid_of_functor (functor_of_hom_monoid c h)) g
    ≈ mon_map h g.
Proof. reflexivity. Qed.

(* Round trip on the functor side: the same functor up to natural
   isomorphism, with identity components. *)
Lemma functor_round (F : Deloop M ⟶ C) :
  functor_of_hom_monoid (F ttt) (hom_monoid_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End Spine.

(** ** Part (b): functors between deloopings are homomorphisms *)

(* Construction/Deloop/Transform.v already proves the dictionary:
   [Deloop_map] / [Deloop_unmap], with the homomorphism-side round trip
   an EQUALITY OF RECORDS ([Deloop_unmap_map], by [eq_refl]) — stronger
   than the pointwise form the spine yields, so nothing is re-proved
   here.  What is added is the two statements Transform.v does not
   make: [Deloop_map] IS the spine at the delooping's single object
   (the types agreeing definitionally by Deloop.v's
   [hom_monoid_Deloop]), and the functor-side round trip in full
   [Functor_Setoid] strength — Transform.v states it only as [eq_refl]
   on [fmap] and a propositional case split on [fobj]
   ([Deloop_map_unmap_fmap]/[_fobj]). *)

Section PartB.

Context {M N : MonObject}.

(* [Deloop_map] is the spine specialized at the single object; the
   homomorphism argument is accepted UNCHANGED, [MonHom M N] and
   [MonHom M (hom_monoid (Deloop N) ttt)] being definitionally the
   same type. *)
Lemma Deloop_map_spine (h : MonHom M N) :
  Deloop_map h ≈ functor_of_hom_monoid (C := Deloop N) ttt h.
Proof.
  exists (fun x => iso_id).
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

(* The functor-side round trip, at [Functor_Setoid] strength. *)
Lemma Deloop_functor_round (F : Deloop M ⟶ Deloop N) :
  Deloop_map (Deloop_unmap F) ≈ F.
Proof.
  unshelve eexists.
  { intro x.
    exact (@Build_Isomorphism (Deloop N) _ _
             (mon_unit : carrier N) (mon_unit : carrier N)
             (mon_op_unit_l mon_unit) (mon_op_unit_l mon_unit)). }
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End PartB.

(** ** Part (c): permutation representations — actions on setoids *)

(* A monoid acting on a setoid; at a [GrpObject] this is a permutation
   representation / G-set (Riehl 1.3.9, left convention: the action law
   is act (g · h) = act g ∘ act h, matching Deloop's composition). *)
Record MSetoidAction (M : MonObject) := {
  act_setoid :> SetoidObject;
  act : carrier M → carrier act_setoid → carrier act_setoid;
  act_respects : Proper (equiv ==> equiv ==> equiv) act;
  act_unit : ∀ x, act mon_unit x ≈ x;
  act_op : ∀ g h x, act (mon_op g h) x ≈ act g (act h x)
}.

Arguments act_setoid {M} _.
Arguments act {M} _ _ _.
Arguments act_respects {M} _.
Arguments act_unit {M} _ _.
Arguments act_op {M} _ _ _ _.

#[export] Existing Instance act_respects.

Section PartC.

Context {M : MonObject}.

Program Definition action_of_functor (F : Deloop M ⟶ Sets) :
  MSetoidAction M := {|
  act_setoid := F ttt;
  act := fun g x => @fmap _ _ F ttt ttt g x;
  act_unit := fun x => @fmap_id _ _ F ttt x;
  act_op := fun g h x => @fmap_comp _ _ F ttt ttt ttt g h x
|}.
Next Obligation.
  intros F g g' Hg x x' Hx.
  rewrite (@fmap_respects _ _ F ttt ttt g g' Hg x).
  exact (proper_morphism (@fmap _ _ F ttt ttt g') _ _ Hx).
Qed.

Program Definition functor_of_action (A : MSetoidAction M) :
  Deloop M ⟶ Sets := {|
  fobj := fun _ => act_setoid A;
  fmap := fun _ _ (g : carrier M) =>
    {| morphism := act A g
     ; proper_morphism := act_respects A g g (Equivalence_Reflexive g) |}
|}.
Next Obligation.
  intros A0 x y f g Hfg p; simpl.
  exact (act_respects A0 f g Hfg p p (Equivalence_Reflexive p)).
Qed.
Next Obligation. intros A0 x p; apply act_unit. Qed.
Next Obligation. intros A0 x y z f g p; apply act_op. Qed.

Lemma action_round (A : MSetoidAction M) (g : carrier M)
  (x : carrier (act_setoid A)) :
  act (action_of_functor (functor_of_action A)) g x ≈ act A g x.
Proof. reflexivity. Qed.

Lemma action_functor_round (F : Deloop M ⟶ Sets) :
  functor_of_action (action_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g x; simpl.
  reflexivity.
Qed.

End PartC.

(** ** Part (c): matrix representations *)

(* A matrix representation: a dimension together with a homomorphism
   into the multiplicative monoid of n × n matrices — the endomorphism
   monoid of n in Matr R.  The dimension IS the chosen object of the
   spine correspondence. *)
Definition MatrixRep (M : MonObject) (R : RigObject) : Type :=
  { n : nat & MonHom M (hom_monoid (Matr R) n) }.

Definition functor_of_matrix_rep {M : MonObject} {R : RigObject}
  (ρ : MatrixRep M R) : Deloop M ⟶ Matr R :=
  functor_of_hom_monoid (C := Matr R) (`1 ρ) (`2 ρ).

Definition matrix_rep_of_functor {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) : MatrixRep M R :=
  (F ttt; hom_monoid_of_functor (C := Matr R) F).

Lemma matrix_rep_dimension {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) :
  `1 (matrix_rep_of_functor F) = F ttt.
Proof. reflexivity. Qed.

(** ** Right actions, along the opposite-monoid identification *)

Section RightActions.

Context {G : MonObject}.

(* Riehl's convention: a right action is a functor out of the OPPOSITE
   of the delooping; [Deloop_op] carries that source to the delooping of
   the opposite monoid, so right actions of G are left actions of
   [MonObject_op G]. *)
Definition right_action_of_op_functor
  (F : (Deloop G)^op ⟶ Sets) : MSetoidAction (MonObject_op G) :=
  action_of_functor (F ◯ from (Deloop_op G)).

Definition op_functor_of_right_action
  (A : MSetoidAction (MonObject_op G)) : (Deloop G)^op ⟶ Sets :=
  functor_of_action A ◯ to (Deloop_op G).

End RightActions.

(** ** Riehl 1.3.10: each group element acts by an automorphism *)

Section Automorphism.

Context {G : GrpObject}.
Context {C : Category}.

(* The named instantiation of [fobj_iso] at the delooped group's
   isomorphisms: the action of g, as an isomorphism of the underlying
   object. *)
Definition action_automorphism (F : Deloop G ⟶ C) (g : carrier G) :
  F ttt ≅ F ttt :=
  fobj_iso F ttt ttt (Deloop_group_iso G ttt ttt g).

(* Its forward leg is the action of g... *)
Lemma action_automorphism_to (F : Deloop G ⟶ C) (g : carrier G) :
  to (action_automorphism F g) ≈ fmap[F] g.
Proof. reflexivity. Qed.

(* ...and its inverse is the action of the inverse of g. *)
Lemma action_automorphism_from (F : Deloop G ⟶ C) (g : carrier G) :
  from (action_automorphism F g) ≈ fmap[F] (grp_inv g).
Proof. reflexivity. Qed.

End Automorphism.

(** ** Awodey §7.1: the cocycle characterization *)

Section Cocycle.

Context {A : Type} {R : relation A} (P : RelationClasses.PreOrder R).
#[local] Existing Instance P.
Context (M : MonObject).

(* A cocycle: an element g_{p,q} for each related pair, independent of
   the witnessing proof (Awodey indexes by the PAIR, and a functor's
   [fmap_respects] forces exactly this over the proset's all-True
   hom-equivalence), with the unit and composition conditions. *)
Record Cocycle := {
  cocycle : ∀ p q : A, R p q → carrier M;
  cocycle_irrel : ∀ p q (h h' : R p q), cocycle p q h ≈ cocycle p q h';
  cocycle_refl : ∀ p,
    cocycle p p (@RelationClasses.PreOrder_Reflexive A R P p) ≈ mon_unit;
  cocycle_trans : ∀ p q r (h : R p q) (k : R q r),
    mon_op (cocycle q r k) (cocycle p q h)
      ≈ cocycle p r
          (@RelationClasses.PreOrder_Transitive A R P p q r h k)
}.

Program Definition functor_of_cocycle (γ : Cocycle) :
  Proset P ⟶ Deloop M := {|
  fobj := fun _ => ttt;
  fmap := fun p q (h : R p q) => cocycle γ p q h
|}.
Next Obligation.
  intros γ p q f g T; exact (cocycle_irrel γ p q f g).
Qed.
Next Obligation. intros γ p; exact (cocycle_refl γ p). Qed.
Next Obligation.
  intros γ x y z g f; symmetry; exact (cocycle_trans γ x y z f g).
Qed.

Program Definition cocycle_of_functor (F : Proset P ⟶ Deloop M) :
  Cocycle := {|
  cocycle := fun p q (h : R p q) => @fmap _ _ F p q h
|}.
Next Obligation.
  intros F p q h h'; exact (@fmap_respects _ _ F p q h h' I).
Qed.
Next Obligation. intros F p; exact (@fmap_id _ _ F p). Qed.
Next Obligation.
  intros F p q r h k; symmetry; exact (@fmap_comp _ _ F p q r k h).
Qed.

Lemma cocycle_round (γ : Cocycle) (p q : A) (h : R p q) :
  cocycle (cocycle_of_functor (functor_of_cocycle γ)) p q h
    ≈ cocycle γ p q h.
Proof. reflexivity. Qed.

(* The functor side, at [Functor_Setoid] strength: the components sit
   over the target's single object, so each is found by case analysis
   on [fobj F x] (a [poly_unit] has no definitional eta, so the match
   is genuine — compare Transform.v's [Deloop_map_unmap_fobj]). *)
Lemma cocycle_functor_round (F : Proset P ⟶ Deloop M) :
  functor_of_cocycle (cocycle_of_functor F) ≈ F.
Proof.
  exists (fun x =>
            match fobj[F] x as u
                  return (@Isomorphism (Deloop M) ttt u) with
            | ttt => iso_id
            end).
  intros p q h; simpl.
  destruct (fobj[F] p), (fobj[F] q); simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End Cocycle.

(** ** The worked witness: (ℤ, ≤) into (ℤ, +) by differences *)

(* The additive group of the integers, as a [GrpObject] — Awodey's ℝ
   transposed to ℤ so the instance layer stays axiom-free (the same
   substitution Theory/Algebra/Rig.v makes for [Int_Ring]). *)
Program Definition Int_Plus : MonObject := {|
  mon_setoid := {| carrier := Z
                 ; is_setoid := {| Setoid.equiv := @eq Z |} |};
  mon_unit := 0%Z;
  mon_op := Z.add
|}.
Next Obligation. intros a b c; simpl; now rewrite Z.add_assoc. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_l. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_r. Qed.

Program Definition Int_Plus_Grp : GrpObject := {|
  grp_monoid := Int_Plus;
  grp_inv := Z.opp
|}.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_l. Qed.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_r. Qed.

(* Awodey's cocycle: g_{x,y} = y − x, with the unit condition x − x = 0
   and the composition condition (z − y) + (y − x) = z − x. *)
Program Definition translation_cocycle :
  Cocycle Z.le_preorder Int_Plus := {|
  cocycle := fun x y _ => (y - x)%Z
|}.
Next Obligation. intros p q h h'; reflexivity. Qed.
Next Obligation. intros p; simpl; now rewrite Z.sub_diag. Qed.
Next Obligation. intros p q r h k; simpl; lia. Qed.

Definition translation_functor :
  Proset Z.le_preorder ⟶ Deloop Int_Plus :=
  functor_of_cocycle Z.le_preorder Int_Plus translation_cocycle.

Example five_le_twelve : (5 <= 12)%Z.
Proof. lia. Qed.

Example translation_5_12 :
  @fmap _ _ translation_functor 5%Z 12%Z five_le_twelve = 7%Z
  := eq_refl.
