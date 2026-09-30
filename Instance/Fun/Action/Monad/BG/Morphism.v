Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Instance.Fun.Action.Monad.BG.

Generalizable All Variables.

(** * #464's two monads are isomorphic in the category of monads *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3, printed p. 142 (PDF
         p. 151) — maclane:VI.2:ex3; and §VI.2, "Group actions", printed
         p. 141 (PDF p. 150)
   Book: Riehl, "Category Theory in Context", 2nd ed., Exercise 5.5.iv,
         printed p. 208 (PDF p. 228) — riehl:5.5:exiv
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")

   WHAT THIS FILE DOES.  Instance/Fun/Action/Monad/BG.v (#464) has two
   monads on Sets with the same functor data, M × X and M × f: [ActMonad
   M] of Instance/Fun/Action/Monad.v, whose unit is Mac Lane's printed
   η x = (u, x), and [BGMonad M], induced by that file's adjunction, whose
   unit is (u u, x).  Their multiplications agree at every triple
   ([BG_join_ActMonad]).  For want of a record of monad morphisms, BG.v
   related them by three separate facts ([BG_T_ActF], [BG_ret_ActMonad],
   [BG_join_ActMonad]) and built Mac Lane's θ* for this instance by hand
   ([BG_Act_EM]); its header says so ("θ* is built for this instance
   alone, with no general record of monad morphisms").  This file states
   the relation with Monad/Morphism.v and takes θ* from Monad/Morphism/
   Algebra.v.  BG.v is not changed: restated for the general θ*, its
   readback [BG_Act_EM_alg] would be refused (below).

   THE MORPHISMS.  [BG_theta M : MonadHom (ActMonad M) (BGMonad M)] and
   [BG_theta_inv M] the other way, each with the identity of Sets as
   every component ([BG_theta_component], [BG_theta_inv_component], at
   [eq_refl]).  Their unit laws are M's unit law [mon_op_unit_l], one way
   and back; naturality and the multiplication laws hold pointwise by
   reflexivity.  [BG_theta_iso]: the two are inverse in Monad/
   Morphism.v's [Monads Sets], componentwise by reflexivity, so the two
   monads are isomorphic objects of the category of monads, which is the
   one statement BG.v's three facts approximate.

   θ*.  Mac Lane's θ : T ⇝ T' gives θ* : X^{T'} → X^T.  With T =
   [ActMonad M] and T' = [BGMonad M], θ* = mh_EM (BG_theta M) runs from
   the algebras of [BGMonad M] to those of [ActMonad M], the direction of
   [BG_Act_EM].  The two functors agree on carriers, on structure maps as
   functions and on the underlying arrows of algebra maps, at [eq_refl]
   ([BG_theta_EM_carrier], [BG_theta_EM_alg_fun], [BG_theta_EM_hom]), and
   as functors at Cat's ≈ with identity components ([BG_theta_EM]).  They
   are not one functor.  θ* gives an algebra with structure map h the
   structure map h ∘ id, a composite in Sets (Monad/Morphism/Algebra.v's
   [mh_EM_alg]), where [BG_Act_EM] keeps h.  The inverse morphism gives
   [Act_BG_EM], θ* of [BG_theta_inv M], from the algebras of [ActMonad M]
   to those of [BGMonad M]: it assembles into a functor BG.v's
   [Act_BG_alg], which that file "kept as a map on algebras" and "not
   assembled into a functor"; they agree on carriers
   ([Act_BG_EM_carrier]) and on structure maps as functions
   ([Act_BG_EM_alg_fun]).

   STRENGTHS.  By [eq_refl]: the four component and θ* readbacks above,
   [Act_BG_EM_carrier] and [Act_BG_EM_alg_fun].  At ≈: the laws of both
   morphisms, [BG_theta_iso], and [BG_theta_EM].  Refused at [eq_refl],
   by conversion, each pinned in Test/ProbeMonadMorphism468.v with its
   positive controls:
   - the structure map of θ* X as a setoid morphism, against X's own,
     that is BG.v's [BG_Act_EM_alg] restated for θ* (R12; controls C29,
     C31 and C32); and that of [Act_BG_EM] against [Act_BG_alg] (R14;
     control C33);
   - θ* X against [BG_Act_EM] X, as whole objects (R13; controls C28 to
     C30).
   The first two are opacity outside the tree.  The composite h ∘ id in
   Sets is Instance/Sets.v's [setoid_morphism_compose] of
   [setoid_morphism_id], whose properness fields are built by instance
   resolution from the CMorphisms lemmas [Reflexive_partial_app_morphism]
   and [proper_proper_proxy], and [subrelation_id_proper] applied to
   [subrelation_refl], all opaque in the tree and in every copy below.
   In a copy of the probe's dependency closure in which only
   Instance/Sets.v changed, its two fields written as the terms
   fun _ _ H => H and fun a b H => proper_morphism g _ _
   (proper_morphism f a b H) (the change #466 measured for its F1), both
   hold at [eq_refl]; with either field alone written so, both are still
   refused.
   Neither is changed by turning every [Qed] of that closure into
   [Defined] with [Transparent Obligations] set (Instance/Sets.v,
   Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/Grp/Free.v
   keeping their [Qed]s).  The whole-object refusal is not opacity: it
   stands in that transparent copy, in the copy with the two fields
   written as terms, and in a copy with both changes, where the carriers
   and structure maps convert and the unit law [t_id] and the action law
   [t_action] of the two algebras are each refused alone.  θ*'s laws are
   Algebra.v's proof chains through [mh_ret] and [mh_join], BG.v's pass
   the variable algebra's own laws along [mon_op_unit_l]; the two differ
   at neutral terms of the variable carrier setoid (argued from the terms,
   not measured further).

   UNIVERSES, read off [About].  Every constant binds [@{o so}] with o < so,
   M : MonObject@{o o o}, except [BG_theta_iso], which adds the object and
   hom levels m1 and m2 of [Monads@{so o m1 m2} Sets], at or above so, and
   the caps o, so <= Projections.u0/u1 of the sigma objects of [Monads], and
   [BG_theta_EM], which adds c with o < c and so < c, the levels of
   [Cat@{c so so so o}], first carried by Instance/Cat.v's [Cat].  o < so is
   first carried by Instance/Sets.v's [Sets].  The two morphisms have
   exactly the block of [BGMonad] and [ActMonad]: the caps compose and ID
   from [Sets], prod_rect and projections from the product carrier, and
   Logic_lemmas.equality and so <= projections from Theory/Adjunction.v's
   [Build_Adjunction'], all named in BG.v's UNIVERSES paragraph.  The θ*
   readbacks and [Act_BG_EM] have the block of [BG_Act_EM], which adds o <=
   Projections.u1 and so <= Projections.u0 from [EilenbergMoore]'s sigma
   objects.  A [simpl] in the proof of [BG_theta_EM] added the strict bound
   o < Projections.u0, as it did to [BG_Act_EM] (BG.v's header); the proof
   has none, and the bound is gone (measured both ways).  No [Set] and no
   equation occur.

   NOT DELIVERED.  BG.v is not rewired onto θ*: its readback
   [BG_Act_EM_alg] would be refused, as above.  The isomorphism in Cat
   between the two Eilenberg–Moore categories that Monad/Morphism/
   Algebra.v's [Monads_EM] makes of [BG_theta_iso] is not stated; BG.v
   already relates both to Set^BG through its comparison functors. *)

(** ** θ : ActMonad M ⟶ BGMonad M, identity components *)

Definition BG_theta@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (ActMonad@{o so} M) (BGMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (ActF@{o so} M) (U_BG@{o so} M ◯ F_BG@{o so} M)
       (ActMonad@{o so} M) (BGMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=ActF@{o so} M) (G:=U_BG@{o so} M ◯ F_BG@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl.
    split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(** ** θ⁻¹ : BGMonad M ⟶ ActMonad M, identity components *)

Definition BG_theta_inv@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (BGMonad@{o so} M) (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) (ActF@{o so} M)
       (BGMonad@{o so} M) (ActMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=U_BG@{o so} M ◯ F_BG@{o so} M) (G:=ActF@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl. split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_inv_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta_inv@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* The two are inverse in [Monads Sets]. *)

Definition BG_theta_iso@{o so m1 m2 |
  o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} (M : MonObject@{o o o}) :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M)
    (BG_theta@{o so} M) (BG_theta_inv@{o so} M) _ _).
  - intros X p. simpl. split; reflexivity.
  - intros X p. simpl. split; reflexivity.
Defined.

(** ** θ* against #464's [BG_Act_EM] *)

Example BG_theta_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)
    = `1 (fobj[BG_Act_EM@{o so} M] x) := eq_refl.

Example BG_theta_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _
              (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)) p)
    = (fun p => @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) p)
  := eq_refl.

Example BG_theta_EM_hom@{o so | o < so +} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  t_alg_hom[fmap[mh_EM@{so o so so} (BG_theta@{o so} M)] f]
    = t_alg_hom[fmap[BG_Act_EM@{o so} M] f] := eq_refl.

Definition BG_theta_EM@{o so c | o < so, o < c, so < c +}
  (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (mh_EM@{so o so so} (BG_theta@{o so} M)) (BG_Act_EM@{o so} M).
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.

(** ** θ⁻¹* assembles #464's [Act_BG_alg] into a functor *)

Definition Act_BG_EM@{o so | o < so +} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so}
      (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M) :=
  mh_EM@{so o so so} (BG_theta_inv@{o so} M).

Example Act_BG_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  `1 (fobj[Act_BG_EM@{o so} M] x) = `1 x := eq_refl.

Example Act_BG_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _ (`2 (fobj[Act_BG_EM@{o so} M] x)) p)
    = (fun p => @t_alg _ _ _ _ (Act_BG_alg@{o so} M (`1 x) (`2 x)) p)
  := eq_refl.
