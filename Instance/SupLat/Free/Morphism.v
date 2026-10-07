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
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Cat.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.

Generalizable All Variables.

(** * θ* between #466's two power-set monads *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3, printed p. 142 (PDF
         p. 151) — maclane:VI.2:ex3; with Exercise 1(d) on the same page
         — maclane:VI.2:ex1
   nLab: https://ncatlab.org/nlab/show/suplattice
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")

   WHAT THIS FILE DOES.  Instance/SupLat/Free.v (#466) has two power-set
   monads on Sets with the same functor data: Instance/Sets/Powerset/
   Monad.v's [Powerset_Monad], whose join is the union ⋃, and
   [SL_induced], the monad of the free complete semilattice adjunction
   [SL_adj], whose join is ⋃ ∘ P id and so agrees with ⋃ at ≈ only
   ([SL_induced_join_equiv]).  Free.v read an algebra of [SL_induced] as
   one of [Powerset_Monad] ([SL_induced_repack], proving the action law
   again) and says, under NOT DELIVERED, "No functor between the
   Eilenberg–Moore categories of [SL_induced] and of [Powerset_Monad] is
   built: the tree has no morphisms of monads, and [SL_induced_repack] is
   the object part of one."  This file builds that functor as Mac Lane's
   θ*, from Monad/Morphism.v's record and Monad/Morphism/Algebra.v's
   construction.  Free.v is not changed.

   THE MORPHISM.  [SL_theta : MonadHom Powerset_Monad SL_induced] has
   the identity of Sets as every component ([SL_theta_component],
   [eq_refl]).  Its naturality and unit law hold pointwise by
   reflexivity; its multiplication law is [SL_induced_join_equiv] after
   Instance/Sets/Powerset.v's [Powerset_Prop_map_id], which removes the
   direct image under the identity.  [SL_theta_inv] is the morphism the
   other way, again with identity components ([SL_theta_inv_component],
   [eq_refl]), its multiplication law the same two steps in the other
   order; [SL_theta_iso]: the two are inverse in Monad/Morphism.v's
   [Monads Sets], componentwise by reflexivity, so the two power-set
   monads are isomorphic objects of the category of monads.  With T =
   [Powerset_Monad] and T' = [SL_induced], θ* runs from the algebras of
   [SL_induced] to those of [Powerset_Monad], the direction of
   [SL_induced_repack].

   θ*.  [SL_EM_theta] is mh_EM SL_theta, the functor Free.v lists as not
   delivered.  On one algebra β, θ*'s structure map agrees with
   [SL_induced_repack β]'s as a function, at [eq_refl]
   ([SL_theta_alg_fun], and [SL_EM_theta_alg_fun] on objects), and the
   carrier is kept ([SL_EM_theta_carrier]).  Free.v's
   [EM_induced_to_SupLat], its functor from the algebras of
   [SL_induced] to complete semilattices, factors through θ* and
   Instance/SupLat.v's [EM_to_SupLat] (Mac Lane's Exercise 1(d) on the
   algebras of [Powerset_Monad]): [SL_factor] states EM_to_SupLat ◯
   SL_EM_theta ≈ EM_induced_to_SupLat at Cat's ≈, with identity
   components.  On objects the two agree at [eq_refl] in the carrier
   setoid ([SL_factor_set]), the order ([SL_factor_le]) and the supremum
   as a function ([SL_factor_sup_fun]), and on arrows in the underlying
   map ([SL_factor_map]).

   STRENGTHS.  By [eq_refl]: [SL_theta_component],
   [SL_theta_inv_component], [SL_theta_alg_fun], [SL_EM_theta_carrier],
   [SL_EM_theta_alg_fun] and the four [SL_factor] readbacks.  At ≈: the
   laws of [SL_theta] and [SL_theta_inv], [SL_theta_iso], and
   [SL_factor].  Refused at [eq_refl], by conversion, each pinned in
   Test/ProbeMonadMorphism468.v with its positive controls:
   - θ*'s structure map as a setoid morphism, against
     [SL_induced_repack]'s (R15; control C34); and the supremum of the
     two semilattices as a setoid morphism (R16; control C35);
   - the two semilattices, as whole objects (R17; controls C35 and
     C36).
   Controls C61, C45 and C62 restate [SL_theta_component],
   [SL_theta_inv_component] and [SL_EM_theta_carrier].
   θ* writes the structure map h as h ∘ id, a composite in Sets (Monad/
   Morphism/Algebra.v's [mh_EM_alg]), where [SL_induced_repack] keeps h,
   and [EM_to_SupLat] takes the supremum to be the structure map.  The
   first two refusals are opacity outside the tree, as for Instance/Fun/
   Action/Monad/BG/Morphism.v: Instance/Sets.v's [setoid_morphism_compose]
   and [setoid_morphism_id] carry properness proofs built from opaque
   CMorphisms lemmas, and in a copy of the probe's dependency closure in
   which only those two fields are written as terms both hold at
   [eq_refl]; with either field alone written so, both are still refused,
   and turning every [Qed] of the closure into [Defined] (Instance/
   Sets.v, Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/
   Grp/Free.v keeping theirs) changes neither.  The whole-object refusal
   is not opacity, argued from the terms and not measured further (no
   copy made Instance/Sets.v transparent): it stands in all three
   copies, and in the one with
   both changes the unit law [t_id] and the action law [t_action] of the
   two algebras are each refused alone, [SL_induced_repack] keeping
   β's unit law and proving its action law again, θ* rebuilding both
   through [mh_ret] and [mh_join].
   CORRECTION (#1347): the copy in which only those two fields are
   written as terms is now the tree: the first two refusals, R15 and R16,
   hold at [eq_refl] and are controls of the probe, and their attribution
   to the standard library's opacity was right; the whole-object refusal,
   R17, still stands.

   UNIVERSES, read off [About].  Every constant binds [@{o so}] with
   Set < o and o < so, except [SL_theta_iso], which adds the object and
   hom levels m1 and m2 of [Monads@{so o m1 m2} Sets], at or above so,
   and the caps of the sigma objects of [Monads], and [SL_factor], which
   adds c with o < c and so < c, the levels of [Cat@{c so so so o}],
   first carried by Instance/Cat.v's [Cat].  [SL_theta], [SL_theta_inv],
   their component readbacks and [SL_theta_alg_fun] have exactly the
   block of [SL_induced]: Set < o, first carried by
   Instance/Sets/Powerset.v's [Powerset_Prop_truth_equiv], the relation
   on Prop (Prop : Type@{Set+1}), as Instance/SupLat.v and
   Instance/Sets/Powerset/Monad.v attribute it; o < so, first carried by
   Instance/Sets.v's [Sets]; and the stdlib caps that Free.v's UNIVERSES
   paragraph attributes.  [SL_EM_theta] and the constants that name it
   have exactly the block of [EM_induced_to_SupLat], which adds o <=
   Projections.u1 and so <= Projections.u0 from [EilenbergMoore]'s sigma
   objects.  No equation occurs.

   NOT DELIVERED.  Free.v is not rewired: its [SL_induced_repack] and
   [EM_induced_to_SupLat] keep their own structure maps, which θ* would
   replace by h ∘ id.  The isomorphism in Cat between the two
   Eilenberg–Moore categories that Monad/Morphism/Algebra.v's
   [Monads_EM] makes of [SL_theta_iso] is not stated. *)

(** ** θ : Powerset_Monad ⟶ SL_induced, identity components *)

Definition SL_theta@{o so | Set < o, o < so +} :
  MonadHom@{so o} Powerset_Monad@{o so} SL_induced@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} Powerset_Prop@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Monad@{o so} SL_induced@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=Powerset_Prop@{o so}) (G:=SL_Forget@{o so} ◯ SL_Free@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    symmetry.
    etransitivity;
      [ exact (SL_induced_join_equiv X (fmap[Powerset_Prop@{o so}] id SS)) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_component@{o so | Set < o, o < so +} (X : SetoidObject@{o o}) :
  mh_transform SL_theta@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* θ* on one algebra against [SL_induced_repack], as a function. *)

Example SL_theta_alg_fun@{o so | Set < o, o < so +} {X : SetoidObject@{o o}}
  (β : @TAlgebra Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
         SL_induced@{o so} X) :
  (fun S => @t_alg _ _ _ _ (mh_algebra SL_theta@{o so} β) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} β) S) := eq_refl.

(** ** θ⁻¹ : SL_induced ⟶ Powerset_Monad, identity components *)

Definition SL_theta_inv@{o so | Set < o, o < so +} :
  MonadHom@{so o} SL_induced@{o so} Powerset_Monad@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Prop@{o so}
       SL_induced@{o so} Powerset_Monad@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=SL_Forget@{o so} ◯ SL_Free@{o so}) (G:=Powerset_Prop@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    etransitivity; [ exact (SL_induced_join_equiv X SS) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    symmetry.
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_inv_component@{o so | Set < o, o < so +}
  (X : SetoidObject@{o o}) :
  mh_transform SL_theta_inv@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* The two are inverse in [Monads Sets]. *)

Definition SL_theta_iso@{o so m1 m2 |
  Set < o, o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so}).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so})
    SL_theta@{o so} SL_theta_inv@{o so} _ _).
  - intros X S. reflexivity.
  - intros X S. reflexivity.
Defined.

(** ** θ* : the functor Free.v lists as NOT DELIVERED *)

Definition SL_EM_theta@{o so | Set < o, o < so +} :
  @EilenbergMoore@{so so so o} Sets@{o so}
    (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
      Powerset_Monad@{o so} :=
  mh_EM@{so o so so} SL_theta@{o so}.

Example SL_EM_theta_carrier@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  `1 (fobj[SL_EM_theta@{o so}] x) = `1 x := eq_refl.

Example SL_EM_theta_alg_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => @t_alg _ _ _ _ (`2 (fobj[SL_EM_theta@{o so}] x)) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} (`2 x)) S)
  := eq_refl.

(** ** [EM_induced_to_SupLat] factors through θ* *)

Example SL_factor_set@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_set (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_le@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_le (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_le (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_sup_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => sl_sup (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x) S)
    = (fun S => sl_sup (fobj[EM_induced_to_SupLat@{o so}] x) S) := eq_refl.

Example SL_factor_map@{o so | Set < o, o < so +}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
  (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] f)
    = slh_map (fmap[EM_induced_to_SupLat@{o so}] f) := eq_refl.

Definition SL_factor@{o so c | Set < o, o < so, o < c, so < c +} :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       SupLat@{o so})
    (EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}) EM_induced_to_SupLat@{o so}.
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (fobj[EM_induced_to_SupLat@{o so}] x) (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_induced_to_SupLat@{o so}] x)
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.
