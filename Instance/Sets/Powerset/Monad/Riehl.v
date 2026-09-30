(** * Riehl's route to the naturality of the union *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(* Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
         5.1.5(i), printed p. 185 (PDF p. 205) — riehl:5.1:example5; with
         her Corollary 4.6.3, printed p. 167, and Example 4.1.8, printed
         p. 134
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2, Exercise 1(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex1
   nLab: https://ncatlab.org/nlab/show/power+set
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   Riehl's Example 5.1.5(i) presents the covariant power set monad under
   "Monads also arise in nature" and says how its two naturality squares
   are proved: "Naturality of the unit with respect to a function f : A → B
   makes use of the fact that f_* : PA → PB is the direct image (rather
   than inverse image) function.  Naturality of the multiplication maps
   makes use of Corollary 4.6.3; the direct image function, as a left
   adjoint, preserves unions."  Corollary 4.6.3 reads: "For any function
   f : A → B, the inverse image f^{-1} : PB → PA, a function between the
   power sets of A and B, preserves both unions and intersections, while
   the direct image f_* : PA → PB only preserves unions", and its proof
   cites the adjunction f_* ⊣ f^{-1} of Example 4.1.8 between the posets of
   subsets and observes that "Unions are colimits and intersections are
   limits in the poset category PA": left adjoints preserve colimits.

   Instance/Sets/Powerset/Monad.v proves the naturality of μ directly, by
   opening the squashed direct image ([Powerset_union_natural]).  This
   satellite takes Riehl's route, twice, through Instance/Powerset.v
   (#382), which has her Example 4.1.8 as [image_preimage_adjunction] and
   the direct-image half of Corollary 4.6.3 in two forms:
   [direct_image_preserves_joins], proved directly at an arbitrary least
   upper bound, and [direct_image_preserves_joins_via_LAPC], read off
   Adjunction/Continuity.v's [left_adjoint_preserves_colimit] at the
   adjunction, which is the corollary's own proof.  The naturality of η is
   #227's [Powerset_Prop_Singleton], whose naturality square is #227's
   [Powerset_Prop_image_singleton], the direct image of a singleton being
   the singleton of the image (Riehl's point that f_* is the direct
   image), and is not revisited.

   THE UNION AS A LEAST UPPER BOUND.  ⋃ SS is the least upper bound,
   under #382's inclusion [subset_le], of the family of its members,
   indexed by the members themselves, the sigma { S & S ∈ SS }
   ([Powerset_union_IsLUB], in Instance/Proset/Limit.v's [IsLUB]); and it
   is ≈ #382's canonical union [subset_union] of that family
   ([Powerset_union_family]).

   THE TWO ROUTES.  [join_natural_via_image]: the direct image of that
   least upper bound is the least upper bound of the images f S, S ∈ SS,
   by [direct_image_preserves_joins]; ⋃ (P (P f) SS) is the least upper
   bound of its own members, which are those images up to ≈; two least
   upper bounds of families with the same upper bounds are equal by the
   antisymmetry of inclusion.  [join_natural_via_LAPC] does the same with
   [direct_image_preserves_joins_via_LAPC] at the family of members,
   moving between #382's canonical union and the monad's by
   [Powerset_union_family].  Preservation of unions does not give the
   square for free: identifying ⋃ (P (P f) SS) with the least upper bound
   of the images still opens the squashed direct image that the direct
   proof opens, in both routes.

   THE ROUTES PROVE THE MONAD'S FIELD.  [Powerset_join_natural_statement f]
   is the type of [Powerset_Monad]'s naturality field [join_fmap_fmap] at
   f.  [join_natural_routes_agree] pairs the field itself with the direct
   lemma and both routes at that one type: it type-checks, so each route
   proves the field's statement as stated, by conversion.  The proofs are
   different terms of a proposition and are not compared.

   COST, measured.  The dependency closure is thirty-two files for
   Instance/Sets/Powerset/Monad.v, eighty-nine for that file with
   Instance/Powerset.v, and ninety for this satellite (the transitive
   closure of the Category.* [Require] lines, each file counted once, the
   root included; Instance/Powerset.v alone reaches eighty-eight), which
   is why the monad keeps the direct proof.  In universes, read off
   [About]: [join_natural_via_image] adds to the block of
   [Powerset_Monad] the caps o <= Relation_Definition.u0,
   first carried by Instance/Proset/Limit.v's [IsLUB] over the standard
   library's [relation], and o <= Projections.u0, the sigma projection of
   the index, first carried by [Powerset_union_IsLUB].
   [join_natural_via_LAPC] adds the strict bounds o < projections.u0 and
   o < projections.u1 (the pair projections), with Set < projections.u0,
   Set < projections.u1 and JMeq.u0 <= JMeq.u1, and the caps
   o <= RelationClasses.Defs.u0, Relation_Definition.u0, eq.u0,
   Logic_lemmas.equality.u0 and Projections.u0.  All are
   [direct_image_preserves_joins_via_LAPC]'s own: the two strict bounds
   and the caps eq.u0 and Logic_lemmas.equality.u0 at its index universe,
   which the family of members puts at o; the caps
   RelationClasses.Defs.u0, Relation_Definition.u0 and Projections.u0 at
   its setoid level o; and the bounds on Set and JMeq unconditionally.
   [join_natural_routes_agree] carries the union of the two.
   [Powerset_union_IsLUB] states [IsLUB] at [IsLUB@{o o Set Set Set}]:
   the bound is a pair of propositions, and with its level at o instead,
   [join_natural_via_image] gained o <= projections.u0 (measured).
   Every constant binds [@{o}] or [@{o so}]; there is no equation.

   STRENGTHS.  The four proofs of the square are at ≈, which is what the
   field states; that their statements are the field's is by conversion
   ([join_natural_routes_agree]).  Nothing here is refused, and no probe
   item pins this file.

   NOT DELIVERED.  No monad is built with Riehl's proof in its naturality
   field; one would differ from [Powerset_Monad] only in that proof.  The
   inverse-image half of Corollary 4.6.3 is #382's. *)

(* ------------------------------------------------------------------------ *)
(** ** The union as a least upper bound *)

(* ⋃ SS is the least upper bound, under inclusion, of the family of its
   members, indexed by the members themselves. *)
Lemma Powerset_union_IsLUB@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  IsLUB@{o o Set Set Set} (@subset_le@{o} X)
    (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i)
    (Powerset_union_pred@{o} SS).
Proof.
  split.
  - intros [S HS] x Hx. exists S; split; assumption.
  - intros n Hn x [S [HS Hx]]. exact (Hn (S; HS) x Hx).
Qed.

(* The same union, as #382's canonical family union [subset_union]. *)
Lemma Powerset_union_family@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} SS
    ≈ subset_union@{o o o}
        (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. exists (S; HS). exact Hx.
  - intros [[S HS] Hx]. exists S; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The naturality of μ, through the direct image as a left adjoint *)

(* Through #382's [direct_image_preserves_joins]: the image of a least upper
   bound is the least upper bound of the images. *)
Lemma join_natural_via_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins f _ _ (Powerset_union_IsLUB SS))
    as Hf.
  pose proof (Powerset_union_IsLUB
                (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)) as Hu.
  destruct Hf as [Hf_ub Hf_least].
  destruct Hu as [Hu_ub Hu_least].
  intro y; split.
  - apply Hu_least. intros [T HT] z Hz.
    apply HT; intros [S [HS E]].
    exact (Hf_ub (S; HS) z (proj2 (E z) Hz)).
  - apply Hf_least. intros [S HS] z Hz.
    refine (Hu_ub (existT _ (Powerset_Prop_image@{o} f S) _) z Hz).
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(* Through #382's [direct_image_preserves_joins_via_LAPC]: Riehl's Corollary
   4.6.3 read off the left adjoint's preservation of colimits, at the
   canonical union of the members. *)
Lemma join_natural_via_LAPC@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins_via_LAPC f
                (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } =>
                   projT1 i)) as Hf.
  destruct Hf as [Hf_ub Hf_least].
  pose proof (@proper_morphism _ _ _ _ (Powerset_Prop_map@{o} f) _ _
                (Powerset_union_family SS)) as E.
  intro y; split.
  - intros [T [HT Hy]]. apply (proj2 (E y)).
    apply HT; intros [S [HS ES]].
    exact (Hf_ub (S; HS) y (proj2 (ES y) Hy)).
  - intro Hy.
    refine (Hf_least (Powerset_union_pred@{o}
                        (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS))
              _ y (proj1 (E y) Hy)).
    intros [S HS] z Hz. exists (Powerset_Prop_image@{o} f S); split;
      [ | exact Hz ].
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The three proofs inhabit the monad's naturality field *)

(* The type of [Powerset_Monad]'s field [join_fmap_fmap] at f. *)
Definition Powerset_join_natural_statement@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  @join _ _ Powerset_Monad@{o so} Y
    ∘ fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f)
  ≈ fmap[Powerset_Prop@{o so}] f ∘ @join _ _ Powerset_Monad@{o so} X.

(* The field itself, the direct lemma, and both of Riehl's routes: the
   quadruple is well typed, so each route proves the field's statement. *)
Definition join_natural_routes_agree@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f :=
  (@join_fmap_fmap _ _ Powerset_Monad@{o so} X Y f,
   fun SS => Powerset_union_natural@{o} f SS,
   fun SS => join_natural_via_image f SS,
   fun SS => join_natural_via_LAPC f SS).
