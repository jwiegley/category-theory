(** * The covariant power-set monad on [Sets] *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.

Generalizable All Variables.

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2, Exercise 1(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex1
   Book: Awodey, "Category Theory", Carnegie Mellon pre-print, September
         2005, §10.2, Example 10.5, printed p. 271 (PDF p. 280) —
         awodey:10.2:example5; and §10.6, Exercise 5, printed p. 291
         (PDF p. 300) — awodey:10:ex5
   Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
         5.1.5(i), printed p. 185 (PDF p. 205) — riehl:5.1:example5;
         with her Corollary 4.6.3, printed p. 167
   nLab: https://ncatlab.org/nlab/show/power+set
   nLab: https://ncatlab.org/nlab/show/monad

   The covariant power set is the monad whose algebras Mac Lane's §VI.2
   Exercise 1, "Complete semi-lattices (E. Manes; thesis)", asks for.
   All three books state the same data, read here from the page images.
   Mac Lane: "Let 𝒫 be the covariant power set functor on Set so that 𝒫X
   is the set of all subsets S ⊂ X, while for each function f : X → Y,
   (𝒫f)S is the direct image of S under f.  For each set X, let
   η_X : X → 𝒫X send each x ∈ X to the one point set {x}, while
   μ_X : 𝒫𝒫X → 𝒫X sends each set of sets into its union.  (a) Prove that
   ⟨𝒫, η, μ⟩ is a monad 𝒫 on Set."  Awodey's Example 10.5 sends each
   function f to "the image mapping im(f)", with η_X(x) = {x} and
   μ_X(α) = ⋃α, and says "The reader should verify as an exercise that
   these operations are in fact natural in X, and that this defines a
   monad (𝒫, {−}, ⋃) on Sets"; his Exercise 10.6.5, "Show that (P, s, ∪)
   is a monad on Sets", is that verification, with
   ∪_X(α) = {x ∈ X | ∃_{U∈α}. x ∈ U}.  Riehl's Example 5.1.5(i), under
   "Monads also arise in nature", has the same unit and multiplication,
   and notes that naturality of the multiplication "makes use of
   Corollary 4.6.3; the direct image function, as a left adjoint,
   preserves unions".  This file is part (a); parts (b), (c) and (d),
   the algebras, are Instance/SupLat.v.

   THE FUNCTOR AND THE UNIT ARE NOT REBUILT.  Instance/Sets/Powerset.v
   (#227) already has the endofunctor [Powerset_Prop : Sets ⟶ Sets]:
   a subset of a setoid is a [Prop]-valued predicate that respects ≈
   ([Powerset_Prop_obj]), two subsets are equal when they have the same
   members, and the action is the direct image with its existential
   squashed ([Powerset_Prop_image]).  It also has Riehl's
   [Powerset_Prop_Singleton : Id ⟹ Powerset_Prop], whose component at
   X sends x to {x} = λ z, squash (x ≈ z).  Both are used verbatim, and
   η IS that transformation's component ([Powerset_Monad_ret], at
   [eq_refl]).  The proof-relevant carrier of the same file,
   [Powerset], lands one universe up and is not an endofunctor, so no
   monad is formable over it (refused, below).

   THE UNION.  ⋃ SS is the predicate λ x, ∃ S, SS S ∧ S x
   ([Powerset_union_pred]).  Both memberships are [Prop]s, so the
   existential is the standard library's [ex] and needs no squash, and
   P(P X) stays at the level of X by the impredicativity of [Prop].
   [Powerset_union] is μ_X as an arrow of [Sets], its respect for ≈
   being [Powerset_union_respects].

   THE LAWS are four pointwise lemmas: μ ∘ Pμ ≈ μ ∘ μP
   ([Powerset_union_assoc]), μ ∘ Pη ≈ id
   ([Powerset_union_image_singleton]), μ ∘ ηP ≈ id
   ([Powerset_union_singleton]) and the naturality of μ
   ([Powerset_union_natural]); the naturality of η is #227's own
   [naturality_sym] field.  [Powerset_Monad] assembles them with
   Theory/Monad.v's [Build_Monad].  The naturality of μ is proved
   directly, by opening the squashed direct image: the union of the
   images is the image of the union.  Riehl's route, through the direct
   image as a left adjoint, needs Instance/Powerset.v (#382): with it
   the dependency closure grows from this file's thirty-two files to
   eighty-nine, and to ninety with the satellite itself (the transitive
   closure of the Category.* [Require] lines, each file counted once,
   the root included), so that route is kept apart, in the satellite
   Instance/Sets/Powerset/Monad/Riehl.v.
   Awodey's remark that "monads can, and often do, arise without coming
   from evident adjunctions" is taken up in Instance/SupLat/Free.v, which
   builds the free complete-semilattice adjunction and measures how far
   its induced monad is this one.  [Powerset_Monad_statement] inhabits
   the type [Powerset_Prop_Monad_statement], which Instance/Sets/
   Powerset.v entered to show that this monad had become statable.

   STRENGTHS.  By [eq_refl]: T X is [Powerset_Prop_obj X] and T f is
   [Powerset_Prop_map f] ([Powerset_Monad_obj], [Powerset_Monad_map]),
   and T f S at y is the squashed ∃ x, S x ∧ f x ≈ y
   ([Powerset_Monad_map_at]); η_X is #227's singleton component and its
   singleton map ([Powerset_Monad_ret], [Powerset_Monad_ret_map]), η x is
   {x} and x's singleton at z is squash (x ≈ z) ([Powerset_Monad_ret_at],
   [Powerset_Monad_ret_member]); μ_X is [Powerset_union]
   ([Powerset_Monad_join]) and μ SS at x is ∃ S, SS S ∧ S x
   ([Powerset_Monad_join_at]).  At ≈ only: the three monad laws and the
   two naturality squares, which compare different predicates with the
   same members.  Refused, each pinned in Test/ProbeSupLat466.v: each of
   those five at [eq_refl], namely associativity (M3), μ ∘ Pη ≈ id (M4),
   μ ∘ ηP ≈ id (M5), the naturality of η at one point (M6), and the
   naturality of μ at one set of subsets (M1) and as a function of the
   point (M7), all conversion refusals that stand in the probe's copy of
   its dependency closure with every [Qed] turned into [Defined] but those
   the probe's header names; and the statement
   [@Monad Sets Powerset] over the proof-relevant carrier (M2, a type
   mismatch between "Sets@{o so} ⟶ Sets@{so sso}" and "Sets@{o so} ⟶
   Sets@{o so}", which Rocq 9.1 and Coq 8.20 explain as the universe
   inconsistency "Cannot enforce so = o because o < so" and Coq 8.19
   prints without that explanation).

   UNIVERSES, read off [About].  The union and the four laws bind [@{o}],
   with the one bound [Set < o], first carried by Instance/Sets/
   Powerset.v's [Powerset_Prop_truth_equiv] ([Prop : Type@{Set+1}]).
   [Powerset_Monad] and its readbacks bind [@{o so}] with a block
   identical to [Powerset_Prop]'s: [Set < o], [o < so] (first carried by
   Instance/Sets.v's [Sets]), and the caps compose and ID from
   Instance/Sets.v's [setoid_morphism_compose] and [setoid_morphism_id].
   [Powerset_Monad_statement] binds [@{u so o}], in the order of
   [Powerset_Prop_Monad_statement]'s own universes, and adds [so <= u]
   and [o <= u], the bounds of that statement's type.  There is no
   equation and no further strict bound.

   NOT DELIVERED.  The Kleisli category of this monad (the category of
   sets and relations) is not identified.  The nearest construction in
   the tree is Instance/Concrete.v's [Rel_Powerset : Rel ⟶ Sets], out of
   Instance/Rel.v's [Rel], whose objects are Coq types and whose arrows
   A ~> Ensemble B are relations: it sends X to the predicates X → Prop
   under pointwise ↔ and a relation R to its direct image
   S ↦ { y | ∃ x ∈ S, R x y }, which is μ ∘ P R, so that, written out on
   types, it is the functor from the Kleisli category of a power-set monad
   to its base; it is faithful ([Rel_Powerset_Faithful]) and makes [Rel]
   concrete, and its comment calls it the Kleisli presentation of Rel over
   the powerset monad.  It is over bare types, every predicate a subset,
   and nothing compares it with this monad, whose subsets are the
   ≈-respecting predicates on a setoid.  Neither the finite power-set
   monad nor a strength or commutativity of this one is built.  No monad
   is built over the proof-relevant carrier, where none is formable.
   That [Powerset_Prop] has no initial algebra (#750, Lambek's lemma with
   Cantor's theorem) remains open. *)

(* ------------------------------------------------------------------------ *)
(** ** The union of a set of subsets *)

(* ⋃ SS = { x | ∃ S ∈ SS, x ∈ S }.  Both memberships are [Prop]s, so the
   existential is the standard library's [ex] and needs no squash. *)
Definition Powerset_union_pred@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x))
       _).
  intros x y Hxy; split; intros [S [HS Hx]]; exists S; split; try exact HS.
  - exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (proj2 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
Defined.

(* The union respects the equivalence of sets of subsets. *)
Lemma Powerset_union_respects@{o} {X : SetoidObject@{o o}}
  (SS TT : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (H : SS ≈ TT) :
  Powerset_union_pred@{o} SS ≈ Powerset_union_pred@{o} TT.
Proof.
  intro x; split; intros [S [HS Hx]]; exists S; split; try exact Hx.
  - exact (proj1 (H S) HS).
  - exact (proj2 (H S) HS).
Qed.

(* μ_X : P(P X) → P X as an arrow of [Sets]. *)
Definition Powerset_union@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))
                         (Powerset_Prop_obj@{o} X) :=
  @Build_SetoidMorphism@{o o o}
    (carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (is_setoid (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
    (λ SS, Powerset_union_pred@{o} SS) (@Powerset_union_respects@{o} X).

(* ------------------------------------------------------------------------ *)
(** ** The monad laws, pointwise *)

(* μ ∘ Pμ ≈ μ ∘ μP: the union of the unions is the union of the union. *)
Lemma Powerset_union_assoc@{o} {X : SetoidObject@{o o}}
  (SSS : carrier (Powerset_Prop_obj@{o}
                    (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} Powerset_union@{o} SSS)
    ≈ Powerset_union_pred@{o} (Powerset_union_pred@{o} SSS).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. hnf in HS. apply HS; intros [SS [HSS HSSS]].
    destruct (proj2 (HSSS x) Hx) as [T [HT HTx]].
    exists T; split; [ exists SS; split; assumption | exact HTx ].
  - intros [S [[SS [HSS HSS']] Hx]].
    exists (Powerset_union_pred@{o} SS); split.
    + apply Powerset_squash_intro. exists SS. split; [ exact HSS | ].
      reflexivity.
    + exists S; split; assumption.
Qed.

(* μ ∘ Pη ≈ id: the union of the singletons of the members of S is S. *)
Lemma Powerset_union_image_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o}
    (Powerset_Prop_image@{o} (@Powerset_Prop_singleton_map@{o} X) S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intros [y [Hy HyT]].
    assert (Hyx : Powerset_squash@{o} (@equiv _ (is_setoid X) y x))
      by exact (proj2 (HyT x) Hx).
    apply Hyx; intro E. exact (proj1 (@proper_morphism _ _ _ _ S y x E) Hy).
  - intro Hx. exists (Powerset_Prop_singleton_pred@{o} x); split.
    + apply Powerset_squash_intro. exists x; split; [ exact Hx | ].
      reflexivity.
    + apply Powerset_squash_intro; reflexivity.
Qed.

(* μ ∘ ηP ≈ id: the union of the one-point set {S} is S. *)
Lemma Powerset_union_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o} (Powerset_Prop_singleton_pred@{o} S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intro E.
    exact (proj2 (E x) Hx).
  - intro Hx. exists S; split; [ apply Powerset_squash_intro | exact Hx ].
    reflexivity.
Qed.

(* Naturality of μ, proved directly: the union of the images is the image
   of the union. *)
Lemma Powerset_union_natural@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  intro y; split.
  - intros [T [HT Hy]]. hnf in HT. apply HT; intros [S [HS E]].
    assert (Hy' : Powerset_Prop_image@{o} f S y) by exact (proj2 (E y) Hy).
    hnf in Hy'. apply Hy'; intros [x [Hx Hfx]].
    apply Powerset_squash_intro.
    exists x; split; [ exists S; split; assumption | exact Hfx ].
  - intro H. hnf in H. apply H; intros [x [[S [HS Hx]] Hfx]].
    exists (Powerset_Prop_image@{o} f S); split.
    + apply Powerset_squash_intro. exists S; split; [ exact HS | ].
      reflexivity.
    + apply Powerset_squash_intro. exists x; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The monad *)

Definition Powerset_Monad@{o so} : @Monad Sets@{o so} Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Monad Sets@{o so} Powerset_Prop@{o so}
       (fun X => @transform _ _ _ _ Powerset_Prop_Singleton@{o so} X)
       (fun X => @Powerset_union@{o} X) _ _ _ _ _).
  - intros X Y f.
    exact (@naturality_sym _ _ _ _ Powerset_Prop_Singleton@{o so} X Y f).
  - intros X SSS. exact (Powerset_union_assoc@{o} SSS).
  - intros X S. exact (Powerset_union_image_singleton@{o} S).
  - intros X S. exact (Powerset_union_singleton@{o} S).
  - intros X Y f SS. exact (Powerset_union_natural@{o} f SS).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

Example Powerset_Monad_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[Powerset_Prop@{o so}] X = Powerset_Prop_obj@{o} X := eq_refl.

Example Powerset_Monad_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop@{o so}] f = Powerset_Prop_map@{o} f := eq_refl.

Example Powerset_Monad_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X
    = transform[Powerset_Prop_Singleton@{o so}] X := eq_refl.

Example Powerset_Monad_ret_map@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X = @Powerset_Prop_singleton_map@{o} X
  := eq_refl.

Example Powerset_Monad_ret_at@{o so} (X : SetoidObject@{o o})
  (x : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x = Powerset_Prop_singleton_pred@{o} x
  := eq_refl.

Example Powerset_Monad_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ Powerset_Monad@{o so} X = @Powerset_union@{o} X := eq_refl.

Example Powerset_Monad_join_at@{o so} (X : SetoidObject@{o o})
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (x : carrier X) :
  @join _ _ Powerset_Monad@{o so} X SS x
    = ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x)
  := eq_refl.

Example Powerset_Monad_map_at@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y) :
  fmap[Powerset_Prop@{o so}] f S y
    = Powerset_squash@{o}
        (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) := eq_refl.

Example Powerset_Monad_ret_member@{o so} (X : SetoidObject@{o o})
  (x z : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x z
    = Powerset_squash@{o} (@equiv _ (is_setoid X) x z) := eq_refl.

(* The formability statement Instance/Sets/Powerset.v entered for this
   monad is now inhabited, by the monad above. *)
Example Powerset_Monad_statement@{u so o} :
  Powerset_Prop_Monad_statement@{u so o} := Powerset_Monad@{o so}.
