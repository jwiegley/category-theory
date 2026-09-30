Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Eilenberg.Moore.Limit.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.

Generalizable All Variables.

(** * A hypothesis-free instantiation of created limits *)

(* Monad/Eilenberg/Moore/Limit.v proves that [EM_Forget T] strictly creates
   every limit for every monad T on every category.  That is a conditional
   statement about an arbitrary monad; this file discharges every
   hypothesis at once, over objects the library already builds: the
   identity monad on [Coq] (Monad/Strong.v), the empty diagram
   ([From_0], Instance/Zero.v), and the terminal object of [Coq]
   downstairs (Instance/Coq.v).  What comes out is the created terminal
   algebra, and its carrier is the apex of the limit downstairs by
   [eq_refl] — creation on the nose.  (Nothing here reduces: the equality
   holds by projection, not by evaluation, for the reason in the next
   paragraph.)

   Two small points of usage.  [Terminal_Limit]
   (Structure/Limit/Terminal.v) is an [↔], which in this library is
   [iffT] (Lib/Foundation.v), so its halves are taken with [fst] and [snd]
   rather than [proj1]/[proj2].  And it is [Qed]-opaque, so the strictness
   equality below is stated against [vertex_obj[Lbelow]] — the apex of the
   limit actually produced — rather than against [unit]. *)

Definition IdC : Coq ⟶ Coq := Id[Coq].

Definition Kempty : 0 ⟶ @EilenbergMoore Coq IdC (@Id_Monad Coq) :=
  From_0 _.

(* The terminal object of [Coq], read as the limit of the empty diagram. *)

Definition Lbelow : Limit (EM_Forget IdC ◯ Kempty) :=
  snd (Terminal_Limit Coq (EM_Forget IdC ◯ Kempty)) Coq_Terminal.

(* The created lift, and the fact that it is limiting. *)

Definition created_terminal_algebra :
  IsALimit Kempty (em_apex IdC Kempty Lbelow) :=
  em_created IdC Kempty Lbelow.

(* The carrier of the created algebra is the apex of the limit downstairs,
   definitionally: [EM_Forget]'s object map is the first projection. *)

Definition created_carrier :
  `1 (em_apex IdC Kempty Lbelow) = vertex_obj[Lbelow] := eq_refl.

(* Terminality upstairs, read back through the empty-diagram theorem. *)

Definition created_terminal :
  @Terminal (@EilenbergMoore Coq IdC (@Id_Monad Coq)) :=
  fst (Terminal_Limit _ Kempty)
    {| limit_cone := em_cone IdC Kempty Lbelow
     ; ump_limits := @ump_limit _ _ _ _ (em_created IdC Kempty Lbelow) |}.

(** ** Mac Lane's "exactly one pair", on the nose: refuted *)

(* Issue #467.  Mac Lane's Definition of creation (§V.1, p. 112) asks in
   clause (i) that to every limiting cone τ: x →· VF there be EXACTLY ONE
   pair ⟨a, σ⟩ with Va = x and Vσ = τ.  Monad/Eilenberg/Moore/Limit.v
   proves that clause for V = [EM_Forget T] at [≈] ([em_alg_unique],
   [em_lift_alg_unique]).  This section proves, without axioms, that its
   on-the-nose form is false for [EM_Forget], so the [≈]-form is the
   faithful reading in this setting rather than a weakening of it.

   The counterexample.  [Bool2] is [bool] under the indiscrete relation
   (every two points are ≈), a setoid that is terminal in [Sets].  For the
   identity monad on [Sets] ([IdSM]) every endomap of [bool] is then a
   structure map ([alg_of]), both algebra laws holding at an indiscrete
   codomain.
   [A_id] and [A_true] are [Bool2] with the structure maps [fun b => b]
   and [fun _ => true], and [A_id_ne_A_true] shows that they are
   different objects of the Eilenberg-Moore category; its proof carries
   the property "the structure map is pointwise the identity" along the
   equation by a [match], with no Eqdep and no UIP.  Over the one-object
   shape [1], [K1] is the diagram at [A_id] and [N1] the cone downstairs
   with apex [Bool2] and leg [id]; [N1_limiting] shows it limiting.  Each
   of [A_id] and [A_true] carries a cone over [K1] whose one leg is [id]
   as a function ([leg_id_from]), and each lies over [N1] with the apex
   equation [eq_refl] and its leg EQUAL to [N1]'s ([lift1_at]); yet their
   apexes differ, while [em_lift_alg_unique_Sets], [em_lift_alg_unique]
   at the example, makes each isomorphic to the created apex over the
   transport.  [em_lift_not_unique_leibniz] is the uniqueness half of
   clause (i) for [K1], with [=] on the apex and on every leg and τ
   ranging over the limiting cones, refuted at τ = [N1].
   [em_limiting_lift_not_unique_leibniz] refutes it again among lifts
   that are themselves limiting, as both are ([lift1_limiting]: every two
   maps into [Bool2] are ≈), so restricting clause (i) by clause (ii)
   does not rescue it.

   This is the setoid encoding, not Mac Lane.  For him, over any X, a
   T-algebra is a pair ⟨x, h⟩ with h an arrow of X (p. 140), arrows are
   compared by equality, and the universal property of the limit
   determines h, so two lifts agree as pairs.  Here h is a
   setoid morphism that the universal property determines only up to the
   carrier's [≈], and on [Bool2] that relation identifies every two maps.
   The statements' [=] between morphisms is the one exception in this
   file to the library's rule of comparing morphisms by [≈]: it is the
   thing refuted.  Test/ProbeEMCreates467.v restates both refutations
   against these constants.

   Universes, read off [About]: every constant binds [o] and [so], the
   arrows and the objects of [Sets@{o so}] ([o] is also the carriers'
   level; [Bool2] binds its two setoid levels); those that mention the
   shape [1] add [j], its objects; and those that say "limiting" add [l]
   and [l0], the levels of [IsLimitCone].  The only strict bound is
   [o < so], from [Sets]; the stdlib caps are inherited, [compose] and
   [ID] from Instance/Sets.v, [eq_ind], [eq_ind_r] and
   [Logic_lemmas.equality] from [_1] (Instance/One.v), and the sigma
   projections' from [EilenbergMoore].

   Three constructions are written the long way, each for a measured
   reason.  The monad is [IdSM], built here with every field given,
   rather than the library's [Id_Monad] (Monad/Strong.v, a [Program
   Instance] local to its section, the monad of the Coq example above):
   [Id_Monad]'s universe list has three levels on Rocq 9.1.1 (one of
   them bounded only from below), five on Coq 8.20.1 and seventeen on
   8.19.2, so that no explicit instance of it compiles on all three,
   and, left implicit under these binders, Coq 8.20.1 reports one of its
   levels unbound ("Universe … is unbound" at [EMS]); [IdSM] also
   carries none of [Id_Monad]'s [prod_rect] and [projections] caps.  The
   functor [K1] is built with every field given, because [refine] with
   its respectfulness field left open resolves that field by an instance
   at [Set] and collapses [o] to [Set].  And [A_id_ne_A_true] reads its
   final equation at [bool] before [discriminate], which otherwise adds
   an [eq_ind] cap of its own. *)

Definition Bool2@{o p} : SetoidObject@{o p} :=
  {| carrier := bool
   ; is_setoid :=
       {| equiv := fun _ _ => True
        ; setoid_equiv :=
            {| Equivalence_Reflexive := fun _ => I
             ; Equivalence_Symmetric := fun _ _ _ => I
             ; Equivalence_Transitive := fun _ _ _ _ _ => I |} |} |}.

Definition IdS@{o so} : Sets@{o so} ⟶ Sets@{o so} := Id[Sets@{o so}].

Definition IdSM@{o so} : @Monad Sets@{o so} IdS@{o so}.
Proof.
  unshelve refine (@Build_Monad Sets@{o so} IdS@{o so}
    (fun _ => id) (fun _ => id) _ _ _ _ _);
    intros; intro; reflexivity.
Defined.

Definition EMS@{o so} : Category@{so o o} :=
  @EilenbergMoore Sets@{o so} IdS@{o so} IdSM@{o so}.

Definition alg_of@{o so} (f : bool → bool) :
  @TAlgebra Sets@{o so} IdS@{o so} IdSM@{o so}
    Bool2@{o o} :=
  @Build_TAlgebra Sets@{o so} IdS@{o so} IdSM@{o so}
    Bool2@{o o}
    (@Build_SetoidMorphism bool (is_setoid Bool2@{o o}) bool
       (is_setoid Bool2@{o o}) f (fun _ _ _ => I))
    (fun _ => I) (fun _ => I).

Definition A_id@{o so} : EMS@{o so} :=
  existT _ Bool2@{o o} (alg_of@{o so} (fun b => b)).

Definition A_true@{o so} : EMS@{o so} :=
  existT _ Bool2@{o o} (alg_of@{o so} (fun _ => true)).

Lemma A_id_ne_A_true@{o so} : A_id@{o so} = A_true@{o so} → False.
Proof.
  intro E.
  pose (P := fun a : EMS@{o so} => ∀ x : carrier (`1 a),
         (let f : SetoidMorphism (`1 a) (`1 a) := t_alg[`2 a] in f x) = x).
  assert (HP : P A_true) by (destruct E; intro x; reflexivity).
  specialize (HP false).
  change (@eq bool true false) in HP.
  discriminate HP.
Qed.

Definition K1@{j o so} : _1@{j o o} ⟶ EMS@{o so} :=
  @Build_Functor _1 EMS (fun _ => A_id) (fun _ _ _ => id)
    (fun _ _ _ _ _ _ => I) (fun _ _ => I) (fun _ _ _ _ _ _ => I).

Definition N1@{j o so} : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}) :=
  @Build_Cone _1 Sets (EM_Forget IdS ◯ K1) Bool2
    (@Build_ACone _1 Sets Bool2 (EM_Forget IdS ◯ K1) (fun _ => id)
       (fun _ _ _ _ => I)).

Definition N1_limiting@{l l0 j o so} : IsLimitCone@{l l0 j o so} N1@{j o so}.
Proof.
  intro M.
  unshelve refine (@Build_Unique _ _ _
    (@Build_SetoidMorphism _ _ _ (is_setoid Bool2) (fun _ => true)
       (fun _ _ _ => I)) _ _);
    repeat intro; exact I.
Defined.

Definition leg_id_from@{o so} (f : bool → bool) :
  existT _ Bool2@{o o} (alg_of@{o so} f) ~{EMS@{o so}}~> A_id@{o so} :=
  @Build_TAlgebraHom Sets IdS IdSM@{o so} Bool2 Bool2
    (alg_of f) (alg_of (fun b => b)) id (fun _ => I).

Definition lift1_at@{j o so} (a : EMS@{o so})
  (p : EM_Forget IdS a = vertex_obj[N1@{j o so}])
  (leg : a ~{EMS}~> A_id)
  (Hleg : hom_rew p (fmap[EM_Forget IdS] leg)
            ≈ (id : Bool2 ~{Sets}~> Bool2)) :
  StrictLift K1@{j o so} (EM_Forget IdS) N1@{j o so} :=
  @Build_StrictLift _1 EMS Sets K1 (EM_Forget IdS) N1
    (@Build_Cone _1 EMS K1 a
       (@Build_ACone _1 EMS a K1 (fun _ => leg) (fun _ _ _ _ => I)))
    p (fun _ => Hleg).

(* The [≈]-form holds here, as it does for every monad: whatever its
   structure map [f], the lift at [Bool2] is isomorphic in [EMS] to the
   apex created from [N1], by an isomorphism lying over the transport,
   which is [eq_refl] here, so that the underlying map is [id] on the
   nose (Test/ProbeEMCreates467.v).  This is [em_lift_alg_unique] at the
   example, and the theorems below refute its [=]-form. *)

Definition em_lift_alg_unique_Sets@{l l0 j o so} (f : bool → bool) :=
  em_lift_alg_unique@{so o j so so l l0} IdS K1 N1 N1_limiting@{l l0 j o so}
    (lift1_at (existT _ Bool2 (alg_of f)) eq_refl (leg_id_from f)
       (fun _ => I)).

Theorem em_lift_not_unique_leibniz@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       vertex_obj[σ] = vertex_obj[σ']) → False.
Proof.
  intro U.
  apply A_id_ne_A_true.
  exact (U N1 N1_limiting
           (slift_cone (lift1_at A_id eq_refl (leg_id_from (fun b => b))
                          (fun _ => I)))
           (slift_cone (lift1_at A_true eq_refl (leg_id_from (fun _ => true))
                          (fun _ => I)))
           eq_refl eq_refl (fun _ => eq_refl) (fun _ => eq_refl)).
Qed.

Definition lift1_limiting@{l l0 j o so} (f : bool → bool) :
  IsLimitCone@{l l0 j o so}
    (slift_cone (lift1_at@{j o so} (existT _ Bool2 (alg_of f)) eq_refl
                   (leg_id_from f) (fun _ => I))).
Proof.
  intro M.
  unshelve refine (@Build_Unique _ _ _
    (@Build_TAlgebraHom Sets IdS IdSM@{o so} _ Bool2 _
       (alg_of f)
       (@Build_SetoidMorphism _ _ _ (is_setoid Bool2) (fun _ => true)
          (fun _ _ _ => I))
       (fun _ => I)) _ _);
    repeat intro; exact I.
Defined.

Theorem em_limiting_lift_not_unique_leibniz@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       IsLimitCone@{l l0 j o so} σ → IsLimitCone@{l l0 j o so} σ' →
       vertex_obj[σ] = vertex_obj[σ']) → False.
Proof.
  intro U.
  apply A_id_ne_A_true.
  exact (U N1 N1_limiting
           (slift_cone (lift1_at A_id eq_refl (leg_id_from (fun b => b))
                          (fun _ => I)))
           (slift_cone (lift1_at A_true eq_refl (leg_id_from (fun _ => true))
                          (fun _ => I)))
           eq_refl eq_refl (fun _ => eq_refl) (fun _ => eq_refl)
           (lift1_limiting (fun b => b)) (lift1_limiting (fun _ => true))).
Qed.
