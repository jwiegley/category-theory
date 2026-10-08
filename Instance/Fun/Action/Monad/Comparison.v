Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Comparison.Resolution.

Generalizable All Variables.

(** * Awodey's uniqueness of the comparison functor, without the coherence *)

(* Book: Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
         September 2005), §10.3, the comparison functor, printed p. 277
         (PDF p. 286) — awodey:10.3:construction-comparison-functor;
         with his Definition 7.10, printed p. 165 (PDF p. 174).
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.3, Theorem 1, printed p. 142 (PDF
         p. 151); §VI.7, the definition of a comparison, printed p. 153
         (PDF p. 162) — maclane:VI.7:def1.
   nLab: https://ncatlab.org/nlab/show/monadic+adjunction

   WHAT THE BOOKS SAY, read from the page images.  Awodey, p. 277: "If we
   start with an adjunction F ⊣ U and construct C^T for T = U ∘ F, we
   then get a comparison functor Φ : D → C^T, with U^T ∘ Φ ≅ U,
   Φ ∘ F = F^T ...  In fact, Φ is unique with this property."  His ≅
   between functors is an isomorphism in the functor category, the
   natural isomorphism of his Definition 7.10 (p. 165), and his = is an
   equality of functors; that mixed property is his reading.  Mac Lane's
   §VI.3 Theorem 1 (p. 142) has an equality in both places: "there is a
   unique functor K : A → X^T with G^T K = G and KF = F^T".  Issue #482
   states the clause at ≈ in both places, "∀ K, EM_Forget ◯ K ≈ U →
   K ◯ F ≈ EM_Free → K ≈ EM_Comparison".

   WHAT HOLDS.  With an isomorphism in the first place the uniqueness is
   false, in both readings, each refuted here at one monad on [Sets]; it
   is true once a comparison carries Monad/Comparison/Resolution.v's
   coherence [cmp_monad]:
   - the issue's reading, ≈ in both places: [bare_awodey_refuted];
   - Awodey's printed reading, U^T ∘ Φ ≅ U at ≈ and Φ ∘ F = F^T at
     Theory/Functor.v's [Functor_StrictEq_Setoid] (objects equal by =,
     arrows by ≈ after transport): [printed_awodey_not_unique];
   - the coherent reading, every comparison over the identity
     identification of the two monads ≈ [EM_Comparison]: Resolution.v's
     [EM_Comparison_unique], with [EM_Comparison_unique_cell] for the
     uniqueness of the isomorphism.
   Mac Lane's reading, with an equality in both places, is his Theorem 1,
   proved in set theory and not formalized here (NOT DELIVERED).  So it
   is the isomorphism in Awodey's first condition that breaks his
   uniqueness clause: with an equality there it is Mac Lane's theorem.

   THE MONOID.  [LZ] is {1, a, b} on [option bool], 1 the unit ([None])
   and a, b ([Some true], [Some false]) left zeros, x y = x unless x = 1;
   σ ([lz_swap]) swaps a and b.  σ is an automorphism ([lz_swap_op],
   [lz_swap_swap]) and not inner, 1 being the only unit; what the
   refutations use is that no c in LZ has c k = σ(k) c for every k, and
   that σ moves a and is injective.  The
   monad is Instance/Fun/Action/Monad.v's [ActMonad LZ], LZ × (−) on
   [Sets], with two of its resolutions: the adjunction [MSet_adj LZ] of
   LZ-sets, and its Kleisli resolution.

   THE ISSUE'S READING, at the adjunction of LZ-sets.  σ* ([Swap_MSet])
   restricts an action along σ, and K is [EM_Comparison] after σ*
   ([K_swap]).  U^T K = U with identity components ([K_forget],
   [K_forget_components]), and K F ≅ F^T through σ × 1 ([K_free],
   [KF_iso]): K satisfies both hypotheses.  K is not ≈ [EM_Comparison]
   ([K_not_EMC]): at the free LZ-set on one point, with the right
   multiplications by k as arrows (Instance/Fun/Action/Monad.v's
   [MSet_extend] of [lz_pick] k), a natural isomorphism would give c with
   c k = σ(k) c for every k.  Hence [bare_awodey_refuted].  The
   coherence is what rules K out: no comparison over Resolution.v's
   [EM_Comparison_theta], the identity identification, has a functor ≈ K
   ([K_no_coherent_comparison], through [EM_Comparison_unique]).  And K
   with [K_free] and [K_forget] IS a comparison, over the monad
   automorphism θ_σ ([K_Comparison]), whose components are σ × 1 at
   [eq_refl] ([theta_sigma], [theta_sigma_component]): the uniqueness is
   relative to the identification θ, as Resolution.v's [Comparison] is.

   AWODEY'S PRINTED READING, at the Kleisli resolution.  Over the
   adjunction of LZ-sets, transporting σ* back "at the free algebras"
   would need a decision of which LZ-sets are free, which an
   [MSetoidAction] does not offer; in the Kleisli resolution every object
   is free.  Φ ([Phi]) sends a Kleisli arrow f to the free extension of
   σ ∘ f, (k, x) ↦ (k σ((f x)₁), (f x)₂): Φ ∘ F = F^T at
   [Functor_StrictEq_Setoid], with [eq_refl] on objects
   ([Phi_free_strict]), and U^T ∘ Φ ≅ U through σ × 1 ([Phi_forget]).
   Φ₀ ([Phi0]), the free extension of f itself, has the same two
   properties ([Phi0_free_strict], [Phi0_forget]) and is ≈ the
   comparison functor of the Kleisli resolution ([Phi0_EMC]).  Φ is not
   ≈ that comparison functor ([Phi_not_EMC]): at the one-point setoid and
   the Kleisli arrows [lz_pick] k, an isomorphism would make σ(k), for
   every k, the image of c k under a map fixing a and b, for one c.  So
   the printed property has two solutions, Φ and Φ₀, that are not even
   isomorphic ([printed_awodey_not_unique]).  Φ₀ is built, rather than
   the comparison functor used, because Φ₀ has Φ ∘ F = F^T with
   [eq_refl] on objects by construction, while the comparison functor's
   left triangle on objects is refused at [eq_refl] at a variable
   adjunction (Test/ProbeResolution482.v, R1).

   STRENGTHS.  Every statement is at ≈ except [Phi_free_strict] and
   [Phi0_free_strict], at [Functor_StrictEq_Setoid] with [eq_refl] on
   objects, and the two [Example]s, at [eq_refl], each restated in
   Test/ProbeResolution482.v (C22, C23), which also holds the positive
   controls: [EM_Comparison] at [MSet_adj LZ] satisfies the two
   hypotheses of [bare_awodey_refuted] (C18, C19) and is a comparison
   over the identity identification (C20) to which [EM_Comparison_unique]
   applies (C21), so that neither refutation is vacuous.  Twenty-two
   proofs end [Defined] and fourteen [Qed] (counted by token).  The
   [Defined]s, measured by closing each alone [Qed] in a copy of this
   file and naming the first command that then stops: [LZ]
   ([lz_swap_first]), [lz_swap_first] ([lz_swap_first_iso]),
   [lz_swap_first_iso] ([Phi_forget]), [lz_pick] ([K_not_EMC]),
   [SwapAct] ([Swap_map]), [Swap_MSet] ([K_forget]), [K_forget]
   ([K_forget_components]), [KF_to] and [KF_from] (each [KF_iso]),
   [KF_iso] ([K_free]), [K_free] ([K_Comparison]), [phi_fun]
   ([phi_hom]), [phi_hom] ([Phi]), [Phi] ([Phi_free_strict]),
   [phi0_fun] ([phi0_hom]), [phi0_hom] ([Phi0]), [Phi0]
   ([Phi0_free_strict]), [Phi0_EMC_iso] ([Phi0_EMC]), [theta_sigma_to]
   and [theta_sigma_from] (each [theta_sigma]), [theta_sigma]
   ([theta_sigma_component]): twenty-one load-bearing.  [K_Comparison],
   which no later command reads, is [Defined] by the data convention
   only.

   UNIVERSES, read off [About] under Set Printing Universes, every one of
   the forty-two names (the [.glob] heads; no [Program] is used and no
   obligation or subproof constant exists).  Every name is universe
   polymorphic, binding zero to six levels; no block mentions [Set] and
   none carries an equation.  The six names on [option bool] alone,
   [lz_op] to [lz_swap_swap] but [LZ], bind no level; [LZ] and [SwapAct]
   bind o, the level of the carrier and of its equality
   (LZ : MonObject@{o o o}); every other name binds o and so, with
   o < so, so the level of the objects of [Sets@{o so}], the bound
   Instance/Sets.v's [Sets] carries.  The Printed section adds the
   levels u and u0 of the Kleisli and Eilenberg–Moore categories there,
   with o < u (o < u0 at [phi_hom] and [phi0_hom]);
   [K_no_coherent_comparison] binds the three further levels that
   [Comparison] and [EM_Comparison_theta] bring.  The Sigma section
   declares m1 and m2, the object and hom levels of [Monads Sets], apart,
   and its five names bind them: θ_σ's type reads Isomorphism@{m1 m2 m2}
   over Monads@{so o m1 m2}, where, unannotated in a copy of this file,
   minimization identified them, Isomorphism@{so so so} over
   Monads@{so o so so} (under Set Printing All; the artifact of issue
   #1363).  The standard library's caps (compose and ID, Specif's
   Projections, Datatypes' projections and prod_rect,
   Logic_lemmas.equality, and eq_ind and eq_rect with their variants)
   are inherited from the donors, none as a strict bound.  Compiled on
   Coq 8.19.2 and 8.20.1 in source overlays, each of the forty-two names
   binds the same number of levels as on Rocq 9.1.1, with no equation and
   no [Set] (compared by [About], by script).

   NOT DELIVERED.  Mac Lane's reading with an equality in both places, as
   an equation of functors in Coq: #475's strict uniqueness for the
   Kleisli comparison needed a coherence hypothesis on its object
   equations (Monad/Kleisli/Comparison.v's
   [Kleisli_Comparison_unique_of_strict]), and the same would be needed
   here.  A counterexample over a group, where σ would have to be an
   outer automorphism, is not given. *)

(* ------------------------------------------------------------------------ *)
(** ** The monoid {1, a, b} and the automorphism σ swapping a and b *)

(* 1 is [None]; a and b are [Some true] and [Some false], each a left
   zero: x y = x unless x = 1. *)
Definition lz_op (x y : option bool) : option bool :=
  match x with None => y | Some c => Some c end.

Lemma lz_op_assoc (x y z : option bool) :
  lz_op x (lz_op y z) = lz_op (lz_op x y) z.
Proof. destruct x, y, z; reflexivity. Qed.

Lemma lz_op_unit_r (x : option bool) : lz_op x None = x.
Proof. destruct x; reflexivity. Qed.

Definition LZ@{o} : MonObject@{o o o}.
Proof.
  unshelve refine
    (@Build_MonObject@{o o o}
       (@Build_SetoidObject@{o o} (option bool) (eq_Setoid@{o} (option bool)))
       None lz_op _ _ _ _).
  - intros x x' Hx y y' Hy; simpl in *; subst; reflexivity.
  - exact lz_op_assoc.
  - intros x; reflexivity.
  - exact lz_op_unit_r.
Defined.

(* σ: an automorphism, not inner, since 1 is the only unit. *)
Definition lz_swap (x : option bool) : option bool :=
  match x with None => None | Some c => Some (negb c) end.

Lemma lz_swap_op (x y : option bool) :
  lz_swap (lz_op x y) = lz_op (lz_swap x) (lz_swap y).
Proof. destruct x as [[]|], y as [[]|]; reflexivity. Qed.

Lemma lz_swap_swap (x : option bool) : lz_swap (lz_swap x) = x.
Proof. destruct x as [[]|]; reflexivity. Qed.

(* σ × 1 on the carrier LZ × X of the free LZ-set on X. *)
Definition lz_swap_first@{o so} (X : SetoidObject@{o o}) :
  act_prod LZ@{o} X ~{Sets@{o so}}~> act_prod LZ@{o} X.
Proof.
  unshelve refine {| morphism := fun p => (lz_swap (fst p), snd p) |}.
  intros p q [H1 H2]; simpl in *.
  split; [ simpl; rewrite H1; reflexivity | exact H2 ].
Defined.

Definition lz_swap_first_iso@{o so} (X : SetoidObject@{o o}) :
  @Isomorphism Sets@{o so} (act_prod LZ@{o} X) (act_prod LZ@{o} X).
Proof.
  unshelve refine (@Build_Isomorphism Sets@{o so} _ _
                     (lz_swap_first@{o so} X) (lz_swap_first@{o so} X) _ _).
  - intros [g x]; simpl. split; [ apply lz_swap_swap | reflexivity ].
  - intros [g x]; simpl. split; [ apply lz_swap_swap | reflexivity ].
Defined.

(* The element k of LZ × 1, as a map 1 → LZ × 1: a Kleisli arrow 1 → 1
   of LZ × (−), and, extended by [MSet_extend], the right multiplication
   by k of the free LZ-set on 1. *)
Definition lz_pick@{o so} (k : option bool) :
  unit_setoid_object@{o o}
    ~{Sets@{o so}}~> act_prod LZ@{o} unit_setoid_object@{o o}.
Proof.
  unshelve refine {| morphism := fun u : poly_unit@{o} => (k, u) |}.
  intros u v H; simpl in *; subst; split; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The issue's reading, refuted at the adjunction of LZ-sets *)

(* σ*: an action restricted along σ. *)
Definition SwapAct@{o} (A : MSetoidAction@{o o o o o o o o} LZ@{o}) :
  MSetoidAction@{o o o o o o o o} LZ@{o}.
Proof.
  unshelve refine
    (@Build_MSetoidAction@{o o o o o o o o} LZ@{o} (act_setoid A)
       (fun (g : option bool) (x : carrier (act_setoid A)) =>
          act A (lz_swap g) x) _ _ _).
  - intros g g' Hg x x' Hx; simpl in Hg; subst.
    apply act_respects; [ reflexivity | exact Hx ].
  - intros x; simpl. exact (act_unit A x).
  - intros g h x; simpl.
    rewrite lz_swap_op.
    exact (act_op A (lz_swap g) (lz_swap h) x).
Defined.

Definition Swap_map@{o so} {A B : MSetoidAction@{o o o o o o o o} LZ@{o}}
  (f : A ~{MSet@{so so o o o o o o} LZ@{o}}~> B) :
  SwapAct A ~{MSet@{so so o o o o o o} LZ@{o}}~> SwapAct B :=
  @Build_Equivariant LZ@{o} (SwapAct A) (SwapAct B) (equiv_map f)
    (fun g x => equivar f (lz_swap g) x).

Definition Swap_MSet@{o so} :
  MSet@{so so o o o o o o} LZ@{o} ⟶ MSet@{so so o o o o o o} LZ@{o}.
Proof.
  unshelve refine
    (@Build_Functor (MSet@{so so o o o o o o} LZ@{o})
       (MSet@{so so o o o o o o} LZ@{o}) SwapAct
       (fun A B f => Swap_map@{o so} f) _ _ _).
  - intros A B f f' Hf x. exact (Hf x).
  - intros A x. reflexivity.
  - intros A B C f g x. reflexivity.
Defined.

(* K, the comparison functor after σ*. *)
Definition K_swap@{o so} :
  MSet@{so so o o o o o o} LZ@{o}
    ⟶ @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} LZ@{o})
          (ActMonad@{o so} LZ@{o}) :=
  EM_Comparison (MSet_adj@{o so} LZ@{o}) ◯ Swap_MSet@{o so}.

(* U^T K = U, with identity components. *)
Lemma K_forget@{o so} :
  EM_Forget (ActF@{o so} LZ@{o}) ◯ K_swap@{o so} ≈ MSet_Forget@{o so} LZ@{o}.
Proof.
  exists (fun A => iso_id).
  intros A B f x; simpl. reflexivity.
Defined.

Example K_forget_components@{o so}
  (A : MSetoidAction@{o o o o o o o o} LZ@{o}) :
  `1 K_forget@{o so} A = iso_id := eq_refl.

Definition KF_to@{o so} (X : SetoidObject@{o o}) :
  fobj[K_swap@{o so} ◯ MSet_Free@{o so} LZ@{o}] X
    ~{@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} LZ@{o})
        (ActMonad@{o so} LZ@{o})}~>
  fobj[EM_Free (ActF@{o so} LZ@{o})] X.
Proof.
  unshelve refine
    (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} LZ@{o})
       (ActMonad@{o so} LZ@{o}) _ _ _ _ (lz_swap_first@{o so} X) _).
  intros [g [h x]]; simpl.
  split; [ destruct g as [[]|], h as [[]|]; reflexivity | reflexivity ].
Defined.

Definition KF_from@{o so} (X : SetoidObject@{o o}) :
  fobj[EM_Free (ActF@{o so} LZ@{o})] X
    ~{@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} LZ@{o})
        (ActMonad@{o so} LZ@{o})}~>
  fobj[K_swap@{o so} ◯ MSet_Free@{o so} LZ@{o}] X.
Proof.
  unshelve refine
    (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} LZ@{o})
       (ActMonad@{o so} LZ@{o}) _ _ _ _ (lz_swap_first@{o so} X) _).
  intros [g [h x]]; simpl.
  split; [ destruct g as [[]|], h as [[]|]; reflexivity | reflexivity ].
Defined.

Definition KF_iso@{o so} (X : SetoidObject@{o o}) :
  @Isomorphism (@EilenbergMoore@{so so so o} Sets@{o so}
                  (ActF@{o so} LZ@{o}) (ActMonad@{o so} LZ@{o}))
    (fobj[K_swap@{o so} ◯ MSet_Free@{o so} LZ@{o}] X)
    (fobj[EM_Free (ActF@{o so} LZ@{o})] X).
Proof.
  unshelve refine (@Build_Isomorphism _ _ _ (KF_to X) (KF_from X) _ _).
  - intros [g x]; simpl.
    split; [ apply lz_swap_swap | reflexivity ].
  - intros [g x]; simpl.
    split; [ apply lz_swap_swap | reflexivity ].
Defined.

(* K F ≅ F^T, through σ × 1. *)
Lemma K_free@{o so} :
  K_swap@{o so} ◯ MSet_Free@{o so} LZ@{o} ≈ EM_Free (ActF@{o so} LZ@{o}).
Proof.
  exists KF_iso.
  intros X Y f [g x]; simpl.
  split; [ symmetry; apply lz_swap_swap | reflexivity ].
Defined.

(* No natural isomorphism K ≅ EM_Comparison: with f its leg at the free
   LZ-set on 1 and c := f (1, ∗), f (k, ∗) is σ(k) c, f being a map of
   algebras into the twisted action, and c k, f commuting with the right
   multiplication by k; LZ has no such c. *)
Lemma K_not_EMC@{o so} :
  K_swap@{o so} ≈ EM_Comparison (MSet_adj@{o so} LZ@{o}) → False.
Proof.
  intros [iso nat].
  set (R := fobj[MSet_Free@{o so} LZ@{o}] unit_setoid_object@{o o}).
  set (f := t_alg_hom[from (iso R)]).
  set (t := t_alg_hom[to (iso R)]).
  assert (Hf : ∀ g h : option bool,
             fst (f (lz_op g h, ttt)) = lz_op (lz_swap g) (fst (f (h, ttt)))).
  { intros g h.
    exact (fst (@t_alg_hom_commutes _ _ _ _ _ _ _ (from (iso R))
                  (g, (h, ttt)))). }
  assert (Hr : ∀ k : option bool,
             fst (f (k, ttt)) = lz_op (fst (f (None, ttt))) k).
  { intros k.
    pose proof (nat R R (@MSet_extend@{o so} LZ@{o} _ R (lz_pick@{o so} k))
                  (f (None, ttt))) as Hn.
    pose proof (iso_to_from (iso R) (None, ttt)) as Htf.
    destruct Hn as [Hn _], Htf as [Htf1 Htf2].
    simpl in Hn, Htf1, Htf2.
    fold t f in Hn, Htf1, Htf2.
    rewrite Htf1, Htf2 in Hn.
    exact (eq_sym Hn). }
  pose proof (Hf (Some true) None) as E1; simpl in E1.
  pose proof (Hf (Some false) None) as E2; simpl in E2.
  pose proof (eq_trans (eq_sym (Hr (Some true))) E1) as E3.
  pose proof (eq_trans (eq_sym (Hr (Some false))) E2) as E4.
  revert E3 E4.
  generalize (fst (f (None, ttt))).
  intros [[]|]; discriminate.
Qed.

(* The issue's reading of Awodey's clause, refuted. *)
Theorem bare_awodey_refuted@{o so} :
  ¬ (∀ K' : MSet@{so so o o o o o o} LZ@{o}
              ⟶ @EilenbergMoore@{so so so o} Sets@{o so}
                    (ActF@{o so} LZ@{o}) (ActMonad@{o so} LZ@{o}),
       EM_Forget (ActF@{o so} LZ@{o}) ◯ K' ≈ MSet_Forget@{o so} LZ@{o} →
       K' ◯ MSet_Free@{o so} LZ@{o} ≈ EM_Free (ActF@{o so} LZ@{o}) →
       K' ≈ EM_Comparison (MSet_adj@{o so} LZ@{o})).
Proof.
  intros H.
  exact (K_not_EMC (H K_swap K_forget K_free)).
Qed.

(* The coherence is what excludes K: no comparison over the identity
   identification of the two monads has a functor ≈ K. *)
Corollary K_no_coherent_comparison@{o so +}
  (P : Comparison (@EM_Adjunction Sets@{o so} (ActF@{o so} LZ@{o})
                     (ActMonad@{o so} LZ@{o}))
         (MSet_adj@{o so} LZ@{o})
         (EM_Comparison_theta (MSet_adj@{o so} LZ@{o}))) :
  cmp_functor _ _ _ P ≈ K_swap@{o so} → False.
Proof.
  intros HP.
  apply K_not_EMC.
  transitivity (cmp_functor _ _ _ P).
  - symmetry. exact HP.
  - exact (EM_Comparison_unique (MSet_adj LZ) P).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Awodey's printed reading, refuted at the Kleisli resolution *)

Section Printed.

Universes o so.
Constraint o < so.

Local Notation SetsU := Sets@{o so}.
Local Notation LZU := LZ@{o}.
Local Notation TU := (ActF@{o so} LZ@{o}).
Local Notation HU := (ActMonad@{o so} LZ@{o}).
Local Notation Kl := (@Kleisli SetsU TU HU).
Local Notation KlFree := (@Kleisli_Free SetsU TU HU).
Local Notation KlForget := (@Kleisli_Forget SetsU TU HU).
Local Notation KlAdj := (@Kleisli_Adjunction SetsU TU HU).
Local Notation KFF := (KlForget ◯ KlFree).
Local Notation TK := (Adjunction_Induced_Monad KlAdj).
Local Notation EMK := (@EilenbergMoore SetsU KFF TK).
Local Notation FT := (@EM_Free SetsU KFF TK).
Local Notation UT := (@EM_Forget SetsU KFF TK).

(* The free extension of σ ∘ f: (k, x) ↦ (k σ((f x)₁), (f x)₂). *)
Definition phi_fun {X Y : SetoidObject@{o o}} (f : X ~{Kl}~> Y) :
  act_prod LZU X ~{SetsU}~> act_prod LZU Y.
Proof.
  unshelve refine
    {| morphism := fun p =>
         (lz_op (fst p) (lz_swap (fst (f (snd p)))), snd (f (snd p))) |}.
  intros p q [H1 H2]; simpl in *.
  destruct (proper_morphism f _ _ H2) as [E1 E2]; simpl in *.
  split; [ simpl; rewrite H1, E1; reflexivity | exact E2 ].
Defined.

Definition phi_hom {X Y : SetoidObject@{o o}} (f : X ~{Kl}~> Y) :
  fobj[FT] X ~{EMK}~> fobj[FT] Y.
Proof.
  unshelve refine (@Build_TAlgebraHom SetsU KFF TK _ _ _ _ (phi_fun f) _).
  intros [g [k x]]; simpl.
  split; [ | reflexivity ].
  destruct g as [[]|], k as [[]|], (fst (f x)) as [[]|]; reflexivity.
Defined.

Definition Phi : Kl ⟶ EMK.
Proof.
  unshelve refine
    (@Build_Functor Kl EMK (fun X => fobj[FT] X)
       (fun X Y f => phi_hom f) _ _ _).
  - intros X Y f f' Hf [k x]; simpl.
    destruct (Hf x) as [E1 E2]; simpl in *.
    split; [ simpl; rewrite E1; reflexivity | exact E2 ].
  - intros X [k x]; simpl.
    split; [ destruct k as [[]|]; reflexivity | reflexivity ].
  - intros X Y Z f g [k x]; simpl.
    split; [ simpl; rewrite lz_swap_op, lz_op_assoc; reflexivity
           | reflexivity ].
Defined.

(* Φ ∘ F = F^T at Theory/Functor.v's strict functor equality. *)
Lemma Phi_free_strict :
  @equiv _ (@Functor_StrictEq_Setoid _ _) (Phi ◯ KlFree) FT.
Proof.
  exists (fun X => eq_refl).
  intros X Y f [k x]; simpl.
  split; reflexivity.
Qed.

(* U^T ∘ Φ ≅ U, through σ × 1. *)
Lemma Phi_forget : UT ◯ Phi ≈ KlForget.
Proof.
  exists lz_swap_first_iso.
  intros X Y f [k x]; simpl.
  split; [ | reflexivity ].
  destruct k as [[]|], (fst (f x)) as [[]|]; reflexivity.
Qed.

(* No natural isomorphism Φ ≅ the comparison functor: at the one-point
   setoid, with s its leg into Φ, which fixes a and b, and c the first
   component of its other leg at (1, ∗), σ(k) would be the first
   component of s (c k, ∗) for every k. *)
Lemma Phi_not_EMC : Phi ≈ EM_Comparison KlAdj → False.
Proof.
  intros [iso nat].
  set (t := t_alg_hom[to (iso unit_setoid_object@{o o})]).
  set (s := t_alg_hom[from (iso unit_setoid_object@{o o})]).
  assert (Hs : ∀ (c : bool) (u : poly_unit@{o}),
             fst (s (Some c, u)) = Some c).
  { intros c u.
    pose proof (@t_alg_hom_commutes _ _ _ _ _ _ _
                  (from (iso unit_setoid_object@{o o}))
                  (Some c, (None, u))) as E.
    destruct E as [E _]. simpl in E. exact E. }
  assert (Hn : ∀ k : option bool,
             lz_swap k
               = fst (s (lz_op (fst (t (None, ttt))) k, snd (t (None, ttt))))).
  { intros k.
    pose proof (nat unit_setoid_object@{o o} unit_setoid_object@{o o}
                  (lz_pick@{o so} k) (None, ttt)) as E.
    destruct E as [E _]. simpl in E.
    exact E. }
  pose proof (Hn (Some true)) as E1.
  pose proof (Hn (Some false)) as E2.
  destruct (fst (t (None, ttt))) as [c|]; simpl in E1, E2.
  - rewrite Hs in E1, E2. rewrite <- E1 in E2. discriminate E2.
  - rewrite Hs in E1. discriminate E1.
Qed.

(* The free extension Φ₀ of f itself has the same property and is ≈ the
   comparison functor. *)
Definition phi0_fun {X Y : SetoidObject@{o o}} (f : X ~{Kl}~> Y) :
  act_prod LZU X ~{SetsU}~> act_prod LZU Y.
Proof.
  unshelve refine
    {| morphism := fun p =>
         (lz_op (fst p) (fst (f (snd p))), snd (f (snd p))) |}.
  intros p q [H1 H2]; simpl in *.
  destruct (proper_morphism f _ _ H2) as [E1 E2]; simpl in *.
  split; [ simpl; rewrite H1, E1; reflexivity | exact E2 ].
Defined.

Definition phi0_hom {X Y : SetoidObject@{o o}} (f : X ~{Kl}~> Y) :
  fobj[FT] X ~{EMK}~> fobj[FT] Y.
Proof.
  unshelve refine (@Build_TAlgebraHom SetsU KFF TK _ _ _ _ (phi0_fun f) _).
  intros [g [k x]]; simpl.
  split; [ | reflexivity ].
  destruct g as [[]|], k as [[]|], (fst (f x)) as [[]|]; reflexivity.
Defined.

Definition Phi0 : Kl ⟶ EMK.
Proof.
  unshelve refine
    (@Build_Functor Kl EMK (fun X => fobj[FT] X)
       (fun X Y f => phi0_hom f) _ _ _).
  - intros X Y f f' Hf [k x]; simpl.
    destruct (Hf x) as [E1 E2]; simpl in *.
    split; [ simpl; rewrite E1; reflexivity | exact E2 ].
  - intros X [k x]; simpl.
    split; [ destruct k as [[]|]; reflexivity | reflexivity ].
  - intros X Y Z f g [k x]; simpl.
    split; [ simpl; rewrite lz_op_assoc; reflexivity | reflexivity ].
Defined.

Lemma Phi0_free_strict :
  @equiv _ (@Functor_StrictEq_Setoid _ _) (Phi0 ◯ KlFree) FT.
Proof.
  exists (fun X => eq_refl).
  intros X Y f [k x]; simpl.
  split; reflexivity.
Qed.

Lemma Phi0_forget : UT ◯ Phi0 ≈ KlForget.
Proof.
  exists (fun X => iso_id).
  intros X Y f [k x]; simpl.
  split; reflexivity.
Qed.

Definition Phi0_EMC_iso (X : SetoidObject@{o o}) :
  @Isomorphism EMK (fobj[Phi0] X) (fobj[EM_Comparison KlAdj] X).
Proof.
  unshelve refine (@Build_Isomorphism EMK (fobj[Phi0] X)
    (fobj[EM_Comparison KlAdj] X)
    (@Build_TAlgebraHom SetsU KFF TK _ _ (projT2 (fobj[Phi0] X))
       (projT2 (fobj[EM_Comparison KlAdj] X)) id _)
    (@Build_TAlgebraHom SetsU KFF TK _ _
       (projT2 (fobj[EM_Comparison KlAdj] X)) (projT2 (fobj[Phi0] X))
       id _) _ _).
  - intros [g [k x]]; simpl.
    split; [ destruct g as [[]|]; reflexivity | reflexivity ].
  - intros [g [k x]]; simpl.
    split; [ destruct g as [[]|]; reflexivity | reflexivity ].
  - intros [k x]; simpl. split; reflexivity.
  - intros [k x]; simpl. split; reflexivity.
Defined.

Lemma Phi0_EMC : Phi0 ≈ EM_Comparison KlAdj.
Proof.
  exists Phi0_EMC_iso.
  intros X Y f [k x]; simpl.
  split; reflexivity.
Qed.

(* Awodey's printed property, U^T Φ ≅ U and Φ F = F^T, has two solutions
   that are not isomorphic. *)
Theorem printed_awodey_not_unique :
  ∃ Φ1 Φ2 : Kl ⟶ EMK,
    (UT ◯ Φ1 ≈ KlForget) *
    (@equiv _ (@Functor_StrictEq_Setoid _ _) (Φ1 ◯ KlFree) FT) *
    (UT ◯ Φ2 ≈ KlForget) *
    (@equiv _ (@Functor_StrictEq_Setoid _ _) (Φ2 ◯ KlFree) FT) *
    (Φ1 ≈ Φ2 → False).
Proof.
  exists Phi, Phi0.
  refine (Phi_forget, Phi_free_strict, Phi0_forget, Phi0_free_strict, _).
  intros H. apply Phi_not_EMC.
  transitivity Phi0; [ exact H | exact Phi0_EMC ].
Qed.

End Printed.

(* ------------------------------------------------------------------------ *)
(** ** K is a comparison, over the monad automorphism θ_σ *)

Section Sigma.

(* m1 and m2, the object and hom levels of [Monads Sets], kept apart. *)
Universes o so m1 m2.
Constraint o < so.

Local Notation TE := (Adjunction_Induced_Monad
  (@EM_Adjunction Sets@{o so} (ActF@{o so} LZ@{o})
     (ActMonad@{o so} LZ@{o}))).

Definition theta_sigma_to :
  MonadHom (Adjunction_Induced_Monad (MSet_adj@{o so} LZ@{o})) TE.
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform'
           (F:=MSet_Forget@{o so} LZ@{o} ◯ MSet_Free@{o so} LZ@{o})
           (G:=EM_Forget (ActF@{o so} LZ@{o}) ◯ EM_Free (ActF@{o so} LZ@{o}))
           (fun X => lz_swap_first@{o so} X) _ |}.
  - intros X Y f [k x]; simpl. split; reflexivity.
  - intros X x; simpl. split; reflexivity.
  - intros X [g [k x]]; simpl.
    split; [ simpl; apply lz_swap_op | reflexivity ].
Defined.

Definition theta_sigma_from :
  MonadHom TE (Adjunction_Induced_Monad (MSet_adj@{o so} LZ@{o})).
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform'
           (F:=EM_Forget (ActF@{o so} LZ@{o}) ◯ EM_Free (ActF@{o so} LZ@{o}))
           (G:=MSet_Forget@{o so} LZ@{o} ◯ MSet_Free@{o so} LZ@{o})
           (fun X => lz_swap_first@{o so} X) _ |}.
  - intros X Y f [k x]; simpl. split; reflexivity.
  - intros X x; simpl. split; reflexivity.
  - intros X [g [k x]]; simpl.
    split; [ simpl; apply lz_swap_op | reflexivity ].
Defined.

(* θ_σ, an isomorphism in [Monads Sets] with components σ × 1. *)
Definition theta_sigma :
  @Isomorphism (Monads@{_ _ m1 m2} Sets@{o so})
    (MSet_Forget@{o so} LZ@{o} ◯ MSet_Free@{o so} LZ@{o};
     Adjunction_Induced_Monad (MSet_adj@{o so} LZ@{o}))
    (EM_Forget (ActF@{o so} LZ@{o}) ◯ EM_Free (ActF@{o so} LZ@{o}); TE).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{_ _ m1 m2} Sets@{o so})
    (MSet_Forget@{o so} LZ@{o} ◯ MSet_Free@{o so} LZ@{o};
     Adjunction_Induced_Monad (MSet_adj@{o so} LZ@{o}))
    (EM_Forget (ActF@{o so} LZ@{o}) ◯ EM_Free (ActF@{o so} LZ@{o}); TE)
    theta_sigma_to theta_sigma_from _ _).
  - intros X [k x]; simpl. split; [ apply lz_swap_swap | reflexivity ].
  - intros X [k x]; simpl. split; [ apply lz_swap_swap | reflexivity ].
Defined.

Example theta_sigma_component (X : SetoidObject@{o o}) :
  transform[mh_transform (to theta_sigma)] X = lz_swap_first@{o so} X
  := eq_refl.

(* K, with the triangles [K_free] and [K_forget], is a comparison over
   θ_σ, where [EM_Comparison] is one over the identity identification. *)
Definition K_Comparison :
  Comparison (@EM_Adjunction Sets@{o so} (ActF@{o so} LZ@{o})
                (ActMonad@{o so} LZ@{o}))
    (MSet_adj@{o so} LZ@{o}) theta_sigma.
Proof.
  unshelve refine {| cmp_functor := K_swap@{o so};
                     cmp_left := K_free@{o so};
                     cmp_right := K_forget@{o so} |}.
  intros X [k x]; simpl. split; reflexivity.
Defined.

End Sigma.
