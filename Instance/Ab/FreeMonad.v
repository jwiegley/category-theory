Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.

Generalizable All Variables.

(** * The free abelian group monad ℤ[−] on Set, and Ab ≅ Set^{ℤ[−]} *)

(* Book: Riehl, "Category Theory in Context", §5.3, the construction
         opening the section, printed pp. 195-196 (PDF pp. 215-216) —
         riehl:5.3:construction-ab-monadic, the box issue #472 appends
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         §VI.4, Exercise 2, printed p. 146 (PDF p. 155) — the case R = ℤ
         of maclane:VI.4:ex2, whose general ring is
         Instance/Mod/FreeMonad.v
   nLab: https://ncatlab.org/nlab/show/free+abelian+group
   nLab: https://ncatlab.org/nlab/show/monadic+functor

   WHAT THE BOOK SAYS, read from the PDF.  "The free ⊣ forgetful
   adjunction … between sets and abelian groups … induces a monad Z[−] on
   Set.  Given a set S, Z[S] is the set of finite formal Z-linear
   combinations of elements of S, and the map Z[f] … carries a formal sum
   n1 s1 + ⋯ + nk sk … to the formal sum n1 f(s1) + ⋯ + nk f(sk) …  there
   is a unique functor from the category of abelian groups to the
   category of Z[−]-algebras that commutes with the left and right
   adjoints.  The image of an abelian group A is the algebra consisting of
   the underlying set of A together with the "evaluation" map
   ϵ_A : Z[A] → A that interprets a finite formal sum as a single element
   of A.  In fact, this functor defines an isomorphism of categories: to
   equip a set A with an "evaluation" function ev : Z[A] → A, so that
   diagrams … commute is precisely to give A the structure of an abelian
   group", the triangle "a 'sanity check' … that it sends a singleton sum
   a ∈ Z[A] to the element a", and an algebra homomorphism "a function
   f : A → B that preserves the evaluation of formal sums, i.e., a group
   homomorphism".

   ROUTE (i), TAKEN.  Instance/Ab/Free.v's free abelian group, in the
   hom-set form [free_ab_adjunction_hom] #472 adds there (its counit
   computes; Ab/Free.v's CORRECTION (#472)).  [FreeAbF] is U ◯ F and
   [FreeAbMonad] is ℤ[−], Monad/Comparison.v's [Adjunction_Induced_Monad]
   of it: ℤ[X] is the free group's setoid of formal sums ([ZM_obj],
   [ZM_carrier]), η the insertion ([ZM_ret], [ZM_ret_fun]), μ = U ε F the
   flattening ([ZM_join_counit], [ZM_join_gen], [ZM_join_fun],
   [ZM_join_zero]), all at [eq_refl]; ℤ[f] relabels at ≈
   ([ZM_map_equiv]), refused at [eq_refl] (Test/ProbeFreeModule472.v,
   R26).  [Ab_K] is the comparison Ab → Set^{ℤ[−]}, [EM_Comparison] of
   the adjunction: K A = ⟨A, ε_A⟩, ε_A the evaluation of a formal sum
   ([Ab_K_alg_fun]), a ↦ a, 0 ↦ 0, ⟨a⟩ + ⟨b⟩ ↦ a + b and −⟨a⟩ ↦ −a at
   [eq_refl] ([Ab_K_alg_*]), K f = f ([Ab_K_map]); it commutes with the
   right adjoints and with the left ones, each up to a natural
   isomorphism whose components are identities (Monad/Comparison.v's two
   triangles at this adjunction, [Ab_K_Forget] and [Ab_K_Free]): that
   file's [EM_Comparison_Forget] and [EM_Comparison_Free] build them so
   (its header; [iso_id], and [EM_Comparison_Free_iso]'s identity
   arrows), and all four end [Qed], so that the components are identities
   is read from that file's source and no readback pins it here
   (Instance/Mod/FreeMonad.v's twins are [RMod_K_Forget] and
   [RMod_K_Free]).
   [EM_to_AbS] sends (A, ev) to [zm_alg_ab]: 0 = ev⟨⟩, a + b =
   ev(⟨a⟩ + ⟨b⟩), −a = ev(−⟨a⟩); the triangle is [zm_alg_unit], every
   group law one instance of [zm_alg_eval_respects], and ev IS the sum in
   that group at ≈ ([zm_alg_fold]); an algebra map is additive
   ([zm_alg_hom_step]).  [Ab_EM_iso : Ab ≅[Cat] Set^{ℤ[−]}] has legs K
   and [EM_to_AbS] and identity components, to and from, at [eq_refl];
   [Ab_EM_equivalence] and [Ab_Forget_Monadic : Monadic Ab_Forget].  The
   argument is Instance/Mod/FreeMonad.v's part (c) without the action,
   and [PropEquiv] again costs no hypothesis ([zm_alg_prop]); issue #1357
   tracks a shared Eilenberg–Moore lemma for term-model monads, keeping
   identity components, that would remove this parallel and its siblings
   in #470 and #471.

   RIEHL'S "ISOMORPHISM OF CATEGORIES".  By Instance/Cat.v an
   isomorphism in Cat is an equivalence of categories, which the identity
   components bring toward hers; the strict identity of Ab and its
   algebras is refused (R27 to R29).  Issue #484 keeps the strict reading
   ([StrictlyMonadic], isomorphism of categories on the nose).  Her Z[S]
   as integer combinations: the carrier here is Ab/Free.v's formal sums
   of generators and their negatives, and that each is a finite
   ℤ-combination is not proved for it (Ab/Free.v's WHAT IS NOT
   DELIVERED); T_R at [Int_Ring] has that reading, but its comparison
   with ℤ[−] is not made.

   ROUTE (ii), MEASURED AND NOT TAKEN.  ℤ[−] as T_R at [Int_Ring] with
   Ab ≅ RMod Int_Ring: no such equivalence is in the tree, only
   Instance/Mod/Cogenerator.v's one-way [Ab_to_ZMod] (#454).  #472's
   scout built it (every ℤ-module's action agrees with the iterated sum,
   ~25 lines) and composed it with [RMod_EM_iso Int_Ring]: the Require of
   Cogenerator.v takes the closure from 70 modules to 191, the composite's
   [iso_from_to] component is refused as the identity ([iso_compose]'s
   obligations), and no [Monadic Ab_Forget] follows, there being no
   monadicity-transport lemma in tree.  Two of the scout's findings
   complete that account.  The 121 modules are Cogenerator.v's own
   closure, not [Ab_to_ZMod]'s: relocated (about 40 lines) to a light
   file, it costs 7, measured on #472's tree by [Print Libraries] after a
   [Require] of Instance/Mod/FreeMonad.v (71 [Category] modules) with
   Instance/Ab/Monoidal.v, whose [zsmul] family it uses (78), and 11 with
   Adjunction/Unitalization.v too, where its [zsmul_mul] lives (82),
   against Cogenerator.v's 192.  And a composite built by hand rather than
   by [iso_compose] would keep identity components (not prototyped).
   Route (i) stays the one taken on fidelity, not cost: Riehl's statement
   is the comparison functor of the free-forgetful adjunction Set ⇄ Ab
   itself, which route (ii) does not give, and the tree has no lemma that
   would transport [Monadic] along Ab ≅ RMod Int_Ring.  Issue #1356 (Ab ≅
   RMod ℤ, and ℤ[−] ≅ T_ℤ as monads; linked to #1150) tracks that
   comparison.

   STRENGTHS.  Every [Example] holds at [eq_refl], restated in the probe.  At ≈
   only: [ZM_map_equiv], [zm_alg_step], [zm_alg_fold], [zm_alg_hom_step] (the
   twins of Instance/Mod/FreeMonad.v's first four) and the
   inverse laws of the isomorphism in Cat; [zm_fold_is_alg_eval] is Leibniz, by
   induction.  Eight proofs end [Defined] (counted by token) and seven are
   load-bearing, measured as in Instance/Mod/FreeMonad.v: [zm_alg_prop]
   ([EM_to_AbS_prop]), [zm_alg_hom_ab] ([EM_to_AbS]), [EM_to_AbS]
   ([Ab_EM_counit_iso]), [Ab_EM_counit_iso] and [Ab_EM_unit_iso]
   ([Ab_EM_equivalence]), [Ab_EM_equivalence] ([Ab_EM_counit_component]) and
   [Ab_EM_iso] ([Ab_EM_iso_to]); [Ab_Forget_Monadic] is [Defined] by the data
   convention only.  Eleven lemmas end [Qed].

   UNIVERSES, read off [About].  The section binds Sets@{c so} and every
   name binds c so first, with c < so.  A closed binder is refused, so
   each is extensible: forty-four names, ℤ[−] and the names built on it
   other than those below ([Ab_K_Forget] among them), bind six more,
   the group category's object level g (Set < g, c < g, Instance/Ab.v's
   [Ab]), Theory/Functor.v's [Compose] level and [FreeAb]'s four internal
   levels; ten bind g and the four: K, its eight readbacks ([Ab_K_carrier]
   to [Ab_K_alg_neg]) and [Ab_K_Free]; [fa_relabel]
   and [fa_flatten] bind g alone; five readbacks comparing across a
   composite bind a second copy (nine or twelve in all), and [ZM_carrier]
   one more for its equation's sort.  The isomorphism in Cat binds k
   (c < k, so < k) and there g is so (Set < so).  No [Set] but these
   bounds, and no equation; no explicit universe instance of a new
   constant is written.  On Coq 8.19.2 and 8.20.1 every name binds the
   same levels (compared by [About]).

   NOT DELIVERED.  The uniqueness of the comparison functor (Riehl's
   "unique functor", Proposition 5.2.13); the strict isomorphism (#484); a
   computing ℤ[f]; the comparison of ℤ[−] with T_R at [Int_Ring], and
   Ab ≃ RMod Int_Ring, which issue #1356 tracks (filed from #472's review,
   linked to #1150, whose ℤ comparison for tensor products waits on the
   same ℤ-module structure of [AbObject]). *)

Section FreeAbMonad.

Universes c so.

(* ℤ[−] = U ◯ F, with F Instance/Ab/Free.v's [FreeAb]. *)
Definition FreeAbF@{+} : Sets@{c so} ⟶ Sets@{c so} := Ab_Forget ◯ FreeAb.

(* ℤ[−], the monad of the hom-set form of the free-forgetful
   adjunction. *)
Definition FreeAbMonad@{+} : @Monad Sets@{c so} FreeAbF :=
  Adjunction_Induced_Monad free_ab_adjunction_hom.

(* The relabelling of a formal sum along u: the fold of insert ∘ u. *)
Definition fa_relabel@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : FATerm Y :=
  fa_eval (A := FreeAbObject Y) (free_ab_insert Y ∘ u) t.

(* A formal sum of formal sums, flattened: the fold of the identity. *)
Definition fa_flatten@{+} {X : Sets@{c so}}
  (k : FATerm (Ab_Forget (FreeAbObject X))) : FATerm X :=
  fa_eval (A := FreeAbObject X)
    (@id Sets@{c so} (Ab_Forget (FreeAbObject X))) k.

(* ℤ[X] is the free group's setoid, whose carrier is the formal sums. *)
Example ZM_obj@{+} (X : Sets@{c so}) :
  fobj[FreeAbF] X = Ab_Forget (FreeAbObject X) := eq_refl.

Example ZM_carrier@{+} (X : Sets@{c so}) :
  carrier (fobj[FreeAbF] X) = FATerm X := eq_refl.

(* η_X is the insertion of generators, as a setoid map, and x ↦ ⟨x⟩. *)
Example ZM_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeAbMonad X = free_ab_insert X := eq_refl.

Example ZM_ret_fun@{+} (X : Sets@{c so}) (x : carrier X) :
  @ret _ _ FreeAbMonad X x = fa_gen x := eq_refl.

(* μ = U ε F, which flattens. *)
Example ZM_join_counit@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom (FreeAb X))
  := eq_refl.

Example ZM_join_gen@{+} (X : Sets@{c so}) (t : FATerm X) :
  @join _ _ FreeAbMonad X (@fa_gen (Ab_Forget (FreeAbObject X)) t) = t
  := eq_refl.

Example ZM_join_fun@{+} (X : Sets@{c so})
  (k : FATerm (Ab_Forget (FreeAbObject X))) :
  @join _ _ FreeAbMonad X k = fa_flatten k := eq_refl.

Example ZM_join_zero@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X fa_zero = fa_zero := eq_refl.

(* ℤ[u] relabels, up to ≈: Riehl's n1 s1 + ⋯ + nk sk ↦ n1 f(s1) + ⋯ +
   nk f(sk). *)
Lemma ZM_map_equiv@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : fmap[FreeAbF] u t ≈ fa_relabel u t.
Proof.
  apply (free_ab_extend_unique (FreeAbObject Y) (free_ab_insert Y ∘ u)
           (fmap[FreeAb] u)).
  intro x. exact (free_ab_fmap_generators u x).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The comparison functor Ab → Set^{ℤ[−]} *)

Definition ZMAlg@{+} : Category@{so c c} :=
  @EilenbergMoore@{so so so c} Sets@{c so} FreeAbF FreeAbMonad.

Definition Ab_K@{+} : Ab ⟶ ZMAlg := EM_Comparison free_ab_adjunction_hom.

(* Riehl's "commutes with the left and right adjoints": Monad/
   Comparison.v's two triangles, at this adjunction. *)
Theorem Ab_K_Forget@{+} :
  @EM_Forget Sets@{c so} FreeAbF FreeAbMonad ◯ Ab_K ≈ Ab_Forget.
Proof. exact (EM_Comparison_Forget free_ab_adjunction_hom). Qed.

Theorem Ab_K_Free@{+} :
  Ab_K ◯ FreeAb ≈ @EM_Free Sets@{c so} FreeAbF FreeAbMonad.
Proof. exact (EM_Comparison_Free free_ab_adjunction_hom). Qed.

Section Algebra.

Context {A : Sets@{c so}}.
Context (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A).

(* The group operations of an algebra (A, ev): 0 = ev⟨⟩,
   a + b = ev(⟨a⟩ + ⟨b⟩) and −a = ev(−⟨a⟩). *)
Definition zm_alg_zero@{+} : carrier A := t_alg[α] (@fa_zero A).

Definition zm_alg_plus@{+} (x y : carrier A) : carrier A :=
  t_alg[α] (@fa_plus A (fa_gen x) (fa_gen y)).

Definition zm_alg_neg@{+} (x : carrier A) : carrier A :=
  t_alg[α] (@fa_neg A (fa_gen x)).

(* The sum the formal sum names, through the operations just defined. *)
Fixpoint zm_alg_eval@{+} (t : FATerm A) : carrier A :=
  match t with
  | fa_gen x    => x
  | fa_zero     => zm_alg_zero
  | fa_plus s u => zm_alg_plus (zm_alg_eval s) (zm_alg_eval u)
  | fa_neg s    => zm_alg_neg (zm_alg_eval s)
  end.

(* Riehl's "sanity check": ev sends a singleton sum a to a. *)
Lemma zm_alg_unit@{+} (x : carrier A) : t_alg[α] (@fa_gen A x) ≈ x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* ev ∘ μ ≈ ev ∘ ℤ[ev], read through the relabelling. *)
Lemma zm_alg_step@{+} (K : FATerm (fobj[FreeAbF] A)) :
  t_alg[α] (@join _ _ FreeAbMonad A K) ≈ t_alg[α] (fa_relabel t_alg[α] K).
Proof.
  symmetry.
  refine (transitivity _ (@t_action _ _ _ _ α K)).
  apply (proper_morphism t_alg[α]).
  symmetry. exact (ZM_map_equiv t_alg[α] K).
Qed.

Lemma zm_alg_plus_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) zm_alg_plus.
Proof.
  intros x x' Hx y y' Hy.
  exact (proper_morphism t_alg[α] _ _ (fae_plus (fae_gen Hx) (fae_gen Hy))).
Qed.

Lemma zm_alg_neg_respects@{+} : Proper (equiv ==> equiv) zm_alg_neg.
Proof.
  intros x x' Hx.
  exact (proper_morphism t_alg[α] _ _ (fae_neg (fae_gen Hx))).
Qed.

(* The evaluation IS the sum in the derived group. *)
Lemma zm_alg_fold@{+} (t : FATerm A) : t_alg[α] t ≈ zm_alg_eval t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl.
  - exact (zm_alg_unit x).
  - reflexivity.
  - refine (transitivity
              (zm_alg_step
                 (@fa_plus (fobj[FreeAbF] A)
                    (@fa_gen (fobj[FreeAbF] A) s)
                    (@fa_gen (fobj[FreeAbF] A) u))) _).
    exact (zm_alg_plus_respects _ _ IHs _ _ IHu).
  - refine (transitivity
              (zm_alg_step
                 (@fa_neg (fobj[FreeAbF] A) (@fa_gen (fobj[FreeAbF] A) s))) _).
    exact (zm_alg_neg_respects _ _ IHs).
Qed.

Lemma zm_alg_eval_respects@{+} (s t : FATerm A) :
  fa_eq s t → zm_alg_eval s ≈ zm_alg_eval t.
Proof.
  intro H.
  refine (transitivity (symmetry (zm_alg_fold s)) _).
  refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
  exact (zm_alg_fold t).
Qed.

(* Every algebra's carrier is propositional, with no hypothesis: x ≈ y
   iff ⟨x⟩ ≈ ⟨y⟩ in ℤ[A], a [Prop]. *)
Definition zm_alg_prop@{+} : PropEquiv (is_setoid A).
Proof using A α.
  unshelve refine
    (@Build_PropEquiv _ (is_setoid A)
       (fun x y => @fa_eq A (fa_gen x) (fa_gen y)) _ _).
  - intros x y H.
    refine (transitivity (symmetry (zm_alg_unit x)) _).
    refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
    exact (zm_alg_unit y).
  - intros x y H. exact (fae_gen H).
Defined.

(* The abelian group of the algebra: each law is one instance of
   [zm_alg_eval_respects] at a constructor of [fa_eq], so that "the
   values assigned to the sums of sums (a1 + a2) + (a3) and (a1) +
   (a2 + a3) are equal" is associativity. *)
Definition zm_alg_ab@{+} : AbObject := {|
  ab_cmon := {|
    cmon_setoid := A;
    cmon_zero := zm_alg_zero;
    cmon_plus := zm_alg_plus;
    cmon_plus_respects := zm_alg_plus_respects;
    cmon_plus_assoc := fun x y z =>
      zm_alg_eval_respects _ _ (fae_assoc (fa_gen x) (fa_gen y) (fa_gen z));
    cmon_plus_comm := fun x y =>
      zm_alg_eval_respects _ _ (fae_comm (fa_gen x) (fa_gen y));
    cmon_plus_zero_l := fun x =>
      zm_alg_eval_respects _ _ (fae_zero_l (fa_gen x));
    cmon_prop := zm_alg_prop
  |};
  ab_neg := zm_alg_neg;
  ab_neg_respects := zm_alg_neg_respects;
  ab_neg_left := fun x => zm_alg_eval_respects _ _ (fae_neg_l (fa_gen x))
|}.

End Algebra.

(* An algebra map is additive: Riehl's "a function f : A → B that
   preserves the evaluation of formal sums, i.e., a group homomorphism". *)
Lemma zm_alg_hom_step@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y)
  (t : FATerm (projT1 x)) :
  t_alg_hom[f] (t_alg[projT2 x] t)
    ≈ t_alg[projT2 y] (fa_relabel t_alg_hom[f] t).
Proof.
  refine (transitivity (@t_alg_hom_commutes _ _ _ _ _ _ _ f t) _).
  apply (proper_morphism t_alg[projT2 y]).
  exact (ZM_map_equiv t_alg_hom[f] t).
Qed.

Definition zm_alg_hom_ab@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  zm_alg_ab (projT2 x) ~{Ab}~> zm_alg_ab (projT2 y).
Proof.
  refine (@Build_CMonHom (zm_alg_ab (projT2 x)) (zm_alg_ab (projT2 y))
            t_alg_hom[f] _ _).
  - exact (zm_alg_hom_step f fa_zero).
  - intros a b. exact (zm_alg_hom_step f (fa_plus (fa_gen a) (fa_gen b))).
Defined.

(* The functor Set^{ℤ[−]} → Ab. *)
Definition EM_to_AbS@{+} : ZMAlg ⟶ Ab.
Proof.
  unshelve refine
    (@Build_Functor ZMAlg Ab (fun x => zm_alg_ab (projT2 x))
       (fun x y f => zm_alg_hom_ab f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The fold of the identity in the derived group IS [zm_alg_eval]
   (Leibniz, by induction). *)
Lemma zm_fold_is_alg_eval@{+} {A : Sets@{c so}}
  (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A) (t : FATerm A) :
  fa_eval (A := zm_alg_ab α) (@id Sets@{c so} (Ab_Forget (zm_alg_ab α))) t
  = zm_alg_eval α t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl;
    try rewrite IHs; try rewrite IHu; reflexivity.
Qed.

(* The algebra round trip, with the identity as its component. *)
Definition Ab_EM_counit_iso@{+} (x : ZMAlg) :
  @Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 (fobj[Ab_K ◯ EM_to_AbS] x)) (projT2 x)
          (@id Sets@{c so} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Ab_K ◯ EM_to_AbS] x))
          (@id Sets@{c so} (projT1 x)) _) _ _).
  - intro t.
    change (fa_eval (A := zm_alg_ab (projT2 x))
              (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
            ≈ t_alg[projT2 x] (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x) t).
    refine (transitivity (symmetry (zm_alg_fold (projT2 x) t)) _).
    apply (proper_morphism t_alg[projT2 x]).
    symmetry. exact (@fmap_id _ _ FreeAbF (projT1 x) t).
  - intro t.
    change (t_alg[projT2 x] t
            ≈ fa_eval (A := zm_alg_ab (projT2 x))
                (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x))))
                (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x)).
    refine (transitivity (zm_alg_fold (projT2 x) t) _).
    apply zm_alg_eval_respects.
    exact (fae_sym (@fmap_id _ _ FreeAbF (projT1 x) t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The group round trip, with the identity as its component: on a group
   the derived operations ARE its own. *)
Definition Ab_EM_unit_iso@{+} (G : Ab) :
  @Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G.
Proof.
  unshelve refine
    (@Build_Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G
       (@Build_CMonHom (fobj[EM_to_AbS ◯ Ab_K] G) G
          (@id Sets@{c so} (Ab_Forget G)) _ _)
       (@Build_CMonHom G (fobj[EM_to_AbS ◯ Ab_K] G)
          (@id Sets@{c so} (Ab_Forget G)) _ _) _ _).
  all: simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. *)
Definition Ab_EM_equivalence@{+} :
  @EquivalenceOfCategories Ab ZMAlg Ab_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => iso_sym (Ab_EM_unit_iso G)). intros G H f a. reflexivity.
Defined.

(* Abelian groups are monadic over Set. *)
Definition Ab_Forget_Monadic@{+} : Monadic Ab_Forget.
Proof.
  exists FreeAb. exists free_ab_adjunction_hom. exact Ab_EM_equivalence.
Defined.

(* Ab ≅ Set^{ℤ[−]} in Cat, from the two component isomorphisms. *)
Definition Ab_EM_iso@{k +} : @Isomorphism Cat@{k so so so c} Ab ZMAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{k so so so c} Ab ZMAlg Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => Ab_EM_unit_iso G). intros G H f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* K G is ⟨G, U ε_G⟩: the evaluation of a formal sum to its actual sum. *)
Example Ab_K_carrier@{+} (G : Ab) : projT1 (fobj[Ab_K] G) = Ab_Forget G
  := eq_refl.

Example Ab_K_map@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  t_alg_hom[fmap[Ab_K] f] = fmap[Ab_Forget] f := eq_refl.

Example Ab_K_alg@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)]
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom G) := eq_refl.

Example Ab_K_alg_fun@{+} (G : Ab) (t : FATerm (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] t = fa_eval (@id Sets@{c so} (Ab_Forget G)) t
  := eq_refl.

Example Ab_K_alg_gen@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_gen x) = x := eq_refl.

Example Ab_K_alg_zero@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)] fa_zero = cmon_zero G := eq_refl.

Example Ab_K_alg_plus@{+} (G : Ab) (x y : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_plus (fa_gen x) (fa_gen y))
    = cmon_plus G x y := eq_refl.

Example Ab_K_alg_neg@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_neg (fa_gen x)) = ab_neg G x := eq_refl.

(* The legs of the isomorphism in Cat. *)
Example Ab_EM_iso_to@{+} : to Ab_EM_iso = Ab_K := eq_refl.

Example Ab_EM_iso_from@{+} : from Ab_EM_iso = EM_to_AbS := eq_refl.

(* The group of an algebra: its carrier, its [Prop] equality and its
   operations. *)
Example EM_to_AbS_prop@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_AbS] x)) a b
    = @fa_eq (projT1 x) (fa_gen a) (fa_gen b) := eq_refl.

Example EM_to_AbS_carrier@{+} (x : ZMAlg) :
  cmon_setoid (fobj[EM_to_AbS] x) = projT1 x := eq_refl.

Example EM_to_AbS_zero@{+} (x : ZMAlg) :
  cmon_zero (fobj[EM_to_AbS] x) = t_alg[projT2 x] fa_zero := eq_refl.

Example EM_to_AbS_plus@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  cmon_plus (fobj[EM_to_AbS] x) a b
    = t_alg[projT2 x] (fa_plus (fa_gen a) (fa_gen b)) := eq_refl.

Example EM_to_AbS_neg@{+} (x : ZMAlg) (a : carrier (projT1 x)) :
  ab_neg (fobj[EM_to_AbS] x) a = t_alg[projT2 x] (fa_neg (fa_gen a))
  := eq_refl.

Example EM_to_AbS_map@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  cmon_map (fmap[EM_to_AbS] f) = t_alg_hom[f] := eq_refl.

(* The round trips keep every operation on the nose ... *)
Example Ab_rt_carrier@{+} (G : Ab) :
  cmon_setoid (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_setoid G := eq_refl.

Example Ab_rt_zero@{+} (G : Ab) :
  cmon_zero (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_zero G := eq_refl.

Example Ab_rt_plus@{+} (G : Ab) :
  cmon_plus (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_plus G := eq_refl.

Example Ab_rt_neg@{+} (G : Ab) :
  ab_neg (fobj[EM_to_AbS ◯ Ab_K] G) = ab_neg G := eq_refl.

Example Ab_rt_hom@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  cmon_map (fmap[EM_to_AbS ◯ Ab_K] f) = cmon_map f := eq_refl.

(* ... and so do the carrier and the maps of the algebra round trip. *)
Example ZMAlg_rt_carrier@{+} (x : ZMAlg) :
  projT1 (fobj[Ab_K ◯ EM_to_AbS] x) = projT1 x := eq_refl.

Example ZMAlg_rt_alg_fun@{+} (x : ZMAlg) (t : FATerm (projT1 x)) :
  t_alg[projT2 (fobj[Ab_K ◯ EM_to_AbS] x)] t
    = fa_eval (A := zm_alg_ab (projT2 x))
        (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
  := eq_refl.

Example ZMAlg_rt_alg_hom@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  t_alg_hom[fmap[Ab_K ◯ EM_to_AbS] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity. *)
Example Ab_EM_iso_to_from_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Ab_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Ab_EM_iso) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_iso_from_to_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (iso_from_to Ab_EM_iso) G)),
   cmon_map (from (projT1 (iso_from_to Ab_EM_iso) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

(* ...and so is every component of the equivalence's counit and unit. *)
Example Ab_EM_counit_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_unit_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)),
   cmon_map (from (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

End FreeAbMonad.
