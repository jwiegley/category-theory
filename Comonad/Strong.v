Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Strong.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.Monoidal.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(** * Costrong comonads *)

(* nLab:      https://ncatlab.org/nlab/show/strong+monad
   nLab:      https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   A costrong comonad on a monoidal category (C, ⨂, I) is a comonad
   (W, ε = extract, δ = duplicate) whose endofunctor carries a tensorial
   costrength: a family

     costrength : W (x ⨂ y) ~> x ⨂ W y

   natural in both variables and coherent with the left unitor λ and the
   associator α ([costrength_id_left], [costrength_assoc], both arriving in
   their inverse orientations, as dualization inverts the structural
   isomorphisms), and compatible with the comonad structure:

     - ε-compat ([costrength_extract]):
         (id ⨂ ε) ∘ costrength ≈ ε            at  W (x ⨂ y) ~> x ⨂ y
     - δ-compat ([costrength_duplicate]):
         (id ⨂ δ) ∘ costrength ≈ costrength ∘ W costrength ∘ δ
                                                at  W (x ⨂ y) ~> x ⨂ W (W y)

   The notion is the formal dual of a (left) strong monad: a costrength for
   W over (C, ⨂) is exactly a strength for W^op over (C^op, ⨂^op).  Duality
   is built into this library so that (C^op)^op = C and (W^op)^op = W hold
   by reflexivity, and Construction/Opposite/Monoidal.v transports monoidal
   structure to the opposite category, so [CostrongComonad] is DEFINED as
   the in-tree [StrongMonad] (Monad/Strong.v) instantiated at
   (C^op, Monoidal_op M) on W^op — no second axiomatization.  The covariant
   accessors and laws below are definitional op-reads of the [StrongMonad]
   fields, in the style of Comonad/Core.v, and [Build_CostrongComonad]
   assembles the bundled structure back out of covariant data, so the
   unfolding runs in both directions.

   Following the [Monoidal_op] precedent, [CostrongComonad] and all the
   transfers in this file are Definitions, not Instances: registering them
   would let instance resolution silently equip a category with a
   (co)strength, which is rarely what an unannotated goal means.  Callers
   select them explicitly.

   Double-op caveat (see Construction/Opposite/Monoidal.v): although the
   underlying category and functor round-trip on the nose, the transported
   monoidal structure does not — [Monoidal_op (Monoidal_op M)] is not
   definitionally M, because the transport rebuilds the functor-law and
   coherence fields as fresh Qed-opaque proof terms.  A strong monad on
   (C, M) and a costrong comonad on (C^op, Monoidal_op M) are therefore
   interchanged by rebuilding the record field by field (every data and law
   component IS convertible across the two monoidal structures), and the
   resulting round trips are stated up to ≈ on the structure maps rather
   than as record equalities: see [StrongMonad_to_op_CostrongComonad],
   [op_CostrongComonad_to_StrongMonad] and the round-trip lemmas at the end
   of this file. *)

(* Why costrength matters

   nLab:  https://ncatlab.org/nlab/show/tensorial+costrength
   Paper: Blute, Cockett, Seely, J. Pure Appl. Algebra 116(1-3), 1997,
          pp. 49-98 (where the term "costrength" is introduced)
   Paper: Kock, Arch. Math. 23, 1972, pp. 113-120 (tensorial strength)

   Strength is what lets a functor travel through paired data.  In
   Moggi's semantics a bare monad cannot interpret programs with more
   than one free variable; the strength carries the ambient environment
   into the effectful computation, and Monad/Strong.v exists for that
   reason.  The comonadic situation is the mirror image: a context
   W (x ⨂ y) spanning a pair must be pushable onto a chosen factor,
   W (x ⨂ y) ~> x ⨂ W y, before a co-Kleisli program can consume the
   y-part in context while passing the x-part through.  That map is
   [costrength].  In Uustalu and Vene's account of dataflow the comonad
   plays the role that strong monads play in Moggi's semantics, with
   effects reintroduced through a distributive law of the comonad over
   a monad (APLAS 2005).

   Orientation deserves care, because the literature does not speak with
   one voice.  Dually to the left and right strengths
   x ⨂ F y ~> F (x ⨂ y), a left-costrength is F (x ⨂ y) ~> x ⨂ F y —
   the form of this file — and a right-costrength is
   F (x ⨂ y) ~> F x ⨂ y.  On a symmetric base either determines the
   other through the braiding, and one says simply "costrength"; on a
   non-symmetric base a full costrength further requires the two induced
   maps F (x ⨂ (y ⨂ z)) ~> (x ⨂ F y) ⨂ z to agree.  The term is due to
   Blute, Cockett and Seely (1997); nLab cautions that Power and
   Robinson (1997) use it for what is here a right-strength.

   Whether strength is data or property depends on the base.  For a
   closed monoidal V, a strength on an endofunctor of V is the same
   thing as a V-enrichment of it, so every endofunctor of Set carries a
   canonical strength; over a general monoidal base nothing of the sort
   holds, which is why the costrength here is data to be supplied
   ([Build_CostrongComonad] takes the family and its laws as inputs)
   rather than property to be derived.

   A final distinction separates strength from monoidality.  The
   programming face of comonads with monoidal structure is Haskell's
   ComonadApply, characterized in Kmett's Control.Comonad documentation
   as "a strong lax symmetric semi-monoidal comonad", under which
   extract and duplicate become symmetric monoidal natural
   transformations; it is the interface on which Foner's comonadic
   fixed point for spreadsheet-like recurrences is built (Haskell
   Symposium 2015).  Lax (semi)monoidal structure on the endofunctor is
   a further layer that this file does not axiomatize. *)

Definition CostrongComonad {C : Category} (M : @Monoidal C) (W : C ⟶ C) : Type :=
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op).

(* Mirroring [Existing Class Comonad] in Comonad/Core.v: [CostrongComonad]
   unfolds to the class [StrongMonad], but typeclass resolution keys on the
   head constant of a goal and does not look through this unfolding.
   Declaring [CostrongComonad] an existing class lets a costrong witness in
   scope be found when the accessors below insert their implicit argument.
   No instance of it is registered anywhere in this file, so no search space
   changes. *)
Existing Class CostrongComonad.

(* ================================================================== *)
(** ** The covariant API: definitional op-reads of the bundled fields  *)
(* ================================================================== *)

Section CostrongComonadAPI.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context {CS : CostrongComonad M W}.

(** The underlying comonad: the op-read of [strongmonad_is_monad]. *)
Definition costrong_is_comonad : @Comonad C W :=
  @strongmonad_is_monad (C^op) (@Monoidal_op C M) (W^op) CS.

(* Let [extract] and [duplicate] from Comonad/Core.v resolve against the
   underlying comonad in the statements below.  The registration is
   section-local and is dropped when the section closes. *)
#[local] Existing Instance costrong_is_comonad.

(** The underlying strong endofunctor over (C^op, Monoidal_op M): the
    op-read of [strongmonad_is_strong]. *)
Definition costrong_is_strong :
  @StrongFunctor (C^op) (@Monoidal_op C M) (W^op) :=
  @strongmonad_is_strong (C^op) (@Monoidal_op C M) (W^op) CS.

(** The costrength W (x ⨂ y) ~> x ⨂ W y: the covariant reading of
    [strength] at (C^op, Monoidal_op M, W^op). *)
Definition costrength {x y : C} : W (x ⨂ y) ~> x ⨂ W y :=
  @strength (C^op) (@Monoidal_op C M) (W^op) costrong_is_strong x y.

(** Joint naturality in both variables: the op-read of [strength_natural].
    The bundled field states the square with the two variables acted on
    separately (via the [Mapping] instances of Theory/Naturality.v); the
    bifunctor interchange law [bimap_id_right_left] merges the per-variable
    actions into the usual joint form. *)
Lemma costrength_natural {x y z w : C} (f : x ~> y) (k : z ~> w) :
  costrength ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ costrength.
Proof.
  pose proof (@strength_natural (C^op) (@Monoidal_op C M) (W^op)
                costrong_is_strong y x f w z k) as SN.
  simpl in SN.
  rewrite <- fmap_comp in SN.
  rewrite bimap_id_right_left in SN.
  rewrite comp_assoc in SN.
  rewrite bimap_id_right_left in SN.
  exact SN.
Qed.

(** Left-unitor coherence: the op-read of [strength_id_left].  Dualization
    inverts the unitor, so in C the law reads against λ⁻¹: precomposing the
    costrength with W (λ⁻¹) is λ⁻¹ at W x. *)
Lemma costrength_id_left {x : C} :
  costrength ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x)).
Proof.
  exact (@strength_id_left (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x).
Qed.

(** Associator coherence: the op-read of [strength_assoc], with α likewise
    arriving in its inverse orientation. *)
Lemma costrength_assoc {x y z : C} :
  costrength ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ costrength) ∘ costrength.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_assoc (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x y z).
Qed.

(** ε-compatibility, the dual of the Kock/Moggi η-compat law
    [strength_ret]: discarding the comonadic context of the right factor
    after applying the costrength is exactly extracting from the whole
    tensor. *)
Lemma costrength_extract {x y : C} :
  (id[x] ⨂ extract) ∘ costrength ≈ (extract : W (x ⨂ y) ~> x ⨂ y).
Proof.
  exact (@strength_ret (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

(** δ-compatibility, the dual of the μ-compat law [strength_join]:
    duplicating the right factor after applying the costrength agrees with
    duplicating the whole tensor and sliding the costrength through both
    W-layers. *)
Lemma costrength_duplicate {x y : C} :
  (id[x] ⨂ duplicate (x:=y)) ∘ costrength
    ≈ costrength ∘ fmap[W] costrength ∘ duplicate.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_join (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

End CostrongComonadAPI.

(* [costrength[W]] names the costrength of a given costrong comonad on W at
   implicit arguments, mirroring the [strength[F]] convention. *)
Notation "costrength[ W ]" := (@costrength _ _ W%functor _ _ _)
  (at level 9, format "costrength[ W ]") : morphism_scope.

(* ================================================================== *)
(** ** Building the bundled structure from covariant data              *)
(* ================================================================== *)

Section BuildCostrongComonad.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.

(* Predictable obligation alignment (the Monad/Kleisli.v precedent): with
   [program_simpl] the unitor and counit compatibility obligations are
   discharged by the tactic itself — their op-statements are convertible
   to the supplied hypotheses [sigma_id_left] and [sigma_extract], so it
   closes them from the local context.  Exactly three obligations remain,
   in order: naturality, the associator law, and δ-compatibility, each a
   re-bracketing of the corresponding covariant hypothesis. *)
#[local] Obligation Tactic := program_simpl.

(** [Build_CostrongComonad] assembles a [CostrongComonad] from a comonad
    together with a covariant costrength family satisfying the covariant
    laws — the inverse reading of the accessor layer above.  The data
    round trip is definitional: see [Build_CostrongComonad_costrength] and
    [Build_CostrongComonad_comonad] just below. *)
Program Definition Build_CostrongComonad
  (H : @Comonad C W)
  (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y)
  (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
    sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z)
  (sigma_id_left : forall x : C,
    sigma I x ∘ fmap[W] (from (@unit_left C M x))
      ≈ from (@unit_left C M (W x)))
  (sigma_assoc : forall x y z : C,
    sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
      ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
          ∘ sigma x ((y ⨂ z)%object))
  (sigma_extract : forall x y : C,
    (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y))
  (sigma_duplicate : forall x y : C,
    (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
      ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate)
  : CostrongComonad M W :=
  @Build_StrongMonad (C^op) (@Monoidal_op C M) (W^op) H
    (@Build_StrongFunctor (C^op) (@Monoidal_op C M) (W^op)
       (fun x y => sigma x y) _ _ _)
    _ _.
Next Obligation.
  (* strength_natural in C^op: merge the separated actions and apply the
     covariant naturality. *)
  rewrite <- fmap_comp.
  rewrite bimap_id_right_left.
  rewrite comp_assoc.
  rewrite bimap_id_right_left.
  apply sigma_natural.
Qed.
Next Obligation.
  (* strength_assoc in C^op: the op-read arrives right-bracketed. *)
  rewrite comp_assoc.
  apply sigma_assoc.
Qed.
Next Obligation.
  (* strength_join in C^op: likewise a re-bracketing of δ-compat. *)
  rewrite comp_assoc.
  apply sigma_duplicate.
Qed.

End BuildCostrongComonad.

Section BuildCostrongComonadAgreement.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).
Context (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y).
Context (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
  sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z).
Context (sigma_id_left : forall x : C,
  sigma I x ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x))).
Context (sigma_assoc : forall x y z : C,
  sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
        ∘ sigma x ((y ⨂ z)%object)).
Context (sigma_extract : forall x y : C,
  (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y)).
Context (sigma_duplicate : forall x y : C,
  (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
    ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate).

(** Reading the costrength back off the assembled structure returns the
    supplied family on the nose. *)
Lemma Build_CostrongComonad_costrength {x y : C} :
  @costrength C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) x y
    ≈ sigma x y.
Proof. reflexivity. Qed.

(** The underlying comonad passes through the assembly unchanged. *)
Lemma Build_CostrongComonad_comonad :
  @costrong_is_comonad C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) = H.
Proof. reflexivity. Qed.

End BuildCostrongComonadAgreement.

(* ================================================================== *)
(** ** Transfers: costrong comonads are strong monads on the opposite  *)
(* ================================================================== *)

(* On a FIXED base (C, M) the correspondence is definitional — a costrong
   comonad on (C, M) literally is a strong monad on (C^op, Monoidal_op M),
   so both passages are the identity and the round trips hold by
   reflexivity. *)

Definition CostrongComonad_to_op_StrongMonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (CS : CostrongComonad M W) :
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op) := CS.

Definition op_StrongMonad_to_CostrongComonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad M W := S.

Lemma CostrongComonad_op_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C} (CS : CostrongComonad M W) :
  op_StrongMonad_to_CostrongComonad (CostrongComonad_to_op_StrongMonad CS)
    = CS.
Proof. reflexivity. Qed.

Lemma op_StrongMonad_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad_to_op_StrongMonad (op_StrongMonad_to_CostrongComonad S)
    = S.
Proof. reflexivity. Qed.

Section StrongMonadOpposite.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {T : C ⟶ C}.

(* The other direction of the duality — a strong monad on (C, M) as a
   costrong comonad on (C^op, Monoidal_op M) — is where the double-op
   caveat bites: the target type unfolds to a [StrongMonad] over
   [Monoidal_op (Monoidal_op M)], which is not definitionally M (its law
   fields are rebuilt Qed-opaque; see Construction/Opposite/Monoidal.v).
   The records are therefore rebuilt field by field.  Every field converts:
   the tensor's object and morphism actions, and the to/from components of
   the transported unitors and associator, all reduce to those of M, so
   each projection of S is accepted at the reindexed type as it stands.
   Only the record types themselves differ, which is why the round trips
   below are stated on the structure maps (up to ≈, or as the literal
   passthrough of the monad component) rather than as record equalities. *)

Definition StrongMonad_to_op_CostrongComonad (S : @StrongMonad C M T) :
  @CostrongComonad (C^op) (@Monoidal_op C M) (T^op) :=
  @Build_StrongMonad ((C^op)^op)
    (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
    (@strongmonad_is_monad C M T S)
    (@Build_StrongFunctor ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
       (fun x y => @strength C M T (@strongmonad_is_strong C M T S) x y)
       (@strength_natural C M T (@strongmonad_is_strong C M T S))
       (@strength_id_left C M T (@strongmonad_is_strong C M T S))
       (@strength_assoc C M T (@strongmonad_is_strong C M T S)))
    (@strength_ret C M T S)
    (@strength_join C M T S).

Definition op_CostrongComonad_to_StrongMonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @StrongMonad C M T :=
  @Build_StrongMonad C M T
    (@strongmonad_is_monad ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@Build_StrongFunctor C M T
       (fun x y => @strength ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S) x y)
       (@strength_natural ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_id_left ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_assoc ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)))
    (@strength_ret ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@strength_join ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S).

(** Covariantly read, the costrength of the opposite costrong comonad IS
    the strength of the strong monad it came from. *)
Lemma op_costrength_strength (S : @StrongMonad C M T) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad S) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

(** Round trips.  The strength data survives both passages on the nose (so
    ≈ holds by reflexivity), and the underlying monad is passed through
    untouched; only the enclosing records differ, per the double-op caveat
    in the header. *)

Lemma StrongMonad_op_roundtrip_strength (S : @StrongMonad C M T) {x y : C} :
  @strength C M T
    (@strongmonad_is_strong C M T
       (op_CostrongComonad_to_StrongMonad
          (StrongMonad_to_op_CostrongComonad S))) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

Lemma StrongMonad_op_roundtrip_monad (S : @StrongMonad C M T) :
  @strongmonad_is_monad C M T
    (op_CostrongComonad_to_StrongMonad (StrongMonad_to_op_CostrongComonad S))
    = @strongmonad_is_monad C M T S.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_costrength
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    x y
    ≈ @costrength (C^op) (@Monoidal_op C M) (T^op) S x y.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_comonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    = @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op) S.
Proof. reflexivity. Qed.

End StrongMonadOpposite.
