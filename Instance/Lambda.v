Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sem.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** The syntactic cartesian closed category of the simply-typed lambda calculus. *)

(* nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
   Wikipedia: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

   This file is the top of the simply-typed lambda calculus (STLC) development
   in Instance/Lambda/ (syntax in Ty.v/Exp.v, de Bruijn renaming/weakening in
   Ren.v, the standard-model interpretation into Coq in Sem.v).  It packages
   that syntax as a category and exhibits its cartesian closed structure, the
   categorical half of the Curry-Howard-Lambek correspondence: STLC is the
   internal language of cartesian closed categories (Lambek & Scott).

   Fixing a typing context `Γ`, the category [Lambda Γ] has

     - objects        types `τ : Ty`,
     - morphisms      `a ~> b  :=  Exp Γ (a ⟶ b)`, i.e. open terms of function
                      type in context `Γ`,
     - identity       `LAM (VAR ZV)`              (the term `λx. x`),
     - composition    `LAM (APP (wk f) (APP (wk g) (VAR ZV)))`   (`λx. f (g x)`).

   Morphism equivalence is *semantic*, not syntactic: `f ≈ g` holds when the
   interpretations `SemExp f` and `SemExp g` agree on every environment (see
   [Exp_Setoid]).  This is the denotational, not the β/η-quotient, equality;
   the laws below are therefore discharged by `SemExp_*` rewriting rather than
   by reasoning about reductions.  The cartesian closed structure is then read
   off the term language: `TyUnit` is terminal, `TyPair` gives products with
   the `Pair`/`Fst`/`Snd` introduction and projections, and `TyArrow` gives
   exponentials with the usual [curry]/[uncurry] adjunction.

   Note: `A` and `L : HostExprsSem A` below are vestigial context.  No class
   named `HostExprsSem` is in scope, so `Generalizable All Variables` quietly
   treats it as a free variable to be generalized; since nothing in this file
   depends on `A` or `L`, both are dropped and [Lambda] reduces to `Env →
   Category` (confirmed by `About Lambda`).  They are kept here as a record of
   the intended host-language extension point used in the sibling files. *)

(* The Curry-Howard-Lambek correspondence, and what it is for

   nLab:
   https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory

   The correspondence realized here was assembled in three stages.  Church
   introduced the simply typed calculus to avoid the paradoxical use of
   the untyped theory (Church, "A formulation of the simple theory of
   types", Journal of Symbolic Logic 1940).  Curry had observed in 1934
   that the types of the combinators read as axiom schemes of
   intuitionistic implicational logic (Curry and Feys, "Combinatory
   Logic", 1958), and Howard's 1969 manuscript, published as "The
   formulae-as-types notion of construction" (Academic Press 1980), made
   the proofs-as-terms analogy explicit.  Lambek supplied the third
   vertex: intuitionistic proofs, typed terms, and the morphisms of a
   cartesian closed category share one equational theory, whence the name
   Curry-Howard-Lambek.  The definitive syntactic statement appears in
   the same Curry Festschrift as Howard's paper — lambda theories
   correspond to cartesian closed categories exactly as algebraic
   theories correspond to Lawvere's finite-product categories (Lambek,
   "From lambda calculus to cartesian closed categories", Academic Press
   1980) — and the book form is Part I of Lambek and Scott, "Introduction
   to Higher Order Categorical Logic" (Cambridge University Press 1986).
   The earlier "Deductive Systems and Categories" chapter of that history
   is told in Structure/Closed.v, whose header names this file as the
   syntactic realization.

   Within the library the theorem is witnessed from both sides.  This
   file is the syntax-to-category direction: the closed structure is read
   off the type formers, so that [fork], [exl], [exr], [curry] and
   [uncurry] below are categorical combinators written as de Bruijn
   terms.  Instance/Coq.v supplies a semantic cartesian closed category,
   and the standard model of Instance/Lambda/Sem.v is the interpretation
   from the one to the other.  One consequence of the semantic equality
   of [Exp_Setoid] deserves emphasis: with [TyUnit] the only base type,
   the standard model identifies more terms than βη-conversion does.  It
   follows that [Lambda Γ] is the image of the syntactic category inside
   the standard model, not the free cartesian closed category of Lambek's
   theorem on the nose.

   The representation has its own ancestry.  Rather than pair a raw term
   with a separate typing derivation, the encoding makes an [Exp] its own
   derivation — the intrinsically-typed representation of Altenkirch and
   Reus ("Monadic Presentations of Lambda Terms Using Generalized
   Inductive Types", CSL 1999).  Its Coq discipline — terms indexed by
   context and type, substitution bootstrapped from renaming,
   coercion-free at simple types — is that of Benton, Hur, Kennedy and
   McBride ("Strongly Typed Term Representations in Coq", Journal of
   Automated Reasoning 2012), and the Ren.v-before-Sub.v layering of the
   sibling files repeats it exactly.

   The correspondence is executable, and the applications exploit that.
   The Categorical Abstract Machine compiles ML-family languages by
   translating lambda terms into exactly such combinators — the
   operations of a cartesian closed category as machine instructions —
   and gave CAML its name (Cousineau, Curien and Mauny, "The categorical
   abstract machine", Science of Computer Programming 1987).  Elliott
   runs the same idea inside GHC: because the simply typed calculus is
   modeled by any cartesian closed category, one program text can be
   reinterpreted in alternative such categories — hardware circuits,
   automatic differentiation, interval analysis (Elliott, "Compiling to
   categories", ICFP 2017).  Downstream, the sibling files make the
   operational reading concrete: call-by-value small-step reduction
   (Instance/Lambda/Step.v) is sound for this semantics
   (Instance/Lambda/Sound.v); β-reduction is strongly normalizing, by the
   computability method of Tait ("Intensional interpretations of
   functionals of finite type I", Journal of Symbolic Logic 1967)
   implemented in Instance/Lambda/Norm.v; and a CEK machine executes
   closed terms with runs checked by `eq_refl` (Instance/Lambda/Eval.v,
   Instance/Lambda/Example.v).  End to end, the development proves that
   well-typed syntax forms a cartesian closed category, that the standard
   model interprets it, that evaluation is sound for that model, and that
   every closed term halts. *)

Section Lambda.

Context {A : Type}.
Context `{L : HostExprsSem A}.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

#[export]
Program Instance TyArrow_Setoid {dom cod} : Setoid (SemTy (dom ⟶ cod)) := {
  equiv := λ f g, f ≈[Coq] g
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

#[export]
Program Instance Exp_Setoid {Γ dom cod} : Setoid (Exp Γ (dom ⟶ cod)) := {
  equiv := λ f g, ∀ E, SemExp f E ≈ SemExp g E
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

Lemma SemExp_identity {Γ τ} (E : SemEnv Γ) :
  SemExp (identity Γ τ) E ≈ id.
Proof. now f_equal. Qed.

Lemma SemExp_composition `(E : SemEnv Γ) {τ τ' τ''}
      (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f g) E ≈ SemExp f E ∘ SemExp g E.
Proof.
  intro.
  unfold composition; simpl.
  now rewrite !SemExp_wk.
Qed.

#[export]
Program Instance composition_respects {Γ τ τ' τ''} :
  Proper (equiv ==> equiv ==> equiv) (@composition Γ τ τ' τ'').
Next Obligation.
  unfold composition; simpl.
  rewrite !SemExp_wk.
  now rewrite H, H0.
Qed.

Lemma composition_identity_right {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition f (identity Γ τ) ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_identity_left {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition (identity Γ τ') f ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_assoc {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition f (composition g h) ≈
  composition (composition f g) h.
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

Lemma composition_assoc_sym {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition (composition f g) h ≈
  composition f (composition g h).
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

#[local] Obligation Tactic := intros.

Program Definition Lambda Γ : Category := {|
  obj     := Ty;
  hom     := λ A B : Ty, Exp Γ (A ⟶ B);
  homset  := @Exp_Setoid Γ;
  id      := @identity Γ;
  compose := @composition Γ;

  compose_respects := @composition_respects Γ;

  id_left := @composition_identity_left Γ;
  id_right := @composition_identity_right Γ;
  comp_assoc := @composition_assoc Γ;
  comp_assoc_sym := @composition_assoc_sym Γ;
|}.

#[export]
Program Instance Lambda_Terminal Γ : @Terminal (Lambda Γ) := {
  terminal_obj := TyUnit;            (* the unit type is the terminal object *)
  one := λ _, LAM EUnit              (* the unique map `λ_. ()` into it *)
}.
Next Obligation.
  repeat intro.
  now destruct (SemExp f E x0), (SemExp g E x0).
Qed.

#[export]
Program Instance Lambda_Cartesian Γ : @Cartesian (Lambda Γ) := {
  product_obj := TyPair;             (* the pair type is the categorical product *)
  fork := λ _ _ _ f g,               (* `⟨f, g⟩ := λx. (f x, g x)` *)
    LAM (Pair (APP (wk f) (VAR ZV)) (APP (wk g) (VAR ZV)));
  exl  := λ _ _, LAM (Fst (VAR ZV)); (* first projection `λp. fst p` *)
  exr  := λ _ _, LAM (Snd (VAR ZV)); (* second projection `λp. snd p` *)
}.
Next Obligation.
  proper.
  rewrite !SemExp_wk.
  now rewrite X, X0.
Qed.
Next Obligation.
  split; repeat intro; simpl.
  - split; intros; rewrite !SemExp_wk.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
  - destruct X.
    rewrite !SemExp_wk.
    rewrite <- e, <- e0.
    simp Keep; simpl.
    rewrite !SemExp_wk.
    simp RenVar; simpl.
    apply surjective_pairing.
Qed.

Definition curry {Γ a b c} (f : Exp Γ (a × b ⟶ c)) : Exp Γ (a ⟶ b ⟶ c) :=
  LAM (LAM (APP (wk (wk f)) (Pair (VAR (SV ZV)) (VAR ZV)))).

Definition uncurry {Γ a b c} (f : Exp Γ (a ⟶ b ⟶ c)) : Exp Γ (a × b ⟶ c) :=
  LAM (APP (APP (wk f) (Fst (VAR ZV))) (Snd (VAR ZV))).

#[local] Obligation Tactic := program_simpl.

#[export]
Program Instance Lambda_Closed Γ : @Closed (Lambda Γ) _ := {
  exponent_obj := TyArrow;           (* the function type is the exponential object *)
  exp_iso := λ _ _ _,                (* the natural iso `Hom(a×b,c) ≅ Hom(a,b⟶c)` *)
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
}.
Next Obligation.
  proper.
  extensionality z.
  unfold wk at 1.
  unfold wk at 2.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  rewrite !SemExp_wk.
  eauto.
Qed.
Next Obligation.
  proper.
  rewrite !SemExp_wk; simpl.
  congruence.
Qed.
Next Obligation.
  extensionality z.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  rewrite SemExp_wk.
  now repeat setoid_rewrite RenSem_skip1; simpl.
Qed.
Next Obligation.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  repeat setoid_rewrite RenSem_skip1; simpl.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.
Next Obligation.
  simp RenVar; simpl.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.

End Lambda.
