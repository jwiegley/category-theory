Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Type-indexed logical predicates and relations for the STLC. *)

(* "Log" here is the *logical relation* / logical predicate of Tait-style
   reducibility, not logarithms or logging.  Given a base predicate [P] on
   well-typed terms, [ExpP] lifts [P] type-directed through the syntax so that
   it is closed under the eliminators (application, projections); [ExpR] is the
   binary analogue lifting a base relation [R].  [Norm.v] instantiates [ExpP]
   with [halts] to obtain the strong-normalization predicate [SN := ExpP halts]
   and runs Tait's reducibility argument.

   Writing [τ |- e] for "[e : Exp Γ τ]", the unary predicate reads:

       ExpP P (e : TyUnit)    :=  P e
       ExpP P (e : σ × ρ)     :=  P e ∧ ExpP P (Fst e) ∧ ExpP P (Snd e)
       ExpP P (e : σ ⟶ ρ)     :=  P e ∧ ∀ x, ExpP P x → ExpP P (APP e x)

   so a function is reducible exactly when it sends reducible arguments to
   reducible results — the arrow case of Tait's "candidat de réductibilité".
   The binary [ExpR] follows the standard logical-relations recipe: related
   functions map related arguments to related results,
   [ExpR R f1 f2] at [σ ⟶ ρ] requiring [∀ x1 x2, ExpR R x1 x2 →
   ExpR R (APP f1 x1) (APP f2 x2)].
   See W. W. Tait, "Intensional interpretations of functionals of finite type
   I", and J. Gallier, "On Girard's 'Candidats de Reductibilité'",
   https://www.cis.upenn.edu/~jean/sngirard.pdf, and
   https://en.wikipedia.org/wiki/Logical_relations.

   Note: [A] and [L : HostExprs A] below are vestigial context.  No class named
   [HostExprs] is in scope, so [Generalizable All Variables] silently treats it
   as a free variable to be generalized; since nothing here depends on [A] or
   [L], both are dropped from the resulting definitions.  They are kept as a
   record of the intended host-language extension point used in sibling files
   (compare the analogous [HostExprsSem] note in [Instance/Lambda.v]). *)

Section Log.

Context {A : Type}.
Context `{L : HostExprs A}.
Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Type.

(** [ExpP] lifts the base predicate [P] type-directed through the syntax. *)
Equations ExpP `(e : Exp Γ τ) : Type :=
  ExpP (τ:=_ ⟶ _) e := P e ∧ (∀ x, ExpP x → ExpP (APP e x));
  ExpP (τ:=_ × _) e := P e ∧ ExpP (Fst e) ∧ ExpP (Snd e);
  ExpP e := P e.

(* [SubP] extends [ExpP] pointwise to substitutions: every pushed term is
   reducible. *)
Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

(* The base predicate is the head component at every type (CR1-style
   extraction): reducibility implies [P]. *)
Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in X; now reduce. Qed.

Variable R : ∀ {τ}, Exp Γ τ → Exp Γ τ → Type.

(** [ExpR] is the binary analogue of [ExpP], lifting the base relation [R]. *)
Equations ExpR {τ} (e1 e2 : Exp Γ τ) : Type :=
  ExpR (τ:=_ ⟶ _) f1 f2 :=
    R f1 f2 ∧ (∀ x1 x2, ExpR x1 x2 → ExpR (APP f1 x1) (APP f2 x2));
  ExpR (τ:=_ × _) e1 e2 :=
    R e1 e2 ∧ ExpR (Fst e1) (Fst e2) ∧ ExpR (Snd e1) (Snd e2);
  ExpR e1 e2 := R e1 e2.

(* The base relation is the head component at every type: relatedness implies
   [R]. *)
Lemma ExpR_R {τ} {e1 e2 : Γ ⊢ τ} : ExpR e1 e2 → R e1 e2.
Proof. intros; induction τ; simpl in *; simp ExpR in X; now reduce. Qed.

(* [SubR] extends [ExpR] pointwise to substitutions. *)
Inductive SubR : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubR : SubR (NoSub (Γ:=Γ))
  | PushR {Γ' τ} (e e' : Exp Γ τ) (s : Sub Γ Γ') :
    ExpR e e' → SubR s → SubR (Push e s).

Derive Signature for SubR.

End Log.
