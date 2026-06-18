Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.

(** Renaming (variable renaming / weakening) for the de Bruijn calculus *)

(* A [Ren Γ Γ'] is an order-preserving embedding (OPE, a.k.a. "thinning") of
   the context Γ' into the context Γ: it lists, in order, which slots of the
   larger context Γ are kept as the variables of the smaller context Γ'.  This
   is the inductive "category of weakenings" of Altenkirch-Hofmann-Streicher
   (1995) / order-preserving embeddings of Chapman (2009).

   The action of a renaming is contravariant: [RenVar]/[RenExp] transport a
   variable / term living in Γ' to one living in the larger Γ, so a renaming
   r : Ren Γ Γ' yields maps  Var Γ' τ → Var Γ τ  and  Exp Γ' τ → Exp Γ τ.
   With composition [RcR] this makes (Env, Ren) a category, and Var(-,τ) and
   Exp(-,τ) presheaves on it; the laws below are exactly its identity,
   associativity, and functoriality equations.

   de Bruijn indices:  https://ncatlab.org/nlab/show/de+Bruijn+index
                       https://en.wikipedia.org/wiki/De_Bruijn_index
   substitution / renaming:  https://ncatlab.org/nlab/show/substitution *)

Section Ren.

Import ListNotations.

(* Renamings as order-preserving embeddings (thinnings):
     NoRen  : the empty thinning [] ↪ []
     Drop r : skip the head slot of the source context (it has no pre-image)
     Keep r : keep the head slot, mapping it to the head of the target *)
Inductive Ren : Env → Env → Set :=
  | NoRen : Ren [] []
  | Drop {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) Γ'
  | Keep {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) (τ :: Γ').

Derive Signature NoConfusion EqDec for Ren.

(* Identity renaming: keep every slot (the identity OPE Γ ↪ Γ). *)
Fixpoint idRen {Γ} : Ren Γ Γ :=
  match Γ with
  | []     => NoRen
  | τ :: Γ => Keep idRen
  end.

(* Keeping the head of an identity renaming is again the identity. *)
Lemma Keep_idRen {Γ τ} : Keep (τ:=τ) (@idRen Γ) = idRen.
Proof. now induction Γ. Qed.

(* The unique thinning into the empty context: drop every slot. *)
Equations DropAll {Γ} : Ren Γ [] :=
  DropAll (Γ:=[])      := NoRen;
  DropAll (Γ:=_ :: xs) := Drop (DropAll (Γ:=xs)).

Corollary NoRen_idRen : NoRen = idRen.
Proof. reflexivity. Qed.

Corollary DropAll_nil_idRen : DropAll (Γ:=[]) = idRen.
Proof. reflexivity. Qed.

(* Single-variable weakening: drop one fresh slot τ, keep the rest. *)
Definition skip1 {Γ τ} : Ren (τ :: Γ) Γ := Drop idRen.

(* Composition of renamings (diagrammatic in the OPE category): RcR r r'
   first applies the inner thinning r' then the outer r. *)
Equations RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') : Ren Γ Γ'' :=
  RcR σ        NoRen    := σ;
  RcR σ        (Drop δ) := Drop (RcR σ δ);
  RcR (Drop σ) (Keep δ) := Drop (RcR σ δ);
  RcR (Keep σ) (Keep δ) := Keep (RcR σ δ).

(* Left identity law of the renaming category: idRen ∘ σ = σ. *)
Lemma RcR_idRen_left {Γ Γ'} (σ : Ren Γ Γ') :
  RcR idRen σ = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

(* Right identity law of the renaming category: σ ∘ idRen = σ. *)
Lemma RcR_idRen_right {Γ Γ'} (σ : Ren Γ Γ') :
  RcR σ idRen = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

(* Associativity law of the renaming category. *)
Lemma RcR_assoc {Γ Γ' Γ'' Γ'''}
      (σ : Ren Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  RcR (RcR σ δ) ν = RcR σ (RcR δ ν).
Proof.
  generalize dependent Γ'''.
  generalize dependent Γ''.
  induction ν; simp RcR; simpl; intros; auto.
  - simp RcR.
    now rewrite IHν.
  - dependent elimination δ; simp RcR; simpl.
    + now rewrite IHν.
    + dependent elimination σ; simp RcR; simpl;
      now rewrite IHν.
Qed.

(* Action of a renaming on a variable (contravariant: Var Γ' → Var Γ).
   A dropped slot shifts the index by one (SV); a kept slot passes the
   most-local variable through unchanged. *)
Equations RenVar {τ Γ Γ'} (r : Ren Γ Γ') (v : Var Γ' τ) : Var Γ τ :=
  RenVar NoRen    v      := v;
  RenVar (Drop σ) v      := SV (RenVar σ v);
  RenVar (Keep σ) ZV     := ZV;
  RenVar (Keep σ) (SV v) := SV (RenVar σ v).

(* Identity law: the identity renaming fixes every variable. *)
Lemma RenVar_idRen {τ Γ} (v : Var Γ τ) :
  RenVar idRen v = v.
Proof.
  induction v; simpl; simp RenVar; intros; auto.
  now rewrite IHv.
Qed.

(* Renaming by skip1 is exactly the variable-shift SV (de Bruijn weakening). *)
Lemma RenVar_skip1 {τ τ' Γ} (v : Var Γ τ) :
  RenVar (skip1 (τ:=τ')) v = SV v.
Proof.
  unfold skip1; simp RenVar.
  now rewrite RenVar_idRen.
Qed.

(* Functoriality of RenVar over composition of renamings. *)
Lemma RenVar_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  RenVar (RcR σ δ) v = RenVar δ (RenVar σ v).
Proof.
  generalize dependent Γ''.
  induction δ; simpl; simp RcR; intros; auto.
  - simp RenVar.
    now rewrite <- IHδ.
  - dependent elimination σ; simpl; simp RcR; simp RenVar.
    + now rewrite IHδ.
    + dependent elimination v; simp RenVar; auto.
      now rewrite IHδ.
Qed.

(* Keep commutes with composition: extending both factors by a kept slot
   and composing equals composing then keeping (used to push renamings
   under binders). *)
Lemma Keep_RcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  Keep (τ := τ) (RcR r r') = RcR (Keep r) (Keep r').
Proof.
  generalize dependent Γ''.
  now induction r'.
Qed.

(* Action of a renaming on a term (the renaming functor on Exp); LAM pushes
   the renaming under the binder via Keep. *)
Fixpoint RenExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | EUnit         => EUnit
  | Pair x y      => Pair (RenExp r x) (RenExp r y)
  | Fst p         => Fst (RenExp r p)
  | Snd p         => Snd (RenExp r p)
  | VAR v         => VAR (RenVar r v)
  | APP e1 e2     => APP (RenExp r e1) (RenExp r e2)
  | LAM e         => LAM (RenExp (Keep r) e)
  end.

(* Renaming preserves term size (no slots are duplicated or erased). *)
Lemma RenExp_preserves_size {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) :
  Exp_size (RenExp r e) = Exp_size e.
Proof.
  generalize dependent r.
  generalize dependent Γ.
  now induction e; simpl; simp RcR; simpl; intros; auto.
Qed.

(* Identity law of the renaming functor: idRen acts as the identity on terms. *)
Lemma RenExp_idRen {τ Γ} (e : Exp Γ τ) :
  RenExp idRen e = e.
Proof.
  induction e; simpl; simp RenVar; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_idRen.
  - now rewrite Keep_idRen, IHe.
Qed.

(* A closed term is fixed by the (unique) thinning out of the empty context. *)
Lemma RenExp_DropAll {τ} (e : Exp [] τ) :
  RenExp DropAll e = e.
Proof.
  rewrite DropAll_nil_idRen.
  now rewrite RenExp_idRen.
Qed.

(* Functoriality of the renaming functor over composition of renamings. *)
Lemma RenExp_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  RenExp (RcR σ δ) e = RenExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_RcR.
  - now rewrite <- IHe; simp RcR.
Qed.

(* Renaming preserves values: the image of a value under any renaming is a
   value of the same shape.  Kept transparent (Defined) as it is computational. *)
Lemma RenExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Ren Γ' Γ) :
  ValueP v → ValueP (RenExp σ v).
Proof.
  intros X.
  now induction X; simpl; intros; try constructor.
Defined.

(* Weakening: introduce one fresh variable τ' on the left (RenExp skip1). *)
Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RenExp skip1.

(* Right-append weakening on variables: Γ ↪ Γ ++ Γ' leaves de Bruijn indices
   into the prefix Γ unchanged. *)
Equations RenExpandVar {Γ Γ' τ} (v : Var Γ τ) : Var (Γ ++ Γ') τ :=
  RenExpandVar ZV     := ZV;
  RenExpandVar (SV v) := SV (RenExpandVar v).

(* Right-append weakening on terms (extends RenExpandVar structurally). *)
Fixpoint RenExpandExp {Γ Γ' τ} (e : Exp Γ τ) : Exp (Γ ++ Γ') τ :=
  match e with
  | EUnit         => EUnit
  | Pair x y      => Pair (RenExpandExp x) (RenExpandExp y)
  | Fst p         => Fst (RenExpandExp p)
  | Snd p         => Snd (RenExpandExp p)
  | VAR v         => VAR (RenExpandVar v)
  | APP e1 e2     => APP (RenExpandExp e1) (RenExpandExp e2)
  | LAM e         => LAM (RenExpandExp e)
  end.

(* Append a context Γ' on the right of an existing context Γ. *)
Definition liftL Γ' `(e : Exp Γ τ) : Exp (Γ ++ Γ') τ := RenExpandExp e.

(* Prepend a context Γ on the left, iterating single weakenings (skip1). *)
Fixpoint liftR Γ `(e : Exp Γ' τ) : Exp (Γ ++ Γ') τ :=
  match Γ with
  | []      => e
  | x :: xs => RenExp skip1 (liftR xs e)
  end.

End Ren.
