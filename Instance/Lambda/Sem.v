Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Denotational semantics of the simply-typed lambda calculus in a CCC *)

(* nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

   This file gives the categorical (denotational) semantics of the de Bruijn
   STLC of Exp.v, realizing the Curry-Howard-Lambek correspondence: a
   cartesian closed category interprets the calculus, with the product type
   denoting the categorical product, the function type denoting the internal
   hom (exponential), and a context denoting the iterated product of its
   types.  Here the interpreting CCC is taken to be Coq's own universe [Type]
   (with [unit] terminal, [*] product, [→] exponential), so the interpretation
   is the standard one read off into that concrete model:

       ⟦TyUnit⟧      := unit                   (terminal object)
       ⟦t1 × t2⟧     := ⟦t1⟧ * ⟦t2⟧            (categorical product)
       ⟦dom ⟶ cod⟧  := ⟦dom⟧ → ⟦cod⟧          (exponential / internal hom)
       ⟦Γ⟧           := ilist ⟦·⟧ Γ            (right-nested product of types)
       ⟦Γ ⊢ t : τ⟧   : ⟦Γ⟧ → ⟦τ⟧              (a morphism in the CCC)

   On terms (SemExp) the standard CCC interpretation is used: a variable is a
   product projection (var = proj), application is evaluation composed with
   pairing (app = eval ∘ ⟨_,_⟩), and lambda abstraction is currying
   (lam = curry).  The remaining results are the semantic compatibility lemmas
   between interpretation and the renaming/substitution machinery of Ren.v and
   Sub.v; they are what make βη-equality sound, witnessed downstream by
   [soundness] in Sound.v ([e ---> v] implies [SemExp e = SemExp v]).  By
   Lambek's theorem the syntax presented here is the free CCC, so this
   interpretation factors uniquely through every model. *)

Section Sem.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyUnit          => unit                  (* terminal object             *)
  | TyPair t1 t2    => SemTy t1 * SemTy t2   (* categorical product         *)
  | TyArrow dom cod => SemTy dom → SemTy cod (* exponential / internal hom  *)
  end.

(* A context denotes the iterated (right-nested) product of its types. *)
Definition SemEnv Γ : Type := ilist (B:=SemTy) Γ.

(* A variable denotes a product projection (var = proj). *)
Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se              (* first projection            *)
  | SV v => λ se, SemVar v (snd se)   (* projection through the tail *)
  end.

Equations RenSem {Γ Γ'} (r : Ren Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  RenSem NoRen    se      := se;
  RenSem (Drop r) (_, se) := RenSem r se;
  RenSem (Keep r) (e, se) := (e, RenSem r se).

Lemma RenSem_inil (r : Ren nil nil) :
  RenSem r () = ().
Proof. now dependent destruction r. Qed.

Lemma RenSem_idRen {Γ} (se : SemEnv Γ) :
  RenSem idRen se = se.
Proof.
  induction Γ; destruct se; simpl; simp RenSem; intros; auto.
  now rewrite IHΓ.
Qed.

Lemma RenSem_skip1 {Γ τ} (e : SemTy τ) (se : SemEnv Γ) :
  RenSem skip1 (e, se) = se.
Proof.
  induction Γ; destruct se; simpl; intros; auto.
  unfold skip1; simp RenSem.
  now rewrite RenSem_idRen.
Qed.

Lemma SemVar_RenSem Γ τ (v : Var Γ τ) Γ' (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemVar v (RenSem r se) = SemVar (RenVar r v) se.
Proof.
  intros.
  induction r; simp RenSem; simp RenVar; simpl;
  destruct se; simp RenSem; auto.
  now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma RenSem_RcR {Γ Γ' Γ''} (f : Ren Γ' Γ'') (g : Ren Γ Γ') (se : SemEnv Γ) :
  RenSem (RcR f g) se = RenSem f (RenSem g se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction Γ; destruct se; simpl; intros; auto.
  - inversion g; subst.
    rewrite RenSem_inil.
    inversion f; subst.
    now rewrite !RenSem_inil.
  - dependent elimination g; simp RenSem.
    + now rewrite <- IHΓ; simp RcR; simp RenSem.
    + dependent elimination f; simp RenSem;
      now rewrite <- IHΓ; simp RcR; simp RenSem.
Qed.

(* The term interpretation ⟦Γ ⊢ e : τ⟧ : ⟦Γ⟧ → ⟦τ⟧, the standard CCC
   semantics read into Coq's [Type]: pairing into the product, the product
   projections, a variable as a projection, λ as currying, and application
   as evaluation composed with pairing. *)
Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | EUnit     => λ _, tt                              (* unique map to terminal *)
  | Pair x y  => λ se, (SemExp x se, SemExp y se)     (* pairing ⟨_,_⟩           *)
  | Fst p     => λ se, fst (SemExp p se)              (* first projection        *)
  | Snd p     => λ se, snd (SemExp p se)              (* second projection       *)
  | VAR v     => SemVar v                             (* var = proj              *)
  | LAM e     => λ se x, SemExp e (x, se)             (* lam = curry             *)
  | APP e1 e2 => λ se, SemExp e1 se (SemExp e2 se)    (* app = eval ∘ ⟨_,_⟩      *)
  end.

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SubSem NoSub      _  := tt;
  SubSem (Push t σ) se := (SemExp t se, SubSem σ se).

Lemma SubSem_inil (s : Sub nil nil) :
  SubSem s () = ().
Proof. now dependent elimination s. Qed.

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite SemVar_RenSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    now repeat f_equal.
  - now rewrite IHe1, IHe2.
Qed.

Lemma ScR_idRen {Γ Γ'} (s : Sub Γ Γ') :
  ScR s idRen = s.
Proof.
  induction s; simp ScR; auto.
  now rewrite RenExp_idRen, IHs.
Qed.

Lemma SubSem_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SubSem (ScR s r) se = SubSem s (RenSem r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp RenSem.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR.
    + now simp SubSem.
    + simp SubSem.
      f_equal.
      * now rewrite SemExp_RenSem.
      * dependent elimination r; simp RenSem;
        now rewrite IHs1.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemExp_wk `(E : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemExp_RenSem; simpl.
  f_equal.
  now rewrite RenSem_skip1.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v (SubSem s se) = SemExp (SubVar s v) se.
Proof.
  intros.
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e (SubSem s se) = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.

End Sem.
