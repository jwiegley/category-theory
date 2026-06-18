Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.

Section Sub.

Import ListNotations.

(** Parallel substitution for the de Bruijn STLC. *)

(* This module develops capture-avoiding, parallel substitution for the
   simply-typed lambda calculus in de Bruijn form (see [Exp]).  A value of type
   [Sub Γ' Γ] is a parallel substitution σ : Γ ⇒ Γ': an environment-indexed
   snoc-list assigning, to every variable of the source context Γ, an
   expression living in the target context Γ'.  Following the σ-calculus and
   Autosubst, substitution is a total function on indices rather than the usual
   name-with-freshness-side-condition operation; de Bruijn indices make terms
   invariant under α-conversion, so no capture can occur.

   References:
     de Bruijn index    https://en.wikipedia.org/wiki/De_Bruijn_index
                        https://ncatlab.org/nlab/show/de+Bruijn+index
     explicit/parallel
       substitution     https://en.wikipedia.org/wiki/Explicit_substitution
                        https://ncatlab.org/nlab/show/substitution

   Writing e[σ] for [SubExp σ e], v[σ] for [SubVar σ v], and σ;δ for the
   diagrammatic composite [ScS σ δ], the operations and their laws are:

     SubExp / SubVar  e[σ]              apply a substitution to an expr/var
     idSub            ι                 identity substitution (VAR on each var)
     ScS              σ;δ               composition of substitutions
     ScR              σ∘r               post-compose a substitution with a Ren
     RcS              r∘σ               pre-compose a Ren with a substitution
     Keepₛ / Dropₛ                      lift / weaken a substitution past a binder

   The contexts Env and the substitutions Sub form a category: idSub is the
   identity ([ScS_idSub_left], [ScS_idSub_right]) and ScS is associative (a
   consequence of the substitution lemma [SubExp_ScS], e[σ;δ] = e[σ][δ]).  The
   remaining lemmas establish that renaming and substitution commute as
   expected ([SubExp_RcS], [SubExp_ScR], [ScR_ScS], [ScS_ScR]). *)

(* A substitution σ : Γ ⇒ Γ' (read as [Sub Γ' Γ], target then source) is a
   snoc-list giving, for each variable of the source context, an expression in
   the target context Γ'.  [NoSub] handles the empty source; [Push] adds the
   image of the most-recently-bound source variable. *)
Inductive Sub (Γ : Env) : Env → Set :=
  | NoSub : Sub []
  | Push {Γ' τ} : Exp Γ τ → Sub Γ' → Sub (τ :: Γ').

Arguments NoSub {Γ}.
Arguments Push {Γ Γ' τ} _ _.

Derive Signature NoConfusion EqDec for Sub.

(* Look up the image of a variable under a substitution.  This is definitionally
   the same operation as [SubVar] below (which is the one used by [SubExp]); it
   is retained here as the elementary lookup form. *)
Equations get `(s : Sub Γ' Γ) `(v : Var Γ τ) : Exp Γ' τ :=
  get (Push x _)   ZV    := x;
  get (Push _ xs) (SV v) := get xs v.

(* σ∘r: post-compose a substitution with a renaming, renaming every image. *)
Equations ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') : Sub Γ Γ'' :=
  ScR NoSub      δ := NoSub;
  ScR (Push t σ) δ := Push (RenExp δ t) (ScR σ δ).

(* ScR is right-unital in the renaming. *)
Lemma ScR_idRen {Γ Γ'} (s : Sub Γ Γ') :
  ScR s idRen = s.
Proof.
  induction s; simp ScR; auto.
  now rewrite RenExp_idRen, IHs.
Qed.

(* The identity substitution ι, mapping every variable to itself.  Under a
   binder it pushes the freshly bound variable and weakens the rest. *)
Fixpoint idSub {Γ} : Sub Γ Γ :=
  match Γ with
  | []     => NoSub
  | τ :: Γ => Push (VAR ZV) (ScR (@idSub Γ) skip1)
  end.

Corollary NoSub_idSub : NoSub (Γ:=[]) = idSub.
Proof. reflexivity. Qed.

(* r∘σ: pre-compose a renaming with a substitution, selecting/reordering its
   images according to r. *)
Equations RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') : Sub Γ Γ'' :=
  RcS NoRen    δ          := δ;
  RcS (Drop σ) (Push t δ) := RcS σ δ;
  RcS (Keep σ) (Push t δ) := Push t (RcS σ δ).

(* Weaken a substitution so its source context gains one more variable. *)
Definition Dropₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  ScR s skip1.

(* Lift a substitution under a binder: the new variable maps to itself and the
   rest is weakened.  This is the action of substitution on the morphism that
   extends a context, and is what [SubExp] applies when descending into [LAM]. *)
Definition Keepₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) (τ :: Γ') :=
  Push (VAR ZV) (Dropₛ s).

Corollary Keepₛ_idSub {Γ τ} :
  Keepₛ (Γ:=Γ) (Γ':=Γ) (τ:=τ) idSub = idSub.
Proof. reflexivity. Qed.

(* v[σ]: the image of variable v under substitution σ. *)
Equations SubVar {Γ Γ' τ} (s : Sub Γ Γ') (v : Var Γ' τ) : Exp Γ τ :=
  SubVar (Push t σ) ZV     := t;
  SubVar (Push t σ) (SV v) := SubVar σ v.

(* e[σ]: apply a parallel substitution throughout an expression, lifting it with
   [Keepₛ] when passing under the binder of [LAM] (this is where capture is
   avoided). *)
Fixpoint SubExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | EUnit         => EUnit
  | Pair x y      => Pair (SubExp s x) (SubExp s y)
  | Fst p         => Fst (SubExp s p)
  | Snd p         => Snd (SubExp s p)
  | VAR v         => SubVar s v
  | APP e1 e2     => APP (SubExp s e1) (SubExp s e2)
  | LAM e         => LAM (SubExp (Keepₛ s) e)
  end.

(* σ;δ: composition of substitutions, applying δ to every image of σ.  This is
   composition in the category of contexts; [SubExp_ScS] shows it agrees with
   sequential application of σ then δ. *)
Fixpoint ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (δ : Sub Γ Γ') : Sub Γ Γ'' :=
  match s with
  | NoSub    => NoSub
  | Push e σ => Push (SubExp δ e) (ScS σ δ)
  end.

(* Fusion of two renamings applied after a substitution (ScR-ScR / RcR). *)
Lemma ScR_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScR σ δ) ν = ScR σ (RcR δ ν).
Proof.
  induction σ; simp ScR; auto.
  now rewrite RenExp_RcR, IHσ.
Qed.

(* Post-renaming commutes through a pre-renaming of a substitution. *)
Lemma ScR_RcS {Γ Γ' Γ'' Γ'''} (σ : Ren Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (RcS σ δ) ν = RcS σ (ScR δ ν).
Proof.
  induction σ; dependent elimination δ; auto.
  - simp RcS.
    now simp ScR.
  - simp RcS.
    simp ScR.
    simp RcS.
    now rewrite IHσ.
Qed.

(* The identity renaming is a left unit for RcS. *)
Lemma RcS_idRen {Γ Γ'} (σ : Sub Γ Γ') :
  RcS idRen σ = σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; auto.
  now rewrite IHσ.
Qed.

(* A renaming acts the same whether pre-composed into idSub or post-composed
   onto idSub: the two ways of viewing a renaming as a substitution agree. *)
Lemma RcS_idSub {Γ Γ'} (σ : Ren Γ Γ') :
  RcS σ idSub = ScR idSub σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; simp ScR; auto.
  - rewrite <- ScR_RcS.
    rewrite IHσ.
    rewrite ScR_ScR.
    unfold skip1.
    simp RcR.
    now rewrite RcR_idRen_right.
  - simpl.
    f_equal.
    rewrite <- ScR_RcS.
    rewrite IHσ.
    rewrite ScR_ScR.
    unfold skip1.
    rewrite ScR_ScR.
    simp RcR.
    rewrite RcR_idRen_left.
    now rewrite RcR_idRen_right.
Qed.

(* Pre-composing the skip renaming drops the freshly pushed image. *)
Lemma RcS_skip1 {Γ Γ' τ} (e : Exp Γ τ) (σ : Sub Γ Γ') :
  RcS skip1 (Push e σ) = σ.
Proof.
  unfold skip1.
  simp RcS.
  now rewrite RcS_idRen.
Qed.

(* Dropping every variable yields the empty substitution. *)
Lemma RcS_DropAll {Γ Γ'} (σ : Sub Γ' Γ) :
  RcS DropAll σ = NoSub.
Proof. now induction σ; simp RcS. Qed.

(* Substituting through a pre-renaming equals renaming the variable first. *)
Lemma SubVar_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (RcS σ δ) v = SubVar δ (RenVar σ v).
Proof.
  induction σ; simp RenVar; auto.
  - dependent elimination δ.
    now simp RcS.
  - dependent elimination δ.
    simp RcS.
    dependent elimination v.
    + now simp RenVar.
    + simp RenVar.
      now simp SubVar.
Qed.

(* Ren-then-sub commutation on expressions: e[r∘σ] = (rename e by r)[σ]. *)
Lemma SubExp_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (RcS σ δ) e = SubExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_RcS.
  - specialize (IHe _ _ (Keep σ) (Keepₛ δ)).
    rewrite <- IHe.
    unfold Keepₛ.
    simp RcS.
    repeat f_equal.
    unfold Dropₛ.
    now apply ScR_RcS.
Qed.

(* Sub-then-ren commutation on variables: v[σ∘r] = rename (v[σ]) by r. *)
Lemma SubVar_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScR σ δ) v = RenExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - now inversion v.
  - now dependent elimination v; simp SubVar.
Qed.

(* Sub-then-ren commutation on expressions: e[σ∘r] = rename (e[σ]) by r. *)
Lemma SubExp_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScR σ δ) e = RenExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_ScR.
  - rewrite <- IHe.
    unfold Keepₛ.
    simp ScR.
    simpl.
    repeat f_equal.
    unfold Dropₛ.
    rewrite !ScR_ScR.
    unfold skip1; simp RcR.
    rewrite RcR_idRen_left.
    now rewrite RcR_idRen_right.
Qed.

(* A renaming inserted between two substitutions may be re-associated. *)
Lemma ScS_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Sub Γ Γ') :
  ScS (ScR σ δ) ν = ScS σ (RcS δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS; simpl; intros; auto.
  simp ScR.
  simpl.
  rewrite IHσ.
  f_equal.
  now rewrite <- SubExp_RcS.
Qed.

(* Post-renaming a composite pushes inside to the right factor. *)
Lemma ScR_ScS {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScS σ δ) ν = ScS σ (ScR δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS; simpl; intros; auto.
  simp ScR.
  rewrite IHσ.
  f_equal.
  now rewrite <- SubExp_ScR.
Qed.

(* The identity substitution sends every variable to itself. *)
Lemma SubVar_idSub {Γ τ} (v : Var Γ τ) :
  SubVar idSub v = VAR v.
Proof.
  induction v; simpl; simp SubVar; auto.
  rewrite SubVar_ScR.
  rewrite IHv.
  simpl.
  now rewrite RenVar_skip1.
Qed.

(* Substitution lemma at variables: v[σ;δ] = (v[σ])[δ]. *)
Lemma SubVar_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScS σ δ) v = SubExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - now inversion v.
  - simpl.
    now dependent elimination v; simp SubVar.
Qed.

(* sub_id: applying the identity substitution is the identity, e[ι] = e. *)
Lemma SubExp_idSub {Γ τ} (e : Exp Γ τ) :
  SubExp idSub e = e.
Proof.
  induction e; simpl; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite SubVar_idSub.
  - f_equal.
    rewrite <- IHe at 2.
    now f_equal.
Qed.

(* The substitution lemma proper: e[σ;δ] = (e[σ])[δ].  Together with the
   identity laws below this gives associativity of ScS and makes (Env, Sub) a
   category. *)
Lemma SubExp_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScS σ δ) e = SubExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_ScS.
  - rewrite <- IHe; clear.
    f_equal.
    unfold Keepₛ.
    unfold Dropₛ.
    simpl.
    simp SubVar.
    f_equal.
    rewrite ScR_ScS.
    remember (ScR δ skip1) as g; clear.
    unfold skip1.
    generalize dependent g.
    generalize dependent Γ0.
    induction σ; simpl; simp ScR; simpl; intros; auto.
    f_equal; auto.
    rewrite <- SubExp_RcS.
    simp RcS.
    now rewrite RcS_idRen.
Qed.

(* Right identity for substitution composition: σ;ι = σ. *)
Lemma ScS_idSub_right {Γ Γ'} (σ : Sub Γ Γ') :
  ScS σ idSub = σ.
Proof.
  induction σ; simpl; auto.
  rewrite IHσ.
  now rewrite SubExp_idSub.
Qed.

(* Left identity for substitution composition: ι;σ = σ. *)
Lemma ScS_idSub_left {Γ Γ'} (σ : Sub Γ Γ') :
  ScS idSub σ = σ.
Proof.
  induction σ; simpl; auto.
  simp SubVar.
  rewrite ScS_ScR.
  unfold skip1.
  simp RcS.
  rewrite RcS_idRen.
  now rewrite IHσ.
Qed.

(* Lifting under a binder is functorial for composition: (Keepₛ f);(Keepₛ g) =
   Keepₛ (f;g).  This is the coherence that lets [SubExp_ScS] descend into LAM. *)
Lemma ScS_Keepₛ {Γ Γ' Γ'' τ} (f : Sub Γ' Γ'') (g : Sub Γ Γ') :
  ScS (Keepₛ (τ:=τ) f) (Keepₛ g) = Keepₛ (ScS f g).
Proof.
  simpl.
  unfold Keepₛ, Dropₛ.
  rewrite ScS_ScR.
  f_equal.
  rewrite ScR_ScS.
  f_equal.
  now rewrite RcS_skip1.
Qed.

(* A literal substitution {|| e ; .. ; f ||} pushes the given expressions onto
   idSub; in particular {|| x ||} is the single substitution that instantiates
   the most-recently-bound variable with x. *)
Notation "{|| e ; .. ; f ||}" := (Push e .. (Push f idSub) ..).

(* A general push factors as a single (instantiation) substitution after a
   lifted one: substituting [Push x s] is the same as lifting s under the binder
   and then instantiating the new variable with x. *)
Lemma SubExp_Push {Γ Γ' τ ty} (x : Exp Γ' ty) (s : Sub Γ' Γ) (e : Exp (ty :: Γ) τ) :
  SubExp (Push x s) e = SubExp {|| x ||} (SubExp (Keepₛ s) e).
Proof.
  rewrite <- SubExp_ScS.
  unfold Keepₛ, Dropₛ; simpl.
  simp SubVar.
  rewrite ScS_ScR.
  rewrite RcS_skip1.
  now rewrite ScS_idSub_right.
Qed.

(* The only substitution on the empty context is the identity, so it acts
   trivially on closed expressions. *)
Corollary SubExp_closed `(s : Sub [] []) `(e : [] ⊢ τ) :
  SubExp s e = e.
Proof.
  dependent elimination s; simpl.
  rewrite NoSub_idSub.
  now rewrite SubExp_idSub.
Qed.

(* Substituting a closed expression and then closing the result again leaves it
   unchanged, since both round-trips collapse to the identity on []. *)
Lemma SubExp_SubExp `(s : Sub [] Γ) (s' : Sub Γ []) `(e : [] ⊢ τ) :
  SubExp s (SubExp s' e) = e.
Proof.
  simpl; induction s.
  - dependent elimination s'; simpl.
    now rewrite !NoSub_idSub, !SubExp_idSub.
  - dependent elimination s'; simpl.
    rewrite <- SubExp_ScS in *.
    simpl.
    now rewrite !NoSub_idSub, !SubExp_idSub.
Qed.

(* As [SubExp_SubExp], but with a renaming on the inside instead of a
   substitution: closing a renamed closed expression is again the identity. *)
Lemma SubExp_RenExp `(s : Sub [] Γ) (r' : Ren Γ []) `(e : [] ⊢ τ) :
  SubExp s (RenExp r' e) = e.
Proof.
  simpl; induction s.
  - dependent destruction r'; simpl.
    rewrite !NoSub_idSub, !SubExp_idSub.
    now rewrite !NoRen_idRen, !RenExp_idRen.
  - dependent elimination r'; simpl.
    rewrite <- SubExp_RcS in *.
    simp RcS.
    now rewrite SubExp_RcS.
Qed.

(* Computation rules for the two variable cases of [Push]. *)
Lemma SubExp_VAR_ZV {Γ τ} (s : Sub [] Γ) (x : Exp [] τ) :
  SubExp (Push x s) (VAR ZV) = x.
Proof. now simpl; simp SubVar. Qed.

Lemma SubExp_VAR_SV {Γ τ τ'} (s : Sub [] Γ) (x : Exp [] τ') (v : Var Γ τ) :
  SubExp (Push x s) (VAR (SV v)) = SubExp s (VAR v).
Proof. now simpl; simp SubVar. Qed.

(* Substitution preserves being a value (it commutes with the value
   constructors).  Proven with [Defined] because it carries computational
   content, mirroring [RenExp_ValueP]. *)
Lemma SubExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Sub Γ' Γ) :
  ValueP v → ValueP (SubExp σ v).
Proof.
  intros X.
  now induction X; simpl; intros; try constructor.
Defined.

End Sub.

Arguments NoSub {Γ}.
Arguments Push {Γ Γ' τ} _ _.

Notation "{|| e ; .. ; f ||}" := (Push e .. (Push f idSub) ..).
