Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Log.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Sound.

Generalizable All Variables.

(** Soundness of the CCC semantics for the small-step reduction of the STLC *)

(* nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
   nLab: https://ncatlab.org/nlab/show/beta-reduction
   Wikipedia: https://en.wikipedia.org/wiki/Denotational_semantics

   This is the semantic payoff of the Curry-Howard-Lambek correspondence for
   the de Bruijn STLC: the denotational interpretation [SemExp] of Sem.v into
   the CCC (here Coq's [Type]) is sound with respect to the call-by-value
   reduction [--->] of Step.v.  Concretely,

       e ---> v   implies   ⟦e⟧ = ⟦v⟧            (as maps ⟦Γ⟧ → ⟦τ⟧)

   so a reduction step never changes the denotation.  Each congruence rule
   (ST_Pair1/2, ST_Fst1, ST_Snd1, ST_AppL/R) follows by the induction
   hypothesis on the reduced subterm; the two projection contractions
   (ST_FstPair, ST_SndPair) hold definitionally because [fst]/[snd] compute on
   a pair; and ST_Beta is the categorical β-law: substitution commutes with
   interpretation ([SemExp_SubSem]), and the single substitution {|| v ||}
   denotes pairing [v] onto the identity environment ([SubSem_idSub]), which is
   exactly the counit (evaluation) of the product-exponential adjunction.  This
   gives soundness of the model; completeness is Lambek's theorem (the syntax
   is the free CCC, Sem.v). *)

(* Reduction preserves denotation: [e ---> v] entails [SemExp e = SemExp v]. *)
Theorem soundness {Γ τ} {e : Exp Γ τ} {v} {se} :
  e ---> v → SemExp e se = SemExp v se.
Proof.
  intros.
  induction H; simpl; auto.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

End Sound.
