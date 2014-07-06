Require Export Monad.
Require Export ACompose.

(* These proofs are due to Mark P. Jones and Luc Duponcheel in their article
   "Composing monads", Research Report YALEU/DCS/RR-1004, December 1993.

   Given any Monad M, and any Premonad N (i.e., having eta), and further given
   an operation [prod] and its accompanying four laws, it can be shown that M
   N is closed under composition.
*)
Global Instance Monad_Compose (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Applicative N}
  (prod : forall  {A : Type}, N (M (N A)) -> M (N A))
  (prod_law_1 : forall {A B : Type} (f : A -> B),
    (@prod B) ∘ fmap[N] (@fmap (fun X => M (N X)) _ _ _ f) =
    (@fmap (fun X => M (N X)) _ _ _ f) ∘ (@prod A))
  (prod_law_2 : forall {A : Type}, (@prod A) ∘ eta/N = id)
  (prod_law_3 : forall {A : Type},
    (@prod A) ∘ fmap[N] (@eta (fun X => M (N X)) _ _) = eta/M)
  (prod_law_4 : forall {A : Type},
    (@prod A) ∘ fmap[N] (mu/M ∘ fmap[M] (@prod A)) =
    mu/M ∘ fmap[M] (@prod A) ∘ (@prod (M (N A))))
  : Monad (fun X => M (N X)) :=
{ is_applicative := Applicative_Compose M N
; mu := fun A => mu/M ∘ fmap[M] (prod A)
}.
Proof.
  - (* monad_law_1 *) intros.
    rewrite <- comp_assoc with (f := mu/M).
    rewrite <- comp_assoc with (f := mu/M).
    rewrite comp_assoc with (f := fmap[M] prod X).
    rewrite <- monad_law_4.
    rewrite <- comp_assoc.
    rewrite comp_assoc with (f := mu/M).
    rewrite comp_assoc with (f := mu/M).
    rewrite <- monad_law_1.
    repeat (rewrite <- comp_assoc).
    repeat (rewrite fun_composition).
    rewrite <- prod_law_4.
    repeat (rewrite <- fun_composition).
    unfold compose_fmap. reflexivity.

  - (* monad_law_2 *) intros.
    rewrite <- monad_law_2.
    rewrite <- prod_law_3. simpl.
    repeat (rewrite <- comp_assoc).
    repeat (rewrite <- fun_composition).
    unfold compose_fmap. reflexivity.

  - (* monad_law_3 *) intros.
    rewrite <- prod_law_2.
    rewrite <- comp_id_left.
    rewrite <- (@monad_law_3 M _ (N X)).
    rewrite <- comp_assoc.
    rewrite <- comp_assoc.
    rewrite app_fmap_compose. simpl.
    rewrite <- fun_composition.
    rewrite <- comp_assoc.
    unfold compose_eta.
    rewrite <- app_fmap_compose.
    reflexivity.

  - (* monad_law_4 *) intros. simpl.
    unfold compose_fmap.
    unfold compose at 3.
    unfold compose at 3.
    unfold compose at 4.
    rewrite comp_assoc at 1.
    rewrite <- monad_law_4.
    repeat (rewrite <- comp_assoc).
    rewrite fun_composition.
    rewrite fun_composition.
    simpl in prod_law_1.
    unfold compose_fmap in prod_law_1.
    unfold compose in prod_law_1 at 2.
    unfold compose in prod_law_1 at 3.
    rewrite <- prod_law_1.
    reflexivity.
Defined.
