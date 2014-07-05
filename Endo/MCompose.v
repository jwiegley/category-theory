Require Export Monad.
Require Export ACompose.

(* "Suppose that (S,μˢ,ηˢ) and (T,μᵗ,ηᵗ) are two monads on a category C.  In
   general, there is no natural monad structure on the composite functor ST.
   On the other hand, there is a natural monad structure on the functor ST if
   there is a distribute law of the monad S over the monad T."

     http://en.wikipedia.org/wiki/Distr_law_between_monads

   My main source for this material was the paper "Composing monads":

     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.138.4552
*)
Class MonadDistribute (M : Type -> Type) (N : Type -> Type)
  `{Applicative M} `{Applicative N} `{Monad (fun X => M (N X))} :=
{ swap {A : Type} : N (M A) -> M (N A) :=
    (@mu (fun X => M (N X)) _ A) ∘ (@eta M _ _) ∘ (fmap (fmap eta))
; prod {A : Type} : N (M (N A)) -> M (N A) :=
    (@mu (fun X => M (N X)) _ A) ∘ (@eta M _ (N (M (N A))))
; dorp {A : Type} : M (N (M A)) -> M (N A) :=
    (@mu (fun A => M (N A)) _ A) ∘ (@fmap (fun A => M (N A)) _ _ _ (fmap eta))

; swap_law_1 : forall {A B : Type} (f : (A -> B)),
    swap ∘ fmap (fmap f) = fmap (fmap f) ∘ swap
; swap_law_2 : forall {A : Type},
    swap ∘ eta = fmap (@eta N _ A)
; swap_law_3 : forall {A : Type},
    swap ∘ fmap (@eta M _ A) = eta
; swap_law_4 : forall {A : Type},
    prod ∘ fmap (@dorp A) = dorp ∘ prod
}.

Definition compose_mu (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Monad N} {A}
  (swap : forall  {A : Type}, N (M A) -> M (N A))
  : M (N (M (N A))) -> M (N A) := fmap mu ∘ mu ∘ fmap swap.

Global Instance Monad_Compose (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Monad N}
  (swap : forall  {A : Type}, N (M A) -> M (N A))
  (swap_law_1 : forall {A B : Type} (f : (A -> B)),
     swap ∘ fmap mu = mu ∘ fmap (@swap A) ∘ swap)
  (swap_law_2 : forall {A : Type},
     swap ∘ eta = fmap (@eta N _ A))
  (swap_law_3 : forall {A : Type},
     swap ∘ fmap (@eta M _ A) = eta)
  (swap_law_4 : forall {A : Type},
     swap ∘ mu = fmap mu ∘ swap ∘ fmap (@swap A))
  : Monad (fun X => M (N X)) :=
{ is_applicative := Applicative_Compose M N
; mu := fun _ => compose_mu M N swap
}.
Proof.
  - (* monad_law_1 *) intros.
    unfold compose_mu, prod. simpl.
    unfold compose_fmap.
    unfold compose at 4.
    repeat (rewrite <- comp_assoc).
    repeat (rewrite fun_composition).

    (* fmap[M N] compose_mu M N = compose_mu M N *)
    admit.

  - (* monad_law_2 *) intros.
    repeat (rewrite <- comp_assoc).
    unfold swap.

    (* fmap mu ∘ mu ∘ fmap (distr (N X)) ∘ fmap eta = id *)

    admit.

  - (* monad_law_3 *) intros.
    repeat (rewrite <- comp_assoc).
    unfold swap.

    (* fmap mu ∘ mu ∘ fmap (distr (N X)) ∘ eta = id *)

    admit.

  - (* monad_law_4 *) intros.
    repeat (rewrite <- comp_assoc).
    unfold swap.

    (* fmap mu ∘ mu ∘ fmap (distr (N Y)) ∘ fmap (fmap f) =
       fmap f ∘ fmap mu ∘ mu ∘ fmap (distr (N X)) *)

    admit.
Defined.

Class CompoundMonad (M : Type -> Type) (N : Type -> Type)
  `{Applicative M} `{Applicative N} `{Monad (fun X => M (N X))} :=
{ dunit : forall {α : Type}, M α -> M (N α)
; dmap  : forall {α β : Type}, (α -> M β) -> M (N α) -> M (N β)
; djoin : forall {α : Type}, M (N (N α)) -> M (N α)

; compound_law_1 : forall {A : Type},
    dmap (@eta M _ A) = id
; compound_law_2 : forall {A B C : Type} (f : (B -> M C)) (g : (A -> B)),
    dmap (f ∘ g) = dmap f ∘ (@fmap (fun A => M (N A)) _ _ _ g)
; compound_law_3 : forall {A B : Type} (f : (A -> M A)),
    dmap f ∘ (@eta (fun A => M (N A)) _ A) = @dunit A ∘ f
; compound_law_4 : forall {A B : Type} (f : (A -> M B)),
    djoin ∘ dmap (dmap f) = dmap f ∘ (@mu (fun A => M (N A)) _ A)
; compound_law_5 : forall {A : Type},
    @djoin A ∘ dunit = id
; compound_law_6 : forall {A : Type},
    djoin ∘ dmap (@eta (fun A => M (N A)) _ A) = id
; compound_law_7 : forall {A : Type},
    djoin ∘ dmap djoin = djoin ∘ (@mu (fun A => M (N A)) _ (N A))
; compound_law_8 : forall {A B : Type} (f : A -> M (N B)),
    (@bind (fun A => M (N A)) _ A B f) = djoin ∘ dmap f
}.

(* "The following definition captures the idea that a triple with functor T2 ∘
    T1 is in a natural way the composite of triples with functors T2 and T1."

   "Toposes, Triples and Theories", Barr and Wells
*)
Class MonadCompatible (M : Type -> Type) (N : Type -> Type)
  `{Monad M} `{Monad N} `{Monad (fun X => M (N X))} :=
{ compatible_1a : forall {A : Type},
    fmap (@eta N _ A) ∘ (@eta M _ A) = (@eta (fun X => M (N X)) _ A)
; compatible_1b : forall {A : Type},
    (@eta M _ (N A)) ∘ (@eta N _ A) = (@eta (fun X => M (N X)) _ A)
; compatible_2 : forall {A : Type},
    (@mu (fun X => M (N X)) _ A) ∘ fmap (fmap (@eta M _ (N A))) =
    fmap (@mu N _ A)
; compatible_3 : forall {A : Type},
    (@mu (fun X => M (N X)) _ A) ∘ fmap eta = (@mu M _ (N A))
}.

(* These proofs are due to Jeremy E. Dawson in "Categories and Monads in
   HOL-Omega".
*)
Theorem compatible_4 : forall (M : Type -> Type) (N : Type -> Type)
  `{MonadCompatible M N} {A},
  (@mu M _ (N A)) ∘ fmap (@mu (fun X => M (N X)) _ A) =
  (@mu (fun X => M (N X)) _ A) ∘ (@mu M _ (N (M (N A)))).
Proof.
  intros.
  rewrite <- compatible_3.
  rewrite <- compatible_3.
  rewrite compatible_3.
  rewrite comp_assoc.
  rewrite <- (@monad_law_1  (fun X => M (N X)) _).
  rewrite <- comp_assoc.
  replace (@fmap (fun X => M (N X)) _ _ _ (@mu (fun X => M (N X)) _ A))
    with (@fmap M _ _ _ ((@fmap N _ _ _ (@mu (fun X => M (N X)) _ A)))).
    rewrite (@fun_composition M _).
    assert ((@eta N _ (M (N A))) ∘ (@mu (fun X => M (N X)) _ A) =
            fmap (@mu (fun X => M (N X)) _ A) ∘ (@eta N _ (M (N (M (N A)))))).
      ext_eq. unfold compose.
      rewrite <- app_homomorphism.
      rewrite app_fmap_unit.
      reflexivity.
    rewrite <- H3.
    rewrite <- fun_composition.
    rewrite <- compatible_3.
    reflexivity.
  apply fmap_compose.
Qed.
