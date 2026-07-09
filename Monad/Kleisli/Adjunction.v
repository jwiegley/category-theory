Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The Kleisli free/forgetful adjunction

    nLab: https://ncatlab.org/nlab/show/Kleisli+category
    Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

    Monad/Adjunction.v shows that every adjunction F ⊣ U induces a monad
    U ◯ F on the domain of F.  This file provides the converse resolution
    through the Kleisli category C_M of a monad M on C (Monad/Kleisli.v):

    - [Kleisli_Free] F_M : C ⟶ C_M is the identity on objects and sends
      f : x ~> y to the pure Kleisli morphism ret ∘ f;
    - [Kleisli_Forget] U_M : C_M ⟶ C sends x to M x, and a Kleisli
      morphism f : x ~> M y to its extension join ∘ fmap[M] f (its bind);
    - [Kleisli_Adjunction] F_M ⊣ U_M: because F_M x = x and U_M y = M y,
      the two hom-setoids of the transposition are literally the same
      setoid x ~> M y, and the adjunction isomorphism [Kleisli_adj_iso]
      is the identity map in both directions.

    The adjunction presents the monad we started with:
    [Kleisli_Monad_agrees] identifies the composite U_M ◯ F_M with M (a
    natural isomorphism whose components are identities),
    [Kleisli_unit_agrees] identifies the adjunction unit with ret, and
    [Kleisli_join_agrees] identifies the U_M-image of the counit — which
    is exactly the multiplication of the monad that Monad/Adjunction.v
    extracts from this adjunction — with join.

    The other canonical resolution of a monad, through the Eilenberg–Moore
    category of algebras, lives in Monad/Eilenberg/Moore/Adjunction.v. *)

Section KleisliAdjunction.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

(** The free functor C ⟶ C_M: identity on objects; a morphism f becomes
    the pure Kleisli computation ret ∘ f.  Identity preservation is the
    right unit law of composition, and functoriality is the unit
    naturality [fmap_ret] against the left unit law [join_fmap_ret]. *)

Program Definition Kleisli_Free : C ⟶ Kleisli := {|
  fobj := fun x => x;
  fmap := fun x y f => ret ∘ f
|}.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation.
  (* ret ∘ (f ∘ g) ≈ join ∘ fmap[M] (ret ∘ f) ∘ (ret ∘ g) *)
  rewrite fmap_comp.
  rewrite (comp_assoc join).
  rewrite join_fmap_ret.
  rewrite id_left.
  rewrite (comp_assoc (fmap f)).
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(** The forgetful functor C_M ⟶ C: on objects, the carrier M x of the free
    algebra on x; on morphisms, Kleisli extension.  Identity preservation
    is the left unit law [join_fmap_ret], and functoriality combines the
    associativity [join_fmap_join] with the multiplication naturality
    [join_fmap_fmap], exactly as in the composition law of Kleisli. *)

Program Definition Kleisli_Forget : Kleisli ⟶ C := {|
  fobj := fun x => M x;
  fmap := fun x y f => join ∘ fmap[M] f
|}.
Next Obligation. proper. now rewrites. Qed.
Next Obligation. apply join_fmap_ret. Qed.
Next Obligation.
  (* join ∘ fmap[M] (join ∘ fmap[M] f ∘ g)
       ≈ (join ∘ fmap[M] f) ∘ (join ∘ fmap[M] g) *)
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.

(** The transposition isomorphism: a Kleisli morphism F_M x ~{C_M}~> y and
    a C-morphism x ~> U_M y are one and the same arrow x ~> M y, so the
    hom-setoid isomorphism of the adjunction is the identity map. *)

Program Definition Kleisli_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier   := @hom Kleisli (Kleisli_Free x) y
     ; is_setoid := @homset Kleisli (Kleisli_Free x) y |}
    {| carrier   := @hom C x (Kleisli_Forget y)
     ; is_setoid := @homset C x (Kleisli_Forget y) |} := {|
  to   := {| morphism := fun f => f |};
  from := {| morphism := fun f => f |}
|}.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Naturality of the transposition in the source argument, stated on the
    underlying arrows: precomposing a Kleisli morphism with a pure one is
    plain precomposition in C. *)

Lemma kleisli_transpose_nat_l {x y z : C} (f : y ~{C}~> M z) (g : x ~{C}~> y) :
  join ∘ fmap[M] f ∘ (ret ∘ g) ≈ f ∘ g.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc join (fmap[M] f) ret).
  rewrite <- fmap_ret.
  rewrite (comp_assoc join ret f).
  rewrite join_ret.
  cat.
Qed.

Program Definition Kleisli_Adjunction : Kleisli_Free ⊣ Kleisli_Forget :=
  @Build_Adjunction' Kleisli C Kleisli_Free Kleisli_Forget Kleisli_adj_iso _ _.
Next Obligation. apply kleisli_transpose_nat_l. Qed.
Next Obligation. reflexivity. Qed.

(** The unit of the adjunction is the unit of the monad. *)

Lemma Kleisli_unit_agrees {x : C} :
  @unit _ _ _ _ Kleisli_Adjunction x ≈ ret[M].
Proof. reflexivity. Qed.

(** The counit at x is the identity arrow on M x, read as the Kleisli
    morphism F_M (U_M x) ~{C_M}~> x that runs the computation. *)

Lemma Kleisli_counit_agrees {x : C} :
  @counit _ _ _ _ Kleisli_Adjunction x ≈ id[M x].
Proof. reflexivity. Qed.

(** The multiplication of the monad induced by this adjunction (per
    Monad/Adjunction.v it is the U_M-image of the counit) is join. *)

Lemma Kleisli_join_agrees {x : C} :
  fmap[Kleisli_Forget] (@counit _ _ _ _ Kleisli_Adjunction x) ≈ join[M].
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers M: the composite U_M ◯ F_M is naturally
    isomorphic to M, with identity components. *)

Theorem Kleisli_Monad_agrees : Kleisli_Forget ◯ Kleisli_Free ≈ M.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  cat.
Qed.

End KleisliAdjunction.
