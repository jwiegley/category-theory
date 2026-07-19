Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.FCoalg.

Generalizable All Variables.

(** * Lambek's lemma *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   Lambek's lemma states that the structure map of an initial F-algebra is an
   isomorphism: if [(μ, α)] is the initial object of [FAlg F], then
   [α : F μ ~> μ] is invertible, so [F μ ≅ μ] and [μ] is a fixed point of [F]
   ("the least fixed point"). The classical one-line argument runs entirely
   inside [FAlg F]:

     - form the algebra [(F μ, fmap α)];
     - the initial mediator [h : μ ~> F μ] into it is an algebra map, so it
       commutes: [h ∘ α ≈ fmap α ∘ fmap h];
     - [α], read as an algebra map [(F μ, fmap α) ~> (μ, α)], composes with the
       mediator to give an endomorphism of the initial object, which by
       initiality is the identity: [α ∘ h ≈ id];
     - feeding [α ∘ h ≈ id] back through the mediator's commuting square and
       functoriality yields [h ∘ α ≈ id].

   Hence [α] and [h] are mutually inverse and [F μ ≅ μ]. By duality the final
   F-coalgebra has an invertible structure map as well, [ν ≅ F ν] (the greatest
   fixed point); [lambek_final] obtains this by applying [lambek] to [F^op] (the
   final F-coalgebra being the initial [F^op]-algebra) and taking the symmetric
   isomorphism. *)

Theorem lambek `(F : C ⟶ C) (I : @Initial (FAlg F)) :
  F (`1 (@initial_obj (FAlg F) I)) ≅ `1 (@initial_obj (FAlg F) I).
Proof.
  (* The initial algebra [(μ, α)] and the auxiliary algebra [(F μ, fmap α)]. *)
  pose (iobj := @initial_obj (FAlg F) I).
  pose (Falg := ((F (`1 iobj))
                   ; (fmap[F] (`2 iobj) : FAlgebra F (F (`1 iobj))))).
  (* [α] itself is an algebra map [(F μ, fmap α) ~> (μ, α)]. *)
  pose (αHom := {| falg_hom := `2 iobj; falg_commutes := ltac:(reflexivity) |}
                : Falg ~{FAlg F}~> iobj).
  (* The unique mediator [h : μ ~> F μ] out of the initial algebra. *)
  pose (hHom := @zero (FAlg F) I Falg).
  (* The mediator is an algebra map, so its carrier commutes with structures. *)
  assert (Hcomm : falg_hom[hHom] ∘ (`2 iobj)
                    ≈ fmap[F] (`2 iobj) ∘ fmap[F] falg_hom[hHom]).
  { exact (@falg_commutes _ _ _ _ _ _ hHom). }
  (* [α ∘ h] is an endomorphism of the initial algebra, hence the identity. *)
  assert (Hαh : (`2 iobj) ∘ falg_hom[hHom] ≈ id).
  { pose proof (zero_unique (αHom ∘ hHom) id) as Huniq; simpl in Huniq;
      exact Huniq. }
  (* Pushing [α ∘ h ≈ id] through the commuting square gives [h ∘ α ≈ id]. *)
  assert (Hhα : falg_hom[hHom] ∘ (`2 iobj) ≈ id).
  { rewrite Hcomm.
    transitivity (fmap[F] ((`2 iobj) ∘ falg_hom[hHom])).
    - symmetry; apply fmap_comp.
    - rewrite Hαh; apply fmap_id. }
  (* [α] and [h] are mutually inverse: [F μ ≅ μ]. *)
  exact {| to := `2 iobj; from := falg_hom[hHom];
           iso_to_from := Hαh; iso_from_to := Hhα |}.
Qed.

(* Dually, the structure map of the final F-coalgebra is an isomorphism. The
   category [FCoalg F] is [(FAlg (F^op))^op], so [@Terminal (FCoalg F)] is
   definitionally [@Initial (FAlg (F^op))] and the final F-coalgebra is the
   initial [F^op]-algebra. Its carrier [ν] is an object of [C^op], so this
   isomorphism lives in [C^op]; applying [lambek] to [F^op] gives
   [F^op ν ≅[C^op] ν], and its symmetric form [iso_sym] is the required
   [ν ≅ F ν]. *)
Theorem lambek_final `(F : C ⟶ C) (T : @Terminal (FCoalg F)) :
  `1 (@terminal_obj (FCoalg F) T) ≅ F (`1 (@terminal_obj (FCoalg F) T)).
Proof.
  exact (iso_sym (lambek (F^op) T)).
Qed.
