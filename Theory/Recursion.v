Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.FCoalg.

Generalizable All Variables.

(** * Catamorphisms and anamorphisms *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Catamorphism
              https://en.wikipedia.org/wiki/Anamorphism

   When the endofunctor [F : C ⟶ C] has an initial F-algebra [(μ, inα)] — the
   initial object of [FAlg F] (Construction/FAlg.v) — its universal property is
   exactly the principle of structural recursion.  For every F-algebra
   [(a, β)] there is a unique carrier map [cata β : μ ~> a] making the square

       F μ --inα--> μ
        |           |
     F(cata β)   cata β
        |           |
        v           v
       F a ---β----> a

   commute; this mediator is the *catamorphism* (a "fold").  Uniqueness and the
   fusion law follow from the uniqueness of the initial-object mediator [zero].

   Dually, a final F-coalgebra [(ν, outγ)] — the terminal object of [FCoalg F]
   (Construction/FCoalg.v) — gives structural corecursion: every coalgebra
   [(a, γ)] has a unique [ana γ : a ~> ν] (an "unfold").  Because the library
   builds [FCoalg F] as [(FAlg (F^op))^op], so that [@Terminal (FCoalg F)] is
   definitionally [@Initial (FAlg (F^op))], the anamorphism package is obtained
   from the catamorphism package for [F^op] purely by op-duality, with
   composition and [fmap] reversed on the nose. *)

Section Catamorphism.

Context {C : Category}.
Context (F : C ⟶ C).
Context (I : @Initial (FAlg F)).

(* The initial F-algebra: its carrier [μ] is the least fixed point of [F] and
   its structure map [inα : F μ ~> μ] is the initial structure (Lambek makes it
   an isomorphism, Theory/Lambek.v). *)
Let iobj : FAlg F := @initial_obj (FAlg F) I.
Let μ : C := `1 iobj.
Let inα : F μ ~> μ := `2 iobj.

(* The catamorphism (fold) into an F-algebra [(a, β)] is the carrier of the
   unique F-algebra mediator [iobj ~> (a; β)] provided by initiality. *)
Definition cata {a : C} (β : FAlgebra F a) : μ ~> a :=
  falg_hom[ @zero (FAlg F) I (a ; β) ].

(* The defining square: the mediator is an F-algebra homomorphism, so its
   carrier commutes the initial structure [inα] with the target structure [β].
   This is exactly [falg_commutes] of that mediator. *)
Lemma cata_commutes {a : C} (β : FAlgebra F a) :
  cata β ∘ inα ≈ β ∘ fmap[F] (cata β).
Proof.
  exact (@falg_commutes _ _ _ _ _ _ (@zero (FAlg F) I (a ; β))).
Qed.

(* Uniqueness: any carrier [h] commuting the same square is the catamorphism.
   Package [h] as an F-algebra homomorphism [iobj ~> (a; β)] and appeal to the
   uniqueness of the initial mediator [zero]. *)
Lemma cata_unique {a : C} (β : FAlgebra F a) (h : μ ~> a)
      (Hh : h ∘ inα ≈ β ∘ fmap[F] h) : h ≈ cata β.
Proof.
  exact (@zero_unique (FAlg F) I (a ; β)
           (@Build_FAlgHom _ F μ a inα β h Hh)
           (@zero (FAlg F) I (a ; β))).
Qed.

(* Fusion: a carrier map [g] of F-algebras absorbs into the fold.  The
   composite [g ∘ cata β] is again an F-algebra mediator [iobj ~> (b; γ)], and
   so it coincides with [cata γ] by initiality. *)
Lemma cata_fusion {a b : C} (β : FAlgebra F a) (γ : FAlgebra F b)
      (g : a ~> b) (Hg : g ∘ β ≈ γ ∘ fmap[F] g) :
  g ∘ cata β ≈ cata γ.
Proof.
  exact (@zero_unique (FAlg F) I (b ; γ)
           ((@Build_FAlgHom _ F a b β γ g Hg : (a ; β) ~{FAlg F}~> (b ; γ))
              ∘ @zero (FAlg F) I (a ; β))
           (@zero (FAlg F) I (b ; γ))).
Qed.

End Catamorphism.

Section Anamorphism.

Context {C : Category}.
Context (F : C ⟶ C).
Context (T : @Terminal (FCoalg F)).

(* The final F-coalgebra: its carrier [ν] is the greatest fixed point of [F]
   and its structure map [outγ : ν ~> F ν] is the final structure.  Since
   [FCoalg F = (FAlg (F^op))^op], the terminal object [T] is definitionally the
   initial [F^op]-algebra, which is what powers the op-transfer below. *)
Let tobj : FCoalg F := @terminal_obj (FCoalg F) T.
Let ν : C := `1 tobj.
Let outγ : ν ~> F ν := `2 tobj.

(* The anamorphism (unfold) out of a coalgebra [(a, γ)] is the catamorphism for
   [F^op], read back through the definitional identity of the two categories. *)
Definition ana {a : C} (γ : FCoalgebra F a) : a ~> ν :=
  @cata (C^op) (F^op) T a γ.

(* The defining square, with composition and [fmap] reversed relative to the
   algebra side; it is [cata_commutes] for [F^op] whose op-composition unfolds
   to the C-composition displayed here. *)
Lemma ana_commutes {a : C} (γ : FCoalgebra F a) :
  outγ ∘ ana γ ≈ fmap[F] (ana γ) ∘ γ.
Proof.
  exact (@cata_commutes (C^op) (F^op) T a γ).
Qed.

(* Uniqueness of the unfold, dual to [cata_unique]. *)
Lemma ana_unique {a : C} (γ : FCoalgebra F a) (h : a ~> ν)
      (Hh : outγ ∘ h ≈ fmap[F] h ∘ γ) : h ≈ ana γ.
Proof.
  exact (@cata_unique (C^op) (F^op) T a γ h Hh).
Qed.

(* Fusion for the unfold, dual to [cata_fusion]. *)
Lemma ana_fusion {a b : C} (γ : FCoalgebra F a) (δ : FCoalgebra F b)
      (g : b ~> a) (Hg : γ ∘ g ≈ fmap[F] g ∘ δ) :
  ana γ ∘ g ≈ ana δ.
Proof.
  exact (@cata_fusion (C^op) (F^op) T a b γ δ g Hg).
Qed.

End Anamorphism.
