Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   Adjunctions transport along equivalences of categories.  Given a
   hom-setoid adjunction F ⊣ U between C and D (Theory/Adjunction.v: the
   left adjoint is F : D ⟶ C, the right adjoint U : C ⟶ D) together with
   equivalences of categories G : C ⟶ C' and K : D ⟶ D'
   (Theory/Equivalence.v), the two conjugated functors

       G ◯ (F ◯ K⁻¹) : D' ⟶ C'      and      (K ◯ U) ◯ G⁻¹ : C' ⟶ D'

   — where G⁻¹ and K⁻¹ are the chosen quasi-inverses — are again adjoint.
   [Transported_Adjunction] below is that adjunction, assembled as the
   three-fold composite (Adjunction/Compose.v) of

       K⁻¹ ⊣ K,   then   F ⊣ U,   then   G ⊣ G⁻¹.

   The two outer constituents are the underlying adjunctions of the
   adjoint equivalences of Theory/Equivalence/Adjoint.v: on the codomain
   side, [equiv_adjunction EC] refines the equivalence carried by G
   directly; on the domain side, the equivalence carried by K is first
   reversed with [EquivalenceOfCategories_sym] (Theory/Equivalence.v) so
   that the quasi-inverse K⁻¹ becomes the left adjoint — this is the same
   pair of constructions that [Equivalence_to_AdjointEquivalence] and
   [AdjointEquivalence_swap] package with their unit/counit isomorphism
   witnesses.

   Alongside the composite adjunction we record its two transposes
   definitionally ([Transported_Adjunction_to]/[_from]: the three-fold
   pasting of the constituent transposes), the standard whiskering
   formulas for its unit and counit in terms of the units and counits of
   the three constituents ([Transported_Adjunction_unit]/[_counit]), and
   the identification of the outer constituents' counits and F-imaged
   units with counit-cell components of the respective equivalences
   ([transported_adj_cod_counit], [transported_adj_dom_counit],
   [transported_adj_cod_fmap_unit], [transported_adj_dom_fmap_unit] —
   all instances of [equiv_adjunction_counit_at] and
   [equiv_adjunction_fmap_unit] from Theory/Equivalence/Adjoint.v).

   Transporting on one side only is the special case in which the other
   equivalence is the identity equivalence [EquivalenceOfCategories_Id]
   (Theory/Equivalence.v), whose quasi-inverse is Id.

   Following Theory/Equivalence.v, nothing in this file is registered for
   instance resolution: the equivalences and the adjunction are data,
   always passed explicitly at use sites. *)

Section TransportedAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {C' : Category}.
Context {D' : Category}.

(* The adjunction being transported, in the variable convention of
   Theory/Adjunction.v: F is the left adjoint. *)
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* The equivalence on the codomain side of F ... *)
Context {G : C ⟶ C'}.
Context (EC : @EquivalenceOfCategories C C' G).

(* ... and the equivalence on its domain side. *)
Context {K : D ⟶ D'}.
Context (ED : @EquivalenceOfCategories D D' K).

(* Section-local shorthands for the two chosen quasi-inverses; the printed
   statements expand them back to [quasi_inverse]. *)
Local Notation Ginv := (@quasi_inverse C C' G EC).
Local Notation Kinv := (@quasi_inverse D D' K ED).

(* The domain-side constituent K⁻¹ ⊣ K: the adjoint-equivalence adjunction
   of the reversed equivalence, whose carrying functor is Kinv and whose
   quasi-inverse is K itself. *)
Definition transported_adj_dom : Kinv ⊣ K :=
  equiv_adjunction (@EquivalenceOfCategories_sym D D' K ED).

(* The codomain-side constituent G ⊣ G⁻¹: the adjoint-equivalence
   adjunction of EC itself. *)
Definition transported_adj_cod : G ⊣ Ginv :=
  equiv_adjunction EC.

(* The transported adjoints: conjugate each of F and U by the two
   equivalences. *)
Definition transported_left_adjoint : D' ⟶ C' := G ◯ (F ◯ Kinv).

Definition transported_right_adjoint : C' ⟶ D' := (K ◯ U) ◯ Ginv.

(* The transported adjunction: paste K⁻¹ ⊣ K, F ⊣ U and G ⊣ G⁻¹ by two
   applications of [Adjunction_Compose]. *)
Definition Transported_Adjunction :
  transported_left_adjoint ⊣ transported_right_adjoint :=
  Adjunction_Compose (Adjunction_Compose transported_adj_dom A)
    transported_adj_cod.

(* The forward transpose of the composite is the pasting of the three
   constituent forward transposes, definitionally: transpose through the
   codomain equivalence, then through the original adjunction, then
   through the domain equivalence. *)
Corollary Transported_Adjunction_to {d : D'} {c : C'}
  (f : G (F (Kinv d)) ~{C'}~> c) :
  to (@adj _ _ _ _ Transported_Adjunction d c) f
    ≈ to (@adj _ _ _ _ transported_adj_dom d (U (Ginv c)))
        (to (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (to (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c) f)).
Proof. reflexivity. Qed.

(* ... and dually for the inverse transpose, in the opposite order. *)
Corollary Transported_Adjunction_from {d : D'} {c : C'}
  (g : d ~{D'}~> K (U (Ginv c))) :
  from (@adj _ _ _ _ Transported_Adjunction d c) g
    ≈ from (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c)
        (from (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (from (@adj _ _ _ _ transported_adj_dom d (U (Ginv c))) g)).
Proof. reflexivity. Qed.

(* The unit of the composite: the domain-side unit, followed by the
   K-image of the unit of A, followed by the (K ◯ U)-image of the
   codomain-side unit — [Adjunction_Compose_unit] applied twice. *)
Corollary Transported_Adjunction_unit {d : D'} :
  @unit _ _ _ _ Transported_Adjunction d
    ≈ fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
        ∘ (fmap[K] (@unit _ _ _ _ A (Kinv d))
             ∘ @unit _ _ _ _ transported_adj_dom d).
Proof.
  transitivity
    (fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
       ∘ @unit _ _ _ _ (Adjunction_Compose transported_adj_dom A) d).
  - apply (Adjunction_Compose_unit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    apply (Adjunction_Compose_unit transported_adj_dom A).
Qed.

(* The counit of the composite, dually: the G-image of (the F-image of the
   domain-side counit, followed by the counit of A), followed by the
   codomain-side counit — [Adjunction_Compose_counit] applied twice. *)
Corollary Transported_Adjunction_counit {c : C'} :
  @counit _ _ _ _ Transported_Adjunction c
    ≈ @counit _ _ _ _ transported_adj_cod c
        ∘ fmap[G] (@counit _ _ _ _ A (Ginv c)
                     ∘ fmap[F] (@counit _ _ _ _ transported_adj_dom
                                  (U (Ginv c)))).
Proof.
  transitivity
    (@counit _ _ _ _ transported_adj_cod c
       ∘ fmap[G] (@counit _ _ _ _ (Adjunction_Compose transported_adj_dom A)
                    (Ginv c))).
  - apply (Adjunction_Compose_counit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    now rewrite (Adjunction_Compose_counit transported_adj_dom A).
Qed.

(* The counit of the codomain-side constituent is the counit-cell
   component of EC. *)
Corollary transported_adj_cod_counit (c : C') :
  @counit _ _ _ _ transported_adj_cod c
    ≈ to (@equivalence_counit_at C C' G EC c).
Proof. exact (equiv_adjunction_counit_at EC c). Qed.

(* The counit of the domain-side constituent is the counit-cell component
   of the reversed equivalence (whose counit cell is the symmetrized unit
   cell of ED). *)
Corollary transported_adj_dom_counit (d : D) :
  @counit _ _ _ _ transported_adj_dom d
    ≈ to (@equivalence_counit_at D' D Kinv
            (@EquivalenceOfCategories_sym D D' K ED) d).
Proof.
  exact (equiv_adjunction_counit_at (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

(* The G-image of the codomain-side unit is an inverse counit-cell
   component of EC ... *)
Corollary transported_adj_cod_fmap_unit (x : C) :
  fmap[G] (@unit _ _ _ _ transported_adj_cod x)
    ≈ from (@equivalence_counit_at C C' G EC (G x)).
Proof. exact (equiv_adjunction_fmap_unit EC x). Qed.

(* ... and the K⁻¹-image of the domain-side unit is an inverse counit-cell
   component of the reversed equivalence. *)
Corollary transported_adj_dom_fmap_unit (d : D') :
  fmap[Kinv] (@unit _ _ _ _ transported_adj_dom d)
    ≈ from (@equivalence_counit_at D' D Kinv
              (@EquivalenceOfCategories_sym D D' K ED) (Kinv d)).
Proof.
  exact (equiv_adjunction_fmap_unit (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

End TransportedAdjunction.
