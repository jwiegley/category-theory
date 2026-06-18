Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.

Generalizable All Variables.

(** The identity functor is monoidal. *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   The identity functor Id[C] on a monoidal category C is canonically a strong
   (indeed strict) monoidal functor.  Because Id x = x on the nose, the two
   comparison maps are identities,

       η     = id : I ~> Id I        (unit comparison, here pure_iso = iso_id),
       μ_x_y = id : Id x ⨂ Id y ~> Id (x ⨂ y)   (tensor comparison),

   so both are trivially invertible (strong) and equal to identities (strict).
   The three coherence squares — left and right unitality against λ and ρ, and
   associativity against the associator α — collapse to the monoidal axioms of
   C itself, discharged below by tensor_assoc and bimap_id_id.  This instance
   is the unit of the 2-category MonCat of monoidal categories and (strong)
   monoidal functors.  [Id_MonoidalFunctor] gives the strong form and
   [Id_LaxMonoidalFunctor] the lax form, both axiom-free. *)

Section MonoidalFunctors.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {G : C ⟶ D}.

Context {E : Category}.
Context `{@Monoidal E}.
Context {F : D ⟶ E}.

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Id_MonoidalFunctor :
  @MonoidalFunctor C C _ _ Id[C] := {
  pure_iso := iso_id;
  ap_functor_iso := {| to   := {| transform := fun _ => _ |}
                     ; from := {| transform := fun _ => _ |} |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation.
  simpl; intros.
  destruct H1; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

#[export] Program Instance Id_LaxMonoidalFunctor :
  @LaxMonoidalFunctor C C _ _ Id[C] := {
  lax_pure := id;
  ap_functor_nat := {| transform := fun _ => _ |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

End MonoidalFunctors.
