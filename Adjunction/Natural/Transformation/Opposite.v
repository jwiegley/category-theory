Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Natural.Transformation.

Generalizable All Variables.

(** * The opposite (dual) of a unit/counit adjunction. *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Adjunctions dualize: from F ⊣ U (here [F ∹ U], with F : D ⟶ C the left
   adjoint and U : C ⟶ D the right adjoint) one obtains an adjunction in the
   opposite categories whose *left* adjoint is U^op and whose *right* adjoint is
   F^op, that is, U^op ⊣ F^op (here [U^op ∹ F^op] : C^op ⇄ D^op). The right
   adjoint U becomes the left adjoint after oppositization, and vice versa, as
   the hom-set bijection Hom_C(F d, c) ≅ Hom_D(d, U c) becomes, on reversing
   every hom-set, Hom_{C^op}(c, F^op d) ≅ Hom_{D^op}(U^op c, d), which is exactly
   the defining bijection of U^op ⊣ F^op.

   Under this duality the unit and counit swap roles: reversing 2-cells turns the
   original counit ε : F ◯ U ⟹ Id into the *unit* Id ⟹ F^op ◯ U^op of the
   opposite adjunction, and the original unit η : Id ⟹ U ◯ F into its *counit*
   U^op ◯ F^op ⟹ Id. Accordingly the new [unit] field is built from [counit]
   and the new [counit] field from [unit], with the two naturality orientations
   (naturality/naturality_sym) exchanged because op reverses naturality squares.
   The two triangle identities map onto each other in the same swapped way: the
   opposite adjunction's triangles are [fmap_counit_unit] and [counit_fmap_unit]
   of the original, reused on the nose. *)

Program Definition Opposite_Adjunction_Transform
        `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  U^op ∹ F^op := {|
  unit := _;
  counit := _
|}.
Next Obligation.
  transform; simpl; intros.
  - apply counit.
  - apply (@naturality_sym _ _ _ _ counit).
  - apply (@naturality _ _ _ _ counit).
Defined.
Next Obligation.
  transform; simpl; intros.
  - apply unit.
  - apply (@naturality_sym _ _ _ _ unit).
  - apply (@naturality _ _ _ _ unit).
Defined.
Next Obligation.
  apply fmap_counit_unit.
Defined.
Next Obligation.
  apply counit_fmap_unit.
Defined.

(* Oppositization is involutive on adjunctions: applying it twice recovers the
   original [A] on the nose. This holds because (F^op)^op = F definitionally and
   the construction merely swaps the unit/counit and naturality fields, so a
   second swap restores them; hence the equality is provable by [reflexivity]. *)

Corollary Opposite_Adjunction_Transform_invol
          `(F : D ⟶ C) `(U : C ⟶ D) (A : F ∹ U) :
  Opposite_Adjunction_Transform
    (U^op) (F^op) (Opposite_Adjunction_Transform F U A) = A.
Proof. reflexivity. Qed.
