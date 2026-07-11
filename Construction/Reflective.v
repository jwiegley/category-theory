Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/reflective+subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Reflective_subcategory

   A reflective subcategory of C is a full subcategory S ⊆ C whose inclusion
   functor [Incl C S : Sub C S ⟶ C] has a left adjoint, the reflector
   [reflector : C ⟶ Sub C S], with [reflector ⊣ Incl C S].  The record
   [Reflective] below bundles exactly these three data: fullness of the
   subcategory ([reflective_full]), the reflector, and the adjunction.

   Dually, a coreflective subcategory is one whose inclusion has a right
   adjoint (the coreflector).  We obtain it by reflectivity in the opposite
   category: [Coreflective S := Reflective (op_subcategory S)], where
   [op_subcategory S] is the subcategory of C^op selecting the same objects
   and the C^op-reverses of the morphisms of S.

   The characteristic property of a *full* reflective subcategory is that the
   counit ε : reflector ∘ Incl ⟹ Id of the adjunction is a natural
   isomorphism: at every object [x] of the subcategory the component
   ε_x : reflector (Incl x) ~> x is invertible.  Its inverse is the unit
   η_{Incl x} : Incl x ~> Incl (reflector (Incl x)) of the adjunction, read
   back into [Sub C S] using fullness — fullness supplies the [shom] witness
   making η into a morphism of the subcategory ([reflective_counit_iso]).  One
   triangle identity ([fmap_counit_unit]) discharges ε_x ∘ η ≈ id, and the
   other ([counit_fmap_unit]) together with naturality of the counit
   ([counit_naturality]) discharges η ∘ ε_x ≈ id. *)

(* The counit of an adjunction is natural at an arbitrary morphism.  The
   corollaries in Theory/Adjunction.v prove this square only when the domain
   is an F-image ([counit_comp]); the general form below (a copy of the
   argument used for the corollaries there) is what the counit-iso proof
   consumes, since its morphism runs out of an arbitrary object of the
   subcategory. *)

Lemma counit_naturality
      {Cadj Dadj : Category} {F : Dadj ⟶ Cadj} {U : Cadj ⟶ Dadj}
      (A : F ⊣ U) {x y : Cadj} (f : x ~> y) :
  @counit Cadj Dadj F U A y ∘ fmap[F] (fmap[U] f)
    ≈ f ∘ @counit Cadj Dadj F U A x.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  now rewrite id_left, id_right.
Qed.

(* The reflector, the fullness witness, and the reflection adjunction. *)

Record Reflective {C : Category} (S : Subcategory C) := {
  reflective_full : Construction.Subcategory.Full C S;
  reflector : C ⟶ Sub C S;
  reflective_adj : reflector ⊣ Incl C S
}.

Arguments reflective_full {C S} r.
Arguments reflector {C S} r.
Arguments reflective_adj {C S} r.

(* The opposite subcategory: the same selected objects, with a C^op-morphism
   x ~> y (that is, a C-morphism y ~> x) selected exactly when the underlying
   C-morphism is selected by S. *)

Definition op_subcategory {C : Category} (S : Subcategory C) :
  Subcategory (C^op) :=
  @Build_Subcategory (C^op)
    (sobj C S)
    (fun x y ox oy f => shom C S oy ox f)
    (fun x y z ox oy oz f g Hf Hg => scomp C S oz oy ox Hg Hf)
    (fun x ox => sid C S ox).

(* A coreflective subcategory of C is a reflective subcategory of C^op on the
   opposite subcategory: the inclusion then has a right adjoint in C. *)

Definition Coreflective {C : Category} (S : Subcategory C) : Type :=
  @Reflective (C^op) (op_subcategory S).

(* For a full reflective subcategory the counit is a componentwise
   isomorphism: reflector (Incl x) ≅ x in Sub C S, with the counit as the
   forward map and the (subcategory-lifted) unit as its inverse. *)

Lemma reflective_counit_iso {C : Category} {S : Subcategory C}
      (R : Reflective S) (x : Sub C S) :
  reflector R (Incl C S x) ≅[Sub C S] x.
Proof.
  unshelve refine
    {| to   := @counit (Sub C S) C (reflector R) (Incl C S)
                 (reflective_adj R) x
     ; from := _
     ; iso_to_from := _
     ; iso_from_to := _ |}.
  - (* inverse: the unit, lifted into the subcategory by fullness *)
    exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - (* ε_x ∘ η ≈ id, one triangle identity *)
    apply (@fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - (* η ∘ ε_x ≈ id, by counit naturality and the other triangle identity *)
    rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.
