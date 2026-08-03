Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Monic/epi duality, carried out through the opposite category *)

(* nLab: https://ncatlab.org/nlab/show/monomorphism
   nLab: https://ncatlab.org/nlab/show/epimorphism
   Book: Riehl, "Category Theory in Context", §1.2 (Lemma 1.2.11)

   Riehl's §1.2 states four facts about monos and epis -- closure under
   composition and cancellation, each in two variances -- and the point of the
   section is that only two of them need proving: the other two are their
   images under C ↦ C^op.  Theory/Morphisms.v proves all four directly, for a
   reason that is structural rather than stylistic, and this file supplies the
   dual route that file cannot.

   WHY NOT IN Theory/Morphisms.v.  Duality needs [Opposite], and
   Construction/Opposite.v requires Theory/Isomorphism.v, which requires
   Theory/Morphisms.v.  Adding the import there is therefore a cycle -- Rocq
   reports "Cannot load a library with the same name as the current one".
   Since the cancellation lemmas are consumed low in the tree (by
   Structure/Factorization/StrongEpi.v and Theory/Subobject.v), they have to
   live below the opposite category, and the dual derivation has to live above
   it.  Hence: direct proofs there, dual derivations here.

   WHAT DUALITY COSTS HERE.  [Monic] and [Epic] are two distinct records, not
   one notion read in two variances, so `@Epic (C^op) y x f` is not literally
   `@Monic C x y f` -- Rocq rejects the identity function between them.  What
   IS true is that their single fields have the same type on the nose, because
   `x ~{C^op}~> z` reduces to `z ~{C}~> x` and `g ∘[C^op] f` to `f ∘[C] g`.
   So each bridge below is one constructor application with no proof content,
   and the derivations that follow genuinely reuse the original argument
   rather than repeating it. *)

(** ** The four bridges *)

Definition Monic_of_op_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic (C^op) y x f) : @Monic C x y f :=
  @Build_Monic C x y f (@epic (C^op) y x f H).

Definition op_Epic_of_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic C x y f) : @Epic (C^op) y x f :=
  @Build_Epic (C^op) y x f (@monic C x y f H).

Definition Epic_of_op_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic (C^op) y x f) : @Epic C x y f :=
  @Build_Epic C x y f (@monic (C^op) y x f H).

Definition op_Monic_of_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic C x y f) : @Monic (C^op) y x f :=
  @Build_Monic (C^op) y x f (@epic C x y f H).

(** ** The dual derivations *)

(* [monic_cancel] obtained from [epic_cancel] with no second argument.  In
   C^op the composite f ∘ g becomes g ∘ f, so cancelling the LEFT factor there
   is cancelling the RIGHT factor here -- which is exactly why the two lemmas
   read as mirror images rather than as the same statement twice. *)
Definition monic_cancel_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic (f ∘ g) → Monic g :=
  fun H => Monic_of_op_Epic g
             (@epic_cancel (C^op) z y x g f (op_Epic_of_Monic (f ∘ g) H)).

(* And [monic_compose] from [epi_compose], the same way. *)
Definition monic_compose_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic f → Monic g → Monic (f ∘ g) :=
  fun Hf Hg =>
    Monic_of_op_Epic (f ∘ g)
      (@epi_compose (C^op) z y x g f
         (op_Epic_of_Monic g Hg) (op_Epic_of_Monic f Hf)).

(* The derived forms prove the same statements as the direct ones.  Stating
   this is the honest way to keep both: nothing here silently replaces
   Theory/Morphisms.v's proofs, and if the two ever drifted apart these would
   stop typechecking. *)
Definition monic_cancel_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic (f ∘ g) → Monic g) * (Monic (f ∘ g) → Monic g) :=
  (@monic_cancel C x y z f g, @monic_cancel_op C x y z f g).

Definition monic_compose_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic f → Monic g → Monic (f ∘ g)) *
  (Monic f → Monic g → Monic (f ∘ g)) :=
  (@monic_compose C x y z f g, @monic_compose_op C x y z f g).
