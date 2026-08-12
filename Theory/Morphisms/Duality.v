Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

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
   Theory/Morphisms.v.  Adding the import there is therefore a cycle, and Rocq
   rejects it (the exact message depends on which .vo files are present -- a
   self-require complaint on a clean tree, an inconsistent-assumptions error
   against a stale Morphisms.vo -- but it is refused either way).
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

(** ** The wide subcategories of monos and of epis *)

(* Riehl, CTiC, §1.2 (Exercise 1.2.ii): the monomorphisms of C form a wide
   subcategory -- wide because every identity is monic, a subcategory because
   monos compose.  Those are exactly [id_monic] and [monic_compose], so the
   record below has no proof content of its own; the point is that the two
   closure lemmas are precisely the subcategory axioms. *)
Definition MonoSub (C : Category) : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => Monic f;
  scomp := fun x y z _ _ _ f g Hf Hg => monic_compose Hf Hg;
  sid   := fun x _ => id_monic x
|}.

Definition MonoSub_Wide (C : Category) : Wide C (MonoSub C) :=
  fun _ => ttt.

(* The dual, obtained through C^op rather than reproved: an epimorphism of C
   is a monomorphism of C^op, so [EpiSub] transports [MonoSub (C^op)] back
   along the bridges above rather than repeating the closure arguments.  Note
   the composition order flips in the opposite category, which is why the
   [scomp] field below feeds its two arguments in the other order. *)
Definition EpiSub (C : Category) : Subcategory C.
Proof.
  unshelve refine {| sobj := fun _ => poly_unit
                   ; shom := fun x y _ _ f => Epic f |}.
  - (* closure under composition, from [monic_compose] read in C^op *)
    intros x y z ox oy oz f g Hf Hg.
    exact (Epic_of_op_Monic (f ∘ g)
             (@monic_compose (C^op) z y x g f
                (op_Monic_of_Epic g Hg) (op_Monic_of_Epic f Hf))).
  - (* identities, from [id_monic] read in C^op *)
    intros x ox.
    exact (Epic_of_op_Monic (@id C x) (@id_monic (C^op) x)).
Defined.

Definition EpiSub_Wide (C : Category) : Wide C (EpiSub C) :=
  fun _ => ttt.
