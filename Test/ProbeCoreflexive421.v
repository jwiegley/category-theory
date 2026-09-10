(** * Probe for Structure/Equalizer/Coreflexive.v (issue #421)

    Pins the measured boundaries of coreflexive pairs and Manes' criterion:
    the notion is the op-dual of a reflexive pair field for field but not
    as a type, the class is neither the dual class nor [HasEqualizers] by
    conversion, the identity index that makes Mac Lane's pair coreflexive
    exists only at the FULL arrow family of Structure/Limit/FromProducts.v,
    and the Sets converse of Exercise 1(b) needs a properness hypothesis.
    Every refutation command below was stripped ONE AT A TIME in a copy of
    the whole file and compiled alone with its error read, so each refusal
    is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [CoreflexivePair f g = @ReflexivePair (C^op) y x f g]
                     is refused at [eq_refl] ("cannot unify"); the fields
                     convert ([p421_field_converts]) and the pair
                     round-trips both ways at [eq_refl] (controls).
     N2 CONVERSION   [HasCoreflexiveEqualizers C = HasReflexiveCoequalizers
                     (C^op)] is refused at [eq_refl]: the existential
                     bodies are [IsEqualizer] and [IsCoequalizer]; both
                     class directions are derivable (controls).
     N3 CONVERSION   [HasCoreflexiveEqualizers C = HasEqualizers C] is
                     refused at [eq_refl]; the inclusion from
                     [HasEqualizers] is an instance (control).
     N4 TYPING       at an abstract generating family, the projection at a
                     chosen index has codomain [F (idx_cod (idx_id x))],
                     not [F x]; it lands at its declared codomain
                     (control), and at the FULL index the tie to [x] is
                     definitional (control, and [p421_id_index] at
                     [eq_refl]).  TRAP, pinned positively: with [idx_cod]
                     left implicit the same ascription is ACCEPTED —
                     [p421_trap_gen_proj_at_x] names a DIFFERENT product,
                     the unifier having solved [?idx_cod (idx_id x) ≡ x]
                     with a constant family.
     N5 TYPING       the choice function carried by [diagonal_in_image]
                     is not a Sets morphism by itself: the record literal
                     is refused with "Cannot infer field proper_morphism";
                     [diagonal_section] with the properness hypothesis is
                     the control, and the IMAGE-level biconditional
                     [diagonal_in_image_iff_through_image] — proper in
                     both directions with no hypothesis, because the image
                     setoid compares codomain components only — is the
                     second control.

    Readbacks: [mc_limit_apex] and [mc_limit_leg] (Theorem 2's explicit
    limit read back through Manes' equalizer), the three identity-index
    [eq_refl]s, and the non-vacuity witness [Sets_Complete_via_Manes].

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the five names the refuted
    declarations would introduce, and the instrument's absent name — so a
    renamed or removed constant breaks the build on a positive line rather
    than letting a refutation pass for the wrong reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Structure.Equalizer.Coreflexive.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe421_absent_name.

(** ** A: the notion is the op-dual in its fields, not as a type *)

Section OpDual.

Context {C : Category} {x y : C} (f g : x ~> y).

(* control: a common left inverse in C IS a common section in C^op, field
   for field *)
Example p421_field_converts (s : y ~> x) (H : s ∘ f ≈ id) :
  f ∘[C^op] s ≈ id := H.

(* controls: the pair repackages both ways and round-trips at [eq_refl] *)
Check (@corefl_op_round C x y f g).
Check (@op_corefl_round C x y f g).

(* N1 CONVERSION: the record types are distinct *)
Fail Example p421_pair_is_op :
  CoreflexivePair f g = @ReflexivePair (C^op) y x f g := eq_refl.

(* N2 CONVERSION: so are the classes — the existential bodies are
   [IsEqualizer] and [IsCoequalizer] *)
Fail Example p421_class_is_op :
  HasCoreflexiveEqualizers C = HasReflexiveCoequalizers (C^op) := eq_refl.

(* controls: both class directions are derivable *)
Check (@HasCoreflexiveEqualizers_of_op C).
Check (@op_HasReflexiveCoequalizers_of_Coreflexive C).

(* N3 CONVERSION: coreflexive equalizers are not all equalizers *)
Fail Example p421_class_is_HasEqualizers :
  HasCoreflexiveEqualizers C = HasEqualizers C := eq_refl.

(* control: the inclusion the other way is an instance *)
Check (fun H : @HasEqualizers C => @HasEqualizers_HasCoreflexiveEqualizers C H).

End OpDual.

(** ** B: the identity index lives in the FULL arrow family only *)

Section GenFamily.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).
Context (idx_id : J → I).

(* N4 TYPING: at an abstract generating family, the projection at a
   chosen index does not land in [F x] — its codomain is
   [idx_cod (idx_id x)], with no definitional tie to [x] *)
Fail Definition p421_gen_proj_at_x (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F x :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(* control: at the declared codomain it lands *)
Definition p421_gen_proj_at_cod (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F (idx_cod (idx_id x)) :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(* TRAP, pinned positively: with [idx_cod] left implicit the SAME
   ascription is accepted — the unifier solves [?idx_cod (idx_id x) ≡ x]
   with a constant family, so this names a DIFFERENT product *)
Definition p421_trap_gen_proj_at_x (x : J) :
  pe_gen_product HP F ~> F x := pe_gen_proj HP F (idx_id x).

(* control: at the full index the tie is definitional *)
Definition p421_full_proj_at_x (x : J) :
  pe_arrow_product HP F ~> F x :=
  pe_arrow_proj HP F (mk_arrow (@id J x)).

Check (@id_index_cod J).

(* readback: the identity index's codomain is [x] on the nose *)
Example p421_id_index (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.

End GenFamily.

(** ** C: the Sets converse needs properness *)

Section SetsConverse.

Context {X Y : SetoidObject} (f g : X ~{Sets}~> Y).

(* N5 TYPING: the choice function carried by [diagonal_in_image] is not by
   itself a Sets morphism — the [proper_morphism] field is missing *)
Fail Definition p421_bare_section (D : diagonal_in_image f g) : Y ~{Sets}~> X :=
  {| morphism := fun b => `1 (D b) |}.

(* control: with the properness hypothesis it is *)
Check (fun (D : diagonal_in_image f g)
           (Hp : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) =>
         diagonal_section f g D Hp).

(* control: the IMAGE-level reading needs no such hypothesis in either
   direction — the image setoid compares codomain components only, so the
   bare choice function is proper there *)
Check (fun D : diagonal_in_image f g =>
         fst (diagonal_in_image_iff_through_image f g) D).
Check (fun (d : Y ~{Sets}~> Sets_Image (f △ g))
           (Hd : Sets_Image_mono (f △ g) ∘ d ≈ id △ id) =>
         snd (diagonal_in_image_iff_through_image f g) (d; Hd)).

End SetsConverse.

(** ** D: readbacks and non-vacuity *)

Check (@mc_limit_apex).
Check (@mc_limit_leg).
Check (@id_index_dom).
Check (@id_index_arr).
Check (@Sets_Complete_via_Manes).
Check (fun (C : Category) (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) =>
         Complete_from_coreflexive_equalizers HP HE).

(** ** Guard block *)

Check @CoreflexivePair.
Check @corefl_retract.
Check @corefl_retract_f.
Check @corefl_retract_g.
Check @HasCoreflexiveEqualizers.
Check @coreflexive_eq.
Check @common_retraction_coreflexive.
Check @HasEqualizers_HasCoreflexiveEqualizers.
Check @functor_preserves_coreflexive.
Check @CoreflexivePair_of_op.
Check @op_ReflexivePair_of_Coreflexive.
Check @corefl_op_round.
Check @op_corefl_round.
Check @HasCoreflexiveEqualizers_of_op.
Check @op_HasReflexiveCoequalizers_of_Coreflexive.
Check @pe_retract.
Check @pe_retract_proj.
Check @pe_retract_s.
Check @pe_retract_t.
Check @pe_coreflexive.
Check @mc_equalizer.
Check @mc_apex.
Check @mc_incl.
Check @mc_IsEqualizer.
Check @mc_cone.
Check @mc_limiting.
Check @mc_limit.
Check @Complete_from_coreflexive_equalizers.
Check @fork_diagonal_of_reflexive.
Check @reflexive_of_fork_diagonal.
Check @ReflexivePair_of_diagonal_factors.
Check @diagonal_factors_of_ReflexivePair.
Check @ReflexivePair_iff_diagonal_factors.
Check @diagonal_in_image.
Check @diagonal_in_image_of_reflexive.
Check @diagonal_section.
Check @reflexive_of_diagonal_in_image.
Check @diagonal_through_image.
Check @diagonal_in_image_of_through_image.
Check @through_image_of_diagonal_in_image.
Check @diagonal_in_image_iff_through_image.
Check @Sets_HasCoreflexiveEqualizers.
Check @ReflexivePair.
Check @HasReflexiveCoequalizers.
Check @HasEqualizers.
Check @pe_gen_product.
Check @pe_gen_proj.
Check @pe_arrow_product.
Check @pe_arrow_proj.
Check @mk_arrow.
Check @Generates.
Check @id.
Check @morphism.
