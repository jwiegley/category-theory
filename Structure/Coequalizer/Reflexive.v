Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(** * Reflexive pairs and reflexive coequalizers *)

(* nLab:      https://ncatlab.org/nlab/show/reflexive+coequalizer
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   A parallel pair f, g : x ~> y is *reflexive* when the two maps share a
   common section s : y ~> x, i.e.

       f ∘ s ≈ id   and   g ∘ s ≈ id.

   The name comes from the motivating example: when x is the total object
   of a relation on y with projections f and g — say a congruence being
   quotiented — a common section is precisely a reflexivity witness,
   embedding y into the relation along the diagonal.

   A *reflexive coequalizer* is a coequalizer of a reflexive pair.
   [HasReflexiveCoequalizers] packages a choice of elementary coequalizer
   (in the [IsCoequalizer] sense of [Structure/Coequalizer.v]) for every
   reflexive pair; it is the reflexive analogue of [HasCoequalizers], and
   a strictly weaker demand on the category.  Reflexive coequalizers are
   the workhorse of the theory of algebras: the canonical presentation of
   an algebra by free algebras is a reflexive pair, so categories of
   algebras are as cocomplete as their reflexive coequalizers allow
   (Linton, "Coequalizers in categories of algebras", 1969).

   Being given by two equations with no quantification over the ambient
   category, reflexive pairs are preserved by arbitrary functors
   ([functor_preserves_reflexive]), just as split coequalizers are in
   [Structure/Coequalizer/Split.v] — although the *coequalizer* of a
   reflexive pair, unlike that of a split one, need not be preserved. *)

(* The equational data: one map that both f and g retract. *)
Record ReflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  refl_section : y ~> x;                   (* the common section *)
  refl_section_f : f ∘ refl_section ≈ id;  (* f retracts it *)
  refl_section_g : g ∘ refl_section ≈ id   (* and so does g *)
}.

Arguments refl_section   {_ _ _ _ _} _.
Arguments refl_section_f {_ _ _ _ _} _.
Arguments refl_section_g {_ _ _ _ _} _.

(* A category has reflexive coequalizers when every reflexive pair
   carries an elementary coequalizer.  Compare [HasCoequalizers] in
   [Structure/Coequalizer.v], which asks the same of every parallel
   pair. *)
Class HasReflexiveCoequalizers (C : Category) := {
  reflexive_coeq {x y : C} (f g : x ~> y) :
    ReflexivePair f g → ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

(** ** Recognizing reflexive pairs *)

(* Exhibiting a common section in the style of [scoeq_t] from
   [Structure/Coequalizer/Split.v] — a single map split by both f and g —
   is exactly what it takes: the record is precisely this data. *)
Lemma common_section_reflexive {C : Category} {x y : C} (f g : x ~> y)
  (s : y ~> x) (Hf : f ∘ s ≈ id) (Hg : g ∘ s ≈ id) :
  ReflexivePair f g.
Proof.
  exact {| refl_section   := s
         ; refl_section_f := Hf
         ; refl_section_g := Hg |}.
Defined.

(* When every parallel pair has a coequalizer, so in particular does
   every reflexive one. *)
#[export] Instance HasCoequalizers_HasReflexiveCoequalizers
  {C : Category} `{H : @HasCoequalizers C} : HasReflexiveCoequalizers C := {|
  reflexive_coeq := fun x y f g _ => @coeq C H x y f g
|}.

(** ** Functors preserve reflexive pairs *)

(* Push the common section through fmap; both retraction laws follow from
   the corresponding law in the source by functoriality.  The proof ends
   with [Defined] so that the transported section [fmap (refl_section R)]
   stays visible to conversion. *)
Theorem functor_preserves_reflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ReflexivePair f g → ReflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| refl_section := fmap[F] (refl_section R) |}.
  - (* fmap f ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_f R).
    apply fmap_id.
  - (* fmap g ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_g R).
    apply fmap_id.
Defined.
