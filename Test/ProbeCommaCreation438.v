(** * Probe for the comma and coslice creation results (issue #438)

    Pins the measured boundaries of Construction/Comma/Creation.v's
    per-diagram and strict-creation additions and of
    Construction/Slice/Creation.v, with negatives of two kinds kept
    lexically apart.  CONVERSION: N1, the all-shapes [PreservesImageLimit]
    and the shape-indexed family of [PreservesLimitCone]s agree at every
    diagram — the accepted controls show both passages — but the two
    [Type]s are not convertible, one binding a [Limit] where the other
    binds a cone with its universal property; N3 and N4, the coslice is
    reached only by transport, so the transported projection's object
    action does not reduce to the first projection and the coslice is not
    the comma category on the nose; N5, the shipped [comma_CreatesLimit]'s
    [creates_lift] discards the cone it is handed and returns the lift of
    the fixed [L], so its apex is refused against that cone's apex, while
    the paired control shows the new strict lift is accepted.  UNIVERSE:
    N2, a discrete-shape base diagram is not formable over a generic [C],
    because [Gdiag] identifies the shape's hom and proof universes with
    [C]'s and [DiscreteCat]'s hom minimizes to [Set] — which is why the
    products clause is stated elementarily over [IsIndexedProduct].

    The [eq_refl] readbacks are positive controls: the per-diagram limit
    projects onto the downstairs limit in apex and legs, so do the indexed
    product and the equalizer, and the strict lift's own two fields are
    [eq_refl] and [reflexivity].  Each refutation was stripped one at a
    time in a copy of the whole file; the import list mirrors the two
    targets'. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.Compose.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe438_absent_name.

(** ** A: CONVERSION — the two preservation hypotheses *)

Section Preservation.

Context {C D : Category}.
Context {U : C ⟶ D}.

(* control: each direction of the passage exists and is proof-free *)
Check (@PreservesImageLimit_Continuous C D U).
Check (@Continuous_PreservesImageLimit C D U).

(* control: the all-shapes hypothesis yields the per-diagram one at every
   diagram, which is the whole content of the weakening below *)
Check (fun (H : @PreservesImageLimit C D U) (J : Category) (G : J ⟶ C) =>
         (fun N HN => H J G (@Build_Limit J C G N HN))
           : PreservesLimitCone G U).

(* N1 CONVERSION: the two [Type]s are nevertheless not convertible *)
Fail Example p438_types :
  @PreservesImageLimit C D U
    = (∀ (J : Category) (G : J ⟶ C), PreservesLimitCone G U) := eq_refl.

End Preservation.

(** ** B: UNIVERSE — the discrete shape is not formable here *)

Section DiscreteShape.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {A : Type}.
Context (F : A → (=(d) ↓ U)).

(* control: the discrete functor itself is formable *)
Check (DiscreteCat_Functor F).

(* N2 UNIVERSE: but its base diagram is not — [Gdiag] pins the shape's hom
   and proof universes to [C]'s, and [DiscreteCat]'s hom minimizes to [Set] *)
Fail Definition p438_discrete := Gdiag (DiscreteCat_Functor F).

(* control: the elementary products clause needs no shape at all *)
Check (@comma_IsIndexedProduct C D U d A F).

End DiscreteShape.

(** ** C: CONVERSION — the coslice is reached only by transport *)

Section Coslice.

Context {C : Category}.
Context (c : C).

(* control: the transported projection exists and creates every limit *)
Check (@coslice_comma_proj C c).
Check (@coslice_comma_proj_CreatesAllLimits C c).

(* N3 CONVERSION: its object action does not reduce to the first projection *)
Fail Example p438_coslice_fobj (x : c ̸co C) :
  fobj[coslice_comma_proj c] x = `1 x := eq_refl.

(* N4 CONVERSION: and the coslice is not the comma category on the nose *)
Fail Example p438_coslice_cat : (c ̸co C) = (=(c) ↓ Id[C]) := eq_refl.

(* controls: the PLAIN projection's two data fields DO reduce, which is why
   strict creation is available for it where it is not for the transported
   one — the n3 refusal above is about [coslice_comma_proj], not about
   coslice projections in general *)
Example p438_plain_fobj (x : c ̸co C) :
  fobj[Coslice_Proj c] x = `1 x := eq_refl.

Example p438_plain_fmap {x y : c ̸co C} (f : x ~{c ̸co C}~> y) :
  fmap[Coslice_Proj c] f = `1 f := eq_refl.

(* N6 CONVERSION: the plain and the transported projections are DIFFERENT
   functors, so what is proved of one does not transfer to the other by
   conversion *)
Fail Example p438_projs_agree :
  Coslice_Proj c = coslice_comma_proj c := eq_refl.

End Coslice.

(** ** C': the plain coslice projection's strict lift *)

Section PlainCoslice.

Context {C : Category}.
Context (c : C).
Context {J : Category}.
Context (K : J ⟶ (c ̸co C)).

(* the lift lies over the GIVEN cone, apex and legs, with no hypothesis *)

Example p438_coslice_apex (N : Cone (Coslice_Proj c ◯ K)) (HN : IsLimitCone N) :
  fobj[Coslice_Proj c]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := Coslice_Proj_StrictlyCreatesLimit c K)
          N HN)])
    = vertex_obj[N] := eq_refl.

Example p438_coslice_legs (N : Cone (Coslice_Proj c ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  fmap[Coslice_Proj c]
    (cone_leg (slift_cone
       (screates (StrictlyCreatesLimit := Coslice_Proj_StrictlyCreatesLimit c K)
          N HN)) j)
    = cone_leg N j := eq_refl.

(* the lifted object's structure map is the mediator, on the nose *)
Example p438_coslice_structure (N : Cone (Coslice_Proj c ◯ K))
  (HN : IsLimitCone N) :
  `2 (coslice_lift_obj c K N HN) = coslice_med c K N HN := eq_refl.

End PlainCoslice.

(** ** D: CONVERSION — the shipped lift against the strict one *)

Section ShippedLift.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HU : @PreservesImageLimit C D U).
Context (L : Limit (Gdiag K)).

Definition p438_HK : PreservesLimitCone (Gdiag K) U :=
  fun N HN => HU J (Gdiag K) (@Build_Limit J C (Gdiag K) N HN).

(* control: the NEW strict lift lies over the given cone on the nose *)
Example p438_new_lift (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  fobj[comma_proj2]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := comma_StrictlyCreatesLimit K p438_HK)
          N HN)])
    = vertex_obj[N] := eq_refl.

(* N5 CONVERSION: the shipped [creates_lift] discards its cone argument and
   returns the lift of the fixed [L] instead *)
Fail Example p438_old_lift (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  fobj[comma_proj2]
    (vertex_obj[creates_lift (CreatesLimit := comma_CreatesLimit HU K L) N HN])
    = vertex_obj[N] := eq_refl.

(* control: what the shipped one DOES say, at its own [L] *)
Example p438_shipped_strict :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L] := eq_refl.

End ShippedLift.

(** ** E: readbacks *)

Section Readbacks.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (L : Limit (Gdiag K)).

Example p438_at_apex :
  comma_proj2 (vertex_obj[comma_limit_at K HK L]) = vertex_obj[L] := eq_refl.

Example p438_at_legs (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit_at K HK L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

Example p438_slift_eq (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  slift_eq (comma_strict_lift K HK N HN) = eq_refl := eq_refl.

(* the issue's name IS the constant it aliases, not merely its type *)
Example p438_alias_limits :
  comma_proj_creates_limits K HK = comma_StrictlyCreatesLimit K HK := eq_refl.

End Readbacks.

Example p438_alias_equalizers {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) :
  comma_creates_equalizers K HK E = comma_equalizer_at K HK E := eq_refl.

Example p438_alias_products {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HP : IsIndexedProduct (comma_prod_fam F) p proj)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  comma_creates_products F p proj HP HU = comma_IsIndexedProduct F p proj HP HU
  := eq_refl.

Example p438_prod_apex {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  comma_proj2 (comma_prod_apex F p proj HU) = p := eq_refl.

Example p438_prod_leg {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) (a : A) :
  fmap[comma_proj2] (comma_prod_proj F p proj HU a) = proj a := eq_refl.

Example p438_equalizer_apex {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_equalizer_at K HK E]) = vertex_obj[E] := eq_refl.

(** ** F: a concrete witness — every coslice of [Sets] is complete *)

(* [Complete C] is the only hypothesis the coslice results consume that is
   not discharged in tree with no premise at all, and [Sets_Complete]
   discharges it.  The witness lives here rather than in
   Construction/Slice/Creation.v so that a Construction/ file does not
   import Instance/Sets. *)

Example p438_sets_coslice_complete (X : Sets) : @Complete (X ̸co Sets) :=
  Coslice_Complete X Sets_Complete.

(** ** G: guard block *)

Check @comma_at_image.
Check @comma_at_phi.
Check @comma_at_phi_commutes.
Check @comma_at_apex_obj.
Check @comma_at_apex_leg.
Check @comma_at_apex_coherence.
Check @comma_at_apex_cone.
Check @comma_at_med.
Check @comma_at_ump.
Check @comma_limit_at.
Check @comma_limit_at_apex.
Check @comma_limit_at_legs.
Check @comma_reflect_at.
Check @comma_strict_lift.
Check @comma_StrictlyCreatesLimit.
Check @comma_CreatesLimit_at.
Check @comma_prod_fam.
Check @comma_prod_phi.
Check @comma_prod_phi_commutes.
Check @comma_prod_apex.
Check @comma_prod_proj.
Check @comma_IsIndexedProduct.
Check @comma_prod_apex_strict.
Check @comma_prod_leg_strict.
Check @comma_equalizer_at.
Check @comma_equalizer_apex_strict.
Check @comma_equalizer_leg_strict.
Check @comma_StrictlyCreatesEqualizers.
Check @comma_CreatesProducts.
Check @comma_proj_creates_limits.
Check @comma_creates_equalizers.
Check @comma_creates_products.
Check @coslice_structure_coherence.
Check @coslice_structure_cone.
Check @coslice_reflect_at.
Check @coslice_med.
Check @coslice_med_commutes.
Check @coslice_lift_obj.
Check @coslice_lift_leg.
Check @coslice_lift_coherence.
Check @coslice_lift_cone.
Check @coslice_lift_ump.
Check @coslice_limit_at.
Check @coslice_strict_lift.
Check @coslice_lift_apex.
Check @coslice_lift_legs.
Check @Coslice_Proj_StrictlyCreatesLimit.
Check @Coslice_Proj_CreatesLimit.
Check @Coslice_Proj_CreatesAllLimits.
Check @Coslice_Complete_direct.
Check @Coslice_Proj.
Check @Id_PreservesImageLimit.
Check @coslice_comma_StrictlyCreatesLimit.
Check @coslice_comma_CreatesAllLimits.
Check @coslice_comma_Complete.
Check @coslice_comma_Complete_via_adjoint.
Check @Coslice_to_Comma.
Check @Coslice_Comma_Equivalence.
Check @Coslice_to_Comma_CreatesAllLimits.
Check @Coslice_Complete.
Check @coslice_comma_proj.
Check @coslice_comma_proj_CreatesLimit.
Check @coslice_comma_proj_CreatesAllLimits.
Check @comma_CreatesLimit.
Check @comma_creates_reflect.
Check @comma_strict_apex.
Check @comma_strict_legs.
Check @comma_image_limitcone.
Check @rbase_cone.
Check @rbase_coherence.
Check @PreservesImageLimit_Continuous.
Check @Continuous_PreservesImageLimit.
Check @StrictlyCreatesLimit.
Check @StrictLift.
Check @CreatesLimit.
Check @CreatesAllLimits.
Check @PreservesLimitCone.
Check @PreservesImageLimit.
Check @IsIndexedProduct.
Check @Equalizer.
Check @Comma_Coslice.
Check @Adjunction_Id.
