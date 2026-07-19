Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Localization.

Generalizable All Variables.

(* The section proofs below draw on context variables (the reflective structure,
   the W-inverting functor G, and the two hypotheses on it) that need not occur
   in every stated type, so capture every section variable rather than the
   [Default Proof Using "Type"] subset inherited from Lib.v. *)
Set Default Proof Using "All".

(* nLab: https://ncatlab.org/nlab/show/reflective+subcategory
         https://ncatlab.org/nlab/show/localization
         https://ncatlab.org/nlab/show/orthogonal+subcategory

   The universal property of orthogonal-subcategory localization.

   SCOPE.  This is the ORTHOGONAL-SUBCATEGORY (reflective) form of
   localization.  We work over a class [W : MorphismClass C] whose full
   subcategory [C_W W] of W-local objects (Construction/Localization.v) is
   reflective, with reflector [reflector R : C ⟶ Sub C (C_W W)] (the
   localization functor) and reflection unit η.  The zig-zag calculus of
   fractions — the syntactic construction of C[W⁻¹] out of formal composites of
   W-arrows and their formal inverses — is out of this file's scope (ledger
   entry 15, permitted by Localization.v's wording); we rely instead on the
   reflective hypothesis [R : Reflective (C_W W)].  This is the sanctioned
   reading of localization for this development, not a gap: every statement
   below is proved at full strength, funext-free and axiom-free.

   THEOREM ([localization_universal]).  For a reflective [C_W W] and any functor
   [G : C ⟶ E] that sends every W-map to an isomorphism, provided the reflection
   units are themselves W-maps, G FACTORS through the reflector L uniquely up to
   natural isomorphism: there is a functor [G' : Sub C (C_W W) ⟶ E] (namely the
   restriction [G ◯ Incl]) with a natural isomorphism [G ≈ G' ◯ L] in the
   functor category [C, E] (functor setoid equality is exactly natural iso, via
   [Functor_Setoid_Nat_Iso]), and G' is unique up to natural isomorphism among
   all such factorizations.

   The side hypothesis that the reflection units lie in W is the honest
   condition making [C_W W] the localization AT W (equivalently, that W is
   saturated enough to contain its own reflection units): under it, W-inversion
   of G specializes to inversion of the units, which is the exact content the
   factorization consumes.  Localization.v's [reflector_inverts_W] complements
   this from the other side, showing the reflector always inverts W.

   PROOF SHAPE.
   - [reflection_unit_naturality]: naturality of the reflection unit
     η : Id ⟹ Incl ◯ reflector at an arbitrary base morphism, from the
     adjunction transposes ([to_adj_nat_l]/[to_adj_nat_r]).
   - [reflection_counit_is_iso]: for a full reflective subcategory the counit
     ε is a componentwise isomorphism (the [IsIsomorphism] repackaging of
     Reflective.v's [reflective_counit_iso], reproved transparently so its
     inverse is available to later coherence proofs).
   - [reflection_retract]: reflector ◯ Incl ≈ Id on the subcategory, from the
     counit iso and its naturality ([counit_naturality]).
   - factorization: G ∘ η is a natural iso G ⟹ (G ◯ Incl) ◯ reflector because
     G inverts every unit; uniqueness: any competing G' satisfies
     G' ≈ G'◯(reflector◯Incl) ≈ (G'◯reflector)◯Incl ≈ G◯Incl. *)

Section Universal.

Context {C : Category}.
Context {W : MorphismClass C}.
Context (R : Reflective (C_W W)).
Context {E : Category}.

(* Parse-time abbreviations, matching Localization.v's [Section Inverts], so
   every adjunction-transpose lemma instance stays in the same syntactic form
   as the goal. *)
Local Notation Su   := (Sub C (C_W W)).
Local Notation Iota := (Incl C (C_W W)).
Local Notation Refl := (reflector R).
Local Notation A    := (reflective_adj R).

(* Naturality of the reflection unit η : Id ⟹ Iota ◯ Refl at an arbitrary base
   morphism f : c ~> c'.  The library's [unit_comp] records this only for
   morphisms of the shape c ~> U y; the general square below is derived from the
   forward transpose's two naturalities. *)
Lemma reflection_unit_naturality {c c' : C} (f : c ~> c') :
  fmap[Iota] (fmap[Refl] f)
    ∘ @Category.Theory.Adjunction.unit Su C Refl Iota A c
    ≈ @Category.Theory.Adjunction.unit Su C Refl Iota A c' ∘ f.
Proof.
  unfold Category.Theory.Adjunction.unit.
  rewrite <- (@to_adj_nat_l Su C Refl Iota A).
  rewrite id_left.
  rewrite <- (@to_adj_nat_r Su C Refl Iota A).
  now rewrite id_right.
Qed.

(* For a full reflective subcategory the counit ε_x : Refl (Iota x) ~> x is an
   isomorphism in the subcategory.  Its inverse is the reflection unit at
   [Iota x], read into [Su] by fullness; both inverse laws are the triangle
   identities (the second after transporting along [counit_naturality]).  This
   is [reflective_counit_iso] repackaged as [IsIsomorphism]; [reflection_retract]
   below names the inverse by destructing this record, which an opaque [Qed]
   proof still permits. *)
Lemma reflection_counit_is_iso (x : Su) :
  IsIsomorphism (@counit Su C Refl Iota A x).
Proof.
  unshelve refine {| two_sided_inverse := _
                   ; is_right_inverse := _
                   ; is_left_inverse := _ |}.
  - exists (@Category.Theory.Adjunction.unit Su C Refl Iota A (Iota x)).
    apply (reflective_full R).
  - apply (@fmap_counit_unit Su C Refl Iota A x).
  - rewrite <- (counit_naturality A).
    apply (@counit_fmap_unit Su C Refl Iota A (Iota x)).
Qed.

(* The reflector restricted to the subcategory is the identity up to natural
   isomorphism: Refl ◯ Iota ≈ Id[Su].  The componentwise isos are the counits,
   and the coherence square is [counit_naturality]. *)
Lemma reflection_retract : Refl ◯ Iota ≈ Id[Su].
Proof.
  exists (fun x => IsIsoToIso _ (reflection_counit_is_iso x)).
  intros x y f.
  destruct (reflection_counit_is_iso y) as [invy Hry Hly].
  change (fmap[Refl ◯ Iota] f) with (fmap[Refl] (fmap[Iota] f)).
  change (fmap[Id[Su]] f) with f.
  cbn [IsIsoToIso to from two_sided_inverse].
  rewrite <- (id_left (fmap[Refl] (fmap[Iota] f))).
  rewrite <- Hly.
  rewrite <- comp_assoc.
  rewrite (counit_naturality A f).
  now rewrite comp_assoc.
Qed.

Context (G : C ⟶ E).

(* G sends every W-map to an isomorphism (the localizing hypothesis). *)
Context (GW : ∀ (a b : C) (w : a ~> b), W a b w → IsIsomorphism (fmap[G] w)).

(* The reflection units are W-maps: the honest saturation condition making
   [C_W W] the localization AT W.  See the header. *)
Context (Hunit : ∀ c : C,
           W c (Iota (Refl c))
             (@Category.Theory.Adjunction.unit Su C Refl Iota A c)).

(* Consequently G inverts every reflection unit — the exact content the
   factorization consumes. *)
Lemma G_inverts_unit (c : C) :
  IsIsomorphism
    (fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c)).
Proof. exact (GW _ _ _ (Hunit c)). Qed.

(* Factorization: the whiskered unit G ∘ η is a natural isomorphism
   G ⟹ (G ◯ Iota) ◯ Refl.  Componentwise it is [fmap[G] η_c], invertible by
   [G_inverts_unit]; the coherence square is [reflection_unit_naturality]
   transported through G. *)
Lemma localization_factors : G ≈ (G ◯ Iota) ◯ Refl.
Proof.
  exists (fun c => IsIsoToIso _ (G_inverts_unit c)).
  intros c c' f.
  destruct (G_inverts_unit c') as [ug Hrg Hlg].
  change (fmap[(G ◯ Iota) ◯ Refl] f)
    with (fmap[G] (fmap[Iota] (fmap[Refl] f))).
  cbn [IsIsoToIso to from two_sided_inverse].
  (* The whiskered unit naturality, transported through G. *)
  assert (KEY : fmap[G] (fmap[Iota] (fmap[Refl] f))
                  ∘ fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c)
                ≈ fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c')
                  ∘ fmap[G] f).
  { rewrite <- !(@fmap_comp _ _ G).
    apply fmap_respects, (reflection_unit_naturality f). }
  rewrite <- comp_assoc.
  rewrite KEY.
  rewrite comp_assoc.
  rewrite Hlg.
  now rewrite id_left.
Qed.

(* The universal property: G factors through the reflector L = Refl, uniquely
   up to natural isomorphism.  The witnessing functor is the restriction
   G' := G ◯ Iota. *)
Theorem localization_universal :
  { G' : Su ⟶ E
  & (G ≈ G' ◯ Refl) *
    (∀ H : Su ⟶ E, G ≈ H ◯ Refl → H ≈ G') }.
Proof.
  exists (G ◯ Iota).
  split.
  - exact localization_factors.
  - intros H HeqG.
    rewrite HeqG.
    rewrite <- fun_equiv_comp_assoc.
    rewrite reflection_retract.
    now rewrite fun_equiv_id_right.
Qed.

End Universal.
