Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(** * Equivalences preserve, reflect, and create limits *)

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/preserved+limit
   nLab: https://ncatlab.org/nlab/show/reflected+limit
   nLab: https://ncatlab.org/nlab/show/created+limit

   An equivalence of categories (Theory/Equivalence.v) interacts with
   limits in every way one could ask: it preserves them, reflects them,
   and carries any limit of a composite diagram F ◯ G back to a limit of
   G.  This file proves the three statements, and their colimit duals,
   packaged in the preservation vocabulary of
   Structure/Limit/Preservation.v.

   - Preservation ([equivalence_preserves_limits]) is adjoint continuity:
     refining E : EquivalenceOfCategories F to an adjoint equivalence
     (Theory/Equivalence/Adjoint.v) and swapping its two sides exhibits F
     as a right adjoint — quasi_inverse ⊣ F — so RAPL
     (Adjunction/Continuity.v) applies.  Dually, F is the left adjoint of
     F ⊣ quasi_inverse, so LAPC makes it preserve all colimits as well
     ([equivalence_preserves_colimits]).

   - Reflection ([equivalence_reflects_limits]) needs only that F is full
     and faithful, so it is proved in that generality first
     ([ff_reflects_limit]): when the image of a cone N under F underlies
     a limit of F ◯ G, the cone N itself is a limit of G.  "The image of
     N is a limit" is stated as an apex-pinned witness
     [IsALimit (F ◯ G) (F (vertex_obj[N]))] together with the family
     identifying its legs with the image legs [fmap[F] (cone_leg N x)]
     (an arbitrary witness at the image apex says nothing about the legs
     of N, so the family is part of the hypothesis).  The mediating
     morphism in C is the [prefmap]-preimage of the mediator in D, and
     both of its laws are recovered from faithfulness — apply [fmap_inj],
     push [fmap[F]] through with [fmap_sur], and conclude among the
     images — since [prefmap] itself carries no functoriality (the issue
     #118 note in Theory/Functor.v).  The same technique gives
     [ff_reflects_isos] and [equivalence_reflects_isos], witnesses for
     the conservative-functor class [ReflectsIsos] of
     Structure/Limit/Preservation.v.

   - Creation ([equivalence_creates_limits]) takes any limit of F ◯ G to
     a limit of G itself: the quasi-inverse is a right adjoint
     (F ⊣ quasi_inverse), so RAPL gives a limit of
     quasi_inverse ◯ (F ◯ G), which the unit cell identifies with G —
     the composite natural isomorphism [equivalence_diagram_iso] — and
     naturally isomorphic diagrams have the same limits: the iso-of-cones
     transport [limit_transport], proved here in full generality
     ([isalimit_transport]/[limit_transport], with the cone conjugates
     [cone_transport]/[cone_transport_inv]).  This produces, for every
     limit in D of the composite diagram, an actual limit in C of the
     original diagram; combined with preservation and reflection it is
     the practical content of "equivalences create limits".

   The colimit statements ride the opposite category, never a second
   proof: a cocone is a cone over the opposite diagram, [IsAColimit] is
   [IsALimit] of the opposite diagram, and F^op is an equivalence
   whenever F is ([EquivalenceOfCategories_op], whose two cells are the
   pointwise opposites of the cells of E).  The only friction is that
   (F ◯ G)^op and F^op ◯ G^op are distinct functor records sharing their
   object and morphism maps, so apex-pinned witnesses are repackaged
   field by field ([isalimit_op_comp], following the precedent of
   [preserves_colimit] in Structure/Limit/Preservation.v).

   Following Theory/Equivalence.v, nothing in this file is registered
   for instance resolution: quasi-inverses, preservation witnesses and
   reflection witnesses are choices, always passed explicitly at use
   sites. *)

(** ** Additions to the covariant accessor toolkit *)

(* Coherence of [cone_leg], the first-class leg accessor of
   Structure/Limit/Preservation.v (which provides the analogous
   [limit_leg_coherence] only for apex-pinned limit witnesses). *)

Lemma cone_leg_coherence {J C : Category} {F : J ⟶ C} (N : Cone F)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

(* Rebundling an apex-pinned limit witness as a bundled [Limit]: the
   converse of [limit_is_alimit].  Purely a repackaging; the cone is the
   witness's own leg family over its pinned apex. *)

Definition isalimit_to_limit {J C : Category} {G : J ⟶ C} {c : C}
  (H : IsALimit G c) : Limit G :=
  @Build_Limit J C G
    (@Build_Cone J C G c (@limit_acone _ _ _ _ H))
    (@ump_limit _ _ _ _ H).

(** ** Transport of limits along a natural isomorphism of diagrams *)

(* Naturally isomorphic diagrams have the same cones and the same limits.
   Given e : G ≈ G' (which, for [Functor_Setoid], is a bundled natural
   isomorphism), a cone over G becomes a cone over G' by composing each
   leg with the componentwise isomorphism, and conversely; an apex-pinned
   limit witness follows, with the same apex.  This is the iso-of-cones
   step of limit creation below, but it is stated in full generality
   because nothing about it is specific to equivalences. *)

Section DiagramIso.

Context {J : Category}.
Context {C : Category}.
Context {G G' : J ⟶ C}.
Context (e : G ≈ G').

(* Push a cone over G across e: compose each leg with the forward
   component of the isomorphism family. *)

Definition cone_transport_leg (N : Cone G) (x : J) :
  vertex_obj[N] ~{C}~> G' x :=
  to (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ cone_transport_leg N x ≈ cone_transport_leg N y.
Proof using e.
  unfold cone_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport (N : Cone G) : Cone G' :=
  @Build_Cone J C G' (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G' (cone_transport_leg N)
       (fun x y f => cone_transport_coherence N f)).

(* Pull a cone over G' back across e: compose each leg with the inverse
   component of the isomorphism family. *)

Definition cone_transport_inv_leg (N : Cone G') (x : J) :
  vertex_obj[N] ~{C}~> G x :=
  from (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_inv_coherence (N : Cone G') {x y : J}
  (f : x ~{J}~> y) :
  fmap[G] f ∘ cone_transport_inv_leg N x ≈ cone_transport_inv_leg N y.
Proof using e.
  unfold cone_transport_inv_leg.
  rewrite comp_assoc.
  rewrite (fun_equiv_fmap_from e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport_inv (N : Cone G') : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (cone_transport_inv_leg N)
       (fun x y f => cone_transport_inv_coherence N f)).

(* The legs of the pulled-back cone, in rewriting-friendly form. *)

Lemma cone_transport_inv_leg_eq (N : Cone G') (x : J) :
  cone_leg (cone_transport_inv N) x ≈ from (`1 e x) ∘ cone_leg N x.
Proof. reflexivity. Qed.

(** *** Transporting an apex-pinned limit witness *)

Section TransportWitness.

Context {c : C}.
Context (HL : IsALimit G c).

Definition isalimit_transport_leg (x : J) : c ~{C}~> G' x :=
  to (`1 e x) ∘ limit_leg HL x.

Lemma isalimit_transport_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ isalimit_transport_leg x ≈ isalimit_transport_leg y.
Proof using e HL.
  unfold isalimit_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (limit_leg_coherence HL f).
Qed.

Definition isalimit_transport_acone : ACone c G' :=
  @Build_ACone J C c G' isalimit_transport_leg
    (fun x y f => isalimit_transport_coherence f).

(* Mediate a competing cone over G' by pulling it back across e and
   mediating through the limit of G; the apexes are untouched, so the
   mediator needs no adjustment at all. *)

Definition isalimit_transport_med (N : Cone G') :
  vertex_obj[N] ~{C}~> c :=
  limit_med HL (cone_transport_inv N).

Lemma isalimit_transport_med_commutes (N : Cone G') :
  ∀ x : J, isalimit_transport_leg x ∘ isalimit_transport_med N
             ≈ cone_leg N x.
Proof using e HL.
  intro x.
  unfold isalimit_transport_leg, isalimit_transport_med.
  rewrite <- comp_assoc.
  rewrite (limit_med_commutes HL (cone_transport_inv N) x).
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma isalimit_transport_med_unique (N : Cone G')
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, isalimit_transport_leg x ∘ v ≈ cone_leg N x) →
  isalimit_transport_med N ≈ v.
Proof using e HL.
  intro Hv.
  unfold isalimit_transport_med.
  apply (limit_med_unique HL (cone_transport_inv N) v).
  intro x.
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite <- (Hv x).
  unfold isalimit_transport_leg.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Definition isalimit_transport_ump (N : Cone G') :
  ∃! u : vertex_obj[N] ~{C}~> c,
    ∀ x : J, isalimit_transport_leg x ∘ u ≈ cone_leg N x :=
  Build_Unique _ _ _ (isalimit_transport_med N)
    (isalimit_transport_med_commutes N)
    (isalimit_transport_med_unique N).

Definition isalimit_transport : IsALimit G' c :=
  @Build_IsALimit J C G' c isalimit_transport_acone isalimit_transport_ump.

End TransportWitness.

(* The bundled form: naturally isomorphic diagrams have the same limits,
   with the same apex. *)

Definition limit_transport (L : Limit G) : Limit G' :=
  isalimit_to_limit (isalimit_transport (limit_is_alimit L)).

End DiagramIso.

(** ** The image of a cone under a functor *)

(* Any functor sends cones over G to cones over F ◯ G, by applying
   [fmap[F]] to every leg.  This is the cone whose limiting behaviour the
   reflection statements below hypothesize. *)

Section ImageCone.

Context {J : Category}.
Context {C D : Category}.
Context (F : C ⟶ D).
Context {G : J ⟶ C}.

Definition fmap_cone_leg (N : Cone G) (x : J) :
  F (vertex_obj[N]) ~{D}~> (F ◯ G) x :=
  fmap[F] (cone_leg N x).

Lemma fmap_cone_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ G] f ∘ fmap_cone_leg N x ≈ fmap_cone_leg N y.
Proof using Type.
  unfold fmap_cone_leg; simpl.
  rewrite <- fmap_comp.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition fmap_cone (N : Cone G) : Cone (F ◯ G) :=
  @Build_Cone J D (F ◯ G) (F (vertex_obj[N]))
    (@Build_ACone J D (F (vertex_obj[N])) (F ◯ G) (fmap_cone_leg N)
       (fun x y f => fmap_cone_coherence N f)).

(* The legs of the image cone, in rewriting-friendly form. *)

Lemma fmap_cone_leg_eq (N : Cone G) (x : J) :
  cone_leg (fmap_cone N) x ≈ fmap[F] (cone_leg N x).
Proof. reflexivity. Qed.

End ImageCone.

(** ** Fully faithful functors reflect isomorphisms and limits *)

Section FullyFaithful.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{HF : @Full C D F}.
Context `{HfF : @Faithful C D F}.

(* A full and faithful functor is conservative: the chosen inverse of f
   is the [prefmap]-preimage of the inverse of fmap[F] f, and its two
   inverse laws are recovered from faithfulness. *)

Definition ff_iso_inverse {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) : y ~{C}~> x :=
  prefmap (@two_sided_inverse D _ _ _ I).

Lemma ff_iso_inverse_right {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  f ∘ ff_iso_inverse f I ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_right_inverse D _ _ _ I).
Qed.

Lemma ff_iso_inverse_left {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  ff_iso_inverse f I ∘ f ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_left_inverse D _ _ _ I).
Qed.

Definition ff_reflects_isos : ReflectsIsos F :=
  @Build_ReflectsIsos C D F
    (fun x y f I =>
       @Build_IsIsomorphism C x y f (ff_iso_inverse f I)
         (ff_iso_inverse_right f I)
         (ff_iso_inverse_left f I)).

(** *** Reflection of limits *)

Section ReflectLimit.

Context {J : Category}.
Context {G : J ⟶ C}.
Context (N : Cone G).
Context (HL : IsALimit (F ◯ G) (F (vertex_obj[N]))).
Context (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)).

(* Mediate a competing cone M over G: take the image of M, mediate in D
   through the hypothesized limit, and choose an [fmap]-preimage of the
   mediator with [prefmap]. *)

Definition ff_reflect_med (M : Cone G) :
  vertex_obj[M] ~{C}~> vertex_obj[N] :=
  prefmap (limit_med HL (fmap_cone F M)).

Lemma ff_reflect_med_commutes (M : Cone G) :
  ∀ x : J, cone_leg N x ∘ ff_reflect_med M ≈ cone_leg M x.
Proof using HF HfF HL Hlegs.
  intro x.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  rewrite <- (Hlegs x).
  rewrite (limit_med_commutes HL (fmap_cone F M) x).
  exact (fmap_cone_leg_eq F M x).
Qed.

Lemma ff_reflect_med_unique (M : Cone G)
  (v : vertex_obj[M] ~{C}~> vertex_obj[N]) :
  (∀ x : J, cone_leg N x ∘ v ≈ cone_leg M x) →
  ff_reflect_med M ≈ v.
Proof using HF HfF HL Hlegs.
  intro Hv.
  apply fmap_inj.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  apply (limit_med_unique HL (fmap_cone F M) (fmap[F] v)).
  intro x.
  rewrite (fmap_cone_leg_eq F M x).
  rewrite (Hlegs x).
  rewrite <- (Hv x).
  rewrite fmap_comp.
  reflexivity.
Qed.

Definition ff_reflect_ump (M : Cone G) :
  ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x :=
  Build_Unique _ _ _ (ff_reflect_med M)
    (ff_reflect_med_commutes M)
    (ff_reflect_med_unique M).

(* Full + faithful functors reflect limits: the cone N, with its own leg
   family, is a limit of G. *)

Definition ff_reflects_limit : IsALimit G (vertex_obj[N]) :=
  @Build_IsALimit J C G (vertex_obj[N]) (@coneFrom _ _ _ N) ff_reflect_ump.

End ReflectLimit.

End FullyFaithful.

(** ** Equivalences and limits *)

Section EquivalenceLimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(** *** Preservation *)

(* Swapping the adjoint equivalence refined from E exhibits F as a right
   adjoint (quasi_inverse ⊣ F); RAPL concludes. *)

Definition equivalence_preserves_limits : PreservesAllLimits F :=
  right_adjoint_preserves_limits
    (AdjointEquivalence_swap_adjunction
       (Equivalence_to_AdjointEquivalence E)).

Definition equivalence_preserves_limit {J : Category} (G : J ⟶ C) :
  PreservesLimit G F :=
  equivalence_preserves_limits J G.

(* Dually, F is the left adjoint of F ⊣ quasi_inverse; LAPC concludes. *)

Definition equivalence_preserves_colimits : PreservesAllColimits F :=
  left_adjoint_preserves_colimits (equiv_adjunction E).

Definition equivalence_preserves_colimit {J : Category} (G : J ⟶ C) :
  PreservesColimit G F :=
  equivalence_preserves_colimits J G.

(* Bundled forms of the preserved (co)limits. *)

Definition equivalence_preserved_limit {J : Category} (G : J ⟶ C)
  (L : Limit G) : Limit (F ◯ G) :=
  isalimit_to_limit
    (@preserves_limit J C G D F (equivalence_preserves_limit G) L).

Definition equivalence_preserved_colimit {J : Category} (G : J ⟶ C)
  (L : Colimit G) : Colimit (F ◯ G) :=
  isalimit_to_limit
    (preserves_colimit (equivalence_preserves_colimit G) L).

(** *** Reflection *)

(* Equivalences are full and faithful (Theory/Equivalence/FullFaithful.v),
   so the fully-faithful reflection results specialize. *)

Definition equivalence_reflects_isos : ReflectsIsos F :=
  ff_reflects_isos
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E).

Definition equivalence_reflects_limits {J : Category} {G : J ⟶ C}
  (N : Cone G)
  (HL : IsALimit (F ◯ G) (F (vertex_obj[N])))
  (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)) :
  IsALimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E)
    N HL Hlegs.

(** *** Creation *)

(* The composite natural isomorphism quasi_inverse ◯ (F ◯ G) ≈ G:
   reassociate and cancel the unit cell. *)

Definition equivalence_diagram_iso {J : Category} (G : J ⟶ C) :
  @quasi_inverse C D F E ◯ (F ◯ G) ≈ G.
Proof.
  rewrite (fun_equiv_comp_assoc (@quasi_inverse C D F E) F G).
  rewrite <- (@equivalence_unit C D F E).
  exact (fun_equiv_id_left G).
Defined.

(* Any limit of F ◯ G is carried back to a limit of G: the quasi-inverse
   (a right adjoint) preserves it, and the diagram isomorphism above
   transports the result from quasi_inverse ◯ (F ◯ G) to G. *)

Definition equivalence_creates_limits {J : Category} (G : J ⟶ C)
  (L : Limit (F ◯ G)) : Limit G :=
  limit_transport (equivalence_diagram_iso G)
    (rapl_limit (equiv_adjunction E) (F ◯ G) L).

End EquivalenceLimit.

(** ** The opposite of an equivalence of categories *)

(* F^op is an equivalence whenever F is: the two cells of E dualize
   pointwise, their isomorphism families running through
   [Isomorphism_Opposite] and their conjugation coherences being those of
   E read at the reversed morphism (composition in the opposite category
   unfolds to reversed composition, so only a reassociation separates the
   two statements). *)

Definition equivalence_counit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  F^op ◯ (@quasi_inverse C D F E)^op ≈ Id[D^op].
Proof.
  exists (fun d =>
            Isomorphism_Opposite (`1 (@equivalence_counit C D F E) d)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_counit C D F E) y x f).
Defined.

Definition equivalence_unit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  Id[C^op] ≈ (@quasi_inverse C D F E)^op ◯ F^op.
Proof.
  exists (fun x =>
            Isomorphism_Opposite (`1 (@equivalence_unit C D F E) x)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_unit C D F E) y x f).
Defined.

Definition EquivalenceOfCategories_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  @EquivalenceOfCategories (C^op) (D^op) (F^op) :=
  @Build_EquivalenceOfCategories (C^op) (D^op) (F^op)
    ((@quasi_inverse C D F E)^op)
    (equivalence_counit_op E)
    (equivalence_unit_op E).

(* (F ◯ G)^op and F^op ◯ G^op share their object and morphism maps but
   differ in the proofs of functoriality, so an apex-pinned limit witness
   over the one repackages field by field as a witness over the other
   (the [preserves_colimit] precedent in Structure/Limit/Preservation.v).
   No destructuring: everything is spelled with projections, so the
   result stays convertible with the input on legs and mediators. *)

Definition isalimit_op_comp {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  {c : D} (H : IsALimit ((F ◯ G)^op) c) : IsALimit (F^op ◯ G^op) c :=
  @Build_IsALimit (J^op) (D^op) (F^op ◯ G^op) c
    (@Build_ACone (J^op) (D^op) c (F^op ◯ G^op)
       (fun x => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x)
       (fun x y f =>
          @cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f))
    (fun N =>
       @ump_limit _ _ _ _ H
         (@Build_Cone (J^op) (D^op) ((F ◯ G)^op) (@vertex_obj _ _ _ N)
            (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ G)^op)
               (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
               (fun x y f =>
                  @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).

(** ** Equivalences and colimits, by op *)

Section EquivalenceColimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* Reflection of colimits: a cocone over G is a cone over G^op, an
   [IsAColimit] witness is an [IsALimit] witness over the opposite
   composite, and F^op is full and faithful because it is an equivalence
   ([EquivalenceOfCategories_op]).  The injection families translate
   definitionally. *)

Definition equivalence_reflects_colimits {J : Category} {G : J ⟶ C}
  (N : Cocone G)
  (HL : IsAColimit (F ◯ G) (F (vertex_obj[N])))
  (Hinjs : ∀ x : J, colimit_inj HL x ≈ fmap[F] (cocone_inj N x)) :
  IsAColimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full (EquivalenceOfCategories_op E))
    (HfF := Equivalence_Faithful (EquivalenceOfCategories_op E))
    N (isalimit_op_comp HL)
    (fun x => Hinjs x).

(* Creation of colimits: repackage the given colimit as a limit of
   F^op ◯ G^op and create through the opposite equivalence. *)

Definition equivalence_creates_colimits {J : Category} (G : J ⟶ C)
  (L : Colimit (F ◯ G)) : Colimit G :=
  equivalence_creates_limits (EquivalenceOfCategories_op E) (G^op)
    (isalimit_to_limit (isalimit_op_comp (limit_is_alimit L))).

End EquivalenceColimit.
