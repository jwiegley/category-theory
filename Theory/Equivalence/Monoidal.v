Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/transport+of+structure

   Transport of monoidal structure along an equivalence of categories.
   Given an equivalence F : C ⟶ D with quasi-inverse G and a monoidal
   structure (I, ⨂, λ, ρ, α) on C, the category D acquires a monoidal
   structure with unit F I and tensor

       (d, d') ↦ F (G d ⨂ G d'),

   whose unitors and associator are assembled from the unit and counit
   isomorphisms of the equivalence together with the images under F of
   the unitors and associator of C.

   Two design points:

   1. STAGING.  The construction is delivered in two layers.  The record
      [MonoidalTransportData] packages the data of a monoidal structure
      *without* the triangle and pentagon coherence laws: unit, tensor,
      unitors, associator, and the six naturality squares.  The assembler
      [Monoidal_from_transport_data] upgrades such data to a genuine
      [Monoidal] once the two coherence laws are supplied.  The transported
      structure is first built as [Transported_Monoidal_Data]; the laws
      [Transported_triangle_identity] and [Transported_pentagon_identity]
      are the final lemmas of the file, and [Transported_Monoidal] puts the
      pieces together.

   2. THE RECTIFIED COUNIT.  An arbitrary quasi-inverse (G, unit, counit)
      need not satisfy the zig-zag identities, and the triangle law of the
      transported structure genuinely needs the zig-zag

          fmap[G] counit'_d ∘ unit_{G d} ≈ id.

      We therefore first correct the counit by the classical adjustment
          counit'_d := counit_d ∘ fmap[F] (defect_d)⁻¹,
          defect_d  := fmap[G] counit_d ∘ unit_{G d},
      which keeps G and the unit and makes the displayed zig-zag hold
      ([quasi_inverse_transport_counit]).  Consequently
      [fmap[G]] of the corrected counit *is* the inverse of the unit
      component, so every coherence computation happens purely in terms of
      the unit isomorphism and the structure of C.  The pentagon needs no
      zig-zag at all: the transported associator mentions only the unit.

   Everything here is a Definition, never an Instance (the [Monoidal_op]
   convention of Construction/Opposite/Monoidal.v): a transported monoidal
   structure is a choice, made explicitly at use sites.  Nothing in this
   file is registered for typeclass resolution. *)

#[local] Obligation Tactic := intros.

(* Functorial images of isomorphisms are taken with the library's
   [fobj_iso] (Theory/Functor.v, the [Proper] instance for [fobj]): its
   [to] and [from] components are the literal [fmap] terms behind a
   transparent obligation, so the [*_unfold] equations below remain
   Leibniz (=) after unfolding. *)

(* Rewriting toolkit for iso and [bimap] chains along left-nested
   composition spines, used by every coherence proof of the transported
   structure: composites are first normalized to the left-nested form
   (via [rewrite !comp_assoc]) and then advanced by spine lemmas, each
   keyed to match exactly one intended redex.  The toolkit is
   transport-agnostic infrastructure, so it is scoped inside a module:
   [Require Import]ing this file does not spill its generically named
   lemmas into the top-level namespace.  The transport development
   [Import]s it right below the module; downstream users opt in with
   [Import Category.Theory.Equivalence.Monoidal.MonoidalTransportSpine]. *)

Module MonoidalTransportSpine.

(* Folding a pair of [fmap]s across a left-nested composition spine. *)
Lemma fmap_fold_spine {A B : Category} (H : A ⟶ B) {t : B} {x y z : A}
  (X : H z ~> t) (f : y ~> z) (g : x ~> y) :
  (X ∘ fmap[H] f) ∘ fmap[H] g ≈ X ∘ fmap[H] (f ∘ g).
Proof.
  rewrite <- comp_assoc.
  now rewrite <- fmap_comp.
Qed.

Section IsoSpine.

Context {A : Category}.

(* From a commuting square against the [to] components of two
   isomorphisms, derive the corresponding square against the [from]
   components.  This turns each to-naturality lemma below into its
   from-naturality companion. *)
Lemma iso_from_natural {x y x' y' : A}
  (i : x ≅ y) (j : x' ≅ y') (f : x ~> x') (g : y ~> y')
  (H : g ∘ to i ≈ to j ∘ f) :
  f ∘ from i ≈ from j ∘ g.
Proof.
  rewrite <- (id_left (f ∘ from i)).
  rewrite <- (iso_from_to j).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to j)).
  rewrite <- H.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* Cancelling a [to]/[from] pair at the tail of a left-nested spine. *)
Lemma iso_cancel_spine_tf {t x y : A} (X : x ~> t) (i : y ≅ x) :
  (X ∘ to i) ∘ from i ≈ X.
Proof.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

Lemma iso_cancel_spine_ft {t x y : A} (X : x ~> t) (i : x ≅ y) :
  (X ∘ from i) ∘ to i ≈ X.
Proof.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  apply id_right.
Qed.

End IsoSpine.

(* The [bimap]-chain spine lemmas. *)
Section BimapSpine.

Context {J K L : Category}.
Context {T : J ∏ K ⟶ L}.

Lemma bimap_split_first {x y z : J} {v w : K}
  (g : x ~> y) (k : y ~> z) (h : v ~> w) :
  bimap[T] (k ∘ g) h ≈ bimap[T] k id ∘ bimap[T] g h.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_left.
Qed.

Lemma bimap_split_first' {x y z : J} {v w : K}
  (g : x ~> y) (k : y ~> z) (h : v ~> w) :
  bimap[T] (k ∘ g) h ≈ bimap[T] k h ∘ bimap[T] g id.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_right.
Qed.

Lemma bimap_split_second {x y : J} {v w u : K}
  (g : x ~> y) (h : v ~> w) (k : w ~> u) :
  bimap[T] g (k ∘ h) ≈ bimap[T] id k ∘ bimap[T] g h.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_left.
Qed.

Lemma bimap_fold_spine {t : L} {x y z : J} {v w u : K}
  (X : T (y, w) ~> t) (f : x ~> y) (g : v ~> w) (h : z ~> x) (i : u ~> v) :
  (X ∘ bimap[T] f g) ∘ bimap[T] h i ≈ X ∘ bimap[T] (f ∘ h) (g ∘ i).
Proof.
  rewrite <- comp_assoc.
  now rewrite <- bimap_comp.
Qed.

Lemma bimap_swap_spine {t : L} {x y : J} {v w : K}
  (X : T (y, w) ~> t) (f : x ~> y) (g : v ~> w) :
  (X ∘ bimap[T] f (id[w])) ∘ bimap[T] (id[x]) g
    ≈ (X ∘ bimap[T] (id[y]) g) ∘ bimap[T] f (id[v]).
Proof.
  rewrite !bimap_fold_spine.
  rewrite !id_left.
  now rewrite !id_right.
Qed.

(* Cancelling an inverse pair of second components along the spine. *)
Lemma bimap_id_cancel_ft_spine {t : L} {x : J} {v w : K}
  (X : T (x, v) ~> t) (i : v ≅ w) :
  (X ∘ bimap[T] (id[x]) (from i)) ∘ bimap[T] (id[x]) (to i) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  apply id_right.
Qed.

(* Cancelling an inverse pair of first components along the spine. *)
Lemma bimap_cancel_ft_spine_l {t : L} {x y : J} {v : K}
  (X : T (x, v) ~> t) (i : x ≅ y) :
  (X ∘ bimap[T] (from i) (id[v])) ∘ bimap[T] (to i) (id[v]) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  apply id_right.
Qed.

End BimapSpine.

(* The nested variant of [bimap_id_cancel_ft_spine]: the cancelling pair
   sits in the first slot of the second component, one bifunctor down. *)
Lemma bimap_bimap_id_cancel_ft_spine
  {J K1 K2 K L : Category} {T : J ∏ K ⟶ L} {S : K1 ∏ K2 ⟶ K}
  {t : L} {a : J} {x' y' : K1} {v : K2}
  (X : T (a, S (x', v)) ~> t) (i : x' ≅ y') :
  (X ∘ bimap[T] (id[a]) (bimap[S] (from i) (id[v])))
    ∘ bimap[T] (id[a]) (bimap[S] (to i) (id[v])) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite <- bimap_comp.
  rewrite iso_from_to.
  rewrite !id_left.
  rewrite !bimap_id_id.
  apply id_right.
Qed.

(* Spine forms of the naturality of the associator and of the pentagon
   law of a monoidal category. *)
Section MonoidalSpine.

Context {C : Category}.
Context (M : @Monoidal C).

Lemma alpha_natural_spine {t x y z w v u : C}
  (X : (y ⨂ (w ⨂ u)) ~> t) (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  (X ∘ bimap g (bimap h i)) ∘ tensor_assoc
    ≈ (X ∘ tensor_assoc) ∘ bimap (bimap g h) i.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply to_tensor_assoc_natural.
Qed.

Lemma alpha_natural_spine_r {t x y z w v u : C}
  (X : (y ⨂ (w ⨂ u)) ~> t) (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  (X ∘ tensor_assoc) ∘ bimap (bimap g h) i
    ≈ (X ∘ bimap g (bimap h i)) ∘ tensor_assoc.
Proof.
  symmetry.
  apply alpha_natural_spine.
Qed.

Lemma alpha_move_third_spine {t x y v u : C}
  (X : (x ⨂ (y ⨂ u)) ~> t) (i : v ~> u) :
  (X ∘ tensor_assoc) ∘ bimap (id[x ⨂ y]) i
    ≈ (X ∘ bimap (id[x]) (bimap (id[y]) i)) ∘ tensor_assoc.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- (@bimap_id_id _ _ _ (@tensor C M) x y).
  symmetry.
  apply to_tensor_assoc_natural.
Qed.

Lemma alpha_move_left_spine {t x y z w : C}
  (X : (y ⨂ (z ⨂ w)) ~> t) (g : x ~> y) :
  (X ∘ bimap g (id[z ⨂ w])) ∘ tensor_assoc
    ≈ (X ∘ tensor_assoc) ∘ bimap (bimap g (id[z])) (id[w]).
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- (@bimap_id_id _ _ _ (@tensor C M) z w).
  apply to_tensor_assoc_natural.
Qed.

Lemma pentagon_spine {t x y z w : C}
  (X : (x ⨂ (y ⨂ (z ⨂ w))) ~> t) :
  ((X ∘ bimap (id[x]) tensor_assoc) ∘ tensor_assoc)
      ∘ bimap tensor_assoc (id[w])
    ≈ (X ∘ tensor_assoc) ∘ tensor_assoc.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply pentagon_identity.
Qed.

End MonoidalSpine.

End MonoidalTransportSpine.

Import MonoidalTransportSpine.

(* ------------------------------------------------------------------ *)
(* The staging record: monoidal data without the coherence laws.       *)

Section TransportData.

Context (X : Category).

(* The data of a monoidal structure on X — unit, tensor, unitors,
   associator, and the six naturality squares — with the triangle and
   pentagon laws deliberately left out.  This is the staging vehicle for
   transported structures: the data and naturality land first, the two
   coherence proofs are supplied separately to
   [Monoidal_from_transport_data]. *)
Record MonoidalTransportData : Type := {
  transport_unit : X;
  transport_tensor : X ∏ X ⟶ X;

  transport_unit_left {x} :
    transport_tensor (transport_unit, x) ≅ x;
  transport_unit_right {x} :
    transport_tensor (x, transport_unit) ≅ x;
  transport_tensor_assoc {x y z} :
    transport_tensor (transport_tensor (x, y), z)
      ≅ transport_tensor (x, transport_tensor (y, z));

  transport_to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ transport_unit_left
      << transport_tensor (transport_unit, x) ~~> y >>
    transport_unit_left ∘ bimap[transport_tensor] id g;
  transport_from_unit_left_natural {x y} (g : x ~> y) :
    bimap[transport_tensor] id g ∘ transport_unit_left⁻¹
      << x ~~> transport_tensor (transport_unit, y) >>
    transport_unit_left⁻¹ ∘ g;

  transport_to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ transport_unit_right
      << transport_tensor (x, transport_unit) ~~> y >>
    transport_unit_right ∘ bimap[transport_tensor] g id;
  transport_from_unit_right_natural {x y} (g : x ~> y) :
    bimap[transport_tensor] g id ∘ transport_unit_right⁻¹
      << x ~~> transport_tensor (y, transport_unit) >>
    transport_unit_right⁻¹ ∘ g;

  transport_to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap[transport_tensor] g (bimap[transport_tensor] h i)
      ∘ transport_tensor_assoc
      << transport_tensor (transport_tensor (x, z), v)
           ~~> transport_tensor (y, transport_tensor (w, u)) >>
    transport_tensor_assoc
      ∘ bimap[transport_tensor] (bimap[transport_tensor] g h) i;
  transport_from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap[transport_tensor] (bimap[transport_tensor] g h) i
      ∘ transport_tensor_assoc⁻¹
      << transport_tensor (x, transport_tensor (z, v))
           ~~> transport_tensor (transport_tensor (y, w), u) >>
    transport_tensor_assoc⁻¹
      ∘ bimap[transport_tensor] g (bimap[transport_tensor] h i)
}.

(* The triangle coherence law over a [MonoidalTransportData]. *)
Definition transport_triangle (T : MonoidalTransportData) : Type :=
  ∀ x y,
    bimap[transport_tensor T] (to (transport_unit_right T)) id
      << transport_tensor T (transport_tensor T (x, transport_unit T), y)
           ~~> transport_tensor T (x, y) >>
    bimap[transport_tensor T] id (to (transport_unit_left T))
      ∘ to (transport_tensor_assoc T).

(* The pentagon coherence law over a [MonoidalTransportData]. *)
Definition transport_pentagon (T : MonoidalTransportData) : Type :=
  ∀ x y z w,
    bimap[transport_tensor T] id (to (transport_tensor_assoc T))
      ∘ to (transport_tensor_assoc T)
      ∘ bimap[transport_tensor T] (to (transport_tensor_assoc T)) id
      << transport_tensor T
           (transport_tensor T (transport_tensor T (x, y), z), w)
           ~~> transport_tensor T
                 (x, transport_tensor T (y, transport_tensor T (z, w))) >>
    to (transport_tensor_assoc T) ∘ to (transport_tensor_assoc T).

(* Assemble a genuine monoidal structure from staged transport data plus
   the two coherence proofs. *)
Definition Monoidal_from_transport_data
  (T : MonoidalTransportData)
  (tri : transport_triangle T)
  (pent : transport_pentagon T) : @Monoidal X :=
  @Build_Monoidal X
    (transport_unit T)
    (transport_tensor T)
    (@transport_unit_left T)
    (@transport_unit_right T)
    (@transport_tensor_assoc T)
    (@transport_to_unit_left_natural T)
    (@transport_from_unit_left_natural T)
    (@transport_to_unit_right_natural T)
    (@transport_from_unit_right_natural T)
    (@transport_to_tensor_assoc_natural T)
    (@transport_from_tensor_assoc_natural T)
    (fun x y => tri x y)
    (fun x y z w => pent x y z w).

End TransportData.

Arguments transport_unit {X} _.
Arguments transport_tensor {X} _.
Arguments transport_unit_left {X} _ {x}.
Arguments transport_unit_right {X} _ {x}.
Arguments transport_tensor_assoc {X} _ {x y z}.
Arguments transport_to_unit_left_natural {X} _ {x y} g.
Arguments transport_from_unit_left_natural {X} _ {x y} g.
Arguments transport_to_unit_right_natural {X} _ {x y} g.
Arguments transport_from_unit_right_natural {X} _ {x y} g.
Arguments transport_to_tensor_assoc_natural {X} _ {x y z w v u} g h i.
Arguments transport_from_tensor_assoc_natural {X} _ {x y z w v u} g h i.
Arguments transport_triangle {X} T.
Arguments transport_pentagon {X} T.
Arguments Monoidal_from_transport_data {X} T tri pent.

(* ------------------------------------------------------------------ *)
(* The transported structure.                                          *)

Section TransportedMonoidal.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).
Context (M : @Monoidal C).

Local Notation G := (@quasi_inverse C D F E).
Local Notation eta := (@equivalence_unit_at C D F E).
Local Notation eps := (@equivalence_counit_at C D F E).

(* Naturality of the unit and counit components — and the conjugation
   form describing how G ◯ F acts on morphisms — is provided by
   [equivalence_unit_to_natural]/[equivalence_unit_from_natural],
   [equivalence_counit_to_natural]/[equivalence_counit_from_natural] and
   [equivalence_unit_conjugate] of Theory/Equivalence.v, stated there
   beside the accessors [equivalence_unit_at]/[equivalence_counit_at]. *)

(* The defect of the chosen unit/counit pair: the composite
   G d ~> G F G d ~> G d measuring how far the pair is from satisfying
   the zig-zag identity at G.  For an adjoint equivalence it would be the
   identity; in general it is merely a natural automorphism of G d. *)
Definition transport_defect (d : D) : G d ≅ G d :=
  fobj_iso G _ _ (eps d) ⊙ eta (G d).

(* The [*_unfold] equations here and below spell out the components of the
   isomorphisms just defined.  Each is Leibniz (=), not ≈, because the two
   sides are the very same term after unfolding the definition — the
   [bimap_fmap] convention of Functor/Bifunctor.v — which lets them be
   used as rewrite rules with no setoid side conditions. *)
Lemma transport_defect_to_unfold (d : D) :
  to (transport_defect d) = fmap[G] (to (eps d)) ∘ to (eta (G d)).
Proof. reflexivity. Qed.

Lemma transport_defect_from_unfold (d : D) :
  from (transport_defect d) = from (eta (G d)) ∘ fmap[G] (from (eps d)).
Proof. reflexivity. Qed.

Lemma transport_defect_to_natural {x y : D} (g : x ~> y) :
  to (transport_defect y) ∘ fmap[G] g ≈ fmap[G] g ∘ to (transport_defect x).
Proof.
  rewrite !transport_defect_to_unfold.
  rewrite <- comp_assoc.
  rewrite equivalence_unit_to_natural.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite equivalence_counit_to_natural.
  rewrite fmap_comp.
  now rewrite <- !comp_assoc.
Qed.

Lemma transport_defect_from_natural {x y : D} (g : x ~> y) :
  from (transport_defect y) ∘ fmap[G] g
    ≈ fmap[G] g ∘ from (transport_defect x).
Proof.
  symmetry.
  apply iso_from_natural.
  symmetry.
  apply transport_defect_to_natural.
Qed.

(* The rectified counit: correcting the chosen counit by the inverse of
   the defect yields a counit for the same quasi-inverse and unit that
   satisfies the zig-zag identity at G (proved below).  This is the
   classical improvement step in showing that every equivalence refines
   to an adjoint equivalence, done here only on the counit side. *)
Definition transport_counit (d : D) : F (G d) ≅ d :=
  eps d ⊙ fobj_iso F _ _ (iso_sym (transport_defect d)).

Lemma transport_counit_to_unfold (d : D) :
  to (transport_counit d)
    = to (eps d) ∘ fmap[F] (from (transport_defect d)).
Proof. reflexivity. Qed.

Lemma transport_counit_from_unfold (d : D) :
  from (transport_counit d)
    = fmap[F] (to (transport_defect d)) ∘ from (eps d).
Proof. reflexivity. Qed.

Lemma transport_counit_to_natural {x y : D} (g : x ~> y) :
  to (transport_counit y) ∘ fmap[F] (fmap[G] g)
    ≈ g ∘ to (transport_counit x).
Proof.
  rewrite !transport_counit_to_unfold.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite transport_defect_from_natural.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite equivalence_counit_to_natural.
  now rewrite <- !comp_assoc.
Qed.

Lemma transport_counit_from_natural {x y : D} (g : x ~> y) :
  fmap[F] (fmap[G] g) ∘ from (transport_counit x)
    ≈ from (transport_counit y) ∘ g.
Proof.
  apply iso_from_natural.
  symmetry.
  apply transport_counit_to_natural.
Qed.

(* The zig-zag identity at G, in its most usable form: G takes the
   rectified counit to the inverse of the unit component. *)
Lemma quasi_inverse_transport_counit (d : D) :
  fmap[G] (to (transport_counit d)) ≈ from (eta (G d)).
Proof.
  rewrite transport_counit_to_unfold.
  rewrite fmap_comp.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite <- transport_defect_to_unfold.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma quasi_inverse_transport_counit_from (d : D) :
  fmap[G] (from (transport_counit d)) ≈ to (eta (G d)).
Proof.
  rewrite transport_counit_from_unfold.
  rewrite fmap_comp.
  rewrite equivalence_unit_conjugate.
  rewrite <- !comp_assoc.
  rewrite <- transport_defect_from_unfold.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* The transported tensor: (d, d') ↦ F (G d ⨂ G d'). *)
Program Definition Transported_Tensor : D ∏ D ⟶ D := {|
  fobj := fun p => F ((G (fst p) ⨂[M] G (snd p))%object);
  fmap := fun x y f => fmap[F] (fmap[G] (fst f) ⨂[M] fmap[G] (snd f))
|}.
Next Obligation.
  intros f g e; destruct e as [e1 e2]; simpl.
  now rewrite e1, e2.
Qed.
Next Obligation.
  simpl.
  rewrite !fmap_id.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.
Next Obligation.
  simpl.
  rewrite !fmap_comp.
  rewrite bimap_comp.
  apply fmap_comp.
Qed.

(* The action of the transported tensor on a pair of morphisms, written
   out.  [bimap[Transported_Tensor] f g] reduces to exactly this term; the
   D-side lemmas below are stated directly in this form so that every
   object index in a proof goal is in the same (reduced) representation.
   The [Build_MonoidalTransportData] at the end of the file converts them
   back to the [bimap] phrasing of the record fields definitionally. *)
Local Notation Tbimap f g := (fmap[F] (fmap[G] f ⨂[M] fmap[G] g)).

(* The transported left unitor:
   F I ⊗' d = F (G (F I) ⨂ G d) ≅ F (I ⨂ G d) ≅ F (G d) ≅ d. *)
Program Definition Transported_unit_left (x : D) :
  F ((G (F (@I C M)) ⨂[M] G x)%object) ≅ x := {|
  to := to (transport_counit x)
          ∘ fmap[F] (to (@unit_left C M (G x))
                       ∘ (from (eta (@I C M)) ⨂[M] id[G x]));
  from := fmap[F] ((to (eta (@I C M)) ⨂[M] id[G x])
                     ∘ from (@unit_left C M (G x)))
            ∘ from (transport_counit x)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite fmap_fold_spine.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_to_from.
  rewrite fmap_id.
  rewrite id_right.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

(* The transported right unitor. *)
Program Definition Transported_unit_right (x : D) :
  F ((G x ⨂[M] G (F (@I C M)))%object) ≅ x := {|
  to := to (transport_counit x)
          ∘ fmap[F] (to (@unit_right C M (G x))
                       ∘ (id[G x] ⨂[M] from (eta (@I C M))));
  from := fmap[F] ((id[G x] ⨂[M] to (eta (@I C M)))
                     ∘ from (@unit_right C M (G x)))
            ∘ from (transport_counit x)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite fmap_fold_spine.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_to_from.
  rewrite fmap_id.
  rewrite id_right.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

Lemma transported_unit_left_to_unfold (x : D) :
  to (Transported_unit_left x)
    = to (transport_counit x)
        ∘ fmap[F] (to (@unit_left C M (G x))
                     ∘ bimap (from (eta (@I C M))) (id[G x])).
Proof. reflexivity. Qed.

Lemma transported_unit_right_to_unfold (x : D) :
  to (Transported_unit_right x)
    = to (transport_counit x)
        ∘ fmap[F] (to (@unit_right C M (G x))
                     ∘ bimap (id[G x]) (from (eta (@I C M)))).
Proof. reflexivity. Qed.

(* The transported associator, assembled purely from the unit
   isomorphism and the associator of C. *)
Program Definition Transported_tensor_assoc (x y z : D) :
  F ((G (F ((G x ⨂[M] G y)%object)) ⨂[M] G z)%object)
    ≅ F ((G x ⨂[M] G (F ((G y ⨂[M] G z)%object)))%object) := {|
  to := fmap[F] ((id[G x] ⨂[M] to (eta ((G y ⨂[M] G z)%object)))
                   ∘ to (@tensor_assoc C M (G x) (G y) (G z))
                   ∘ (from (eta ((G x ⨂[M] G y)%object)) ⨂[M] id[G z]));
  from := fmap[F] ((to (eta ((G x ⨂[M] G y)%object)) ⨂[M] id[G z])
                     ∘ from (@tensor_assoc C M (G x) (G y) (G z))
                     ∘ (id[G x] ⨂[M] from (eta ((G y ⨂[M] G z)%object))))
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_cancel_spine_tf.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

Lemma transported_tensor_assoc_to_unfold (x y z : D) :
  to (Transported_tensor_assoc x y z)
    = fmap[F] (bimap (id[G x]) (to (eta ((G y ⨂ G z)%object)))
                 ∘ to (@tensor_assoc C M (G x) (G y) (G z))
                 ∘ bimap (from (eta ((G x ⨂ G y)%object))) (id[G z])).
Proof. reflexivity. Qed.

(* The image under G of the transported unitors: the zig-zag identity
   collapses the counit factor, so the image is the corresponding unitor
   of C conjugated by a single unit component. *)
Lemma G_transported_unit_left (y : D) :
  fmap[G] (to (Transported_unit_left y))
    ≈ to (@unit_left C M (G y)) ∘ bimap (from (eta (@I C M))) (id[G y])
        ∘ from (eta ((G (F (@I C M)) ⨂ G y)%object)).
Proof.
  rewrite transported_unit_left_to_unfold.
  rewrite fmap_comp.
  rewrite quasi_inverse_transport_counit.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Lemma G_transported_unit_right (x : D) :
  fmap[G] (to (Transported_unit_right x))
    ≈ to (@unit_right C M (G x)) ∘ bimap (id[G x]) (from (eta (@I C M)))
        ∘ from (eta ((G x ⨂ G (F (@I C M)))%object)).
Proof.
  rewrite transported_unit_right_to_unfold.
  rewrite fmap_comp.
  rewrite quasi_inverse_transport_counit.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

(* The C-side naturality squares of the transported unitors. *)

Lemma transported_unit_left_square {x y : D} (g : x ~> y) :
  (to (@unit_left C M (G y)) ∘ bimap (from (eta (@I C M))) (id[G y]))
      ∘ bimap (id[G (F (@I C M))]) (fmap[G] g)
    ≈ fmap[G] g
        ∘ (to (@unit_left C M (G x)) ∘ bimap (from (eta (@I C M))) (id[G x])).
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_id_right_left.
  rewrite <- bimap_id_left_right.
  rewrite comp_assoc.
  rewrite <- to_unit_left_natural.
  now rewrite <- comp_assoc.
Qed.

Lemma transported_unit_right_square {x y : D} (g : x ~> y) :
  (to (@unit_right C M (G y)) ∘ bimap (id[G y]) (from (eta (@I C M))))
      ∘ bimap (fmap[G] g) (id[G (F (@I C M))])
    ≈ fmap[G] g
        ∘ (to (@unit_right C M (G x))
             ∘ bimap (id[G x]) (from (eta (@I C M)))).
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_id_left_right.
  rewrite <- bimap_id_right_left.
  rewrite comp_assoc.
  rewrite <- to_unit_right_natural.
  now rewrite <- comp_assoc.
Qed.

(* The six naturality fields of the transported structure. *)

Lemma Transported_to_unit_left_natural {x y : D} (g : x ~> y) :
  g ∘ to (Transported_unit_left x)
    ≈ to (Transported_unit_left y) ∘ Tbimap (id[F (@I C M)]) g.
Proof.
  rewrite !transported_unit_left_to_unfold.
  rewrite fmap_id.
  rewrite <- (comp_assoc (to (transport_counit y))).
  rewrite <- fmap_comp.
  rewrite transported_unit_left_square.
  rewrite (fmap_comp (fmap[G] g)).
  rewrite (comp_assoc (to (transport_counit y))).
  rewrite transport_counit_to_natural.
  now rewrite !comp_assoc.
Qed.

Lemma Transported_from_unit_left_natural {x y : D} (g : x ~> y) :
  Tbimap (id[F (@I C M)]) g ∘ from (Transported_unit_left x)
    ≈ from (Transported_unit_left y) ∘ g.
Proof.
  apply iso_from_natural.
  apply Transported_to_unit_left_natural.
Qed.

Lemma Transported_to_unit_right_natural {x y : D} (g : x ~> y) :
  g ∘ to (Transported_unit_right x)
    ≈ to (Transported_unit_right y) ∘ Tbimap g (id[F (@I C M)]).
Proof.
  rewrite !transported_unit_right_to_unfold.
  rewrite fmap_id.
  rewrite <- (comp_assoc (to (transport_counit y))).
  rewrite <- fmap_comp.
  rewrite transported_unit_right_square.
  rewrite (fmap_comp (fmap[G] g)).
  rewrite (comp_assoc (to (transport_counit y))).
  rewrite transport_counit_to_natural.
  now rewrite !comp_assoc.
Qed.

Lemma Transported_from_unit_right_natural {x y : D} (g : x ~> y) :
  Tbimap g (id[F (@I C M)]) ∘ from (Transported_unit_right x)
    ≈ from (Transported_unit_right y) ∘ g.
Proof.
  apply iso_from_natural.
  apply Transported_to_unit_right_natural.
Qed.

Lemma Transported_to_tensor_assoc_natural {x y z w v u : D}
  (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  Tbimap g (Tbimap h i) ∘ to (Transported_tensor_assoc x z v)
    ≈ to (Transported_tensor_assoc y w u) ∘ Tbimap (Tbimap g h) i.
Proof.
  rewrite !transported_tensor_assoc_to_unfold.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite id_left.
  rewrite <- equivalence_unit_from_natural.
  rewrite bimap_split_first'.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite <- equivalence_unit_to_natural.
  rewrite bimap_split_second.
  rewrite alpha_natural_spine.
  reflexivity.
Qed.

Lemma Transported_from_tensor_assoc_natural {x y z w v u : D}
  (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  Tbimap (Tbimap g h) i ∘ from (Transported_tensor_assoc x z v)
    ≈ from (Transported_tensor_assoc y w u) ∘ Tbimap g (Tbimap h i).
Proof.
  apply iso_from_natural.
  apply Transported_to_tensor_assoc_natural.
Qed.

(* The staged transport data for the transported structure. *)
Definition Transported_Monoidal_Data : MonoidalTransportData D :=
  @Build_MonoidalTransportData D
    (F (@I C M))
    Transported_Tensor
    Transported_unit_left
    Transported_unit_right
    Transported_tensor_assoc
    (@Transported_to_unit_left_natural)
    (@Transported_from_unit_left_natural)
    (@Transported_to_unit_right_natural)
    (@Transported_from_unit_right_natural)
    (@Transported_to_tensor_assoc_natural)
    (@Transported_from_tensor_assoc_natural).

(* The triangle law of the transported structure.  The zig-zag identity
   collapses the counit factors of the two unitors, after which the law
   reduces to the triangle of C conjugated by unit components. *)
Lemma Transported_triangle_identity (x y : D) :
  Tbimap (to (Transported_unit_right x)) (id[y])
    ≈ Tbimap (id[x]) (to (Transported_unit_left y))
        ∘ to (Transported_tensor_assoc x (F (@I C M)) y).
Proof.
  rewrite transported_tensor_assoc_to_unfold.
  rewrite <- fmap_comp.
  apply fmap_respects.
  rewrite !fmap_id.
  rewrite G_transported_unit_right.
  rewrite G_transported_unit_left.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_cancel_spine_ft.
  rewrite id_left.
  rewrite bimap_split_second.
  rewrite alpha_natural_spine.
  rewrite <- triangle_identity.
  rewrite bimap_fold_spine.
  rewrite id_left.
  rewrite <- bimap_comp.
  rewrite id_left.
  now rewrite !comp_assoc.
Qed.

(* The pentagon law of the transported structure.  No zig-zag is needed:
   the associator mentions only the unit isomorphism, whose components
   cancel pairwise, and the residue is the pentagon of C surrounded by
   naturality moves of the associator. *)
Lemma Transported_pentagon_identity (x y z w : D) :
  Tbimap (id[x]) (to (Transported_tensor_assoc y z w))
      ∘ to (Transported_tensor_assoc x (F ((G y ⨂[M] G z)%object)) w)
      ∘ Tbimap (to (Transported_tensor_assoc x y z)) (id[w])
    ≈ to (Transported_tensor_assoc x y (F ((G z ⨂[M] G w)%object)))
        ∘ to (Transported_tensor_assoc (F ((G x ⨂[M] G y)%object)) z w).
Proof.
  rewrite !transported_tensor_assoc_to_unfold.
  rewrite !fmap_id.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  rewrite !equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite !bimap_split_second.
  rewrite !bimap_split_first.
  rewrite !comp_assoc.
  rewrite bimap_id_cancel_ft_spine.
  rewrite bimap_cancel_ft_spine_l.
  rewrite alpha_natural_spine_r.
  rewrite bimap_bimap_id_cancel_ft_spine.
  rewrite pentagon_spine.
  rewrite bimap_swap_spine.
  rewrite alpha_move_third_spine.
  rewrite alpha_move_left_spine.
  reflexivity.
Qed.

(* The transported monoidal structure, assembled from the staged data and
   the two coherence laws.  A Definition, never an Instance. *)
Definition Transported_Monoidal : @Monoidal D :=
  Monoidal_from_transport_data Transported_Monoidal_Data
    (fun x y => Transported_triangle_identity x y)
    (fun x y z w => Transported_pentagon_identity x y z w).

End TransportedMonoidal.
