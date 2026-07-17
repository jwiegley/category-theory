Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/local+object
         https://ncatlab.org/nlab/show/reflective+subcategory
         https://ncatlab.org/nlab/show/localization

   Orthogonal-subcategory localization.  Fix a category C and a class W of
   morphisms (a [MorphismClass C], from Theory/Morphisms/Classes.v).  An object
   x of C is *W-local* when it "sees every W-map as invertible": for every
   w : a ~> b in W the precomposition map on hom-sets

       (- ∘ w) : Hom(b, x) ⟶ Hom(a, x)

   is an isomorphism of setoids.  This precomposition map is exactly the action
   of the contravariant hom-functor [Hom ─, x] = Curried_CoHom C x on the arrow
   w (read as an arrow b ~{C^op}~> a), so we state W-locality directly as an
   [IsIsomorphism] in [Sets] of [fmap[[Hom ─, x]] w].  See Functor/Hom.v for
   the presheaf [Hom ─, x] and Instance/Sets.v for isomorphisms in [Sets].

   The W-local objects span a *full* subcategory [C_W W] of C (built on
   Construction/Subcategory.v with [shom] retaining every morphism, so the
   fullness witness is trivial).  When this subcategory is reflective
   (Construction/Reflective.v) the reflector *inverts W*: it carries every W-map
   to an isomorphism.  The proof runs entirely through the reflection
   adjunction's hom-set transposes together with W-locality of the reflections
   [Iota (reflector _ a)] and [Iota (reflector _ b)]; it needs neither a
   calculus of fractions nor any classical or extensionality principle.  We also
   record the companion fact on which localizations rest, that the reflection
   unit at a W-local object is an isomorphism ([unit_at_local_iso]) — the dual,
   for the unit, of the counit-iso lemma [reflective_counit_iso]. *)

(* Where localization comes from, and what it is for

   nLab:  https://ncatlab.org/nlab/show/localization
          https://ncatlab.org/nlab/show/reflective+localization
          https://ncatlab.org/nlab/show/orthogonal+subcategory+problem
   Wikipedia:
     https://en.wikipedia.org/wiki/Localization_(commutative_algebra)

   Localization universally inverts a chosen class of morphisms.  Given
   W it is the initial way to pass from C to a category C[W⁻¹] in which
   every W-map becomes an isomorphism, so that any functor carrying W to
   isomorphisms factors, essentially uniquely, through it.  It lets a
   family of maps be turned into isomorphisms — the weak equivalences of
   spaces, the quasi-isomorphisms of chain complexes, a multiplicative
   system in a ring — so that work proceeds in the setting where that
   identification holds, while a universal comparison back to C is kept
   (nLab, "localization"; Gabriel–Zisman, "Calculus of Fractions and
   Homotopy Theory", Springer 1967).

   The vocabulary descends from commutative algebra, where the ring of
   fractions S⁻¹R adjoins formal inverses to a multiplicative set and is
   universal among ring maps sending it to units.  Øystein Ore gave the
   corresponding condition for non-commutative rings, and the categorical
   calculus of fractions is its direct analogue, whence both the names
   "localization" and "fractions" (Wikipedia; nLab, "calculus of
   fractions").

   The general categorical construction is due to Gabriel and Zisman,
   whose 1967 monograph localized a category at an arbitrary class of
   morphisms and built the category of fractions C[W⁻¹] — its morphisms
   finite zig-zags modulo relations, or explicit spans under the
   Ore-style calculus — with the homotopy category, spaces localized at
   the weak homotopy equivalences, as its headline application.  The
   motivating case from homological algebra is Verdier's derived
   category: in his thesis under Grothendieck in the 1960s he built D(A)
   by formally inverting the quasi-isomorphisms of chain complexes and
   introduced triangulated categories and the Verdier quotient, the first
   published account being Hartshorne, "Residues and Duality" (Springer
   Lecture Notes in Mathematics 20, 1966).

   This file takes the reflective, rather than the syntactic, reading,
   whose theory is due to Freyd and Kelly.  Rather than the zig-zag
   category the localization is identified with the full subcategory of
   W-local objects [C_W], and Freyd and Kelly ("Categories of continuous
   functors, I", Journal of Pure and Applied Algebra 2, 1972) studied
   exactly this orthogonal subcategory problem — when such a subcategory
   is reflective — as the mechanism behind reflective localizations.
   Passing to W-local objects sidesteps the size questions and the Ore
   hypotheses the syntactic construction carries, which is why
   [reflector_inverts_W] needs neither.

   The applications span the mathematics the construction was built for.
   The homotopy category of spaces is Top[W⁻¹] at the weak homotopy
   equivalences; the derived category is chain complexes localized at
   quasi-isomorphisms, pervasive in sheaf cohomology and duality; and the
   sheaves on a site are the reflective subcategory of presheaves
   orthogonal to the covering sieves, sheafification being the reflector
   — the prototypical Freyd–Kelly orthogonality example, whose full
   subcategory inclusion Theory/Sheaf/Category.v realizes in-tree, with
   sheafification, the reflector, a named deferral there.  More generally
   every reflective subcategory is a reflective localization at the class
   its reflector inverts, so abelianizations, completions and idempotent
   reflections are all instances, the homotopical form being left
   Bousfield localization (nLab, "reflective localization").

   Computationally a reflective localization is an idempotent monad.  The
   round trip [Incl] ∘ [reflector] is a monad on C whose multiplication
   is invertible, its algebras are exactly the local objects, and to be
   local is to be a fixed point while to localize is to apply the monad:
   idempotent normalization into the full subcategory of already
   saturated objects, where the inverted maps are isomorphisms.  This is
   the correspondence of Construction/Reflective/Idempotent.v (reflective
   subcategory if and only if idempotent monad, with the Eilenberg–Moore
   equivalence), and the same structure homotopy type theory studies as a
   reflective modality (Rijke, Shulman, Spitters, "Modalities in homotopy
   type theory", arXiv:1706.07526, 2020).  The universal property that
   makes the reflector the localization is established separately in
   Construction/Localization/Universal.v. *)

(* [WLocal W x]: the object x is local with respect to the class W.  The
   morphism [fmap[[Hom ─, x]] w] is the [Sets]-map [Hom b x -> Hom a x] sending
   g to g ∘ w (precomposition by w); W-locality asserts it is invertible in
   [Sets] for every w selected by W. *)

Definition WLocal {C : Category} (W : MorphismClass C) (x : C) : Type :=
  ∀ (a b : C) (w : a ~> b), W a b w →
    IsIsomorphism (@fmap (C^op) Sets (Curried_CoHom C x) b a w).

(* From W-locality, the two elementary hom-set facts used downstream: the
   precomposition [(- ∘ w)] into a W-local object is split-surjective ... *)

Lemma WLocal_surj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (p : a ~> x) :
  { q : b ~> x & q ∘ w ≈ p }.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  exists (phi p).
  exact (Hr p).
Qed.

(* ... and injective. *)

Lemma WLocal_inj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (g1 g2 : b ~> x) :
  g1 ∘ w ≈ g2 ∘ w → g1 ≈ g2.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  intro Heq.
  transitivity (phi (g1 ∘ w)).
  - symmetry. exact (Hl g1).
  - transitivity (phi (g2 ∘ w)).
    + apply (proper_morphism phi). exact Heq.
    + exact (Hl g2).
Qed.

(* The full subcategory of W-local objects.  Objects are the W-local ones;
   every C-morphism between them is retained ([shom := True]), so composition
   and identities are closed trivially. *)

Definition C_W {C : Category} (W : MorphismClass C) : Subcategory C :=
  {| sobj  := fun x => WLocal W x
   ; shom  := fun x y ox oy f => True
   ; scomp := fun x y z ox oy oz f g _ _ => I
   ; sid   := fun x ox => I |}.

(* The subcategory C_W is full: every morphism between W-local objects is in it
   (the [shom] witness is [I]). *)

Definition Full_C_W {C : Category} (W : MorphismClass C) :
  Construction.Subcategory.Full C (C_W W) :=
  fun x y ox oy f => I.

(* The reflection unit at a W-local object is an isomorphism.  For any object s
   of the reflective subcategory C_W, the unit η : Iota s ~> Iota (reflector s)
   is invertible in C, with inverse [fmap[Iota] (counit s)].  This is the dual,
   for the unit, of [reflective_counit_iso]; the two triangle identities supply
   both inverse laws, the second one after transporting the subcategory-level
   [zeta ∘ counit ≈ id] along the inclusion functor. *)

Lemma unit_at_local_iso {C : Category} {W : MorphismClass C}
      (R : Reflective (C_W W)) (s : Sub C (C_W W)) :
  IsIsomorphism
    (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
       (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)).
Proof.
  (* zeta : the unit at [Incl s], lifted into the subcategory by fullness. *)
  pose (zeta := (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                   (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)
                 ; reflective_full R (Incl C (C_W W) s)
                     (Incl C (C_W W) (reflector R (Incl C (C_W W) s)))
                     (`2 s) (`2 (reflector R (Incl C (C_W W) s)))
                     (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                        (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)))
                : s ~{Sub C (C_W W)}~> reflector R (Incl C (C_W W) s)).
  (* zeta ∘ counit ≈ id in the subcategory (the [from ∘ to] triangle). *)
  assert (Hlaw2 : zeta ∘ (@counit (Sub C (C_W W)) C (reflector R)
                            (Incl C (C_W W)) (reflective_adj R) s) ≈ id).
  { rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)). }
  unshelve econstructor.
  - (* the inverse: the inclusion of the counit *)
    exact (fmap[Incl C (C_W W)]
             (@counit (Sub C (C_W W)) C (reflector R)
                (Incl C (C_W W)) (reflective_adj R) s)).
  - (* is_right_inverse: η ∘ fmap[Incl] counit ≈ id *)
    change (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
              (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s))
      with (fmap[Incl C (C_W W)] zeta).
    rewrite <- fmap_comp.
    rewrite Hlaw2.
    apply fmap_id.
  - (* is_left_inverse: fmap[Incl] counit ∘ η ≈ id, a triangle identity *)
    apply (@fmap_counit_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) s).
Qed.

(* The localization theorem: when C_W is reflective, the reflector inverts every
   W-map.  For w : a ~> b in W, [fmap[reflector R] w] is an isomorphism of the
   subcategory.  The inverse is [⌈q⌉], where q : b ~> Iota (reflector a) is any
   filler of the unit η_a through [(- ∘ w)] (available by W-locality of the
   reflection Iota (reflector a)); both inverse laws are then discharged through
   the adjunction transposes and W-locality of Iota (reflector b). *)

Section Inverts.
Context {C : Category} {W : MorphismClass C}.
Context (R : Reflective (C_W W)).

(* Parse-time abbreviations: these expand to the full terms, keeping the goal
   and every adjunction-transpose lemma instance in the same syntactic form
   (a [set]-folded form would not match the lemmas' unfolded functor). *)
Local Notation Su   := (Sub C (C_W W)).
Local Notation Iota := (Incl C (C_W W)).
Local Notation Refl := (reflector R).
Local Notation A    := (reflective_adj R).

Theorem reflector_inverts_W {a b : C} (w : a ~> b) (Hw : W a b w) :
  IsIsomorphism (fmap[Refl] w).
Proof.
  (* fill the unit η_a through precomposition by w, using W-locality of the
     reflection Iota (Refl a). *)
  destruct (WLocal_surj (`2 (Refl a)) w Hw
              (@Category.Theory.Adjunction.unit Su C Refl Iota A a)) as [q Hq].
  (* the candidate inverse, transposed back into the subcategory *)
  assert (Hli : from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w ≈ id).
  { transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a))
           (from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A a (Refl a)))).
    rewrite (@to_adj_nat_l Su C Refl Iota A a b (Refl a)
               (from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite (@from_adj_comp_law Su C Refl Iota A b (Refl a) q).
    exact Hq. }
  unshelve refine {| two_sided_inverse := from (@adj Su C Refl Iota A b (Refl a)) q |}.
  - (* is_right_inverse: fmap[Refl] w ∘ ⌈q⌉ ≈ id *)
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b))
           (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A b (Refl b)))).
    apply (WLocal_inj (`2 (Refl b)) w Hw).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b)
                 (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b) id w).
    apply (proper_morphism (to (@adj Su C Refl Iota A a (Refl b)))).
    rewrite id_left.
    rewrite <- comp_assoc.
    rewrite Hli.
    rewrite id_right.
    reflexivity.
  - (* is_left_inverse: ⌈q⌉ ∘ fmap[Refl] w ≈ id *)
    exact Hli.
Qed.

End Inverts.
