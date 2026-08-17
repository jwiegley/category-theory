Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Huq's correspondence: natural transformations as sections of the comma
    projections. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Wikipedia: "If the domains of S, T are equal, then the diagram which
   defines morphisms in S↓T with α=β, α′=β′, g=h is identical to the diagram
   which defines a natural transformation S ⟹ T. The difference between the
   two notions is that a natural transformation is a particular collection of
   morphisms of type of the form S(α) → T(α), while objects of the comma
   category contains all morphisms of type of such form. A functor to the
   comma category selects that particular collection of morphisms. This is
   described succinctly by an observation by Huq that a natural transformation
   η : S → T, with S, T : A → C, corresponds to a functor A → (S↓T) which maps
   each object α to (α, α, η α) and maps each morphism g to (g, g). This is a
   bijective correspondence between natural transformations S ⟹ T and functors
   A ⟶ (S↓T) which are sections of both forgetful functors from S↓T."

   This is also given in Mac Lane, page 47, exercise 4.

   The two definitions below realize the two directions of Huq's bijection for
   functors S T : D ⟶ C sharing the domain D (the "domains equal" case above).
   Comma_Functor sends a natural transformation F : S ⟹ T to the functor
   D ⟶ (S ↓ T) of the observation, X ↦ (X, X; F X) and f ↦ (f, f); it is a
   common section of comma_proj1 and comma_proj2 by construction. Comma_Transform
   is the inverse: from a functor F : D ⟶ (S ↓ T) together with witnesses that
   it is a section of both projections (comma_proj1 ◯ F ≈ Id and
   comma_proj2 ◯ F ≈ Id), it recovers a natural transformation S ⟹ T. *)

(* WHAT IS PROVED HERE, AND AT WHAT STRENGTH

   Mac Lane's exercise (catalog maclane:II.6:ex4, "natural transformations as
   sections of the comma projections (S. A. Huq)") asks, for functors
   T, S : D ⟶ C, that a natural transformation τ : T ⟹ S be the same thing
   as a functor τ : D ⟶ (T ↓ S) with P τ = Q τ = id_D, where P and Q are the
   comma projections (phrasing per the catalog's statement_summary paraphrase,
   doc/plan/books/maclane/inventory/II.json, not the book's wording).  Both
   texts name the SOURCE of the transformation first in their own letters --
   his is T, this file's is S -- so his T and S are this file's S and T.
   Nothing else differs.

   THE SECTION EQUATIONS, AT TWO STRENGTHS.

   Mac Lane's "P τ = id_D" is an equality of functors, on the nose.
   [Comma_Functor_proj1_strict] and [Comma_Functor_proj2_strict] deliver
   exactly that, at [Functor_StrictEq_Setoid] — the hom-setoid of StrictCat,
   in which two functors are identified when their object maps are equal
   propositionally and their morphism maps agree after transport along that
   equality.  Both hold with [eq_refl] as the object witness, because
   [comma_proj1 ◯ Comma_Functor τ] has object map [fun X => fst (X, X)], which
   is [fun X => X] by iota, and likewise on morphisms; every transport in the
   coherence condition therefore vanishes and the condition is [f ≈ f].  This
   is the strongest sense in which this library can say "on the nose": Coq's
   own equality of the two functor RECORDS is not available, since they carry
   proof fields that nothing identifies.

   [Comma_Functor_proj1] and [Comma_Functor_proj2] are the same two facts at
   [Functor_Setoid], the hom-setoid of Cat, in which "equal" means naturally
   isomorphic — so ≈[Cat] and ≅[Cat] read as EQUIVALENCE, not isomorphism, of
   categories.  Those are the witnesses [Comma_Transform] consumes, which is
   why the backward direction proved here GENERALIZES the book's: it accepts a
   functor that sections the projections only up to natural isomorphism, of
   which a functor sectioning them on the nose is the special case.  (They are
   built directly, with [iso_id] components, rather than transported from the
   strict versions along [strict_equiv_implies_fun_equiv]; that bridge is
   Qed-opaque, so the components of the isomorphism it produces would not
   reduce, and the round trip below needs them to compute to [id].)

   WITNESS DEPENDENCE, AND WHY IT DECIDES THE PACKAGING.

   The generalization has a price, and it is not incidental.
   [Comma_Transform F p q] is a function of the WITNESSES p and q, not of F
   alone: [Comma_Transform_witness_shift] computes that replacing (p, q) by
   (p', q') conjugates every component,

     Comma_Transform F p' q' d
       ≈ fmap[T] (to (`1 q' d) ∘ from (`1 q d)) ∘ Comma_Transform F p q d
           ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d)),

   by automorphisms of d assembled from the two witness pairs;
   [Comma_Transform_witness_irrelevant] is the complementary reading, that
   only the [to] components of the witnesses matter, and only up to ≈.

   That conjugation is not merely a formal possibility, and the file does not
   ask the reader to take it on faith.  [huq_witness_separates], at the end,
   exhibits ONE section functor over B(Z/2) — the delooping of the two-element
   group, where every element is a natural automorphism of the identity
   because the group is abelian — carrying two witness pairs whose recovered
   transformations compute to [false] and to [true], with the two values
   pinned by [eq_refl] examples.  So a setoid of section functors whose
   equivalence compared the FUNCTOR alone, discarding the witnesses, provably
   could not support [Comma_Transform] as a map out of it: that one functor
   would have to be sent to two distinct transformations.  That is why
   [HuqSection] bundles the witnesses as data rather than asserting the
   section property.

   Retreating to on-the-nose witnesses would not remove the phenomenon, only
   relocate it: a strict witness is still data, a family of object equalities
   [∀ x, fst ``(F x) = x], and two such families differ by a family of loops
   in obj[D] that nothing here identifies.  Identifying them uniformly is a
   UIP hypothesis on the objects of D, which this development does not take.

   THE PACKAGING, AND THE EQUIVALENCE IT QUOTIENTS BY.

   [HuqSection] is a section functor packaged with its two witnesses.  Two of
   them are [HuqCompatible] when there is a natural isomorphism θ between the
   section functors — an inhabitant of [huq_functor X ≈[Cat] huq_functor Y],
   so θ carries its naturality, it is not merely a pointwise family — ALONG
   WHICH the witnesses correspond:

     to (`1 (huq_sec1 X) d) ≈ to (`1 (huq_sec1 Y) d) ∘ fst `1 (to (`1 θ d))

   and likewise for the second witness.  This is the geometric condition, "X
   and Y are isomorphic AS SECTIONS"; it is deliberately NOT defined as the
   kernel of the recovery map.  That it coincides with that kernel is the
   theorem [huq_compatible_iff]: X and Y are compatible if and only if
   [huq_transform X ≈ huq_transform Y].  The forward half is well-definedness
   of the recovery map on the quotient.  The backward half is the substantive
   one: from a bare equivalence of the two recovered transformations it builds
   the comparison isomorphism, whose components are forced to be
   [from (witness of Y) ∘ (witness of X)] — that is the opening step of
   [huq_compatible_transform] — and whose NATURALITY does not consume the
   hypothesis at all, [huq_compare_natural] using only the coherence fields of
   the four witnesses.  The hypothesis is spent exactly once, on the commuting
   square of the comparison, which the comma hom-setoid then ignores.

   So the equivalence is not a convenience chosen to make a round trip close:
   it is the coarsest relation for which the recovery map is injective, and it
   is exhibited independently as the relation of being isomorphic as sections.
   Nor is it so coarse as to collapse to "same underlying functor":
   [huq_witness_sections_incompatible] separates two packaged sections whose
   functors are literally the same.

   [Huq_roundtrip] packages the correspondence as an isomorphism in Sets
   between [huq_dom], the natural transformations S ⟹ T under
   [Transform_Setoid], and [huq_cod], the packaged sections under
   [HuqCompatible] — the shape used by Adjunction/Conjugate.v's
   [conjugate_bijection] and Theory/Bicategory/Mates.v's [mate_iso].

   Both round trips are available unpackaged, and neither rests on the kernel
   characterization.  [Comma_Transform_Comma_Functor] is the transformation
   side: at the canonical witnesses the conjugation collapses to
   [fmap id ∘ τ X ∘ fmap id].  [Comma_Functor_Comma_Transform] is the section
   side at its honest strength — a natural isomorphism
   [Comma_Functor (Comma_Transform F p q) ≈[Cat] F] for ARBITRARY F, p and q,
   whose component at d is the comma isomorphism between ((d, d); the
   recovered arrow) and F d with legs the two witnesses at d.  It is not
   available on the nose from these hypotheses, and the reason is visible in
   the statement: F d is ((a, b); h) with a and b merely isomorphic to d, not
   equal to it.  [huq_section_compatible] reads that isomorphism back into the
   quotient, so the section-side round trip of [Huq_roundtrip] is discharged
   by the explicit comparison rather than by [huq_compatible_iff]. *)

(* natural transformation S ⟹ T  ↦  section functor D ⟶ (S ↓ T) *)
Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

#[local] Obligation Tactic := simpl; intros.

(* section functor D ⟶ (S ↓ T) of both projections  ↦  natural transformation
   S ⟹ T (the inverse direction of Huq's bijection) *)
Program Definition Comma_Transform {C D : Category} {S T : D ⟶ C}
        (F : D ⟶ (S ↓ T))
        (proj1 : comma_proj1 ◯ F ≈[Cat] Id)
        (proj2 : comma_proj2 ◯ F ≈[Cat] Id) : S ⟹ T := {|
  transform := fun X =>
    fmap (to (`1 proj2 X)) ∘ `2 (F X) ∘ fmap (from (`1 proj1 X))
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.

  spose (`2 proj1 _ _ f) as X0.
  spose (`2 proj2 _ _ f) as X1.

  rewrite <- (id_left f) at 1.
  rewrite <- (iso_to_from (`1 proj2 y)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f).
  rewrites.
  rewrite fmap_comp.
  comp_left.

  symmetry.
  rewrite <- (id_right f) at 1.
  rewrite <- (iso_to_from (`1 proj1 x)).
  rewrite !comp_assoc.
  rewrites.
  rewrite fmap_comp.
  comp_right.

  exact (`2 (fmap[F] f)).
Qed.
Next Obligation.
  symmetry.
  apply Comma_Transform_obligation_1.
Qed.

Section HuqBijection.

Context {C D : Category}.
Context {S T : D ⟶ C}.

(** ** The canonical section witnesses *)

(* [Comma_Functor tau] is a common section of the two projections on the nose:
   the object map of [comma_proj1 ◯ Comma_Functor tau] is
   [fun X => fst (X, X)], which is [fun X => X] by iota, and likewise for its
   morphism map, so the object witness required by [Functor_StrictEq_Setoid] is
   [eq_refl] and both transports vanish. This is the strict (on-the-nose)
   reading of the book's "sections of both forgetful functors". *)

Program Definition Comma_Functor_proj1_strict (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

Program Definition Comma_Functor_proj2_strict (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

(* The same two facts at the strength [Comma_Transform] consumes, namely in
   Cat's hom-setoid [Functor_Setoid], where equality of functors is natural
   isomorphism. These are built directly, with identity components, rather
   than routed through [strict_equiv_implies_fun_equiv] (Instance/StrictCat/
   ToCat.v): that bridge is [Qed]-opaque, so the components of the natural
   isomorphism it produces do not reduce, whereas the round trip below needs
   [to (`1 (Comma_Functor_proj2 tau) X)] to compute to [id]. *)

Program Definition Comma_Functor_proj1 (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

Program Definition Comma_Functor_proj2 (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

(** ** Round trip 1: recovering a natural transformation *)

(* At the canonical witnesses the conjugation of [Comma_Transform] collapses:
   both isomorphism components are the identity, so the recovered component is
   [fmap id ∘ tau X ∘ fmap id]. *)

Theorem Comma_Transform_Comma_Functor (tau : S ⟹ T) :
  Comma_Transform (Comma_Functor tau)
    (Comma_Functor_proj1 tau) (Comma_Functor_proj2 tau) ≈ tau.
Proof.
  intro X; simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** ** Witness dependence *)

(* [Comma_Transform] is a function of the section witnesses, not of the section
   functor alone. Replacing (p, q) by (p', q') conjugates every component by
   the automorphisms [to (`1 p d) ∘ from (`1 p' d)] of d and
   [to (`1 q' d) ∘ from (`1 q d)] of d. *)

Theorem Comma_Transform_witness_shift
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Transform F p' q' d
    ≈ fmap[T] (to (`1 q' d) ∘ from (`1 q d))
        ∘ Comma_Transform F p q d
        ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d)).
Proof.
  assert (Hq : fmap[T] (to (`1 q' d) ∘ from (`1 q d)) ∘ fmap[T] (to (`1 q d))
                 ≈ fmap[T] (to (`1 q' d))).
  { rewrite <- fmap_comp, <- comp_assoc, iso_from_to, id_right.
    reflexivity. }
  assert (Hp : fmap[S] (from (`1 p d)) ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d))
                 ≈ fmap[S] (from (`1 p' d))).
  { rewrite <- fmap_comp, comp_assoc, iso_from_to, id_left.
    reflexivity. }
  simpl.
  rewrite !comp_assoc, Hq.
  rewrite <- !comp_assoc, Hp.
  reflexivity.
Qed.

(* The dependence is exactly on the [to] components of the witnesses: two
   witness pairs with pointwise equivalent components give the same
   transformation. So nothing beyond those components can matter, and the
   conjugation of [Comma_Transform_witness_shift] is trivial precisely when
   they agree. *)

Corollary Comma_Transform_witness_irrelevant
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) :
  (∀ d, to (`1 p d) ≈ to (`1 p' d)) →
  (∀ d, to (`1 q d) ≈ to (`1 q' d)) →
  Comma_Transform F p' q' ≈ Comma_Transform F p q.
Proof.
  intros Hp Hq d.
  rewrite (Comma_Transform_witness_shift F p p' q q' d).
  rewrite <- (Hq d), (Hp d), !iso_to_from, !fmap_id, id_left, id_right.
  reflexivity.
Qed.

(** ** Round trip 2: recovering the section functor *)

(* The comparison isomorphism between [Comma_Functor (Comma_Transform F p q) d]
   — that is, ((d, d); the recovered component) — and [F d]; its legs are the
   two section witnesses at d. *)

Program Definition Comma_Functor_Comma_Transform_iso
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Functor (Comma_Transform F p q) d ≅ F d := {|
  to   := ((from (`1 p d), from (`1 q d)); _);
  from := ((to   (`1 p d), to   (`1 q d)); _)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.
Next Obligation. split; apply iso_from_to. Qed.
Next Obligation. split; apply iso_to_from. Qed.

(* Naturality of that comparison. Note it uses only the coherence fields of
   the two witnesses; no property of [Comma_Transform] is needed. *)

Lemma Comma_Functor_Comma_Transform_natural
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (x y : D) (f : x ~> y) :
  fmap[Comma_Functor (Comma_Transform F p q)] f
    ≈ from (Comma_Functor_Comma_Transform_iso F p q y)
        ∘ fmap[F] f
        ∘ to (Comma_Functor_Comma_Transform_iso F p q x).
Proof.
  spose (`2 p x y f) as Hp.
  spose (`2 q x y f) as Hq.
  split; simpl.
  - rewrite Hp.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
  - rewrite Hq.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
Qed.

(* Packaged transparently (not by [exists ...; Qed]) so that the components of
   the natural isomorphism remain observable downstream — [huq_section_
   compatible] below reads them. *)

Definition Comma_Functor_Comma_Transform
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) :
  Comma_Functor (Comma_Transform F p q) ≈[Cat] F :=
  (Comma_Functor_Comma_Transform_iso F p q;
   Comma_Functor_Comma_Transform_natural F p q).

(** ** The bijection *)

(* Two isomorphism-cancellation lemmas, used to compare two sections of the
   projections through their witnesses. *)

Lemma iso_conj_cancel {E : Category} {a b c : E} (i : a ≅ c) (j : b ≅ c) :
  (from j ∘ to i) ∘ (from i ∘ to j) ≈ id.
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to i)).
  rewrite iso_to_from, id_left.
  apply iso_from_to.
Qed.

Lemma iso_conj_recompose {E : Category} {p q m p' q' m' : E}
      (u : p ≅ m) (v : q ≅ m) (u' : p' ≅ m') (v' : q' ≅ m') (g : m' ~> m) :
  (from u ∘ to v) ∘ (from v ∘ g ∘ to v') ∘ (from v' ∘ to u')
    ≈ from u ∘ g ∘ to u'.
Proof.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from u) (to v) (from v)).
  rewrite iso_to_from, id_right.
  rewrite <- (comp_assoc (from u ∘ g) (to v') (from v')).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* A section of both projections, packaged with its two witnesses. The
   witnesses are DATA, not a property: [Comma_Transform] genuinely depends on
   them ([Comma_Transform_witness_shift] above), so they cannot be discarded. *)

Record HuqSection : Type := {
  huq_functor : D ⟶ (S ↓ T);
  huq_sec1    : comma_proj1 ◯ huq_functor ≈[Cat] Id;
  huq_sec2    : comma_proj2 ◯ huq_functor ≈[Cat] Id
}.

Definition huq_transform (X : HuqSection) : S ⟹ T :=
  Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X).

Definition huq_section (tau : S ⟹ T) : HuqSection :=
  {| huq_functor := Comma_Functor tau;
     huq_sec1    := Comma_Functor_proj1 tau;
     huq_sec2    := Comma_Functor_proj2 tau |}.

Lemma huq_transform_apply (X : HuqSection) (d : D) :
  huq_transform X d
    ≈ fmap[T] (to (`1 (huq_sec2 X) d))
        ∘ `2 (huq_functor X d)
        ∘ fmap[S] (from (`1 (huq_sec1 X) d)).
Proof. reflexivity. Qed.

Theorem huq_transform_section (tau : S ⟹ T) : huq_transform (huq_section tau) ≈ tau.
Proof. apply Comma_Transform_Comma_Functor. Qed.

(* Two packaged sections are compatible when there is a natural isomorphism
   between the section functors ALONG WHICH the two pairs of witnesses
   correspond: the triangles below say that the witness of X factors through
   the witness of Y across the comparison. *)

Definition HuqCompatible (X Y : HuqSection) : Type :=
  ∃ theta : huq_functor X ≈[Cat] huq_functor Y,
      (∀ d, to (`1 (huq_sec1 X) d)
              ≈ to (`1 (huq_sec1 Y) d) ∘ fst `1 (to (`1 theta d)))
    * (∀ d, to (`1 (huq_sec2 X) d)
              ≈ to (`1 (huq_sec2 Y) d) ∘ snd `1 (to (`1 theta d))).

(* Well-definedness of the backward map on the quotient. *)

Theorem huq_compatible_transform (X Y : HuqSection) :
  HuqCompatible X Y → huq_transform X ≈ huq_transform Y.
Proof.
  intros [theta [H1 H2]] d.
  spose (`2 (to (`1 theta d))) as Hsq.
  assert (Hu0 : fst `1 (to (`1 theta d))
                  ≈ from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d)).
  { rewrite (H1 d), comp_assoc, iso_from_to, id_left; reflexivity. }
  assert (Hu : fst `1 (to (`1 theta d)) ∘ from (`1 (huq_sec1 X) d)
                 ≈ from (`1 (huq_sec1 Y) d)).
  { rewrite Hu0, <- comp_assoc, iso_to_from, id_right; reflexivity. }
  unfold huq_transform; simpl.
  rewrite <- Hu, (H2 d), !fmap_comp.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry; exact Hsq.
Qed.

(* The converse: the compatible-witness relation is exactly the kernel of the
   backward map, so the equivalence above is not an arbitrary choice but the
   coarsest one that makes [huq_transform] injective. The comparison
   isomorphism is forced — its components are [from (witness of Y) ∘
   (witness of X)] — and its NATURALITY is automatic, using only the coherence
   fields of the four witnesses; the hypothesis is spent only on the comma
   square. *)

(* Undoing the conjugation on the [S] side: the recovered transformation,
   precomposed with the first witness, is the comma component of F d
   postcomposed with the second. *)
Lemma huq_transform_unconj (X : HuqSection) (d : D) :
  huq_transform X d ∘ fmap[S] (to (`1 (huq_sec1 X) d))
    ≈ fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d).
Proof.
  rewrite (huq_transform_apply X d).
  rewrite <- (comp_assoc (fmap[T] (to (`1 (huq_sec2 X) d))
                            ∘ `2 (huq_functor X d))).
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.

(* The two recovered transformations agree, so the [X]-side conjugation of
   the comma component of [F X] equals the [Y]-side one, up to the two
   witnesses at d. This is the whole use made of the hypothesis. *)
Lemma huq_transform_shift (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (d : D) :
  fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d)
    ≈ fmap[T] (to (`1 (huq_sec2 Y) d)) ∘ `2 (huq_functor Y d)
        ∘ fmap[S] (from (`1 (huq_sec1 Y) d))
        ∘ fmap[S] (to (`1 (huq_sec1 X) d)).
Proof.
  rewrite <- (huq_transform_apply Y d).
  rewrite <- (H d).
  symmetry; apply huq_transform_unconj.
Qed.

Program Definition huq_compare (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ~{S ↓ T}~> huq_functor Y d :=
  ((from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d),
    from (`1 (huq_sec2 Y) d) ∘ to (`1 (huq_sec2 X) d)); _).
Next Obligation.
  rewrite !fmap_comp.
  rewrite <- (comp_assoc (fmap[T] (from (`1 (huq_sec2 Y) d)))).
  rewrite (huq_transform_shift X Y H d).
  rewrite !comp_assoc, <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.

Program Definition huq_compare_iso (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ≅ huq_functor Y d := {|
  to   := huq_compare X Y H d;
  from := huq_compare Y X (symmetry H) d
|}.
Next Obligation. split; apply iso_conj_cancel. Qed.
Next Obligation. split; apply iso_conj_cancel. Qed.

Lemma huq_compare_natural (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (x y : D) (f : x ~> y) :
  fmap[huq_functor X] f
    ≈ from (huq_compare_iso X Y H y)
        ∘ fmap[huq_functor Y] f
        ∘ to (huq_compare_iso X Y H x).
Proof.
  spose (`2 (huq_sec1 X) x y f) as H1X.
  spose (`2 (huq_sec1 Y) x y f) as H1Y.
  spose (`2 (huq_sec2 X) x y f) as H2X.
  spose (`2 (huq_sec2 Y) x y f) as H2Y.
  split; simpl.
  - rewrite H1X, H1Y.
    symmetry; apply iso_conj_recompose.
  - rewrite H2X, H2Y.
    symmetry; apply iso_conj_recompose.
Qed.

Definition huq_compare_equiv (X Y : HuqSection)
           (H : huq_transform X ≈ huq_transform Y) :
  huq_functor X ≈[Cat] huq_functor Y :=
  (huq_compare_iso X Y H; huq_compare_natural X Y H).

Theorem huq_transform_compatible (X Y : HuqSection) :
  huq_transform X ≈ huq_transform Y → HuqCompatible X Y.
Proof.
  intro H.
  exists (huq_compare_equiv X Y H).
  split; intro d; simpl;
  rewrite comp_assoc, iso_to_from, id_left; reflexivity.
Qed.

Theorem huq_compatible_iff (X Y : HuqSection) :
  HuqCompatible X Y ↔ huq_transform X ≈ huq_transform Y.
Proof.
  split.
  - apply huq_compatible_transform.
  - apply huq_transform_compatible.
Qed.

(* The section-side round trip, at the level of the quotient. This LEMMA is
   proved directly from the comparison isomorphism of
   [Comma_Functor_Comma_Transform] — it does not go through
   [huq_transform_compatible] — so the round trip itself does not rest on the
   kernel characterisation.  (The packaged [Huq_roundtrip] as a whole still
   does, elsewhere: the forward map's respectfulness consumes
   [huq_transform_compatible], and [HuqSection_Setoid]'s Equivalence
   obligation routes through the kernel reading — the latter stylistically,
   reflexivity at least having a direct geometric proof.) *)

Theorem huq_section_compatible (X : HuqSection) :
  HuqCompatible (huq_section (huq_transform X)) X.
Proof.
  exists (Comma_Functor_Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X)).
  split; intro d; simpl; symmetry; apply iso_to_from.
Qed.

Program Definition HuqSection_Setoid : Setoid HuqSection := {|
  equiv := HuqCompatible
|}.
Next Obligation.
  constructor.
  - intro X.
    apply huq_transform_compatible; reflexivity.
  - intros X Y HXY.
    apply huq_transform_compatible.
    symmetry; now apply huq_compatible_transform.
  - intros X Y Z HXY HYZ.
    apply huq_transform_compatible.
    transitivity (huq_transform Y); now apply huq_compatible_transform.
Qed.

Definition huq_dom : SetoidObject := {| carrier := S ⟹ T |}.
Definition huq_cod : SetoidObject :=
  {| carrier := HuqSection; is_setoid := HuqSection_Setoid |}.

Program Definition Huq_roundtrip : @Isomorphism Sets huq_dom huq_cod := {|
  to   := {| morphism := huq_section |};
  from := {| morphism := huq_transform |}
|}.
Next Obligation.
  proper.
  apply huq_transform_compatible.
  rewrite !huq_transform_section.
  assumption.
Qed.
Next Obligation.
  proper.
  now apply huq_compatible_transform.
Qed.
Next Obligation. apply huq_section_compatible. Qed.
Next Obligation. apply huq_transform_section. Qed.

End HuqBijection.

(** ** Witness dependence is not merely formal *)

(* The conjugation of [Comma_Transform_witness_shift] can be non-trivial, and
   the witness B(Z/2) shows it. In the delooping of the two-element group
   composition is [xorb] and the identity arrow is [false]; the group is
   abelian, so EVERY element is a natural automorphism of the identity functor
   (naturality of a family over a one-object category is exactly commutativity
   with each arrow). Hence [true] gives a second witness that
   [comma_proj1 ◯ Comma_Functor nat_id] is the identity, inequivalent to the
   canonical one, and the two transformations recovered from THE SAME section
   functor are [false] and [true].

   So the ill-definedness that motivates [HuqSection]'s bundling of witnesses
   is exhibited, not assumed: no map out of a setoid of section functors that
   discarded the witnesses could agree with [Comma_Transform], since one and
   the same functor would have to be sent to two distinct transformations.

   UNIVERSES: everything above this section is fully polymorphic with no
   [Set] anywhere.  The separation witness alone is pinned -- [Bool_Xor]'s
   carrier is [bool : Set], so [BZ2 : Category@{u Set Set}] has its hom and
   proof levels at [Set] -- the expected price of a concrete witness (the
   Instance/Grp/Center.v S3 precedent), and a counterexample needs only one
   instance. *)

Local Notation BZ2 := (Deloop Bool_Xor).

Definition huq_sep_tau : Id[BZ2] ⟹ Id[BZ2] := nat_id.

Definition huq_sep_F : BZ2 ⟶ (Id[BZ2] ↓ Id[BZ2]) := Comma_Functor huq_sep_tau.

(* The twisted witness: the component is [true], self-inverse in Z/2, and the
   coherence condition holds because conjugating by [true] on both sides is the
   identity. *)
Program Definition huq_sep_twist :
  comma_proj1 ◯ huq_sep_F ≈[Cat] Id := (fun _ => {| to := true; from := true |}; _).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. now destruct f. Qed.

Definition huq_sep_canonical : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := Comma_Functor_proj1 huq_sep_tau;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Definition huq_sep_twisted : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := huq_sep_twist;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Example huq_sep_canonical_value : huq_transform huq_sep_canonical ttt = false :=
  eq_refl.

Example huq_sep_twisted_value : huq_transform huq_sep_twisted ttt = true :=
  eq_refl.

Theorem huq_witness_separates :
  huq_transform huq_sep_canonical ≈ huq_transform huq_sep_twisted → False.
Proof.
  intro H.
  specialize (H ttt).
  discriminate.
Qed.

(* The quotient of [Huq_roundtrip] therefore distinguishes two packaged
   sections with the SAME underlying functor: [HuqCompatible] is strictly
   finer than equality of section functors. *)

Corollary huq_witness_sections_incompatible :
  HuqCompatible huq_sep_canonical huq_sep_twisted → False.
Proof.
  intro HC.
  now apply huq_witness_separates, huq_compatible_transform.
Qed.
