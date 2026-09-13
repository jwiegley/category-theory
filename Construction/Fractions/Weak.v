Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * The universal property of [C[C⁻¹]] at [Functor_Setoid] strength

    nLab:      https://ncatlab.org/nlab/show/localization
    nLab:      https://ncatlab.org/nlab/show/calculus+of+fractions
    Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
          printed p. 137 — the inclusion of groupoids into categories has a
          left adjoint, the category of fractions
    Book: Gabriel, Zisman, Calculus of Fractions and Homotopy Theory,
          Ergebnisse 35, Springer 1967, §I.1

    WHAT THIS FILE IS FOR.  [Construction/Fractions.v] proves the universal
    property of the zig-zag localization at STRICT strength: its
    [Fractions_UMP] and [Fractions_UMP_groupoid] are [Unique] records over
    [Functor_StrictEq_Setoid], i.e. Leibniz equality on objects together
    with `≈` on morphisms conjugated by [hom_cast].  That is the strength
    [Construction/Quotient.v] and [Construction/Free/Groupoid.v] state their
    own uniqueness clauses at, and it is the wrong strength for
    [Theory/Universal/Arrow.v]'s [universal_arrow_from_UMP], which reads the
    `∃!` at the AMBIENT category's hom-setoid.  The ambient here is [Cat],
    whose hom-setoid is [Functor_Setoid] — natural isomorphism.  The header
    of [Construction/Fractions.v] records the resulting mismatch and quotes
    the refusal in full.

    This file removes the mismatch by REPROVING the uniqueness clause
    against natural isomorphism.  Existence needed no work: it transfers
    along [Instance/StrictCat/ToCat.v]'s [strict_equiv_implies_fun_equiv],
    which is exactly the statement that strict equality of functors refines
    natural isomorphism.  Uniqueness does not transfer in that direction —
    a functor that factors [F] only up to natural isomorphism need not
    factor it up to object equality, so the strict statement says nothing
    about it — and it is reproved here from the beginning.

    WHY THE ARGUMENT WORKS.  Three facts about [Fractions C] make it go
    through, and all three are conversions, not lemmas: [Fractions C] has
    exactly the objects of [C] ([ZQuiver]'s [nodes] is [@obj C], and neither
    [FreeOnQuiver] nor [QuotientCong] disturbs the object type),
    [FractionsProj C] is the identity on objects, and a hom of
    [Fractions C] IS a [Lib/TList.v] word in the glued quiver, the quotient
    coarsening only the setoid.  So a natural isomorphism between the two
    restrictions [G1 ◯ FractionsProj C] and [G2 ◯ FractionsProj C] already
    supplies its component at every object of [Fractions C]; only naturality
    has to be extended, from the generators to all words.

    That extension is the induction [Fractions_weak_word], and it has the
    same shape as [Construction/Fractions.v]'s [ZigZagLift_unique] — the
    word is peeled with [tlist_app_cons], the tail handled by the induction
    hypothesis and the head letter by a separate lemma — with the
    [hom_cast] of the strict argument replaced throughout by conjugation
    with the components of the isomorphism.  The head letter splits the same
    way too: a forward letter is a generator and is given, while a backward
    letter is pinned because both [G1] and [G2] carry the two cancellation
    equations of [Construction/Fractions.v] to two-sided inverses
    ([zbwd_zfwd_functor], [zfwd_zbwd_functor], which hold for ANY functor out
    of the localization), and a two-sided inverse is determined up to `≈`.
    [iso_conj_inverse] is the replacement for [hom_cast_inverse]: it says
    that if [a] and [a'] correspond under conjugation by two isomorphisms,
    then so do their inverses.

    NO GROUPOID HYPOTHESIS ON THE TARGET, for the uniqueness half.
    [Fractions_weak_word] and [Fractions_proj_epic_weak] hold for an
    arbitrary target category [D]; the invertibility they use is that of the
    IMAGES of the generators, which the localization already forces.  Only
    existence needs [IsGroupoid D], and only to produce the [Finv] argument
    of [FractionsLift].

    WHAT IS PROVED, AND WHAT IS NOT.  [Fractions_UMP_weak] is the same
    [Unique] record as [Fractions_UMP_groupoid] with [Functor_StrictEq_Setoid]
    replaced by [Functor_Setoid] in both positions.  It is genuinely WEAKER
    than the strict one, and deliberately so: the two are not
    interchangeable, and [Test/ProbeFractionsAdjunction972.v] pins the
    direction by refusing the strict statement where only the weak one has
    been proved.  Nothing here says the strict version is subsumed, and
    [Construction/Fractions.v] keeps it — [Fractions_proj_epic] and
    [frac_restrict_recovers] still read at the strict setoid. *)

(** ** Conjugating a two-sided inverse

    The weak counterpart of [Construction/Fractions.v]'s [hom_cast_inverse].
    There the correspondence between [a] and [a'] was transport along
    equalities of the endpoints; here it is conjugation by isomorphisms of
    the endpoints, which is the shape [Functor_Setoid] states naturality in
    ([fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x)]). *)

Lemma iso_conj_inverse {D : Category} {X1 Y1 X2 Y2 : D}
  (p : X1 ≅ X2) (q : Y1 ≅ Y2)
  (a : X1 ~> Y1) (b : Y1 ~> X1) (a' : X2 ~> Y2) (b' : Y2 ~> X2)
  (Hba : b ∘ a ≈ id) (Ha'b' : a' ∘ b' ≈ id)
  (Ha : a ≈ from q ∘ a' ∘ to p) :
  b ≈ from p ∘ b' ∘ to q.
Proof.
  assert (Hac : a ∘ (from p ∘ b' ∘ to q) ≈ id).
  { rewrite Ha.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to p) (from p)).
    rewrite iso_to_from, id_left.
    rewrite (comp_assoc a' b').
    rewrite Ha'b', id_left.
    apply iso_from_to. }
  rewrite <- (id_left (from p ∘ b' ∘ to q)).
  rewrite <- Hba.
  rewrite <- comp_assoc.
  rewrite Hac.
  now rewrite id_right.
Qed.

(** ** Naturality spreads from the generators to every zig-zag word *)

Section FractionsWeak.

Context {C D : Category}.

(* A single letter of a zig-zag word.  The forward letter IS a generator —
   [tlist_singleton (inl f)] is [zfwd f], which is [fmap[FractionsProj C] f]
   by conversion — so it is the hypothesis read back.  The backward letter is
   the content: it is inverse to the forward letter under both functors, and
   a conjugate of an inverse is the inverse of the conjugate. *)

Lemma Fractions_weak_edge
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x))
  {x y : C} (e : ZEdge (WAll C) x y) :
  fmap[G1] (tlist_singleton e)
    ≈ from (iso y) ∘ fmap[G2] (tlist_singleton e) ∘ to (iso x).
Proof.
  destruct e as [f | [g w]].
  - exact (Hgen x y f).
  - exact (iso_conj_inverse (iso y) (iso x)
             (fmap[G1] (zfwd (WAll C) g)) (fmap[G1] (zbwd (WAll C) g w))
             (fmap[G2] (zfwd (WAll C) g)) (fmap[G2] (zbwd (WAll C) g w))
             (zbwd_zfwd_functor (WAll C) G1 g w)
             (zfwd_zbwd_functor (WAll C) G2 g w)
             (Hgen y x g)).
Qed.

(* The induction on words, in the shape of [ZigZagLift_unique]: the empty
   word is the identity and the isomorphism cancels, and [e ::: rest] is
   [rest ∘ (e)], where the two conjugations meet at the middle object and
   the inner [to (iso b) ∘ from (iso b)] collapses. *)

Lemma Fractions_weak_word
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x)) :
  ∀ (x y : C) (u : x ~{Fractions C}~> y),
    fmap[G1] u ≈ from (iso y) ∘ fmap[G2] u ∘ to (iso x).
Proof.
  intros x y u.
  induction u as [| a b e rest IH].
  - rewrite !fmap_id, id_right.
    now rewrite iso_from_to.
  - assert (Hu : (e ::: rest)
                 = @compose (Fractions C) a b y rest (tlist_singleton e))
      by apply tlist_app_cons.
    rewrite Hu, !fmap_comp.
    rewrite IH, (Fractions_weak_edge G1 G2 iso Hgen e).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite !comp_assoc.
    apply compose_respects; [ | reflexivity ].
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite comp_assoc.
    now rewrite iso_to_from, id_left.
Qed.

End FractionsWeak.

(** ** Precomposition with the projection is injective, at [Functor_Setoid]

    The weak counterpart of [Construction/Fractions.v]'s
    [Fractions_proj_epic], and unlike that one it needs NO hypothesis on the
    target: the whole content is [Fractions_weak_word], and the isomorphism
    family is carried over unchanged because the objects of [Fractions C]
    are the objects of [C]. *)

Theorem Fractions_proj_epic_weak {C D : Category} (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) L L'.
Proof.
  destruct E as [iso Hn].
  exists iso.
  exact (Fractions_weak_word L L' iso Hn).
Qed.

(** ** The universal property, at [Functor_Setoid] strength *)

Section FractionsUMPWeak.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

Let Finv := fun (x y : C) (f : x ~> y) => Dg (F x) (F y) (fmap[F] f).

(* Existence is free: the strict factorization of [Construction/Fractions.v]
   pushed forward along [strict_equiv_implies_fun_equiv]. *)

Lemma FractionsLift_factors_weak :
  @equiv _ (@Functor_Setoid C D) F (FractionsLift F Finv ◯ FractionsProj C).
Proof.
  symmetry.
  apply strict_equiv_implies_fun_equiv.
  exact (FractionsLift_factors F Finv).
Qed.

Lemma FractionsLift_unique_weak (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) (FractionsLift F Finv) L.
Proof.
  apply Fractions_proj_epic_weak.
  transitivity F.
  - symmetry; exact FractionsLift_factors_weak.
  - exact E.
Qed.

(* Riehl 4.1.15, left half, in the shape [universal_arrow_from_UMP] consumes:
   the same [Unique] record as [Fractions_UMP_groupoid], over
   [Functor_Setoid] in both positions instead of [Functor_StrictEq_Setoid]. *)

Definition Fractions_UMP_weak :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  @Build_Unique _ (@Functor_Setoid (Fractions C) D) _
    (FractionsLift F Finv)
    FractionsLift_factors_weak
    FractionsLift_unique_weak.

End FractionsUMPWeak.
