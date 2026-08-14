Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Dagger categories

    nLab:      https://ncatlab.org/nlab/show/dagger+category
    Wikipedia: https://en.wikipedia.org/wiki/Dagger_category
    Book:      Mac Lane, "Categories for the Working Mathematician",
               2nd ed., GTM 5, §I.7 (printed p. 26): Rel carries the
               converse operation R† [maclane:I.7:construction8]
    Book:      Awodey, "Category Theory", 2nd ed., §1.9 Exercise 2
               (printed p. 29): the self-duality Rel ≅ Rel^op
    Paper:     Selinger, "Dagger compact closed categories and
               completely positive maps", ENTCS 170 (2007) — the modern
               axiomatization and the name

    A DAGGER CATEGORY is a category equipped with an
    identity-on-objects involution reversing every morphism: each
    f : x ~> y has a dagger f† : y ~> x with (f†)† ≈ f, id† ≈ id, and
    (f ∘ g)† ≈ g† ∘ f† — an anti-homomorphism for composition.  The
    concept axiomatizes "reversal" structure that a bare category
    cannot see: relation converse in Rel, adjoints of linear maps in
    Hilbert spaces, path reversal in groupoids.  Selinger's dagger
    compact closed categories are the semantic backbone of categorical
    quantum mechanics — the ZX-calculus prose in Instance/ZX.v and the
    compact-closed remarks in Structure/Monoidal/StarAutonomous.v both
    name daggers; this class is the light common vocabulary those
    discussions were missing (no compatibility with monoidal structure
    is demanded here — dagger monoidal/compact closed towers are left
    for the developments that need them).

    The class is deliberately minimal: the four laws above and nothing
    else, with the operation packaged as data ([dagger]) plus a
    [Proper] field so it respects the hom-setoids.  A dagger is
    equivalently an identity-on-objects functor C^op ⟶ C squaring to
    the identity; instances may expose that functor separately (as
    Instance/Rel/Dagger.v does for Rel, where it assembles into the
    self-duality isomorphism Rel ≅ Rel^op in Cat — Awodey's Exercise
    1.9.2(a)). *)

Class DaggerCategory (C : Category) := {
  dagger {x y : C} : (x ~> y) → (y ~> x);

  dagger_respects {x y : C} :
    Proper (equiv ==> equiv) (@dagger x y);

  dagger_involution {x y : C} (f : x ~> y) :
    dagger (dagger f) ≈ f;

  dagger_id {x : C} : dagger (@id C x) ≈ id;

  (* The anti-homomorphism law: reversal exchanges the order of
     composition. *)
  dagger_compose {x y z : C} (f : y ~> z) (g : x ~> y) :
    dagger (f ∘ g) ≈ dagger g ∘ dagger f
}.

#[export] Existing Instance dagger_respects.

Notation "f †" := (dagger f) (at level 30) : morphism_scope.
