(** * Regression test for issue #118: the [Full] type class.

    https://github.com/jwiegley/category-theory/issues/118

    The [Full] type class must express the *standard* notion of a full
    functor: a section [prefmap] of the hom-map [fmap[F]] together with the
    surjectivity witness [fmap_sur] — and nothing more.  No functoriality may
    be demanded of [prefmap].  The previous definition additionally carried
    [prefmap_respects], [prefmap_id] and [prefmap_comp]; those three fields
    were extraneous and have been removed, leaving exactly:

      Class Full `(F : C ⟶ D) := {
        prefmap {x y} (g : F x ~> F y) : x ~> y;
        fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g
      }.

    This file pins that two-field shape.  It constructs a [Full] instance
    using *only* [prefmap] and [fmap_sur]:

      - [Id_Full_build] applies the generated constructor [Build_Full] to
        exactly those two values.  Under the old five-field class this is a
        partial application whose type still expects the three dropped fields,
        so it is rejected; under the corrected class it has type [Full Id[C]].

      - [Full_from_section] does the same via a record literal that lists only
        the two surviving fields.  Under the old class the omitted fields turn
        into unresolved implicit arguments (a hard error); under the corrected
        class the literal is complete.

    Either construction therefore compiles only against the corrected
    definition and fails against the old one.  Finally we reference
    [FullyFaithful] — the lemma whose proof previously relied on the removed
    [prefmap_comp] / [prefmap_id] — to confirm it still typechecks under the
    leaner class. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** ** Constructor form.

    [Build_Full] is the constructor generated for the [Full] class.  We feed
    it exactly the two fields of the corrected definition.  The identity
    functor's hom-map is the identity on [x ~> y], so the chosen preimage is
    [g] itself and [fmap_sur] holds by reflexivity (recall that [fmap[Id[C]] g]
    reduces to [g]). *)
Definition Id_Full_build (C : Category) : Full (Id[C]) :=
  Build_Full _ _ Id[C]
    (fun x y (g : Id[C] x ~> Id[C] y) => g)
    (fun x y (g : Id[C] x ~> Id[C] y) => reflexivity g).

(** ** Record-literal form.

    The same two-field shape, expressed as a section of an arbitrary functor's
    hom-map.  The literal mentions only [prefmap] and [fmap_sur]; under the old
    class the missing functoriality fields would be unresolved implicits. *)
Definition Full_from_section
  `(F : C ⟶ D)
  (pre : ∀ x y, F x ~> F y → x ~> y)
  (sec : ∀ x y (g : F x ~> F y), fmap[F] (pre x y g) ≈ g) : Full F :=
  {| prefmap x y g := pre x y g
   ; fmap_sur x y g := sec x y g |}.

(** The identity functor is full: every hom-map is the identity, hence its own
    section.  The witness is exhibited through [Full_from_section], with the
    section law closed explicitly by [reflexivity] rather than left to the
    ambient [Program] obligation tactic — so the test states its own proof. *)
Definition Id_Full {C : Category} : Full (@Id C) :=
  Full_from_section Id (fun _ _ g => g) (fun _ _ g => reflexivity g).

(** Register an instance so resolution of the leaner class is exercised too. *)
#[local] Existing Instance Id_Full.

(** The two surviving projections, with their expected types under the
    corrected definition. *)
Check @prefmap.
Check @fmap_sur.

(** ** [FullyFaithful] under the leaner class.

    The identity functor is trivially faithful; combined with fullness this
    lets us instantiate [FullyFaithful] and confirm the lemma — whose proof no
    longer has access to [prefmap_comp] / [prefmap_id] — still elaborates. *)
#[local] Program Instance Id_Faithful (C : Category) : Faithful (Id[C]) := {|
  fmap_inj := fun x y (f g : x ~> y) (H : f ≈ g) => H
|}.

Definition FullyFaithful_under_lean_Full
  `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y := FullyFaithful F.

(** Pin a concrete instantiation as well, independent of implicit inference. *)
Check (fun C : Category =>
         @FullyFaithful C C Id[C] (Id_Full_build C) (Id_Faithful C)).
