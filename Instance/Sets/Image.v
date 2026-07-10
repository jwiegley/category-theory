Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Factorization.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Images in [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/image
   Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)

   Concrete images in the category of setoids: every morphism f : X ~> Y
   of [Sets] splits as an epimorphism onto its image followed by a
   monomorphism into its codomain.

   The image object carries the proof-relevant sigma type

       { y : Y & { x : X & f x ≈ y } }

   — a point of Y together with a chosen preimage and the witness that f
   sends that preimage to it — and its setoid compares Y-components only:

       (y1; _) ≈ (y2; _)  :=  y1 ≈ y2.

   The epi leg sends x to (f x; (x; _)), the mono leg is the first
   projection, and their composite agrees with f pointwise on the nose.

   Both class memberships are established directly from these definitions;
   in particular the construction needs no epis-are-surjections result for
   [Sets] — the factorization is direct.  The left leg is epic because two
   morphisms out of the image that agree on all points of the shape
   (f x; (x; _)) agree everywhere: every image point is ≈ to one of that
   shape by its stored witness.  The right leg is monic because agreement
   of first projections is exactly the image setoid's equivalence.  The
   whole package is bundled as [Sets_Image_Factorization], an (Epi, Mono)
   [Factorization] in the sense of Structure/Factorization.v. *)

Section SetsImage.

Context {X Y : SetoidObject}.
Context (f : X ~{Sets}~> Y).

(* Comparing image points by their Y-components only is an equivalence,
   inherited from the setoid on Y. *)
Lemma Sets_Image_equivalence :
  Equivalence (fun p q : ∃ y : Y, ∃ x : X, f x ≈ y => `1 p ≈ `1 q).
Proof.
  constructor.
  - intro p.
    simpl.
    reflexivity.
  - intros p q H.
    simpl in *.
    symmetry.
    exact H.
  - intros p q r H1 H2.
    simpl in *.
    transitivity (`1 q).
    + exact H1.
    + exact H2.
Qed.

(* The setoid of image points: pairs of a point of Y with a chosen
   f-preimage, compared by their Y-components only. *)
Definition Sets_Image_setoid : Setoid (∃ y : Y, ∃ x : X, f x ≈ y) := {|
  equiv        := fun p q => `1 p ≈ `1 q;
  setoid_equiv := Sets_Image_equivalence
|}.

(* The image of f as an object of [Sets]. *)
Definition Sets_Image : SetoidObject := {|
  carrier   := ∃ y : Y, ∃ x : X, f x ≈ y;
  is_setoid := Sets_Image_setoid
|}.

(* The epi leg X ~> Sets_Image: send x to f x, remembering x itself as the
   chosen preimage. *)
Definition Sets_Image_epi : X ~{Sets}~> Sets_Image.
Proof.
  unshelve refine {| morphism        := fun x => (f x; (x; _))
                   ; proper_morphism := _ |}.
  - reflexivity.
  - repeat intro.
    simpl.
    now apply (proper_morphism f).
Defined.

(* The mono leg Sets_Image ~> Y: the first projection.  Respectfulness is
   the identity: the image equivalence IS agreement of first projections. *)
Definition Sets_Image_mono : Sets_Image ~{Sets}~> Y.
Proof.
  unshelve refine {| morphism        := fun p => `1 p
                   ; proper_morphism := _ |}.
  repeat intro.
  assumption.
Defined.

(* The two legs compose to f, pointwise by reflexivity. *)
Lemma Sets_Image_comm : Sets_Image_mono ∘ Sets_Image_epi ≈ f.
Proof.
  intro x.
  simpl.
  reflexivity.
Qed.

(* The epi leg is epic: given g1 ∘ epi ≈ g2 ∘ epi and an image point
   (y; (x; hx)), rewrite it to the canonical point (f x; (x; _)) using the
   stored witness hx : f x ≈ y, where the hypothesis applies. *)
Lemma Sets_Image_epi_epic : Epic Sets_Image_epi.
Proof.
  constructor.
  intros Z g1 g2 HB.
  simpl in HB.
  intro p.
  destruct p as [y [x hx]].
  transitivity (g1 (Sets_Image_epi x)).
  - apply (proper_morphism g1).
    simpl.
    symmetry.
    exact hx.
  - transitivity (g2 (Sets_Image_epi x)).
    + exact (HB x).
    + apply (proper_morphism g2).
      simpl.
      exact hx.
Qed.

(* The mono leg is monic: mono ∘ g1 ≈ mono ∘ g2 says the first projections
   agree pointwise, which is precisely the image setoid's equivalence. *)
Lemma Sets_Image_mono_monic : Monic Sets_Image_mono.
Proof.
  constructor.
  intros Z g1 g2 HB.
  intro p.
  exact (HB p).
Qed.

(* The bundled (Epi, Mono)-factorization of f through its image. *)
Definition Sets_Image_Factorization :
  Factorization f EpiClass MonoClass :=
  @Build_Factorization Sets X Y f EpiClass MonoClass
    Sets_Image
    Sets_Image_epi
    Sets_Image_epi_epic
    Sets_Image_mono
    Sets_Image_mono_monic
    Sets_Image_comm.

End SetsImage.
