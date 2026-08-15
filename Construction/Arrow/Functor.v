(** * Functors into the arrow category classify natural transformations *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Instance.Sets.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.4, printed pp. 40–42 (PDF 50–52) —
              maclane:II.4:construction1, maclane:II.4:ex7
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
              Example 7.15, printed p. 171 (PDF p. 180) —
              awodey:7.7:example15
   nLab:      https://ncatlab.org/nlab/show/arrow+category

   Mac Lane's Exercise II.4.7: a functor into the arrow category is
   exactly a natural transformation.  From H : C ⟶ Arrow B one reads
   off two functors — the domain and codomain of the arrows H picks
   out — and the arrows themselves assemble into a natural
   transformation between them, BECAUSE the morphism part of H is a
   commuting square; conversely a natural transformation τ : S ⟹ T
   materializes as the functor c ↦ (τ c), naturality supplying the
   squares.  The two passages are mutually inverse, and this file
   states the bijection at the strength the library supports: a
   setoid isomorphism in Sets between functors C ⟶ Arrow B under
   [Functor_Setoid] (natural isomorphism) and transformation triples
   (S, T, τ) under componentwise natural isomorphism intertwining τ.

     - [ArrowTriple]/[triple_dom]/[triple_cod]/[triple_nat]: the
       bundle (S, T, τ : S ⟹ T) with its boundary accessors
     - [Arrow_dom]/[Arrow_cod]: the boundary functors of a functor
       into the arrow category, and [Arrow_generic H] — the arrows H
       picks out, assembled into a transformation (Ex. 7 forward);
       [Arrow_dom_boundary]/[Arrow_cod_boundary] record that the
       generic arrow's components have the projected boundaries
     - [Arrow_intro (S, T, τ)]: the classifying functor H_τ with
       object action c ↦ τ c and morphism action the naturality
       square (Ex. 7 inverse)
     - [ArrowTriple_Setoid]: triples up to componentwise natural
       isomorphism intertwining the transformations
     - [Arrow_classification]: the bijection, as an isomorphism in
       Sets between the functor setoid and the triple setoid

   Design:

   1. THE COMPARISON WITH [_2, B] IS ALREADY IN THE TREE, AND IS NOT
      REBUILT.  Theory/Shapes.v proves
      [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C] (with the strict half
      [Arrow_Fun_Arrow_strict]), for [C : Category@{o Set Set}] — a
      restriction [_2]'s Set-level homs force through [Fun].  This
      file is the OTHER half of Mac Lane's §II.4 story, and it is
      free of that Set-level pin: the classification never mentions
      [_2], only the comma presentation [Arrow B := Id ↓ Id], so hom
      and proof universes may sit strictly above [Set] (the
      library's ambient h = p constraint that [Functor] imposes
      still applies, as it does to every functor statement).
      Awodey's Example 7.15 reads C^1 = C, C^2 = the arrow category,
      C^I = powers: the first is Theory/Shapes.v's [One_Fun_iso]
      (itself under the same Set-level restriction as
      [Two_Fun_Arrow], for the same reason), the second is
      [Two_Fun_Arrow], and the discrete third is issue #276's
      Instance/Fun/Discrete.v.

   2. THE TRIPLE SETOID MIRRORS [Functor_Setoid].  Two triples are
      identified when their boundary functors are naturally
      isomorphic AND the isomorphisms intertwine the two
      transformations (ρ c ∘ τ c ≈ τ' c ∘ σ c).  This is forced:
      the functor side identifies H ≈ H' by natural isomorphisms
      whose components are commuting squares of [Arrow B], and a
      square's two legs are exactly the σ/ρ components while the
      square condition is exactly the intertwining.  The explicit
      symmetric/transitive witnesses [fs_sym]/[fs_trans] for
      [Functor_Setoid] are built by hand (iso_sym/iso_compose
      families) so their component families stay transparent — the
      instance's own Equivalence proof is opaque and cannot be
      computed through.

   3. ROUND TRIPS.  Extraction after introduction is definitional on
      every component (identity isomorphism families); introduction
      after extraction differs from the original functor only by
      sigT/pair eta — H c is ((p, h)) while the rebuilt object is
      ((fst p, snd p), h) — repaired by the identity-legged square,
      the same pair-eta phenomenon Construction/Product/Special.v
      documents. *)

(** ** Transformation triples *)

(* The data Ex. 7 classifies: two functors and a transformation. *)
Definition ArrowTriple (C B : Category) : Type :=
  { S : C ⟶ B & { T : C ⟶ B & S ⟹ T } }.

Definition triple_dom {C B : Category} (t : ArrowTriple C B) : C ⟶ B := `1 t.
Definition triple_cod {C B : Category} (t : ArrowTriple C B) : C ⟶ B :=
  `1 (`2 t).
Definition triple_nat {C B : Category} (t : ArrowTriple C B) :
  triple_dom t ⟹ triple_cod t := `2 (`2 t).

(** ** Transparent equivalence witnesses for [Functor_Setoid] *)

(* [Functor_Setoid]'s own Equivalence proof is opaque; the
   classification needs to compute with the component families of
   symmetric and transitive witnesses, so they are rebuilt here with
   transparent families and opaque (Qed) naturality parts. *)

Lemma fs_sym_nat {C D : Category} {F G : C ⟶ D} (σ : F ≈ G) :
  ∀ x y (f : x ~{C}~> y),
    fmap[G] f ≈ from (iso_sym (`1 σ y)) ∘ fmap[F] f ∘ to (iso_sym (`1 σ x)).
Proof.
  intros x y f; simpl.
  rewrite (`2 σ x y f).
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- !comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Definition fs_sym {C D : Category} {F G : C ⟶ D} (σ : F ≈ G) : G ≈ F :=
  existT _ (fun c => iso_sym (`1 σ c)) (fs_sym_nat σ).

Lemma fs_trans_nat {C D : Category} {F G K : C ⟶ D}
      (σ : F ≈ G) (σ' : G ≈ K) :
  ∀ x y (f : x ~{C}~> y),
    fmap[F] f ≈ from (iso_compose (`1 σ' y) (`1 σ y)) ∘ fmap[K] f
                  ∘ to (iso_compose (`1 σ' x) (`1 σ x)).
Proof.
  intros x y f; simpl.
  rewrite (`2 σ x y f).
  rewrite (`2 σ' x y f).
  rewrite !comp_assoc.
  reflexivity.
Qed.

Definition fs_trans {C D : Category} {F G K : C ⟶ D}
           (σ : F ≈ G) (σ' : G ≈ K) : F ≈ K :=
  existT _ (fun c => iso_compose (`1 σ' c) (`1 σ c)) (fs_trans_nat σ σ').

Lemma fs_refl_nat {C D : Category} (F : C ⟶ D) :
  ∀ x y (f : x ~{C}~> y),
    fmap[F] f ≈ from (@iso_id D (F y)) ∘ fmap[F] f ∘ to (@iso_id D (F x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Definition fs_refl {C D : Category} (F : C ⟶ D) : F ≈ F :=
  existT _ (fun c => iso_id) (fs_refl_nat F).

(** ** The triple setoid *)

Program Definition ArrowTriple_Setoid {C B : Category} :
  Setoid (ArrowTriple C B) := {|
  equiv := fun t u =>
    { σ : triple_dom t ≈ triple_dom u
    & { ρ : triple_cod t ≈ triple_cod u
      & ∀ c, @equiv _ (@homset B (triple_dom t c) (triple_cod u c))
               (to (`1 ρ c) ∘ triple_nat t c)
               (triple_nat u c ∘ to (`1 σ c)) } }
|}.
Next Obligation.
  intros C B; constructor.
  - (* reflexivity *)
    intro t.
    exists (fs_refl _), (fs_refl _).
    intro c; simpl; cat.
  - (* symmetry *)
    intros t u (σ & ρ & compat).
    exists (fs_sym σ), (fs_sym ρ).
    intro c; simpl.
    rewrite <- id_right.
    rewrite <- (iso_to_from (`1 σ c)); simpl.
    rewrite comp_assoc.
    rewrite <- (comp_assoc _ (triple_nat u c)).
    rewrite <- compat.
    rewrite !comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - (* transitivity *)
    intros t u v (σ & ρ & compat) (σ' & ρ' & compat').
    exists (fs_trans σ σ'), (fs_trans ρ ρ').
    intro c; simpl.
    rewrite <- comp_assoc.
    rewrite compat.
    rewrite comp_assoc.
    rewrite compat'.
    rewrite comp_assoc.
    reflexivity.
Qed.

(** ** Ex. 7 forward: reading a triple off a functor into [Arrow B] *)

Definition Arrow_dom {C B : Category} (H : C ⟶ @Arrow B) : C ⟶ B :=
  comma_proj1 ◯ H.

Definition Arrow_cod {C B : Category} (H : C ⟶ @Arrow B) : C ⟶ B :=
  comma_proj2 ◯ H.

(* The arrows H picks out, assembled into a transformation: the
   component at c is the arrow part of the object H c, and naturality
   is exactly the square that is the morphism part of H.  This is the
   whiskering of Construction/Comma.v's [comma_proj_nat] along H — the
   two agree componentwise — built directly because [comma_proj_nat]'s
   transform is a tactic-synthesized match on the destructured comma
   object, which does not reduce at an opaque [H c]. *)
Program Definition Arrow_generic {C B : Category} (H : C ⟶ @Arrow B) :
  Arrow_dom H ⟹ Arrow_cod H := {|
  transform := fun c => `2 (H c)
|}.
Next Obligation.
  intros C B H x y f; simpl.
  symmetry.
  exact (`2 (fmap[H] f)).
Qed.
Next Obligation.
  intros C B H x y f; simpl.
  exact (`2 (fmap[H] f)).
Qed.

(* Boundary lemmas: the generic arrow's component at c runs from the
   projected domain to the projected codomain, definitionally. *)
Lemma Arrow_dom_boundary {C B : Category} (H : C ⟶ @Arrow B) (c : C) :
  Arrow_dom H c = fst (`1 (H c)).
Proof. reflexivity. Qed.

Lemma Arrow_cod_boundary {C B : Category} (H : C ⟶ @Arrow B) (c : C) :
  Arrow_cod H c = snd (`1 (H c)).
Proof. reflexivity. Qed.

Definition Arrow_extract {C B : Category} (H : C ⟶ @Arrow B) :
  ArrowTriple C B :=
  (Arrow_dom H; (Arrow_cod H; Arrow_generic H)).

(** ** Ex. 7 inverse: the classifying functor of a transformation *)

(* A natural transformation materializes as a functor into the arrow
   category: objects go to components, morphisms to naturality
   squares. *)
Program Definition Arrow_intro {C B : Category} (t : ArrowTriple C B) :
  C ⟶ @Arrow B := {|
  fobj := fun c => ((triple_dom t c, triple_cod t c); triple_nat t c);
  fmap := fun x y f =>
    ((fmap[triple_dom t] f, fmap[triple_cod t] f); _)
|}.
Next Obligation.
  intros C B t x y f; simpl.
  symmetry.
  apply (naturality[triple_nat t]).
Qed.
Next Obligation.
  intros C B t x y f g Hfg; simpl; split.
  - now rewrite Hfg.
  - now rewrite Hfg.
Qed.
Next Obligation.
  intros C B t c; simpl; split.
  - apply fmap_id.
  - apply fmap_id.
Qed.
Next Obligation.
  intros C B t x y z f g; simpl; split.
  - apply fmap_comp.
  - apply fmap_comp.
Qed.

(** ** Component isomorphisms for the classification *)

(* An isomorphism of arrow objects projects to isomorphisms of the two
   boundaries; its to-square is the intertwining.  (Cf.
   Construction/Comma.v's [comma_proj_mor_iso], which packages the
   same content as a single isomorphism in the product category.) *)
Program Definition Arrow_proj_dom_iso {B : Category} {a b : @Arrow B}
        (i : a ≅ b) : fst (`1 a) ≅ fst (`1 b) := {|
  to   := fst (`1 (to i));
  from := fst (`1 (from i))
|}.
Next Obligation.
  intros B a b i; exact (fst (iso_to_from i)).
Qed.
Next Obligation.
  intros B a b i; exact (fst (iso_from_to i)).
Qed.

Program Definition Arrow_proj_cod_iso {B : Category} {a b : @Arrow B}
        (i : a ≅ b) : snd (`1 a) ≅ snd (`1 b) := {|
  to   := snd (`1 (to i));
  from := snd (`1 (from i))
|}.
Next Obligation.
  intros B a b i; exact (snd (iso_to_from i)).
Qed.
Next Obligation.
  intros B a b i; exact (snd (iso_from_to i)).
Qed.

Lemma Arrow_extract_dom_nat {C B : Category} {H H' : C ⟶ @Arrow B}
      (Θ : ∀ c, H c ≅ H' c)
      (Θnat : ∀ x y (f : x ~{C}~> y),
          fmap[H] f ≈ from (Θ y) ∘ fmap[H'] f ∘ to (Θ x)) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_dom H] f
      ≈ from (Arrow_proj_dom_iso (Θ y)) ∘ fmap[Arrow_dom H'] f
          ∘ to (Arrow_proj_dom_iso (Θ x)).
Proof.
  intros x y f; exact (fst (Θnat x y f)).
Qed.

Lemma Arrow_extract_cod_nat {C B : Category} {H H' : C ⟶ @Arrow B}
      (Θ : ∀ c, H c ≅ H' c)
      (Θnat : ∀ x y (f : x ~{C}~> y),
          fmap[H] f ≈ from (Θ y) ∘ fmap[H'] f ∘ to (Θ x)) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_cod H] f
      ≈ from (Arrow_proj_cod_iso (Θ y)) ∘ fmap[Arrow_cod H'] f
          ∘ to (Arrow_proj_cod_iso (Θ x)).
Proof.
  intros x y f; exact (snd (Θnat x y f)).
Qed.

(* Boundary isomorphisms intertwining the transformations assemble into
   an isomorphism of the classifying functors' values. *)
Program Definition Arrow_intro_component_iso {C B : Category}
        {t u : ArrowTriple C B}
        (σ : triple_dom t ≈ triple_dom u) (ρ : triple_cod t ≈ triple_cod u)
        (compat : ∀ c, @equiv _ (@homset B (triple_dom t c) (triple_cod u c))
                    (to (`1 ρ c) ∘ triple_nat t c)
                    (triple_nat u c ∘ to (`1 σ c)))
        (c : C) :
  @Isomorphism (@Arrow B) (Arrow_intro t c) (Arrow_intro u c) := {|
  to   := ((to (`1 σ c), to (`1 ρ c)); _);
  from := ((from (`1 σ c), from (`1 ρ c)); _)
|}.
Next Obligation.
  intros C B t u σ ρ compat c; simpl.
  symmetry; apply compat.
Qed.
Next Obligation.
  (* the reverse square, by conjugating the intertwining with inverses *)
  intros C B t u σ ρ compat c; simpl.
  transitivity ((`1 ρ c)⁻¹ ∘ ((`1 ρ c ∘ triple_nat t c) ∘ (`1 σ c)⁻¹)).
  - rewrite !comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - rewrite (compat c).
    rewrite <- (comp_assoc (triple_nat u c)).
    rewrite iso_to_from, id_right.
    reflexivity.
Qed.
Next Obligation.
  intros C B t u σ ρ compat c; split; simpl.
  - apply (iso_to_from (`1 σ c)).
  - apply (iso_to_from (`1 ρ c)).
Qed.
Next Obligation.
  intros C B t u σ ρ compat c; split; simpl.
  - apply (iso_from_to (`1 σ c)).
  - apply (iso_from_to (`1 ρ c)).
Qed.

(* Introduction after extraction differs from the original only by
   sigT/pair eta, repaired by the identity-legged square. *)
Program Definition Arrow_eta_iso {C B : Category} (H : C ⟶ @Arrow B)
        (c : C) :
  @Isomorphism (@Arrow B) (Arrow_intro (Arrow_extract H) c) (H c) := {|
  to   := ((id, id); _);
  from := ((id, id); _)
|}.
Next Obligation.
  intros C B H c; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; split; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; split; simpl; cat.
Qed.

(** ** The classification *)

(* Ex. 7 as a bijection: functors into the arrow category, up to
   natural isomorphism, are exactly transformation triples up to
   componentwise natural isomorphism intertwining the
   transformations. *)
Program Definition Arrow_classification (C B : Category) :
  ({| carrier := C ⟶ @Arrow B;
      is_setoid := @Functor_Setoid C (@Arrow B) |} : SetoidObject)
    ≅[Sets]
  {| carrier := ArrowTriple C B;
     is_setoid := @ArrowTriple_Setoid C B |} := {|
  to   := {| morphism := fun H => Arrow_extract H |};
  from := {| morphism := fun t => Arrow_intro t |}
|}.
Next Obligation.
  (* to respects ≈: a natural iso of functors into Arrow B projects to
     boundary isos, and its squares are the intertwining *)
  intros C B H H' (Θ & Θnat).
  exists (existT _ (fun c => Arrow_proj_dom_iso (Θ c))
                 (Arrow_extract_dom_nat Θ Θnat)).
  exists (existT _ (fun c => Arrow_proj_cod_iso (Θ c))
                 (Arrow_extract_cod_nat Θ Θnat)).
  intro c; simpl.
  exact (symmetry (`2 (to (Θ c)))).
Qed.
Next Obligation.
  (* from respects ≈: boundary isos with intertwining assemble into a
     natural iso of classifying functors, componentwise squares *)
  intros C B t u (σ & ρ & compat).
  exists (fun c => Arrow_intro_component_iso σ ρ compat c).
  intros x y f; split; simpl.
  - exact (`2 σ x y f).
  - exact (`2 ρ x y f).
Qed.
Next Obligation.
  (* to ∘ from ≈ id on triples: extraction after introduction is
     definitional on every component *)
  intros C B t.
  exists (fs_refl _), (fs_refl _).
  intro c; simpl; cat.
Qed.
Next Obligation.
  (* from ∘ to ≈ id on functors: introduction after extraction differs
     only by sigT/pair eta, repaired by identity-legged squares *)
  intros C B H.
  exists (fun c => Arrow_eta_iso H c).
  intros x y f; split; simpl; cat.
Qed.
