Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Comma.

Context {A B C : Category}.

Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

(** The comma category (S ↓ T) of two functors with common codomain. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Given functors S : A ⟶ C and T : B ⟶ C, the comma category S ↓ T has as
   objects the triples (a, b, h) of objects a : A and b : B together with a
   morphism h : S a ~> T b in C; here a triple is encoded as the dependent
   pair (∃ p : A ∏ B, S (fst p) ~> T (snd p)), so `1 x is the pair (a, b) and
   `2 x is the mediating morphism h. A morphism (a, b, h) ~> (a', b', h') is a
   pair of morphisms (f : a ~> a' in A, g : b ~> b' in B) making the square

       S a  --h-->  T b
        |            |
      S f           T g           commute, i.e.  h' ∘ S f ≈ T g ∘ h.
        v            v
       S a' --h'--> T b'

   Identity is (id, id) and composition is componentwise, (f, g) ∘ (f', g') :=
   (f ∘ f', g ∘ g'); both laws hold because they hold in A and B. Equivalence
   of morphisms is the componentwise conjunction of ≈ in A and ≈ in B (the
   commuting-square proof component is irrelevant to equality).

   The construction is due to Lawvere (1963), who used a comma punctuation mark
   for it; the name persists even though the modern notation is the arrow ↓.

   Special cases: taking S = T = Id[C] gives the arrow category C^→, whose
   objects are the morphisms of C and whose morphisms are commuting squares;
   taking S = Id[C] and T = Δ(c) the constant functor at c : C gives the slice
   C/c (see Construction/Slice.v, where C ̸ c ≅ (Id ↓ =(c)) is proven); dually
   S = Δ(c), T = Id[C] gives the coslice c/C. The projection functors below,
   comma_proj1 : S ↓ T ⟶ A and comma_proj2 : S ↓ T ⟶ B, recover a and b, and
   comma_proj_nat is the natural transformation S ◯ comma_proj1 ⟹ T ◯
   comma_proj2 whose component at (a, b, h) is h. Comma categories characterize
   adjunctions and universal arrows: a universal arrow from S to T is an
   initial object of the appropriate comma category. *)

(* Reification, the adjoint functor theorems, and gluing

   nLab: https://ncatlab.org/nlab/show/comma+object
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab: https://ncatlab.org/nlab/show/scone

   The construction first appeared as an unnamed auxiliary device in
   Lawvere's thesis (Lawvere, "Functorial Semantics of Algebraic Theories",
   Columbia University PhD thesis 1963; summarized in Proc. Nat. Acad. Sci.
   50 (1963), 869-872; republished with an author's commentary as Reprints
   in Theory and Applications of Categories 5, 2004), where it serves to
   characterize adjoint functors.  The original notation (S, T) generalizes
   the hom-set notation C(x, y), and the nLab records that the name is a
   holdover from that punctuation.  Wikipedia notes that the device became
   generally known only many years later; its textbook treatment is
   section II.6 of Mac Lane, "Categories for the Working Mathematician"
   (Springer GTM 5; 2nd ed. 1998).

   What the definition provides is reification.  A morphism between an
   S-image and a T-image becomes an OBJECT of the category [Comma], so that
   universal properties quantified over morphisms become initial-object
   properties quantified over objects, where the general machinery of this
   library applies.  Beyond the special cases named above, the category of
   cones over a diagram F is the comma Δ ↓ F (Instance/Cones/Comma.v), the
   product category A ∏ B is the comma of two functors into the terminal
   category (Construction/Product/Comma.v), and natural transformations
   S ⟹ T correspond to functors A ⟶ (S ↓ T) sectioning both projections —
   an observation Wikipedia credits to Huq, an exercise in Mac Lane —
   formalized in Construction/Comma/Natural/Transformation.v.  Invariance
   of S ↓ T under natural isomorphism of S and T is
   Construction/Comma/Isomorphism.v.

   The adjunction story that motivated the definition is carried through
   in-tree at each of its historical layers.  A universal arrow from d to U
   is an initial object of =(d) ↓ U, and a family of them assembles into an
   adjunction (Theory/Universal/Arrow.v, [AdjunctionFromUniversalArrows]).
   Lawvere's own criterion — F ⊣ G precisely when (F ↓ Id) ≅ (Id ↓ G)
   compatibly with the projections, which Wikipedia reports as the original
   motivation for the construction — is packaged as [lawvere_equiv] in
   Construction/Comma/Adjunction.v.  Freyd's General Adjoint Functor
   Theorem (Freyd, "Abelian Categories", Harper & Row 1964, exercises of
   chapter 3; reprinted as TAC Reprints 3, 2003) reduces the existence of a
   left adjoint to U to an initial object in each =(d) ↓ U; the library
   executes exactly this route in Adjunction/GAFT.v ([GAFT_from_initials],
   [GAFT]), with completeness of the comma category supplied by
   [Comma_Complete] in Construction/Comma/Limit.v, where the projection
   [comma_proj2] creates the limits.  Creation of limits in comma
   categories was studied early by Pellegrino (two papers, Riv. Mat. Univ.
   Parma 3 and Atti Sem. Mat. Fis. Univ. Modena 23, both 1974).

   Two further readings locate the construction in the wider theory.
   Viewed 2-categorically, [Comma] is the strict comma object of the
   cospan A ⟶ C ⟵ B in Cat — the instance that gives the general notion
   its name — and comma objects are PIE-limits, constructible from
   pullbacks and the power C^2 (nLab, "comma object").  Viewed logically,
   the Freyd cover, or scone, of a category T is the comma Set ↓ Γ over
   the global-sections functor Γ := T(1, −); gluing arguments through it
   prove the disjunction and existence properties of intuitionistic
   higher-order logic (Lambek and Scott 1980; Freyd and Scedrov,
   "Categories, Allegories", North-Holland 1990; Johnstone, "Sketches of
   an Elephant", C3.6), and Artin gluing generalizes this: when a functor
   f between topoi preserves pullbacks, the comma category Id ↓ f is
   again a topos (nLab, "comma category").  In programming-language
   theory the same gluing underlies logical-relations proofs.  Finally,
   Rydeheard and Burstall ("Computational Category Theory", Prentice Hall
   1988, section 5.2) read the comma category as a program-construction
   device: given code once for [Comma], colimit algorithms for derived
   categories such as graphs are inherited from colimit algorithms for
   their ingredients. *)

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma : Category := {|
  (* objects: triples (a, b, h : S a ~> T b) *)
  obj     := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p);
  (* morphisms: pairs (f, g) with the commuting square h' ∘ S f ≈ T g ∘ h *)
  hom     := fun x y =>
    ∃ f : (fst (`1 x) ~{A}~> fst (`1 y)) * (snd (`1 x) ~{B}~> snd (`1 y)),
      `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x;
  (* equivalence: componentwise ≈ in A and B (square proof is irrelevant) *)
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);    (* identity (id_a, id_b) *)
  (* composition is componentwise (f ∘ f', g ∘ g') *)
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros.
  simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ?; simpl.
  intros [[]] [[]]; simpl in *.
  rewrite !fmap_comp.
  rewrite comp_assoc.
  rewrites.
  rewrite <- !comp_assoc.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation.
  intros; simpl.
  split; now rewrite id_left.
Qed.
Next Obligation.
  intros. simpl.
  split; now rewrite id_right.
Qed.
Next Obligation.
  intros.
  simpl.
  split; apply comp_assoc.
Qed.
Next Obligation.
  intros. simpl.
  split; apply comp_assoc_sym.
Qed.

Program Instance comma_proj  : Comma ⟶ A ∏ B := {|
  fobj := fun x => ``x;
  fmap := fun _ _ f => ``f
|}.
Next Obligation.
  intros ? ? ? ? [e0 e1].
  now split.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj1 : Comma ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj2 : Comma ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

#[local] Obligation Tactic := cat_simpl.

Program Instance comma_proj_nat : S ◯ comma_proj1 ⟹ T ◯ comma_proj2.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_mor_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y → `1 x ≅[A ∏ B] `1 y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Defined.

Theorem comma_proj_com_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  ∀ iso : x ≅ y,
    `2 x ≈ fmap[T] (snd `1 (from iso)) ∘ `2 y ∘ fmap[S] (fst `1 (to iso)).
Proof.
  intros.
  pose proof (iso_from_to iso); simpl in X.
  destruct (from iso), x0; simpl in *.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst X).
  cat.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(* The "cocomma" defined here is the comma category formed in the opposite
   categories, @Comma (B^op) (A^op) (C^op) (T^op) (S^op). Since the comma of
   opposite functors is the opposite of the comma, this is (S ↓ T)^op up to
   isomorphism: it dualizes S ↓ T by reversing every arrow. Note this is the
   pointwise/op dual and is NOT the cocomma *object* of nLab (the colimit-side
   dual, a.k.a. the collage), which is a genuinely different construction. *)
Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
