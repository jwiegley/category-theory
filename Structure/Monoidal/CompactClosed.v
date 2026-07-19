Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * Compact closed categories *)

(* nLab: https://ncatlab.org/nlab/show/compact+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Compact_closed_category

   A compact closed category is a symmetric monoidal category in which every
   object [X] has a (chosen) dual [X^*], i.e. it is a rigid (autonomous)
   symmetric monoidal category. Symmetry forces the left and right duals to
   coincide, so a single dual [X^*] suffices. The structure comprises:

       dual X       X^*                         (the chosen dual object)
       cc_unit X    η_X : I ~> X^* ⨂ X          (unit / coevaluation / "cup")
       cc_counit X  ε_X : X ⨂ X^* ~> I          (counit / evaluation / "cap")

   subject to the two snake / zigzag (triangle, "yanking") identities. In this
   library's notation, with λ = [unit_left], ρ = [unit_right], α =
   [tensor_assoc], and [to]/[from] the forward/inverse iso components:

     snake_left  (= id[X]):
       λ_X ∘ (ε ⨂ id) ∘ α⁻¹_{X,X^*,X} ∘ (id ⨂ η) ∘ ρ⁻¹_X

     snake_right (= id[X^*]):
       ρ_{X^*} ∘ (id ⨂ ε) ∘ α_{X^*,X,X^*} ∘ (η ⨂ id) ∘ λ⁻¹_{X^*}

   These match the Wikipedia statements λ ∘ (ε⊗id) ∘ α⁻¹ ∘ (id⊗η) ∘ ρ⁻¹ = id_A
   and ρ ∘ (id⊗ε) ∘ α ∘ (η⊗id) ∘ λ⁻¹ = id_{A^*}; the unitors here are folded
   into the identity rather than written as a separate [λ ∘ ρ⁻¹] coherence.

   Compact closed categories are the setting for finite-dimensional vector
   spaces (FdVect), the category Rel of relations, and — once a compatible
   dagger is added (a dagger-compact category) — the ZX-calculus.

   Hypergraph categories are a special case: every object is its own dual via
   [X^* := X], with unit and counit built from the special commutative
   Frobenius (SCFA) structure as [η := δ ∘ η_X] and [ε := ε_X ∘ μ]. *)

(* Duals as internal adjunctions: history, applications, and neighbours

   nLab:  https://ncatlab.org/nlab/show/compact+closed+category
   Paper: Kelly, "Many-variable functorial calculus. I.", in Coherence
          in Categories, Springer LNM 281, 1972
   Paper: Kelly, Laplaza, "Coherence for compact closed categories",
          Journal of Pure and Applied Algebra 19, 1980
   Paper: Abramsky, Coecke, "A categorical semantics of quantum
          protocols", LiCS 2004

   The content of the definition is that every object is an adjoint:
   [cc_unit] and [cc_counit] are the unit and counit of an adjunction
   X ⊣ X^* internal to the monoidal structure, and [snake_left] and
   [snake_right] are its triangle identities.  It follows that the
   category is closed: maps C ⨂ A ~> B correspond naturally to maps
   C ~> B ⨂ A^*, so the internal hom of A and B is representable as
   B ⨂ A^* — the closure the name records (nLab).  The same adjunction
   yields map–state duality: the name of f : A ~> B is the state
   ⌜f⌝ := (id ⨂ f) ∘ η_A : I ~> A^* ⨂ B; every morphism of that type
   is the name of a unique map A ~> B, and duality extends to a
   contravariant functor with A^{**} naturally isomorphic to A
   (Abramsky–Coecke 2004).  A compact closed category is thereby the
   degenerate star-autonomous category whose dualizing object is the
   tensor unit itself (nLab), the model of multiplicative linear logic
   in which ⊗ and ⅋ coincide; the general dualizing-object picture is
   developed in Structure/Monoidal/StarAutonomous.v.

   The notion is due to Kelly (1972, above); its coherence theory is
   Kelly–Laplaza (1980): a well-formed equation in the language of
   compact closed categories follows from the axioms precisely when
   both sides have isomorphic string diagrams.  Selinger's survey ("A
   survey of graphical languages for monoidal categories", 2009)
   states this as its Theorem 4.33, and the caveat after it records
   that Kelly–Laplaza proved the simple-signature case and that the
   fully general case does not appear in the literature.  Coherence is
   what licenses the bent-wire calculus: [cc_unit] creates a pair of
   oppositely oriented wires, [cc_counit] joins such a pair, and the
   snake identities say a bent wire may be pulled straight — whence
   "yanking".  Concretely, in Rel every object is its own dual and η_X
   relates the sole element of the unit to each pair (x, x); in
   FdVect, η_V sends 1 to Σ ē_i ⊗ e_i against a chosen basis, and
   names are exactly the passage between matrices and vectors
   (Abramsky–Coecke 2004).  Dualizability is a finiteness condition:
   FdVect and FdHilb are compact closed while their
   infinite-dimensional counterparts are not even autonomous, and the
   cobordism category under disjoint union is compact closed with
   duals given by orientation reversal (Selinger 2009).

   Every compact closed category carries a canonical trace, and
   conversely the Int construction of Joyal, Street and Verity
   ("Traced monoidal categories", Math. Proc. Camb. Phil. Soc. 119,
   1996) freely completes a traced monoidal category to a compact
   closed one, with composition given by tracing — the categorical
   backbone of Girard's Geometry of Interaction (Abramsky, Haghverdi,
   Scott, "Geometry of Interaction and Linear Combinatory Algebras",
   MSCS 12(5), 2002).  The traced interface in this library is
   Structure/Monoidal/Traced.v; neither bridge is formalized in-tree
   yet.

   The applications track these readings.  Abramsky and Coecke (2004)
   express teleportation and entanglement swapping in any compact
   closed category with biproducts, reading preparation of an
   entangled state as a name and an observational branch as a coname;
   adding a compatible dagger yields the dagger-compact setting named
   by Selinger ("Dagger compact closed categories and completely
   positive maps", ENTCS 170, 2007).  The DisCoCat model of
   natural-language meaning (Coecke, Sadrzadeh, Clark, "Mathematical
   Foundations for a Compositional Distributional Model of Meaning",
   2010) lifts Lambek pregroup type reductions to morphisms
   transforming FdVect word vectors into the meaning of the whole
   sentence.  The structure is also rigid: finite products in a
   compact closed category are automatically biproducts (Houston,
   "Finite products are biproducts in a compact closed category",
   JPAA 212, 2008), and in this library Structure/Monoidal/Collapse.v
   assumes [CompactClosed] over a relevance monoidal category to prove
   Abramsky's no-cloning collapse — uniform copying forces the
   braiding to be the identity.  Downstream of the derivation below,
   Construction/Cospan/Hypergraph.v points its clients at
   [Hypergraph_CompactClosed] for their cups and caps. *)

Section CompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CompactClosed : Type := {
  (* The chosen dual object [X^*] of each object [X]. *)
  dual : C -> C;

  (* Unit / coevaluation ("cup")    η_X : I ~> X^* ⨂ X. *)
  cc_unit   : forall X : C, I ~> dual X ⨂ X;
  (* Counit / evaluation ("cap")    ε_X : X ⨂ X^* ~> I. *)
  cc_counit : forall X : C, X ⨂ dual X ~> I;

  (* Left snake / zigzag, "yanking" the X-strand straight:
       λ ∘ (ε ⨂ id) ∘ α⁻¹ ∘ (id ⨂ η) ∘ ρ⁻¹ ≈ id[X]. *)
  snake_left : forall X : C,
    to (@unit_left C _ X)
      ∘ bimap (cc_counit X) id[X]
      ∘ from (@tensor_assoc C _ X (dual X) X)
      ∘ bimap id[X] (cc_unit X)
      ∘ from (@unit_right C _ X)
    ≈ id[X];

  (* Right snake / zigzag, "yanking" the X^*-strand straight:
       ρ ∘ (id ⨂ ε) ∘ α ∘ (η ⨂ id) ∘ λ⁻¹ ≈ id[X^*]. *)
  snake_right : forall X : C,
    to (@unit_right C _ (dual X))
      ∘ bimap id[dual X] (cc_counit X)
      ∘ to (@tensor_assoc C _ (dual X) X (dual X))
      ∘ bimap (cc_unit X) id[dual X]
      ∘ from (@unit_left C _ (dual X))
    ≈ id[dual X]
}.

End CompactClosed.

Arguments CompactClosed C {S}.
Arguments dual {C S _} X.
Arguments cc_unit {C S _} X.
Arguments cc_counit {C S _} X.

(** * Every hypergraph category is compact closed (self-dual) *)

(* For [X^* := X] we set

      cc_unit X   := δ ∘ η : I ~> X ⨂ X
      cc_counit X := ε ∘ μ : X ⨂ X ~> I

   built from the special commutative Frobenius algebra carried by every
   object of a hypergraph category. The snake identities collapse via the
   Frobenius law together with the monoid unit and comonoid counit laws (see
   the worked proofs below); specialness ([μ ∘ δ ≈ id]) is not needed for the
   snake equations themselves. This construction is not exported as a [Global
   Instance], to avoid typeclass-search blowups: clients opt in via [Existing
   Instance Hypergraph_CompactClosed]. *)

Section HypergraphIsCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* Self-dual unit, given an SCFA on [X]. *)
Definition hcc_unit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : I ~> X ⨂ X := scfa_delta F ∘ scfa_eta F.

(* Self-dual counit, given an SCFA on [X]. *)
Definition hcc_counit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : X ⨂ X ~> I := scfa_epsilon F ∘ scfa_mu F.

End HypergraphIsCompactClosed.

(** * The derivation [Hypergraph C -> CompactClosed C] *)

(* Self-dual: [dual X := X], [cc_unit X := scfa_delta ∘ scfa_eta],
   [cc_counit X := scfa_epsilon ∘ scfa_mu].

   Both snake equations reduce by the same pattern:
     1. Distribute [bimap (ε∘μ) id ≈ bimap ε id ∘ bimap μ id] and dually
        [bimap id (δ∘η) ≈ bimap id δ ∘ bimap id η].
     2. Apply the Frobenius law [frob_law_left] (resp. [frob_law_right])
        to collapse [bimap μ id ∘ α⁻¹ ∘ bimap id δ] to [δ ∘ μ].
     3. Apply the monoid unit law [mu_unit_right] to collapse
        [μ ∘ bimap id η] to [unit_right], cancelling with [unit_right⁻¹].
     4. Apply the comonoid counit law [delta_counit_left] to collapse
        [bimap ε id ∘ δ] to [unit_left⁻¹], cancelling with [unit_left].

   Not exported as a [Global Instance] to avoid typeclass-search blowups;
   clients opt in with [Existing Instance Hypergraph_CompactClosed]. *)

Section HypergraphToCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(* Re-expose the unfoldings of [cc_unit] / [cc_counit] for the self-dual
   construction; these isolate the [scfa_*] form for rewriting. *)
Lemma cc_unit_unfold (X : C) :
  hcc_unit X (F := scfa X) = scfa_delta (scfa X) ∘ scfa_eta (scfa X).
Proof. reflexivity. Qed.

Lemma cc_counit_unfold (X : C) :
  hcc_counit X (F := scfa X) = scfa_epsilon (scfa X) ∘ scfa_mu (scfa X).
Proof. reflexivity. Qed.

(* The snake-left calculation, abstracted away from the iso unfoldings. *)
Lemma hypergraph_snake_left (X : C) :
  to (@unit_left C _ X)
    ∘ bimap (hcc_counit X (F := scfa X)) id[X]
    ∘ from (@tensor_assoc C _ X X X)
    ∘ bimap id[X] (hcc_unit X (F := scfa X))
    ∘ from (@unit_right C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  (* Distribute bimap over the SCFA composites. *)
  rewrite (bimap_comp_id_right (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_left (scfa_delta _) (scfa_eta _)).
  (* Bring frob_law_left into focus: bimap μ id ∘ α⁻¹ ∘ bimap id δ ≈ δ ∘ μ. *)
  (* Currently: unit_left ∘ (bimap ε id ∘ bimap μ id) ∘ α⁻¹
                 ∘ (bimap id δ ∘ bimap id η) ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap (scfa_mu _) id)).
  rewrite (comp_assoc (bimap (scfa_mu _) id ∘ from tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_left (Frobenius := scfa X)).
  (* Now: unit_left ∘ bimap ε id ∘ (δ ∘ μ) ∘ bimap id η ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap id eta)).
  rewrite (mu_unit_right (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  (* Now: unit_left ∘ (bimap ε id ∘ δ) ≈ id. *)
  rewrite (delta_counit_left (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(* The snake-right calculation, symmetric to [snake_left] under [paws]. *)
Lemma hypergraph_snake_right (X : C) :
  to (@unit_right C _ X)
    ∘ bimap id[X] (hcc_counit X (F := scfa X))
    ∘ to (@tensor_assoc C _ X X X)
    ∘ bimap (hcc_unit X (F := scfa X)) id[X]
    ∘ from (@unit_left C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  rewrite (bimap_comp_id_left  (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_right (scfa_delta _) (scfa_eta _)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap id (scfa_mu _))).
  rewrite (comp_assoc (bimap id (scfa_mu _) ∘ to tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_right (Frobenius := scfa X)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap eta id)).
  rewrite (mu_unit_left (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  rewrite (delta_counit_right (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(* The derived compact-closed structure on a hypergraph category.

   [dual X := X] (self-dual), and [cc_unit] / [cc_counit] are the SCFA-derived
   morphisms [hcc_unit] / [hcc_counit]. The snake identities follow from
   [hypergraph_snake_left] and [hypergraph_snake_right]. *)
Program Instance Hypergraph_CompactClosed : @CompactClosed C S := {|
  dual      := fun X => X;
  cc_unit   := fun X => hcc_unit X (F := scfa X);
  cc_counit := fun X => hcc_counit X (F := scfa X);

  snake_left  := hypergraph_snake_left;
  snake_right := hypergraph_snake_right
|}.

End HypergraphToCompactClosed.
