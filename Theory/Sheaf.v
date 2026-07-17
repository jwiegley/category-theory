Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(** * Presheaves, sites (coverages), and sheaves *)

(* nLab: https://ncatlab.org/nlab/show/presheaf
   Wikipedia: https://en.wikipedia.org/wiki/Presheaf_(category_theory)

   A C-valued presheaf on a category U is a functor U^op ⟶ C; the classical
   case takes C := Sets. Its action fmap[X] f on a morphism f : a ~> b of U is
   the restriction map X(b) → X(a). Presheaves on U form the functor category
   [U^op, C], and a copresheaf is the covariant variant U ⟶ C (a presheaf on
   U^op). *)

(* nLab: https://ncatlab.org/nlab/show/site
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_topology

   A site is a category C equipped with a coverage J, which assigns to each
   object u a collection of covering families { fᵢ : uᵢ ~> u } subject to the
   pullback-stability axiom: for any covering family of u and any g : v ~> u
   there is a covering family { hⱼ : vⱼ ~> v } of v such that every composite
   g ∘ hⱼ factors through some fᵢ (i.e. fᵢ ∘ k ≈ g ∘ hⱼ for some k). *)

(* nLab: https://ncatlab.org/nlab/show/sheaf
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   A presheaf X : C^op ⟶ Sets is a sheaf for a covering family
   { fᵢ : uᵢ ~> u } when every matching (compatible) family of local sections
   xᵢ ∈ X(uᵢ) — sections agreeing on overlaps, X(g)(xᵢ) ≈ X(h)(xⱼ) whenever
   fᵢ ∘ g ≈ fⱼ ∘ h — glues to a unique global section x ∈ X(u) with
   X(fᵢ)(x) ≈ xᵢ for all i (existence is the gluing axiom, uniqueness is the
   separated/locality axiom). A separated presheaf asks only for uniqueness. *)

(* Where sheaves come from, and what they are for

   nLab:      https://ncatlab.org/nlab/show/sheaf
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+topology
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   A sheaf is the systematic bookkeeping of the passage from local data
   to global data.  A presheaf already assigns data to each object and,
   through the restriction maps that are the contravariant action of a
   [Presheaf], cuts that data down along morphisms; the sheaf condition
   adds the discipline that makes the data behave like genuine sections
   on a space.  Two clauses carry it.  Gluing, the existence clause, asks
   that local sections on a cover which agree on their overlaps determine
   an actual global section; locality, or separatedness, the uniqueness
   clause, asks that a section be fixed by its restrictions to a cover,
   so that two sections agreeing locally everywhere coincide (Wikipedia,
   "Sheaf (mathematics)").  Equivalently, the value over a covered object
   is the limit — an equalizer — of the values on the cover, so the sheaf
   condition IS a descent condition (nLab, "sheaf").  This is the content
   a mere presheaf may lack, and [restriction] is what the in-tree
   [Sheaf] class records over the single [coverage] family that a [Site]
   supplies; the header above and Theory/Sheaf/Category.v disclose that
   this per-object, per-leg encoding is a deliberately scoped
   approximation of the classical predicate.

   The subject has a dated origin.  Jean Leray, held as a prisoner of war
   in Oflag XVII-A from 1940 to 1945, there developed sheaves, sheaf
   cohomology, and spectral sequences, coining "faisceau" in his 1946
   Comptes Rendus notes (Haynes Miller, "Leray in Oflag XVIIA: The
   origins of sheaf theory, sheaf cohomology, and spectral sequences").
   Henri Cartan's seminar then reworked the notion through étalé spaces,
   Serre carried it into algebraic geometry as coherent sheaves (Serre,
   "Faisceaux Algébriques Cohérents", Annals of Mathematics 1955), and
   Godement fixed the standard formalism (Godement, "Topologie
   algébrique et théorie des faisceaux", 1958).  To do cohomology on
   schemes, where the Zariski topology is too coarse, and to attack the
   Weil conjectures, Grothendieck replaced open covers by covering
   families in an abstract category — a Grothendieck topology, hence a
   site — first as a pretopology in Artin's 1962 Harvard notes and then
   through sieves in SGA 4 (nLab, "Grothendieck topology").

   The utility runs well past geometry.  For a site the sheaves form a
   Grothendieck topos: a reflective, left-exact localization of a
   presheaf topos, carrying a subobject classifier and an internal
   higher-order intuitionistic logic whose truth values form a Heyting
   algebra rather than two points (Mac Lane, Moerdijk, "Sheaves in
   Geometry and Logic: A First Introduction to Topos Theory", Springer
   1992).  Such a topos is read as the sheaf theory of a generalized
   space, and for a subcanonical topology the Yoneda map composed with
   sheafification embeds that space fully faithfully into its own sheaves
   (nLab, "Grothendieck topology").  Fong and Spivak model a behavior
   type as a sheaf on a space of time, where a truth value is the open
   set of times on which a property holds and safety becomes a statement
   of temporal logic (Fong, Spivak, "Seven Sketches in Compositionality",
   Cambridge UP 2019, Ch. 7).  Abramsky and Brandenburger recast quantum
   non-locality and contextuality as the obstruction to a global section
   of a sheaf of local empirical models, grading the Bell, Hardy, and GHZ
   arguments in a hierarchy (Abramsky, Brandenburger, "The
   Sheaf-Theoretic Structure of Non-Locality and Contextuality", New
   Journal of Physics 2011).

   The split carries a type-theoretic reading.  A presheaf is a family of
   local states indexed by objects, its restriction a contravariant
   reindexing; the sheaf condition is then a descent obligation, taking a
   cover-indexed tuple of locally consistent pieces to a unique whole —
   the agree-on-overlaps merge discipline of distributed data.  The
   in-tree [Site] and [Sheaf] classes make that obligation a proof
   obligation whose covering and matching data carry computational
   witnesses, which is why the file states them over the Type-valued
   [ForallT] and [ExistsT] rather than the Prop-valued vector predicates.
   The other half of the story is sheafification: every presheaf reflects
   into a sheaf, the inclusion into presheaves having a left-exact left
   adjoint (Wikipedia, "Sheaf (mathematics)"; nLab, "sheaf").  That
   reflection is the piece deferred here (ledger 1), though
   Theory/Sheaf/Category.v already builds Sheaves C as the full
   subcategory of presheaves cut out by [Sheaf].  Presheaf categories
   themselves recur across the library: the free cocompletion and target
   of the Yoneda embedding (Instance/Fun.v, Functor/Hom/Yoneda.v), the
   subobject presheaf feeding the classifier (Theory/Subobject/Functor.v),
   and the elementary topos development (Structure/Topos.v). *)

(* A C-valued presheaf on some category U.
  C is often taken to be Sets. *)
Definition Presheaf (U C : Category) := U^op ⟶ C.

(* The category of C-valued presheaves on a category U. *)
Definition Presheaves {U C : Category} := [U^op, C].

(* A C-valued copresheaf on U: a covariant functor, i.e. a presheaf on U^op. *)
Definition Copresheaf (U C : Category) := U ⟶ C.

(* The category of C-valued copresheaves on a category U. *)
Definition Copresheaves {U C : Category} := [U, C].

(* Custom data type to express Forall propositions on vectors over Type. *)
Inductive ForallT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ForallT_nil : ForallT (nil A)
  | ForallT_cons (n : nat) (x : A) (v : t A n) :
    P x → ForallT v → ForallT (cons A x n v).

(* Likewise the Type-valued analogue of Vector.Exists, carrying witness data. *)
Inductive ExistsT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ExistsT_cons_hd (m : nat) (x : A) (v : t A m) :
    P x → ExistsT (cons A x m v)
  | ExistsT_cons_tl (m : nat) (x : A) (v : t A m) :
    ExistsT v → ExistsT (cons A x m v).

(* A coverage on a category C consists of a function assigning to each object
   U ∈ C a collection of families of morphisms { fᵢ : Uᵢ → U } (i∈I), called
   covering families, such that

   if { fᵢ : Uᵢ → U } (i∈I) is a covering family
   and g : V → U is a morphism,
   then there exists a covering family { hⱼ : Vⱼ → V }
   such that each composite g ∘ hⱼ factors through some fᵢ. *)

Class Site (C : Category) := {
  (* A covering family of u is a finite (vector-indexed) list of morphisms
     uᵢ ~> u into u; sigT packages the length together with the vector. *)
  covering_family (u : C) := sigT (Vector.t (∃ uᵢ, uᵢ ~> u));

  (* This encoding picks a single covering family per object rather than the
     usual collection of covering families; it suffices to state the sheaf
     condition below, but is less general than a full coverage. *)
  coverage (u : C) : covering_family u;

  (* The coverage axiom (pullback stability), per the site reference above. *)
  coverage_condition
    (u  : C) (fs : covering_family u)
    (v  : C) (g  : v ~> u) :
    ∃ hs : covering_family v,
      ForallT (A := ∃ vⱼ, vⱼ ~> v) (λ '(vⱼ; hⱼ),
          ExistsT (A := ∃ uᵢ, uᵢ ~> u) (λ '(uᵢ; fᵢ),
              ∃ k : vⱼ ~> uᵢ, fᵢ ∘ k ≈ g ∘ hⱼ)
            (`2 fs))
        (`2 hs)
}.

(* If { fᵢ : Uᵢ → U } (i∈I) is a family of morphisms with codomain U,
   a presheaf X : Cᵒᵖ → Set is called a sheaf for this family if:

   for any collection of elements xᵢ ∈ X(Uᵢ)
   such that,
     whenever g : V → Uᵢ and h : V → Uⱼ
     are such that fᵢ ∘ g = fⱼ ∘ h,
     we have X(g)(xᵢ) = X(h)(xⱼ),
   then there exists a unique x ∈ X(U)
   such that X(fᵢ)(x) = xᵢ for all i . *)

Class Sheaf `{@Site C} (X : Presheaf C Sets) := {
  restriction :
    ∀ u : C,
      let '(i; f) := coverage u in
      ForallT
        (A := ∃ uᵢ, uᵢ ~> u)
        (λ '(uᵢ; fᵢ),
            ∀ xᵢ : X uᵢ,
              (∀ (v : C) (g : v ~> uᵢ),
                  ForallT
                    (A := ∃ uⱼ, uⱼ ~> u)
                    (λ '(uⱼ; fⱼ),
                      ∀ h : v ~> uⱼ,
                        fᵢ ∘ g ≈ fⱼ ∘ h →
                        ∀ xⱼ : X uⱼ,
                          fmap[X] g xᵢ ≈ fmap[X] h xⱼ)
                    f) →
              ∃! x : X u, fmap[X] fᵢ x ≈ xᵢ)
        f
}.
