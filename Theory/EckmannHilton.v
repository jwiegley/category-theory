Require Import Category.Lib.

Generalizable All Variables.

(** * The Eckmann–Hilton argument *)

(* nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument
   Paper:     Eckmann, Hilton, "Group-like structures in general categories
              I. Multiplications and comultiplications", Mathematische
              Annalen 145, 1962
   Paper:     Eckmann, Hilton, "Structure maps in group theory", Fundamenta
              Mathematicae 50, 1961 (Theorem 1.12)
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.5 Exercise 5 (printed p. 45)

   Suppose one carrier bears two binary operations, each with a two-sided
   unit, and suppose the two operations INTERCHANGE: evaluating a 2x2 array
   rows-first agrees with evaluating it columns-first,

       f (g a b) (g c d)  ≈  g (f a c) (f b d).

   Then the two units coincide, the two operations coincide, and the single
   operation that remains is commutative and associative.  Nothing else is
   assumed — no associativity, no commutativity, not even that either
   operation is a monoid on its own.  Both laws are OUTPUTS.

   This file states and proves exactly that, over a bare setoid.  It is
   deliberately PRE-CATEGORICAL: its only import is [Category.Lib], and in
   particular it does not import [Category.Theory.Category].  The argument
   never mentions objects, morphisms, or composition; it is a fact about a
   set with two interchanging unital operations, and the categorical
   instances below are instances, not the content. *)

(* Where the argument comes from, and what it is used for

   Eckmann and Hilton isolated the principle while studying H-spaces and
   the dual "H-cospaces": a space with a multiplication and a
   comultiplication that are compatible in the above sense has an abelian
   fundamental structure.  The 1961 paper in Fundamenta Mathematicae proves
   it for group-like structure maps (Theorem 1.12); the 1962 Mathematische
   Annalen paper generalises multiplications and comultiplications to an
   arbitrary category.  The argument is now folklore, and it explains a
   long list of otherwise unrelated facts:

   - The higher homotopy groups π_n(X, x) for n ≥ 2 are abelian.  Two
     concatenations of n-cubes are available in that range (along any two
     of the n coordinate directions), they share the constant map as unit,
     and they interchange because the two directions are independent.

   - A monoid object in the category of monoids is a commutative monoid;
     a group object in Grp is an abelian group.  The ambient
     multiplication and the internal one interchange because the internal
     one is a homomorphism for the ambient one.  This is the reason the
     tower of "monoids in monoids in ..." collapses at the second rung, so
     that further categorification must add BRAIDING rather than a further
     multiplication.

   - The endomorphisms of an identity — 2-cells on an identity 1-cell in a
     2-category, the endomorphism monoid of the unit object of a monoidal
     category — form a COMMUTATIVE monoid.  (In this tree "the centre of a
     monoidal category" names the Drinfeld or premonoidal centres,
     Structure/Monoidal/Drinfeld.v — categories, not monoids — so that
     phrase is deliberately avoided here.)  Vertical and
     horizontal composition of such cells interchange (that is the middle
     four interchange law) and there they genuinely share a unit, which is
     precisely the special position that makes the collapse bite.

   In this library the principle is cited in several background essays and
   is now proved once here:

   - Structure/Semiadditive.v derives commutativity and associativity of
     the convolution addition on hom-setoids from the interchange law
     between its two convolutions [conv] and [conv_pr]; those three
     lemmas ([conv_conv_pr], [conv_comm], [conv_assoc]) are instances of
     this file's [eh_ops], [eh_comm] and [eh_assoc].
   - Instance/Cat/TwoCategory.v's [NatBase_centre] exhibits the collapse
     concretely: the 2-cells on the identity functor of the delooping of
     (ℕ, +) compose to the same thing vertically and horizontally, and
     both composites compute to addition (by [eq_refl]).
   - Theory/TwoCategory.v (:148, :169) explains why a 2-category does not
     degenerate: its two compositions have DIFFERENT units in general, so
     the argument only bites where the units collapse.
   - Structure/Monoid.v:90 (the microcosm remark), Structure/Group.v:73
     (group objects in Grp are abelian), Structure/Abelian.v:124,
     Structure/Monoidal/Braided.v:90 and Structure/Monoidal/Proofs.v:339
     all appeal to the principle in prose.

   SCOPE, stated precisely.  The theorem below takes SEPARATE units, one
   for each operation, and DERIVES their coincidence ([eh_units]).  That is
   strictly more general than the in-tree instance it now serves:
   Structure/Semiadditive.v's two convolutions both have [zero_mor] as
   unit, so the coincidence there is [reflexivity] and that file never
   needed the lemma.  A reader who only wants the common-unit form may
   instantiate with [ug := uf] and ignore [eh_units].

   The hypotheses are Section variables rather than fields of a class, so
   after [End] every lemma below takes them as explicit arguments.  That is
   the intended interface: a consumer supplies its two operations, its two
   units, the four unit laws and the interchange law, and reads off the
   conclusions. *)

(* Lib.v sets [Default Proof Using "Type"], which keeps only the Section
   variables occurring in a lemma's STATEMENT.  Every statement here
   mentions only [f], [g], [uf] and [ug]; the respectfulness, unit and
   interchange hypotheses are consumed in the PROOFS alone, so they must be
   requested explicitly.  Declaring "All" once is clearer than repeating a
   variable list on each lemma, and it makes the discharged interface
   uniform: every lemma below takes the same seven hypotheses. *)
Local Set Default Proof Using "All".

Section EckmannHilton.

Context {A : Type}.
Context `{sA : Setoid A}.

(* The two operations and their units. *)
Context (f g : A → A → A).
Context (uf ug : A).

(* Both operations respect the carrier's equivalence.  These are stated as
   [Proper] hypotheses so that setoid rewriting can work underneath them.
   They are Section hypotheses, NOT global instances: [Context] registers a
   class-typed binder as a local instance for the duration of the Section,
   which is what makes [rewrite] see them, and at [End] they discharge as
   ordinary EXPLICIT arguments rather than as instances anything downstream
   could resolve by accident. *)
Context (f_respects : Proper (equiv ==> equiv ==> equiv) f).
Context (g_respects : Proper (equiv ==> equiv ==> equiv) g).

(* [uf] is a two-sided unit for [f], and [ug] one for [g].  Note that
   nothing yet relates the two. *)
Context (f_unit_left  : ∀ a, f uf a ≈ a).
Context (f_unit_right : ∀ a, f a uf ≈ a).
Context (g_unit_left  : ∀ a, g ug a ≈ a).
Context (g_unit_right : ∀ a, g a ug ≈ a).

(* The interchange law.  The orientation is the one Structure/Semiadditive.v
   proves for its convolutions ([conv_interchange]): [f] is the operation
   applied LAST on the left and FIRST on the right. *)
Context (interchange : ∀ a b c d, f (g a b) (g c d) ≈ g (f a c) (f b d)).

(* Eckmann–Hilton, step one: the two units coincide.

   Read the interchange law at the array whose entries are the two units
   arranged antidiagonally,

       ( uf  ug )
       ( ug  uf ).

   Evaluating with [g] first collapses both rows to [uf] (because [ug] is
   [g]'s unit), and then [f] collapses [f uf uf] to [uf].  Evaluating with
   [f] first collapses both columns to [ug] (because [uf] is [f]'s unit),
   and then [g] collapses [g ug ug] to [ug].  Interchange says the two
   readings agree. *)
Lemma eh_units : uf ≈ ug.
Proof.
  transitivity (f (g uf ug) (g ug uf)).
  - rewrite g_unit_right, g_unit_left.
    now rewrite f_unit_left.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite g_unit_left.
Qed.

(* With the units identified, [uf] is a two-sided unit for [g] as well, so
   the padding arguments below can be written with a single unit. *)
Lemma eh_common_unit_left (a : A) : g uf a ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_left.
Qed.

Lemma eh_common_unit_right (a : A) : g a uf ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_right.
Qed.

(* Eckmann–Hilton, step two: the two operations coincide.

   In the three chains that follow, [1] abbreviates the common unit — [uf],
   which by [eh_common_unit_left]/[eh_common_unit_right] is now a two-sided
   unit for [g] as well.

   Pad [a] and [b] with the common unit so that both become [g]-composites,
   then push the interchange law through and strip the [f]-units:

       f a b  ≈  f (g a 1) (g 1 b)  ≈  g (f a 1) (f 1 b)  ≈  g a b.       *)
Lemma eh_ops (a b : A) : f a b ≈ g a b.
Proof.
  transitivity (f (g a uf) (g uf b)).
  - now rewrite eh_common_unit_right, eh_common_unit_left.
  - rewrite interchange.
    now rewrite f_unit_right, f_unit_left.
Qed.

(* Eckmann–Hilton, step three: the operation is commutative.

   The same padding, with the units placed on the other side, so that
   interchange transposes the two arguments; the last step is [eh_ops]
   read backwards:

       f a b  ≈  f (g 1 a) (g b 1)  ≈  g (f 1 b) (f a 1)  ≈
       g b a  ≈  f b a.                                                   *)
Lemma eh_comm (a b : A) : f a b ≈ f b a.
Proof.
  transitivity (f (g uf a) (g b uf)).
  - now rewrite eh_common_unit_left, eh_common_unit_right.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite <- eh_ops.
Qed.

(* Eckmann–Hilton, step four: the operation is associative.

   Pad only the first argument, and read interchange in both directions
   around the intermediate term [f (g a 1) (g b c)]:

       f (f a b) c  ≈  g (f a b) (f 1 c)  ≈  f (g a 1) (g b c)  ≈
       f a (g b c)  ≈  f a (f b c).                                       *)
Lemma eh_assoc (a b c : A) : f (f a b) c ≈ f a (f b c).
Proof.
  transitivity (f (g a uf) (g b c)).
  - rewrite interchange.
    rewrite f_unit_left.
    now rewrite <- eh_ops.
  - rewrite eh_common_unit_right.
    now rewrite <- eh_ops.
Qed.

(* The [g]-side readings.  Since the operations coincide these are one
   rewrite away, but they are what a consumer holding only [g] wants. *)
Lemma eh_g_comm (a b : A) : g a b ≈ g b a.
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_comm.
Qed.

Lemma eh_g_assoc (a b c : A) : g (g a b) c ≈ g a (g b c).
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_assoc.
Qed.

(* The theorem, packaged.

   PACKAGING CHOICE: the library's `≈` is a [crelation], i.e. Type-valued,
   so the four conclusions cannot be conjoined with [and].  They are
   conjoined with the library's [∧], which is [prod] (Lib/Foundation.v:78),
   right-associated.  A record was the alternative; a nested product was
   chosen because it needs no new inductive type and its components are
   reachable with the ordinary [fst]/[snd] of a pair.  The four components
   are, in order, [eh_units], [eh_ops], [eh_comm] and [eh_assoc]; the
   [g]-side corollaries are deliberately left out, being immediate from the
   second component. *)
Definition eckmann_hilton :
  (uf ≈ ug)
    ∧ (∀ a b : A, f a b ≈ g a b)
    ∧ (∀ a b : A, f a b ≈ f b a)
    ∧ (∀ a b c : A, f (f a b) c ≈ f a (f b c)) :=
  (eh_units, (eh_ops, (eh_comm, eh_assoc))).

End EckmannHilton.
