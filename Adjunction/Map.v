Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Maps of adjunctions *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/mate
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
     p. 99: the definition of a map of adjunctions, which the page gives as
     unnumbered prose (catalog id `maclane:IV.7:def1`), and Proposition 1,
     which the page does number in bold.
   Riehl, "Category Theory in Context", §4.2, printed p. 143,
     Exercise 4.2.v (strict morphism of adjunctions).

   Given two adjunctions A : F ⊣ U over (C, D) and A' : F' ⊣ U' over
   (C', D') -- so F : D ⟶ C and U : C ⟶ D, the library's orientation -- a
   MAP OF ADJUNCTIONS from A to A' is a pair of functors K : C ⟶ C' and
   L : D ⟶ D' such that the two squares

       K ◯ F  =  F' ◯ L        (as functors D ⟶ C')
       L ◯ U  =  U' ◯ K        (as functors C ⟶ D')

   commute, together with one further condition on the hom-sets, which
   Mac Lane displays as the commuting square

       C(F x, a)  --φ-->  D(x, U a)
           | K                | L
           v                  v
       C'(K F x, K a)     D'(L x, L U a)
           ||                 ||
       C'(F' L x, K a) --φ'-> D'(L x, U' K a)

   for ALL objects x of D and a of C.  The two double bars are the object
   equalities supplied by the two squares.  [SquaresHom] below is exactly
   that square, quantified over every transposable arrow k : F x ~> a
   rather than evaluated at one distinguished argument.

   LETTERS.  Mac Lane writes K : A → A' and L : X → X', where his F : X → A
   is the left adjoint; so his A is this file's C and his X is this file's
   D, and the names [sq_K] and [sq_L] follow him.  Riehl writes the same two
   functors H : C → C' and K : D → D', but her F : C → D is the left
   adjoint, so her source category is this file's D: her H is this file's L
   and her K is this file's K.  The two books therefore agree on the letter
   K and disagree on the other one.

   PROPOSITION 1 (Mac Lane) / Exercise 4.2.v (Riehl).  Given the two squares,
   the hom-set condition is equivalent to the unit condition Lη = η'L and to
   the counit condition Kε = ε'K.  All three are proved here, in both
   directions and as separately named constants:
   [squares_hom_iff_unit], [squares_hom_iff_counit] and
   [map_of_adjunctions_unit_iff_counit].

   THE MODELLING DECISION, AND WHAT WAS MEASURED.

   "The squares commute" is an equality of functors, and this library has
   two of those.  BOTH readings are delivered here, and the choice of which
   is primary is settled by the sources rather than by convenience.

   (a) The STRICT reading, taken as primary.  Mac Lane's display (3) joins
   C'(K F x, K a) to C'(F' L x, K a) with a double bar, and Riehl's version
   of the same square joins D'(K F c, K d) to D'(F' H c, K d) with an equals
   sign; her exercise is titled "strict morphism of adjunctions" and writes
   KF = F'H.  So both sources identify the two hom-sets by an EQUALITY of
   objects.  [AdjSquares] therefore carries [sq_left : ∀ x, K (F x) =
   F' (L x)] as data, at Leibniz equality of objects, together with the
   transported agreement of the two arrow actions ([sq_left_nat], written
   with [id_cast] of Construction/Quotient.v -- the same shape
   Adjunction/LeftInverse.v uses for its [lali_obj]/[lali_counit] pair and
   Theory/Equivalence/Strict.v for [lari_obj]/[lari_unit]).

   Those two fields ARE, up to conversion, the two arguments of
   Theory/Skeleton.v's [strict_equiv_of_id_cast_nat], whose conclusion is
   [@equiv _ (@Functor_StrictEq_Setoid _ _) (K ◯ F) (F' ◯ L)] -- the tree's
   strict functor equality.  That passage is NOT taken inside this file, on
   a measured ground: requiring Theory/Skeleton.v takes this file's
   transitive dependency closure from 21 modules to 32, pulling in
   Instance/Cat, Instance/Fun, Instance/StrictCat, Instance/StrictCat/ToCat,
   Instance/Discrete, Structure/Discrete, Construction/Subcategory and the
   three Theory/Equivalence modules.  Test/ProbeMapAdj393.v pays that cost
   once and checks the claim there, by applying that very constant to the
   two fields of an arbitrary [AdjSquares].

   (b) The ≈ reading, also delivered.  Under [Functor_Setoid] -- the
   library's default setoid on functors, which IS natural isomorphism -- the
   two squares become [K ◯ F ≈ F' ◯ L] and [L ◯ U ≈ U' ◯ K].  This reading
   DOES typecheck: an element of [Functor_Setoid] equality supplies a family
   of isomorphisms K (F x) ≅ F' (L x), and inserting those isomorphisms in
   place of the double bars makes the hom-set condition well typed with no
   transport at all.  [WeakAdjSquares], [WeakSquaresHom] and
   [WeakMapOfAdjunctions] are that version, with its own three-way
   equivalence ([weak_hom_iff_unit], [weak_hom_iff_counit],
   [weak_unit_iff_counit]).  So the objection that the ≈ version cannot be
   stated is refuted by construction.

   Neither version is a rewriting of the other: both are instantiations of
   ONE engine, the section [MapCompare], which fixes an arbitrary pair of
   comparison ISOMORPHISM families [al], [be] and proves the three-way
   equivalence over them.  The strict record feeds it [id_cast_iso] of its
   object equalities; the ≈ record feeds it the first projection of its two
   [Functor_Setoid] witnesses.  [strict_hom_is_weak_hom] records, at
   Leibniz equality of TYPES and by [reflexivity], that the strict hom
   condition IS the ≈ one at the comparison isomorphisms the strict data
   supplies, so the passage
   [WeakMapOfAdjunctions_of_MapOfAdjunctions] costs no proof at all.

   WHAT IS LOST relative to Mac Lane's own formulation, and what is gained.
   Under (b) the two squares hold only up to isomorphism, so
   [wsq_K W (F x)] and [F' (wsq_L W x)] need not be the same object;
   nothing in the ≈ version supports substituting one for the other in a
   type, which is what Mac
   Lane's double bar does.  Under (a) they are the same object, and the
   price is that the two squares are Leibniz equations between objects,
   which a category presented up to isomorphism will rarely satisfy.  The
   engine shows that the mathematics of Proposition 1 needs neither: it
   needs only invertible comparisons, natural in the sense recorded by
   [CompareLeftNat] and [CompareRightNat].

   WHICH NATURALITY EACH DIRECTION SPENDS.  The four passages of the engine
   take their naturality hypotheses EXPLICITLY, so the type of each records
   what it consumes.  [map_hom_to_unit] and [map_hom_to_counit] consume
   neither.  [map_unit_to_hom] consumes only the RIGHT square's naturality;
   [map_counit_to_hom] only the LEFT square's.

   RELATION TO Adjunction/Conjugate.v, WHICH IS THE SAME SECTION OF THE
   SAME BOOK.  That file already states both of the conditions Proposition 1
   equates with the hom-set square: [ConjugateUnit] (:183) and
   [ConjugateCounit] (:186), with [conjugate_characterizations] (:309)
   proving the four-way equivalence including [Conjugate ↔ ConjugateCounit]
   at :313.  Its configuration is different -- two adjunctions between the
   SAME pair of categories, compared by natural transformations σ : F' ⟹ F
   and τ : U ⟹ U', with no functors and no squares -- and this file is the
   general case with arbitrary K and L between DIFFERENT categories.  The
   two are related here, ON THE NOSE: [map_adj_hom_is_conjugate] proves

       MapAdjHom A A' Id[C] Id[D] al be = Conjugate A A' conj_sigma conj_tau

   at Leibniz equality of TYPES, by [reflexivity], where [conj_sigma] has
   components [from (al x)] and [conj_tau] components [to (be a)].  No
   padding transformation is needed, because [Id]'s object and arrow actions
   are the literal identities; the padding trap that
   Instance/Cat/Bicategory/Conjugate.v records is a bicategorical one and
   does not arise on this route.

   THE RESIDUE of that identification, stated exactly.  A map of adjunctions
   supplies INVERTIBLE comparison data -- an equality of objects under (a),
   an isomorphism under (b) -- whereas [Conjugate σ τ] places no
   invertibility requirement on σ or τ.  So what the K = Id, L = Id case
   recovers is a conjugate pair whose two transformations are pointwise
   invertible, and not every conjugate pair arises this way.  Only that
   one inclusion is machine-checked.  The converse -- that every conjugate
   pair with both legs pointwise invertible does arise this way -- is NOT
   built below, and no constant in this file takes an invertibility-family
   hypothesis.  Conjugate.v's own
   [conjugate_invertible_iff] (:632) says that under the square those two
   pointwise invertibility conditions imply each other, so demanding it of
   one of the two comparison families is no weaker than demanding it of
   both.  Nothing here claims more.

   RELATION TO Theory/Bicategory/Mates.v: NOT MACHINE-CHECKED HERE.  That
   file's [mate] carries a 2-cell f' ∘ a ⟹ b ∘ f to a 2-cell a ∘ u ⟹ u' ∘ b
   over bounding 1-cells a and b, and the expected statement is that a map
   of adjunctions is the case in Cat where a := L, b := K and the two
   comparison 2-cells are identities, each being the mate of the other.
   That statement is NOT proved in this file and is not asserted: exhibiting
   it needs C and D as 0-cells of the Cat bicategory and the padding
   transformations between F' ◯ Id and F' that
   Instance/Cat/Bicategory/Conjugate.v is built to mediate.  For the record,
   the closure cost was measured: Theory/Bicategory/Mates.v alone is +3
   modules over this file's 21, Instance/Cat/Bicategory/Adjunction.v is +8
   and Instance/Cat/Bicategory/Conjugate.v is +14; the reason it is not done
   is the missing padding work, not the dependency cone.  The
   ordinary-vocabulary shadow of [mate] is Conjugate.v's [conj_mate], and
   the relation to THAT is the on-the-nose identification above.

   RELATION TO Instance/Adj.v.  That file's [Adj] (:56) takes as its hom the
   bare product setoid of pairs of natural transformations, and its CAVEAT
   block (:29) says so and names [Conjugate] as the condition it does not
   impose.  Retyping that hom is explicitly future work there and is NOT
   attempted here; this file adds no instance and changes no other file.

   UNIVERSES, read off both the binder and the constraint block.
   [AdjSquares@{u u0 u1 u2 u3 u4}] is over C : Category@{u u0 u0},
   D : Category@{u1 u0 u0}, C' : Category@{u2 u3 u3} and
   D' : Category@{u4 u3 u3}: hom is identified with proof, and C's hom level
   with D's, by REUSING the level variable in the BINDER, while its
   constraint block carries only the bound u0 <= u3 and no equation at all.
   All four object universes are free.  The engine's theorems read the other
   way round: [map_adj_unit_iff_counit]'s binder keeps C's and D's hom levels
   apart while its BLOCK carries u0 = u2 and u6 = u8, so reading either one
   alone gets it wrong.  Of the 126 constants this file contributes, ZERO
   carry a [Set] in a binder or a block.  The hom = proof identification is
   inherited and has at least two donors, each sufficient on its own and
   pinned in the probe: [id_cast] of Construction/Quotient.v, and
   [Adjunction] with no [id_cast] in the command.  [Isomorphism] and
   [Functor] are NOT donors -- both are accepted at hom and proof levels
   declared strictly apart, where the three negatives are refused.

   WHAT IS NOT DELIVERED.  No category (or 2-category) of adjunctions and
   maps between them: [MapOfAdjunctions_id] and [MapOfAdjunctions_compose]
   are the identity and composition, but no associativity or unit law is
   stated, and none could be stated as a morphism equation without first
   choosing a setoid on maps of adjunctions, which is not done.  No converse
   to [WeakMapOfAdjunctions_of_MapOfAdjunctions].  No mates statement, as
   above.  No transport of a map of adjunctions along an equivalence, no
   relation to Adjunction/Compose.v, and no statement about when K or L is
   full, faithful or an equivalence. *)

(** ** Two [id_cast] identities not present in Construction/Quotient.v

    Both belong beside their donors in that file's [HomCast] section; they
    are stated here because this file is their only consumer so far.  Both
    are proved by eliminating the object equalities, whose endpoints are
    universally quantified variables here, so no uniqueness of identity
    proofs is used and no hypothesis is taken. *)

Lemma id_cast_sym_trans {X : Category} {u v w : X} (p : u = v) (q : v = w) :
  id_cast (eq_sym (eq_trans p q))
    ≈ id_cast (eq_sym p) ∘ id_cast (eq_sym q).
Proof. destruct p, q; cat. Qed.

Lemma fmap_id_cast_sym {X Y : Category} (G : X ⟶ Y) {u v : X} (e : u = v) :
  id_cast (eq_sym (f_equal G e)) ≈ fmap[G] (id_cast (eq_sym e)).
Proof. destruct e; simpl; symmetry; apply fmap_id. Qed.

(** ** The engine: comparison isomorphisms and the three-way equivalence *)

(* Everything Proposition 1 needs is a pair of invertible comparison
   families [al] and [be] between the two composites, plus the naturality of
   each.  The strict and the ≈ readings below are both instances. *)

Section MapCompare.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (al : ∀ x : D, K (F x) ≅ F' (L x)).
Context (be : ∀ a : C, L (U a) ≅ U' (K a)).

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).
Notation "'η²' x" := (@unit   _ _ _ _ A' x) (at level 9).
Notation "'ε²' a" := (@counit _ _ _ _ A' a) (at level 9).

(* Naturality of the two comparison families. *)

Definition CompareLeftNat : Type :=
  ∀ (x y : D) (f : x ~> y),
    to (al y) ∘ fmap[K] (fmap[F] f) ≈ fmap[F'] (fmap[L] f) ∘ to (al x).

Definition CompareRightNat : Type :=
  ∀ (a b : C) (f : a ~> b),
    to (be b) ∘ fmap[L] (fmap[U] f) ≈ fmap[U'] (fmap[K] f) ∘ to (be a).

(* An invertible natural family is natural in the inverse direction too. *)
Lemma compare_left_nat_from (Hal : CompareLeftNat) (x y : D) (f : x ~> y) :
  from (al y) ∘ fmap[F'] (fmap[L] f) ≈ fmap[K] (fmap[F] f) ∘ from (al x).
Proof.
  transitivity
    (from (al y) ∘ (fmap[F'] (fmap[L] f) ∘ (to (al x) ∘ from (al x)))).
  { now rewrite iso_to_from, id_right. }
  rewrite (comp_assoc (fmap[F'] (fmap[L] f))).
  rewrite <- (Hal x y f).
  rewrite comp_assoc, comp_assoc, iso_from_to.
  now rewrite id_left.
Qed.

(* Mac Lane's display (3), quantified over every transposable arrow. *)
Definition MapAdjHom : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    ⌊ fmap[K] k ∘ from (al x) ⌋² ≈ to (be a) ∘ fmap[L] ⌊ k ⌋.

(* Mac Lane's Lη = η'L, with the comparison split across the two sides. *)
Definition MapAdjUnit : Type :=
  ∀ x : D,
    to (be (F x)) ∘ fmap[L] (η x) ≈ fmap[U'] (from (al x)) ∘ η² (L x).

(* Mac Lane's Kε = ε'K, likewise. *)
Definition MapAdjCounit : Type :=
  ∀ a : C,
    fmap[K] (ε a) ∘ from (al (U a)) ≈ ε² (K a) ∘ fmap[F'] (to (be a)).

(* Mac Lane's own argument: chase the identity arrow around display (3). *)
Lemma map_hom_to_unit : MapAdjHom → MapAdjUnit.
Proof.
  intros H x.
  pose proof (H x (F x) id) as Hx.
  rewrite fmap_id, id_left in Hx.
  rewrite (to_adj_unit (H:=A')) in Hx.
  now rewrite <- Hx.
Qed.

Lemma map_unit_to_hom : CompareRightNat → MapAdjUnit → MapAdjHom.
Proof.
  intros Hbe H x a k.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite <- (H x : _ ≈ _).
  rewrite comp_assoc.
  rewrite <- (Hbe (F x) a k).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now rewrite <- (to_adj_unit (H:=A)).
Qed.

(* The dual chase: instantiate display (3) at the counit. *)
Lemma map_hom_to_counit : MapAdjHom → MapAdjCounit.
Proof.
  intros H a.
  pose proof (H (U a) a (ε a)) as Ha.
  rewrite (to_adj_counit (H:=A)) in Ha.
  rewrite fmap_id, id_right in Ha.
  apply (snd (adj_univ (H:=A') _ _)) in Ha.
  rewrite Ha.
  now rewrite (from_adj_counit (H:=A')).
Qed.

Lemma map_counit_to_hom : CompareLeftNat → MapAdjCounit → MapAdjHom.
Proof.
  intros Hal H x a k.
  apply (fst (adj_univ (H:=A') _ _)).
  rewrite (from_adj_counit (H:=A')).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (H a : _ ≈ _).
  rewrite <- comp_assoc.
  rewrite (compare_left_nat_from Hal _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Theorem map_adj_hom_iff_unit :
  CompareRightNat → (MapAdjHom ↔ MapAdjUnit).
Proof.
  intros Hbe; split; [ exact map_hom_to_unit | exact (map_unit_to_hom Hbe) ].
Qed.

Theorem map_adj_hom_iff_counit :
  CompareLeftNat → (MapAdjHom ↔ MapAdjCounit).
Proof.
  intros Hal; split;
    [ exact map_hom_to_counit | exact (map_counit_to_hom Hal) ].
Qed.

Theorem map_adj_unit_iff_counit :
  CompareLeftNat → CompareRightNat → (MapAdjUnit ↔ MapAdjCounit).
Proof.
  intros Hal Hbe; split; intro H.
  - exact (map_hom_to_counit (map_unit_to_hom Hbe H)).
  - exact (map_hom_to_unit (map_counit_to_hom Hal H)).
Qed.

End MapCompare.

(** ** The two squares, at Leibniz equality of objects *)

Section StrictSquares.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.

(* Mac Lane's display (2).  The [_nat] fields are the transported agreement
   of the two arrow actions; together with the object equalities above them
   they are the two arguments of Theory/Skeleton.v's
   [strict_equiv_of_id_cast_nat], whose conclusion is the tree's strict
   functor equality (see the header, and Test/ProbeMapAdj393.v). *)
Record AdjSquares : Type := {
  sq_K : C ⟶ C';
  sq_L : D ⟶ D';

  sq_left : ∀ x : D, sq_K (F x) = F' (sq_L x);
  sq_left_nat : ∀ (x y : D) (f : x ~> y),
    id_cast (sq_left y) ∘ fmap[sq_K] (fmap[F] f)
      ≈ fmap[F'] (fmap[sq_L] f) ∘ id_cast (sq_left x);

  sq_right : ∀ a : C, sq_L (U a) = U' (sq_K a);
  sq_right_nat : ∀ (a b : C) (f : a ~> b),
    id_cast (sq_right b) ∘ fmap[sq_L] (fmap[U] f)
      ≈ fmap[U'] (fmap[sq_K] f) ∘ id_cast (sq_right a)
}.

(* The comparison isomorphisms the engine consumes. *)

Definition sq_al (S : AdjSquares) (x : D) : sq_K S (F x) ≅ F' (sq_L S x)
  := id_cast_iso (sq_left S x).

Definition sq_be (S : AdjSquares) (a : C) : sq_L S (U a) ≅ U' (sq_K S a)
  := id_cast_iso (sq_right S a).

(* The composite object equalities Mac Lane's Lη = η'L and Kε = ε'K use. *)

Definition sq_unit_eq (S : AdjSquares) (x : D)
  : sq_L S (U (F x)) = U' (F' (sq_L S x))
  := eq_trans (sq_right S (F x)) (f_equal U' (sq_left S x)).

Definition sq_counit_eq (S : AdjSquares) (a : C)
  : sq_K S (F (U a)) = F' (U' (sq_K S a))
  := eq_trans (sq_left S (U a)) (f_equal F' (sq_right S a)).

End StrictSquares.

(** ** Mac Lane's Definition 1 and Proposition 1 *)

Section StrictMap.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').

(* Display (3), quantified over every transposable arrow. *)
Definition SquaresHom (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    to (@adj _ _ _ _ A' _ _)
       (fmap[sq_K S] k ∘ id_cast (eq_sym (sq_left S x)))
      ≈ id_cast (sq_right S a) ∘ fmap[sq_L S] (to (@adj _ _ _ _ A _ _) k).

Definition SquaresUnit (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ x : D,
    id_cast (sq_right S (F x)) ∘ fmap[sq_L S] (@unit _ _ _ _ A x)
      ≈ fmap[U'] (id_cast (eq_sym (sq_left S x)))
          ∘ @unit _ _ _ _ A' (sq_L S x).

Definition SquaresCounit (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ a : C,
    fmap[sq_K S] (@counit _ _ _ _ A a) ∘ id_cast (eq_sym (sq_left S (U a)))
      ≈ @counit _ _ _ _ A' (sq_K S a) ∘ fmap[F'] (id_cast (sq_right S a)).

(* Each of the three IS the engine's condition at the comparison
   isomorphisms [sq_al], [sq_be], at Leibniz equality of types. *)

Lemma squares_hom_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S = MapAdjHom A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma squares_unit_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S = MapAdjUnit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma squares_counit_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresCounit S = MapAdjCounit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma sq_left_CompareLeftNat (S : @AdjSquares C D F U C' D' F' U') :
  CompareLeftNat (sq_K S) (sq_L S) (sq_al S).
Proof. exact (sq_left_nat S). Qed.

Lemma sq_right_CompareRightNat (S : @AdjSquares C D F U C' D' F' U') :
  CompareRightNat (sq_K S) (sq_L S) (sq_be S).
Proof. exact (sq_right_nat S). Qed.

(* Proposition 1, in three named biconditionals. *)

Theorem squares_hom_iff_unit (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S ↔ SquaresUnit S.
Proof.
  exact (map_adj_hom_iff_unit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_right_CompareRightNat S)).
Qed.

Theorem squares_hom_iff_counit (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S ↔ SquaresCounit S.
Proof.
  exact (map_adj_hom_iff_counit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_left_CompareLeftNat S)).
Qed.

Theorem map_of_adjunctions_unit_iff_counit
  (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S ↔ SquaresCounit S.
Proof.
  exact (map_adj_unit_iff_counit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_left_CompareLeftNat S) (sq_right_CompareRightNat S)).
Qed.

(* Mac Lane's own spelling: the whole identification on one side, so that
   the two displayed equations read Lη = η'L and Kε = ε'K. *)

Theorem squares_unit_fused (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S
    ↔ (∀ x : D,
         id_cast (sq_unit_eq S x) ∘ fmap[sq_L S] (@unit _ _ _ _ A x)
           ≈ @unit _ _ _ _ A' (sq_L S x)).
Proof.
  unfold SquaresUnit, sq_unit_eq; split; intros H x.
  - rewrite <- id_cast_trans.
    rewrite <- comp_assoc.
    rewrite (H x).
    rewrite <- fmap_id_cast.
    rewrite comp_assoc, <- fmap_comp, id_cast_inv_r, fmap_id.
    now rewrite id_left.
  - rewrite <- (H x).
    rewrite <- id_cast_trans.
    rewrite <- comp_assoc.
    rewrite <- fmap_id_cast.
    rewrite comp_assoc, <- fmap_comp, id_cast_inv_l, fmap_id.
    now rewrite id_left.
Qed.

Theorem squares_counit_fused (S : @AdjSquares C D F U C' D' F' U') :
  SquaresCounit S
    ↔ (∀ a : C,
         fmap[sq_K S] (@counit _ _ _ _ A a)
           ≈ @counit _ _ _ _ A' (sq_K S a) ∘ id_cast (sq_counit_eq S a)).
Proof.
  unfold SquaresCounit, sq_counit_eq; split; intros H a.
  - rewrite <- id_cast_trans.
    rewrite <- fmap_id_cast.
    rewrite comp_assoc.
    rewrite <- (H a).
    rewrite <- comp_assoc, id_cast_inv_l.
    now rewrite id_right.
  - rewrite (H a).
    rewrite <- id_cast_trans.
    rewrite <- fmap_id_cast.
    rewrite <- !comp_assoc, id_cast_inv_r.
    now rewrite id_right.
Qed.

(* Definition 1: the squares together with display (3). *)
Record MapOfAdjunctions : Type := {
  map_squares : @AdjSquares C D F U C' D' F' U';
  map_hom : SquaresHom map_squares
}.

Definition map_K (M : MapOfAdjunctions) : C ⟶ C' := sq_K (map_squares M).
Definition map_L (M : MapOfAdjunctions) : D ⟶ D' := sq_L (map_squares M).

Definition map_unit (M : MapOfAdjunctions) : SquaresUnit (map_squares M) :=
  fst (squares_hom_iff_unit (map_squares M)) (map_hom M).

Definition map_counit (M : MapOfAdjunctions) : SquaresCounit (map_squares M)
  := fst (squares_hom_iff_counit (map_squares M)) (map_hom M).

Definition MapOfAdjunctions_of_unit
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresUnit S)
  : MapOfAdjunctions :=
  {| map_squares := S; map_hom := snd (squares_hom_iff_unit S) H |}.

Definition MapOfAdjunctions_of_counit
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresCounit S)
  : MapOfAdjunctions :=
  {| map_squares := S; map_hom := snd (squares_hom_iff_counit S) H |}.

(* Building a map from either of the two other conditions leaves the squares
   untouched, on the nose. *)

Example map_of_unit_squares
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresUnit S) :
  map_squares (MapOfAdjunctions_of_unit S H) = S.
Proof. reflexivity. Qed.

Example map_of_counit_squares
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresCounit S) :
  map_squares (MapOfAdjunctions_of_counit S H) = S.
Proof. reflexivity. Qed.

End StrictMap.

(** ** Identity and composition *)

Section SquaresIdComp.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}.

Program Definition AdjSquares_id : @AdjSquares C D F U C D F U := {|
  sq_K := Id[C];
  sq_L := Id[D];
  sq_left  := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.

Program Definition AdjSquares_compose
  (S : @AdjSquares C D F U C' D' F' U')
  (T : @AdjSquares C' D' F' U' C'' D'' F'' U'')
  : @AdjSquares C D F U C'' D'' F'' U'' := {|
  sq_K := sq_K T ◯ sq_K S;
  sq_L := sq_L T ◯ sq_L S;
  sq_left := fun x =>
    eq_trans (f_equal (sq_K T) (sq_left S x)) (sq_left T (sq_L S x));
  sq_right := fun a =>
    eq_trans (f_equal (sq_L T) (sq_right S a)) (sq_right T (sq_K S a))
|}.
Next Obligation.
  rewrite <- !id_cast_trans.
  rewrite <- !fmap_id_cast.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (sq_left_nat S).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite (sq_left_nat T).
  now rewrite <- comp_assoc.
Qed.
Next Obligation.
  rewrite <- !id_cast_trans.
  rewrite <- !fmap_id_cast.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (sq_right_nat S).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite (sq_right_nat T).
  now rewrite <- comp_assoc.
Qed.

End SquaresIdComp.

Section MapIdComp.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}
        (A'' : F'' ⊣ U'').

Program Definition MapOfAdjunctions_id : MapOfAdjunctions A A := {|
  map_squares := AdjSquares_id
|}.
Next Obligation.
  intros x a k; simpl.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.

Program Definition MapOfAdjunctions_compose
  (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : MapOfAdjunctions A A'' := {|
  map_squares :=
    AdjSquares_compose (map_squares A A' M) (map_squares A' A'' N)
|}.
Next Obligation.
  intros x a k; simpl.
  rewrite id_cast_sym_trans.
  rewrite fmap_id_cast_sym.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (map_hom A' A'' N (sq_L (map_squares A A' M) x)
             (sq_K (map_squares A A' M) a)
             (fmap[sq_K (map_squares A A' M)] k
                ∘ id_cast (eq_sym (sq_left (map_squares A A' M) x)))).
  rewrite (map_hom A A' M x a k).
  rewrite fmap_comp.
  rewrite fmap_id_cast.
  rewrite comp_assoc.
  now rewrite id_cast_trans.
Qed.

(* The data of both is read back on the nose. *)

Example map_id_K : map_K A A MapOfAdjunctions_id = Id[C].
Proof. reflexivity. Qed.

Example map_id_L : map_L A A MapOfAdjunctions_id = Id[D].
Proof. reflexivity. Qed.

Example map_id_left_square (x : D) :
  sq_left (map_squares A A MapOfAdjunctions_id) x = eq_refl.
Proof. reflexivity. Qed.

Example map_compose_K (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : map_K A A'' (MapOfAdjunctions_compose M N)
      = map_K A' A'' N ◯ map_K A A' M.
Proof. reflexivity. Qed.

Example map_compose_L (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : map_L A A'' (MapOfAdjunctions_compose M N)
      = map_L A' A'' N ◯ map_L A A' M.
Proof. reflexivity. Qed.

End MapIdComp.

(** ** The ≈ reading: the squares up to natural isomorphism *)

Section WeakSquares.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.

(* [≈] on functors is [Functor_Setoid], which IS natural isomorphism. *)
Record WeakAdjSquares : Type := {
  wsq_K : C ⟶ C';
  wsq_L : D ⟶ D';
  wsq_left  : wsq_K ◯ F ≈ F' ◯ wsq_L;
  wsq_right : wsq_L ◯ U ≈ U' ◯ wsq_K
}.

Definition wsq_al (W : WeakAdjSquares) (x : D)
  : wsq_K W (F x) ≅ F' (wsq_L W x) := `1 (wsq_left W) x.

Definition wsq_be (W : WeakAdjSquares) (a : C)
  : wsq_L W (U a) ≅ U' (wsq_K W a) := `1 (wsq_right W) a.

Lemma wsq_left_nat (W : WeakAdjSquares) :
  CompareLeftNat (wsq_K W) (wsq_L W) (wsq_al W).
Proof.
  intros x y f.
  rewrite (`2 (wsq_left W) x y f).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma wsq_right_nat (W : WeakAdjSquares) :
  CompareRightNat (wsq_K W) (wsq_L W) (wsq_be W).
Proof.
  intros a b f.
  rewrite (`2 (wsq_right W) a b f).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(* A strict square is in particular a ≈ one. *)

Lemma strict_weak_left (S : @AdjSquares C D F U C' D' F' U') :
  ∀ (x y : D) (f : x ~> y),
    fmap[sq_K S] (fmap[F] f)
      ≈ id_cast (eq_sym (sq_left S y)) ∘ fmap[F'] (fmap[sq_L S] f)
          ∘ id_cast (sq_left S x).
Proof.
  intros x y f.
  rewrite <- comp_assoc.
  rewrite <- (sq_left_nat S x y f).
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_left.
Qed.

Lemma strict_weak_right (S : @AdjSquares C D F U C' D' F' U') :
  ∀ (a b : C) (f : a ~> b),
    fmap[sq_L S] (fmap[U] f)
      ≈ id_cast (eq_sym (sq_right S b)) ∘ fmap[U'] (fmap[sq_K S] f)
          ∘ id_cast (sq_right S a).
Proof.
  intros a b f.
  rewrite <- comp_assoc.
  rewrite <- (sq_right_nat S a b f).
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_left.
Qed.

Definition WeakAdjSquares_of_AdjSquares
  (S : @AdjSquares C D F U C' D' F' U') : WeakAdjSquares := {|
  wsq_K := sq_K S;
  wsq_L := sq_L S;
  wsq_left  := existT _ (fun x => id_cast_iso (sq_left S x))
                        (strict_weak_left S);
  wsq_right := existT _ (fun a => id_cast_iso (sq_right S a))
                        (strict_weak_right S)
|}.

End WeakSquares.

Section WeakMap.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').

Definition WeakSquaresHom (W : @WeakAdjSquares C D F U C' D' F' U') : Type :=
  MapAdjHom A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Definition WeakSquaresUnit (W : @WeakAdjSquares C D F U C' D' F' U') : Type :=
  MapAdjUnit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Definition WeakSquaresCounit (W : @WeakAdjSquares C D F U C' D' F' U')
  : Type := MapAdjCounit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Theorem weak_hom_iff_unit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresHom W ↔ WeakSquaresUnit W.
Proof.
  exact (map_adj_hom_iff_unit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W)
           (wsq_right_nat W)).
Qed.

Theorem weak_hom_iff_counit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresHom W ↔ WeakSquaresCounit W.
Proof.
  exact (map_adj_hom_iff_counit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W)
           (wsq_left_nat W)).
Qed.

Theorem weak_unit_iff_counit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresUnit W ↔ WeakSquaresCounit W.
Proof.
  exact (map_adj_unit_iff_counit A A' (wsq_K W) (wsq_L W) (wsq_al W)
           (wsq_be W) (wsq_left_nat W) (wsq_right_nat W)).
Qed.

Record WeakMapOfAdjunctions : Type := {
  wmap_squares : @WeakAdjSquares C D F U C' D' F' U';
  wmap_hom : WeakSquaresHom wmap_squares
}.

(* The strict hom condition IS the ≈ one at the comparison isomorphisms the
   strict data supplies -- at Leibniz equality of types, by [reflexivity].
   The passage below therefore carries [map_hom] across unchanged. *)
Lemma strict_hom_is_weak_hom (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom A A' S = WeakSquaresHom (WeakAdjSquares_of_AdjSquares S).
Proof. reflexivity. Qed.

Definition WeakMapOfAdjunctions_of_MapOfAdjunctions
  (M : MapOfAdjunctions A A') : WeakMapOfAdjunctions := {|
  wmap_squares := WeakAdjSquares_of_AdjSquares (map_squares A A' M);
  wmap_hom := map_hom A A' M
|}.

End WeakMap.

(** ** The identity-bounding-functor case IS Adjunction/Conjugate.v *)

Section ConjugateCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F' : D ⟶ C} {U' : C ⟶ D} (A' : F' ⊣ U').
Context (al : ∀ x : D, F x ≅ F' x).
Context (be : ∀ a : C, U a ≅ U' a).
Context (Hal : CompareLeftNat (F:=F) (F':=F') Id[C] Id[D] al).
Context (Hbe : CompareRightNat (U:=U) (U':=U') Id[C] Id[D] be).

Program Definition conj_sigma : F' ⟹ F := {|
  transform := fun x => from (al x)
|}.
Next Obligation.
  symmetry; exact (compare_left_nat_from Id[C] Id[D] al Hal x y f).
Qed.
Next Obligation.
  exact (compare_left_nat_from Id[C] Id[D] al Hal x y f).
Qed.

Program Definition conj_tau : U ⟹ U' := {|
  transform := fun a => to (be a)
|}.
Next Obligation. symmetry; exact (Hbe x y f). Qed.
Next Obligation. exact (Hbe x y f). Qed.

Theorem map_adj_hom_is_conjugate :
  MapAdjHom A A' Id[C] Id[D] al be = Conjugate A A' conj_sigma conj_tau.
Proof. reflexivity. Qed.

End ConjugateCase.

(** ** A map of adjunctions that is not the identity *)

(* The witness carries an ARBITRARY adjunction: the product of A with itself
   carries the symmetry [Swap] as a map of adjunctions to itself.  The
   product of two adjunctions is built here because the tree has none, and
   that was measured two ways: no term anywhere has a type of the shape
   [_ ∏⟶ _ ⊣ _ ∏⟶ _] (swept multiline over declaration heads, since a
   same-line grep under-approximates), and the only names in the tree
   pairing those two words are Adjunction/Diagonal/Product.v's
   [Diagonal_Product_Adjunction] and, read case-insensitively,
   Adjunction/Diagonal/Coproduct.v's [Diagonal_Coproduct_Adjunction] --
   both diagonal adjunctions inside one category, and both a different
   construction. *)

Section ProductAdjunction.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {E B : Category} {G : B ⟶ E} {V : E ⟶ B} (A2 : G ⊣ V).

Program Definition prod_adj_iso (x : D ∏ B) (y : C ∏ E) :
  @Isomorphism Sets
    {| carrier   := @hom (C ∏ E) ((F ∏⟶ G) x) y;
       is_setoid := @homset (C ∏ E) ((F ∏⟶ G) x) y |}
    {| carrier   := @hom (D ∏ B) x ((U ∏⟶ V) y);
       is_setoid := @homset (D ∏ B) x ((U ∏⟶ V) y) |} := {|
  to   := {| morphism := fun f => (to (@adj _ _ _ _ A  _ _) (fst f),
                                   to (@adj _ _ _ _ A2 _ _) (snd f)) |};
  from := {| morphism := fun g => (from (@adj _ _ _ _ A  _ _) (fst g),
                                   from (@adj _ _ _ _ A2 _ _) (snd g)) |}
|}.
Next Obligation.
  intros f g Hfg; split; simpl;
    [ now rewrite (fst Hfg) | now rewrite (snd Hfg) ].
Qed.
Next Obligation.
  intros f g Hfg; split; simpl;
    [ now rewrite (fst Hfg) | now rewrite (snd Hfg) ].
Qed.
Next Obligation.
  split; simpl;
    [ exact (from_adj_comp_law (H:=A)  h)
    | exact (from_adj_comp_law (H:=A2) h0) ].
Qed.
Next Obligation.
  split; simpl;
    [ exact (to_adj_comp_law (H:=A)  h)
    | exact (to_adj_comp_law (H:=A2) h0) ].
Qed.

Definition AdjunctionProduct : (F ∏⟶ G) ⊣ (U ∏⟶ V) :=
  Build_Adjunction' prod_adj_iso
    (fun x y z f g => (to_adj_nat_l (Adjunction:=A)  (fst f) (fst g),
                       to_adj_nat_l (Adjunction:=A2) (snd f) (snd g)))
    (fun x y z f g => (to_adj_nat_r (Adjunction:=A)  (fst f) (fst g),
                       to_adj_nat_r (Adjunction:=A2) (snd f) (snd g))).

End ProductAdjunction.

Section SwapWitness.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).

(* Both squares hold at [eq_refl]: [Swap] and [_ ∏⟶ _] are both spelled
   with [fst]/[snd] rather than by matching on a pair, so the two composites
   reduce to the same term at a variable object. *)
Program Definition SwapSquares :
  @AdjSquares (C ∏ C) (D ∏ D) (F ∏⟶ F) (U ∏⟶ U)
              (C ∏ C) (D ∏ D) (F ∏⟶ F) (U ∏⟶ U) := {|
  sq_K := Swap;
  sq_L := Swap;
  sq_left  := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.

Program Definition SwapMap
  : MapOfAdjunctions (AdjunctionProduct A A) (AdjunctionProduct A A) := {|
  map_squares := SwapSquares
|}.
Next Obligation.
  intros x a k; split; simpl;
    [ rewrite id_left; apply (to_adj_respects (H:=A)); apply id_right
    | rewrite id_left; apply (to_adj_respects (H:=A)); apply id_right ].
Qed.

Example swap_map_K_moves (x y : C) :
  fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A) SwapMap] (x, y)
    = (y, x).
Proof. reflexivity. Qed.

(* So the swap map agrees with the identity map at (x, y) only when the two
   objects coincide. *)
Theorem swap_map_not_identity (x y : C) :
  fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A) SwapMap] (x, y)
    = fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A)
             (MapOfAdjunctions_id (AdjunctionProduct A A))] (x, y)
  → x = y.
Proof. intros H; exact (f_equal snd H). Qed.

End SwapWitness.

(** ** An unconditional separation, over a two-object category *)

(* The base category is chosen only to supply two objects that are distinct
   at Leibniz equality; its hom-setoid is trivial, so the SEPARATION below
   is object-level.  All the equational content of the witness above is
   proved at an arbitrary adjunction A. *)

Program Definition MapAdjTwo : Category := {|
  obj     := bool;
  hom     := fun _ _ => poly_unit;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => ttt;
  compose := fun _ _ _ _ _ => ttt
|}.

Program Definition MapAdjTwo_adj : Id[MapAdjTwo] ⊣ Id[MapAdjTwo] :=
  Build_Adjunction' (fun x y => iso_id) _ _.

Definition MapAdjTwoSwap := SwapMap MapAdjTwo_adj.

Example mapadj_two_swap_moves :
  fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             MapAdjTwoSwap] (true, false)
    = (false, true).
Proof. reflexivity. Qed.

Theorem mapadj_two_swap_not_identity :
  fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             MapAdjTwoSwap] (true, false)
    = fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
                 (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (MapOfAdjunctions_id
                (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj))]
        (true, false)
  → False.
Proof.
  intro H.
  pose proof (swap_map_not_identity MapAdjTwo_adj true false H) as Hb.
  discriminate Hb.
Qed.
