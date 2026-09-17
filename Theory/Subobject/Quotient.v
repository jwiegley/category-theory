Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(* Quotient objects, and their lattice, by transport through C^op

   nLab:  https://ncatlab.org/nlab/show/quotient+object
   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/coimage

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF pp. 135-136), Definition 3, is the source.
   Having defined a subobject of x as an equivalence class of monos into
   x ordered by factorization (Definition 2, the previous file), Mac Lane
   defines a QUOTIENT OBJECT of x to be the dual: an equivalence class of
   epis OUT of x, two epis being equivalent when each factors through the
   other, and the order again given by factorization.  He observes that
   in a category whose epis are surjections these classes are the usual
   quotients -- for groups, the quotient objects of G are exactly the
   G/N for N normal in G, the surjection G ↠ G/N standing for its class.
   Neither clause is discharged in this file, and the NOT DELIVERED
   paragraph below says so in terms.

   THE IDIOM.  A quotient object of x in C is a subobject of x in C^op,
   so the definition is one line and every consequence is an
   instantiation.  That is the library's standard device for dual
   notions: Theory/Monad.v is [Comonad `{M : C ⟶ C} := @Monad (C^op)
   (M^op)], and Comonad/Duality.v ([op_Monad_of_Comonad],
   [Comonad_of_op_Monad]) are the two bridges between the readings, each
   proved by [:= H] -- no data moves, only the name of the direction.
   The same holds here: [QuotObj x := @SubObj (C^op) x], and every lemma
   in the order theory below is a [:=] instantiation of its subobject
   counterpart at C^op, not a second proof.  The only constants in this
   file with proof content of their own are [quot_equiv_iff_iso] with its
   one-directional corollary [quot_equiv_of_cod_iso] (first proved in the
   Grp witness during the parallel build and lifted here), and
   [mk_quot_respects] (the covariant repackaging of the setoid, whose
   necessity is measured below), and the four-field permutations
   [Iso_of_op_Iso]/[op_Iso_of_Iso] -- five in all.

   WHY THE COVARIANT READINGS ARE FREE.  Construction/Opposite.v
   builds [Opposite] by permuting fields rather than by composing them
   with symmetry proofs: [hom := fun x y => @hom C y x] and
   [compose := fun _ _ _ f g => g ∘ f], so a C^op-arrow into x IS
   a C-arrow out of x and a C^op-composite IS the reversed C-composite,
   both on the nose.  Two consequences are pinned here as [eq_refl]
   readbacks, because they are about the DATA and not about a morphism.
   [QuotObj_op_is_SubObj] : [@QuotObj (C^op) x = @SubObj C x] -- quotient
   objects of C^op are subobjects of C, C^op^op being C by conversion.
   [quot_le_unfold] : [quot_le q r] is literally
   [{ k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }], the
   covariant factorization order, with no rewriting.

   MONIC IN C^op IS EPIC IN C, AND CONVERSELY.  The issue that prompted
   this file (#446) recorded, as one of its gaps, that there is "no lemma
   identifying Monic in C^op with the Epic class of Theory/Morphisms.v".
   That was STALE when written and is cited here as such:
   Theory/Morphisms/Duality.v carries all four bridges --
   [Monic_of_op_Epic], [op_Epic_of_Monic],
   [Epic_of_op_Monic] and [op_Monic_of_Epic] -- each a single
   constructor application, because [Monic] and [Epic] are two distinct
   one-field records whose fields have the SAME type once the opposite
   hom and composition are unfolded (that file's header says exactly
   this).  [monic_op_iff_epic] below is the pair of the two
   directions this file consumes, and [epic_of_monic_op] /
   [monic_op_of_epic] name its projections.  The other two bridges are
   the reason [QuotObj_op_is_SubObj] closes the circle rather than
   merely pointing one way: an [Epic] in C^op is a [Monic] in C by
   [Monic_of_op_Epic], so the quotient objects of C^op and the
   subobjects of C carry the same monicity witness as well as the same
   arrow.  (The issue cited [Epic] at the wrong place in
   Theory/Morphisms.v; its declaration was re-measured in this worktree
   with grep -n '^Class Epic'.)

   WHAT THE SETOID COSTS, MEASURED.  The one place where the transport
   is NOT free is the equivalence.  Theory/Subobject.v's
   [SubObj_Setoid] witnesses [u ≈ v] by an isomorphism of the DOMAINS
   commuting with the monos; read at C^op that witness is an
   isomorphism IN C^op of the codomains, whose [to] component is a
   C-arrow pointing the other way.  So the definitional unfolding of
   [q ≈ r] is [quot_equiv_unfold] below --
   [{ i : @Isomorphism (C^op) (quot_cod q) (quot_cod r)
      & (to i ∘[C] quot_epi r) ≈ quot_epi q }] -- which needs BOTH the
   C^op spelling of the isomorphism and the composition annotated with
   its category, and which is an [eq_refl].  The naive covariant
   spelling is REFUSED, and this is the measurement, not a guess: with
   the same requirement list,
     [Example m (q r : QuotObj x) :
        (q ≈ r) = { i : quot_cod q ≅ quot_cod r
                  & to i ∘ quot_epi q ≈ quot_epi r } := eq_refl.]
   is rejected as
     "The term "eq_refl" has type "(q ≈ r) = (q ≈ r)" while it is
      expected to have type "(q ≈ r) = ∃ i : quot_cod q ≅ quot_cod r,
      i ∘ quot_epi q ≈ quot_epi r" (cannot unify ...)" --
   a CONVERSION refusal.  The covariant characterization is therefore a
   LEMMA and is stated at ≈, never at [eq_refl]: [quot_equiv_iff_iso]
   says [q ≈ r] iff there is an isomorphism [i : quot_cod q ≅[C]
   quot_cod r] of the codomains IN C with [to i ∘ quot_epi q ≈ quot_epi
   r], the orientation one expects of two epis presenting the same
   quotient.  Its two halves are carried by [Iso_of_op_Iso] and
   [op_Iso_of_Iso], which permute the four fields of [Isomorphism]
   between C^op and C with no proof content -- [iso_to_from] at one side
   IS [iso_from_to] at the other, the two composites having swapped
   endpoints.  An in-tree bridge of this kind already exists, [iso_unop]
   at Functor/Hom/Yoneda/Iso.v, and is NOT required here: it lives in
   the Yoneda development, far above this file, and its orientation is
   the other one ([to := from i], giving [x ≅ y] from [@Isomorphism C^op
   x y], where the orientation needed below is [to := to i], giving
   [y ≅ x]).  Construction/Opposite.v's [Isomorphism_Opposite] goes
   only from C to C^op.

   WHICH ORDER, AND WHICH BOUND IS WHICH.  [quot_le q r] holds when the
   epi of q factors through the epi of r; q is then the COARSER
   quotient, the one further from x.  For groups, with q = (G ↠ G/N) and
   r = (G ↠ G/M), that reads M ⊆ N: the order on quotient objects is the
   REVERSE of the inclusion order on the kernels.  Everything below is
   stated for [quot_le] and the reader must not silently substitute the
   other convention.  In particular [quot_meet] -- [sub_meet] at C^op,
   which is the PUSHOUT in C of the two epis -- is the GREATEST LOWER
   BOUND for [quot_le]: the finest quotient that FACTORS THROUGH both q
   and r, i.e. the finest one below both (an earlier revision of this
   sentence had the direction of "factors through" backwards, saying
   "that both q and r factor through"; an audit caught it against the
   definition two paragraphs up), which for groups is G/(NM).  A reader
   who orders quotients
   by the size of the codomain, or who identifies a quotient with its
   kernel, sees that same object as a JOIN (NM is the join of N and M as
   subgroups).  It is not named [quot_join] here, and [quot_join] below
   means something else: the least upper bound for [quot_le], the
   coimage of the pairing, G/(N ∩ M) in the same illustration.  The two
   ends match: [quot_top] is the identity quotient (the finest, the top
   for [quot_le]) and [quot_bot] is the quotient by the terminal object
   (the coarsest, the bottom), which exists only when [one : x ~> 1] is
   epic.

   WHAT IS TRANSPORTED, AND FROM WHERE.  Theory/Subobject.v supplies the
   record, the setoid, the preorder [sub_le] with its
   monic and unique mediating arrow, and
   [sub_equiv_iff_mutual]; all five arrive here as [quot_cod] /
   [quot_epi] / [QuotObj_Setoid] / [quot_le] / [quot_le_epic] /
   [quot_le_unique] / [quot_equiv_iff_mutual].  Theory/Subobject/
   Lattice.v supplies the order structure: [sub_top] and
   [sub_bot] with [zero_monic_of_strict], the binary
   meet by pullback with its two projections, its
   greatest-lower-bound property and the four laws, the order vocabulary
   [IsIntersection] / [IsMeet], the wide intersection, the [ImageOf]
   record and [HasImages] class, the join by image of the copairing, and
   the absorption pair.
   Three dualizations make the transport work.  Structure/Pushout.v's
   [HasPullbacks_op_of_HasPushouts] turns the [HasPushouts C] hypothesis
   into the [HasPullbacks (C^op)] that [sub_meet] consumes.
   Structure/Cocartesian.v defines [@Cocartesian C] as NOTATION for
   [@Cartesian (C^op)], so the [Cocartesian (C^op)] that [sub_join]
   consumes is [@Cartesian (C^op^op)] and a plain [Cartesian C] is
   accepted for it by conversion -- MEASURED, with
   [Definition m : @Cocartesian (C^op) := _.] compiling under a
   [Context `{@Cartesian C}].  That is why the join half of this file is
   conditional on PRODUCTS of C: [quot_pairing q r] is
   [⟨quot_epi q, quot_epi r⟩ : x ~> quot_cod q × quot_cod r], the C^op
   copairing read forwards, and the join is its coimage.  Likewise
   Structure/Initial.v defines [Initial C] as [@Terminal (C^op)], so
   [sub_bot] at C^op takes a [Terminal C] and a [Monic] of the opposite
   arrow, that is an [Epic (one : x ~> 1)] in C.

   COIMAGES.  [CoimageOf f := @ImageOf (C^op) y x f] for [f : x ~> y],
   read covariantly: a quotient [e : x ↠ z] of x, a map [m : z ~> y]
   with [m ∘ e ≈ f], and the clause that e is the LEAST such quotient
   for [quot_le] -- that is, the COARSEST quotient of x through which f
   factors, which in Sets is x modulo the fibres of f.  [HasCoimages C]
   is notation for [@HasImages (C^op)], following the [Cocartesian] and
   [Initial] precedent so that instance resolution still fires.  One
   inference trap is worth recording, because it cost a compilation
   here: [CoimageOf] takes its category from the type of its argument,
   and an argument SPELLED as a C^op-arrow makes Rocq choose C^op for
   that category and produce [@ImageOf (C^op^op) ...] with the two
   objects swapped.  Hence [quot_pairing], whose type is written in C;
   applying [CoimageOf] to it fixes the category on the first try.

   UNIVERSES, measured with [Set Printing Universes. About ...] rather
   than read off the source, which carries no annotation.  Every
   constant here binds its category as [Category@{u u0 u0}], the hom
   universe identified with the proof universe -- [quot_le], [quot_epi],
   [quot_meet], [quot_join], [CoimageOf], [Iso_of_op_Iso] and the rest;
   [QuotObj] itself prints as
   [QuotObj@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}}, obj[C] →
   Type@{u}], the same collapse with the result level named.  It is
   INHERITED and belongs to Theory/Subobject.v, the first carrier in
   dependency order, whose [SubObj] record holds a mono and its [Monic]
   proof under two universe variables and prints as
   [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] →
   Type@{max(u,u0)}]; Theory/Subobject/Lattice.v's header records the
   same inheritance for the same reason, and nothing is re-attributed
   here.  Two further constraints are likewise inherited, not
   introduced.  [quot_meet] carries [u0 <= prod_rect.u0],
   [u0 <= prod_rect.u1] and [u0 <= prod_rect.u2], the stdlib bounds that
   come with the sigma and pair types of [sub_le] and the pullback
   universal property.  [quot_equiv_iff_iso] carries the STRICT bound
   [u0 < u1]; measured on the donors, [SubObj_Setoid] at
   Theory/Subobject.v already carries [p < u0] and so do
   [sub_equiv_iff_mutual] and [sub_le_antisym]
   (Theory/Subobject/Lattice.v), the [Setoid] record sitting
   strictly above the proof universe.  No constant here is pinned to
   [Set].

   NOT DELIVERED.  No concrete category: this file has no [HasPushouts],
   no [WidePullback] at C^op, no [HasCoimages] and no [Terminal]
   instance for anything, and exhibits no quotient object of any object
   -- the whole development is a conditional over structure supplied
   from outside, and docs/INHABITATION.md is where the question of which
   witnesses exist is settled.  Mac Lane's two illustrations are
   therefore NOT here: the clause that quotient objects are the usual
   quotients where epis are surjections is not stated over [Sets] (the
   ingredient exists, [epic_implies_surjective] at Instance/Sets.v,
   and is not consumed), and the G/N reading of the quotient objects of
   a group appears only as prose in this header, the tree carrying no
   group theory wired to [QuotObj].  No wide pushouts: Structure/
   Pullback/Wide.v has no wide-pushout vocabulary at all (grep for
   WidePushout over the tree returns nothing) and NONE IS ADDED here --
   [quot_wide_meet] takes a [WidePullback] IN C^op, which is a wide
   pushout of C spelled the other way, and the reader must supply it as
   such.  No total forms: [sub_intersection] under [HasWidePullbacks]
   and [sub_wide_join_via] over an indexed coproduct are not
   transported, and neither are the degenerate-index lemmas
   ([IsIntersection_empty], [IsUnion_empty_of_least], the singletons) or
   [sub_meet_is_wide_intersection].  No coimages from a factorization
   system: [ImageOf_of_OFS] at C^op would need an (E, MonoClass) system
   in C^op and none is built.  No distributivity, no Heyting or Boolean
   structure, no complement and no negation on [QuotObj x].  No
   antisymmetry at Leibniz equality: [quot_le] is Type-valued, its
   induced equivalence is the setoid, and every law below holds at ≈
   only -- [quot_le_antisym] is [sub_equiv_iff_mutual] read at C^op, and
   the two "q ≤ r iff" pairs are four separate lemmas for the same
   reason as in the subobject file.  No respectfulness for the
   accessors: [mk_quot_respects] is proved, a [quot_epi_respects] is
   not, since the epis of two equivalent quotients live over different
   codomains and the statement relating them IS [quot_equiv_iff_iso].
   No functoriality: nothing here says how quotient objects transport
   along a morphism of x, and no Galois connection or adjointness claim
   about such a transport appears. *)

(** ** Quotient objects as subobjects in the opposite category *)

(* Mac Lane §V.7: a quotient object of x is (an equivalence class of) an
   epimorphism out of x.  Since [Epic] in C is [Monic] in C^op
   (Theory/Morphisms/Duality.v), the definition is one line, the idiom of
   Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)]. *)
Definition QuotObj {C : Category} (x : C) : Type := @SubObj (C^op) x.

Section QuotientAccessors.

Context {C : Category}.
Context {x : C}.

(* Covariant readings of the record's fields: a C^op-arrow into x is a
   C-arrow out of x, definitionally (Construction/Opposite.v). *)
Definition quot_cod (q : QuotObj x) : C := sub_dom q.

Definition quot_epi (q : QuotObj x) : x ~> quot_cod q := sub_mono q.

Definition quot_is_epic (q : QuotObj x) : Epic (quot_epi q) :=
  Epic_of_op_Monic (quot_epi q) (sub_is_monic q).

(* A quotient object from an epimorphism of C. *)
Definition mk_quot {y : C} (e : x ~> y) (He : Epic e) : QuotObj x :=
  @Build_SubObj (C^op) x y e (op_Monic_of_Epic e He).

(* The setoid and the factorization preorder, read in quotient orientation:
   q ≤ r when the epi of q factors through the epi of r. *)
#[export] Instance QuotObj_Setoid : Setoid (QuotObj x) :=
  @SubObj_Setoid (C^op) x.

Definition quot_le (q r : QuotObj x) : Type := @sub_le (C^op) x q r.

End QuotientAccessors.

(** ** Isomorphisms carried across the opposite category *)

(* Four-field permutations, with no proof content: [iso_to_from] on one
   side is [iso_from_to] on the other, because the two round trips swap
   endpoints when the composition is reversed.  Construction/Opposite.v:
   146's [Isomorphism_Opposite] covers only the C-to-C^op direction and
   fixes [to := from i]; both directions and the other orientation are
   needed below. *)

Section OppositeIso.

Context {C : Category}.

Definition Iso_of_op_Iso {a b : C} (i : @Isomorphism (C^op) a b) : b ≅[C] a :=
  @Build_Isomorphism C b a (to i) (from i) (iso_from_to i) (iso_to_from i).

Definition op_Iso_of_Iso {a b : C} (j : a ≅[C] b) :
  @Isomorphism (C^op) b a :=
  @Build_Isomorphism (C^op) b a (to j) (from j) (iso_from_to j)
    (iso_to_from j).

End OppositeIso.

(** ** The covariant API *)

Section QuotientCovariant.

Context {C : Category}.
Context {x : C}.

(* C^op^op is C by conversion, so the quotient objects of C^op ARE the
   subobjects of C, at Leibniz equality and with no tactic -- a claim
   about the DATA of the type, which is the one place Leibniz equality
   is the right relation. *)
Example QuotObj_op_is_SubObj : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(* The factorization order, covariantly, on the nose. *)
Example quot_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(* The setoid, covariantly, as far as conversion reaches: the witness is
   an isomorphism IN C^op and the composition must be annotated.  The
   naive spelling, with a C-isomorphism [quot_cod q ≅ quot_cod r] and
   [to i ∘ quot_epi q ≈ quot_epi r], is REFUSED here (cannot unify); the
   header quotes the refusal.  [quot_equiv_iff_iso] below is the
   covariant statement, at ≈ rather than at [eq_refl]. *)
Example quot_equiv_unfold (q r : QuotObj x) :
  (q ≈ r)
  = { i : @Isomorphism (C^op) (quot_cod q) (quot_cod r)
    & (to i ∘[C] quot_epi r) ≈ quot_epi q }
  := eq_refl.

Definition quot_le_refl (q : QuotObj x) : quot_le q q :=
  @sub_le_refl (C^op) x q.

Definition quot_le_trans (q r s : QuotObj x) :
  quot_le q r → quot_le r s → quot_le q s :=
  @sub_le_trans (C^op) x q r s.

(* The mediating arrow of a factorization between quotient objects is
   itself an EPI of C: [sub_le_monic] (Theory/Subobject.v) read at
   C^op, then carried back by [Epic_of_op_Monic].  Both the target type
   and the bridge's category have to be given explicitly, since the
   arrow's type is spelled at C^op and Rocq would otherwise read [Epic]
   there -- which is [Monic] in C, the wrong claim. *)
Definition quot_le_epic (q r : QuotObj x) (H : quot_le q r) :
  @Epic C (quot_cod r) (quot_cod q) (`1 H) :=
  @Epic_of_op_Monic C (quot_cod r) (quot_cod q) (`1 H)
    (@sub_le_monic (C^op) x q r H).

(* Mediating arrows are unique, by epicness of the epi factored through. *)
Definition quot_le_unique (q r : QuotObj x)
  (k k' : quot_cod r ~> quot_cod q) :
  k ∘ quot_epi r ≈ quot_epi q → k' ∘ quot_epi r ≈ quot_epi q → k ≈ k' :=
  @sub_le_unique (C^op) x q r k k'.

(* Mac Lane's equivalence of epis: each factors through the other. *)
Definition quot_equiv_iff_mutual (q r : QuotObj x) :
  (q ≈ r) ↔ (quot_le q r * quot_le r q) :=
  @sub_equiv_iff_mutual (C^op) x q r.

Definition quot_le_antisym (q r : QuotObj x) :
  quot_le q r → quot_le r q → q ≈ r :=
  @sub_le_antisym (C^op) x q r.

Definition quot_le_of_equiv (q r : QuotObj x) : q ≈ r → quot_le q r :=
  @sub_le_of_equiv (C^op) x q r.

Definition quot_ge_of_equiv (q r : QuotObj x) : q ≈ r → quot_le r q :=
  @sub_ge_of_equiv (C^op) x q r.

(* The covariant characterization of the setoid, which conversion does
   NOT give (see [quot_equiv_unfold]): two quotient objects are
   equivalent exactly when an isomorphism of their codomains IN C
   carries the one epi to the other.  Both directions go through the
   symmetry of the setoid, because the C^op reading of [q ≈ r] carries
   the isomorphism in the opposite orientation; the field permutations
   then leave nothing to prove, and each branch ends in [exact]. *)
Theorem quot_equiv_iff_iso (q r : QuotObj x) :
  (q ≈ r) ↔ { i : quot_cod q ≅[C] quot_cod r
            & to i ∘ quot_epi q ≈ quot_epi r }.
Proof.
  split.
  - intros H.
    symmetry in H.
    destruct H as [i Hi].
    exists (Iso_of_op_Iso i).
    exact Hi.
  - intros [j Hj].
    symmetry.
    exists (op_Iso_of_Iso j).
    exact Hj.
Defined.

(* Equivalent epis out of x present the same quotient object, the
   identity isomorphism witnessing it. *)
Definition mk_quot_respects {y : C} (e e' : x ~> y)
  (He : Epic e) (He' : Epic e') : e ≈ e' → mk_quot e He ≈ mk_quot e' He'.
Proof.
  intros Hee.
  apply quot_equiv_iff_iso.
  exists iso_id.
  simpl.
  rewrite id_left.
  now symmetry.
Defined.

(* The one-directional form with the isomorphism handed in the OTHER way
   round -- from the codomain of the second argument to that of the
   first -- which is the shape a consumer comparing a computed quotient
   with a named one (Instance/Grp/QuotObj.v's isomorphism-theorem reading)
   actually has in hand.  First proved in that file during the parallel
   build; lifted here at integration as a corollary of
   [quot_equiv_iff_iso] rather than kept as a second proof. *)
Corollary quot_equiv_of_cod_iso (q r : QuotObj x)
  (i : quot_cod r ≅[C] quot_cod q)
  (H : to i ∘ quot_epi r ≈ quot_epi q) : q ≈ r.
Proof.
  symmetry.
  exact (snd (quot_equiv_iff_iso r q) (i; H)).
Defined.

End QuotientCovariant.

(** ** Monic in C^op is Epic in C, both ways *)

Definition monic_op_iff_epic {C : Category} {x y : C} (f : x ~> y) :
  (@Monic (C^op) y x f → @Epic C x y f) * (@Epic C x y f → @Monic (C^op) y x f)
  := (Epic_of_op_Monic f, op_Monic_of_Epic f).

Section Bridges.

Context {C : Category}.
Context {x y : C}.

(* The two projections, named.  The other two bridges of
   Theory/Morphisms/Duality.v go the other way round the square --
   [Monic_of_op_Epic] turns an [Epic] of C^op into a [Monic] of C
   and [op_Epic_of_Monic] turns a [Monic] of C into an [Epic] of
   C^op -- which is what makes [QuotObj_op_is_SubObj] a genuine
   identification rather than a one-way reading: the monicity witness a
   subobject of C carries is exactly the epicness witness a quotient
   object of C^op carries. *)
Definition epic_of_monic_op (f : x ~> y) : @Monic (C^op) y x f → @Epic C x y f
  := fst (monic_op_iff_epic f).

Definition monic_op_of_epic (f : x ~> y) : @Epic C x y f → @Monic (C^op) y x f
  := snd (monic_op_iff_epic f).

End Bridges.

(** ** The top quotient: x by the identity *)

Section QuotientTop.

Context {C : Category}.
Context {x : C}.

(* [sub_top] at C^op.  It is the FINEST quotient of x, and the greatest
   element of [quot_le]: every quotient of x factors through it. *)
Definition quot_top : QuotObj x := @sub_top (C^op) x.

Example quot_top_cod : quot_cod quot_top = x := eq_refl.
Example quot_top_epi : quot_epi quot_top = @id C x := eq_refl.

Definition quot_top_greatest (q : QuotObj x) : quot_le q quot_top :=
  @sub_top_greatest (C^op) x q.

End QuotientTop.

(** ** The lattice of quotient objects, by transport of the subobject one *)

Section QuotientMeet.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(* The pushout of two epis, read as a quotient object: the meet for
   [quot_le] -- the greatest lower bound, the finest quotient that
   factors through both (the interface stub's gloss had the direction of
   "factors through" backwards; corrected at integration). *)
Definition quot_meet (q r : QuotObj x) : QuotObj x :=
  @sub_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeet.

(** *** The meet laws, all instantiated at C^op *)

Section QuotientMeetLaws.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(* Below both factors: the two pushout injections, read backwards. *)
Definition quot_meet_le_l (q r : QuotObj x) : quot_le (quot_meet q r) q :=
  @sub_meet_le_l (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_le_r (q r : QuotObj x) : quot_le (quot_meet q r) r :=
  @sub_meet_le_r (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(* Mac Lane §V.7 dualized: the pushout is the GREATEST quotient object
   below both, in the factorization order [quot_le] -- the finest
   quotient that factors through both q and r.  See the header on why a
   reader who orders by the size of the codomain reads this as a join. *)
Definition quot_meet_is_glb (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le w q → quot_le w r → quot_le w (quot_meet q r) :=
  @sub_meet_is_glb (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(* The order-theoretic predicate transports unchanged: [IsMeet] at C^op
   is the two-element case of [IsIntersection], whose two clauses are
   stated with [sub_le], which at C^op is [quot_le] on the nose. *)
Definition quot_meet_IsMeet (q r : QuotObj x) :
  @IsMeet (C^op) x q r (quot_meet q r) :=
  @sub_meet_IsMeet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

#[export] Instance quot_meet_respects :
  Proper (equiv ==> equiv ==> equiv) (@quot_meet C HP x) :=
  @sub_meet_respects (C^op) (HasPullbacks_op_of_HasPushouts HP) x.

Definition quot_meet_comm (q r : QuotObj x) : quot_meet q r ≈ quot_meet r q :=
  @sub_meet_comm (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_assoc (q r s : QuotObj x) :
  quot_meet (quot_meet q r) s ≈ quot_meet q (quot_meet r s) :=
  @sub_meet_assoc (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r s.

Definition quot_meet_idem (q : QuotObj x) : quot_meet q q ≈ q :=
  @sub_meet_idem (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(* The identity quotient is a unit for the meet. *)
Definition quot_meet_top (q : QuotObj x) : quot_meet q quot_top ≈ q :=
  @sub_meet_top (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(* "q ≤ r iff q ∧ r ≈ q", in two lemmas: [quot_le] is Type-valued data
   and the two directions carry different data. *)
Definition quot_meet_of_le (q r : QuotObj x) :
  quot_le q r → quot_meet q r ≈ q :=
  @sub_meet_of_le (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_le_of_meet (q r : QuotObj x) :
  quot_meet q r ≈ q → quot_le q r :=
  @sub_le_of_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeetLaws.

(** *** The bottom quotient, under an epic arrow to the terminal object *)

Section QuotientBottom.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x : C}.

(* [sub_bot] at C^op.  Structure/Initial.v makes [Initial (C^op)] the
   same thing as [Terminal C], and [sub_bot]'s hypothesis [Monic zero]
   becomes [Epic (one : x ~> 1)] through [op_Monic_of_Epic].  The
   hypothesis is REAL but OBJECT-DEPENDENT rather than rare, and it is
   left standing here only because this file builds no witness: in
   [Sets] the arrow x → 1 is epic at every INHABITED x and is NOT epic
   at the empty setoid (two maps 1 → Y agree after ∅ → 1 for free), and
   Instance/Sets/QuotObj.v carries both halves -- the three-line
   [Sets_one_epic_of_inhabited], whence the bottom quotient object
   [Sets_quot_bot] at every inhabited setoid, and the refutation
   [Sets_one_not_epic_empty].  The same inhabited/empty split governs
   [Grp], [Ab] and [Top], while in a thin category every arrow is epic.
   An earlier revision of this paragraph said "in most categories the
   arrow to the terminal object is not epic", which an audit refuted by
   discharging the hypothesis at [Sets] on [bool]; a second revision
   said the discharge "lives with the witnesses" before any had been
   landed, which a second audit caught. *)
Definition quot_bot (He : Epic (@one C T x)) : QuotObj x :=
  @sub_bot (C^op) T x (op_Monic_of_Epic (@one C T x) He).

(* The coarsest quotient: every quotient object of x sits above it. *)
Definition quot_bot_least (He : Epic (@one C T x)) (q : QuotObj x) :
  quot_le (quot_bot He) q :=
  @sub_bot_least (C^op) T x (op_Monic_of_Epic (@one C T x) He) q.

(* The formal dual of [zero_monic_of_strict] (Theory/Subobject/
   Lattice.v) at C^op, recorded for SYMMETRY ONLY: its strict-
   initial hypothesis reads here as a COSTRICT terminal object -- every
   object receiving a map from 1 is isomorphic to 1 -- which is a
   near-vacuous condition: it does not hold in [Sets] (1 → bool exists
   and bool is not 1) and in any category with a zero object it forces every
   object to be terminal, so it is satisfied essentially only by the
   trivial category.  It is NOT the practical route to [Epic one]; that
   route is the object-by-object one described above (inhabitedness at
   [Sets]).  The isomorphism is supplied in C and carried over by
   [op_Iso_of_Iso]; no category in this tree is shown to satisfy the
   hypothesis, and none should be expected to. *)
Definition one_epic_of_costrict
  (Hco : ∀ (y : C) (f : @terminal_obj C T ~> y),
           @terminal_obj C T ≅[C] y) :
  Epic (@one C T x) :=
  Epic_of_op_Monic (@one C T x)
    (@zero_monic_of_strict (C^op) T x
       (fun y f => op_Iso_of_Iso (Hco y f))).

End QuotientBottom.

(** *** Wide meets, over a wide pullback of C^op *)

Section QuotientWideMeet.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → QuotObj x).

(* [sub_wide_intersection] at C^op.  The [WidePullback] argument is a
   wide pullback IN C^op, which is a wide pushout of C; Structure/
   Pullback/Wide.v supplies no wide-pushout vocabulary and none is added
   here, so the caller states it in the C^op spelling.  The index [j0]
   survives the transport for the reason recorded in the subobject
   file's header: the wide record carries no leg to the common
   codomain, so the epi into the apex is read off a chosen member. *)
Definition quot_wide_meet (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) : QuotObj x :=
  @sub_wide_intersection (C^op) x J S j0 W.

Definition quot_wide_meet_IsIntersection (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  @IsIntersection (C^op) x J S (quot_wide_meet j0 W) :=
  @sub_wide_intersection_IsIntersection (C^op) x J S j0 W.

Definition quot_wide_meet_index_irrelevant (j0 j1 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  quot_wide_meet j0 W ≈ quot_wide_meet j1 W :=
  @sub_wide_intersection_index_irrelevant (C^op) x J S j0 j1 W.

End QuotientWideMeet.

(** ** Coimages, and joins by coimage of the pairing *)

Section Coimages.

Context {C : Category}.

(* An image of C^op, read forwards: the coarsest quotient of x through
   which f factors.  Its fields read [im_sub : QuotObj x],
   [im_factor : quot_cod im_sub ~> y] with
   [im_factor ∘[C] quot_epi im_sub ≈ f] -- the composition MUST be
   annotated with C, for the same reason as in [quot_equiv_unfold]:
   written bare, [∘] is elaborated in C^op from [im_factor]'s spelled
   type and the sentence does not typecheck -- and [im_least] saying
   that any quotient w of x with [g ∘[C] quot_epi w ≈ f] satisfies
   [quot_le im_sub w]. *)
Definition CoimageOf {x y : C} (f : x ~> y) : Type := @ImageOf (C^op) y x f.

End Coimages.

(* Following the [Cocartesian] (Structure/Cocartesian.v) and
   [Initial] (Structure/Initial.v) precedent, this is NOTATION rather
   than a definition, so that instance resolution for the underlying
   [HasImages] class still fires at C^op. *)
Notation "'HasCoimages' C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.
Notation "@HasCoimages C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.

Section QuotientJoin.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context {x : C}.

(* The copairing of C^op is the pairing of C.  Spelling it in C is what
   makes [CoimageOf] below pick the right category (see the header). *)
Definition quot_pairing (q r : QuotObj x) :
  x ~{C}~> @product_obj C CC (quot_cod q) (quot_cod r) :=
  @fork C CC x (quot_cod q) (quot_cod r) (quot_epi q) (quot_epi r).

(* The join of two quotient objects: the coimage of the pairing of their
   epis into the product of their codomains, given such a coimage. *)
Definition quot_join_via (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) : QuotObj x :=
  @sub_join_via (C^op) CC x q r I.

Definition quot_join_via_le_l (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le q (quot_join_via q r I) :=
  @sub_join_via_le_l (C^op) CC x q r I.

Definition quot_join_via_le_r (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le r (quot_join_via q r I) :=
  @sub_join_via_le_r (C^op) CC x q r I.

(* The coimage is the LEAST quotient object above both. *)
Definition quot_join_via_is_lub (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) (w : QuotObj x) :
  quot_le q w → quot_le r w → quot_le (quot_join_via q r I) w :=
  @sub_join_via_is_lub (C^op) CC x q r I w.

Definition quot_join_via_IsJoin (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  @IsJoin (C^op) x q r (quot_join_via q r I) :=
  @sub_join_via_IsJoin (C^op) CC x q r I.

End QuotientJoin.

(** *** The join as a lattice operation, with coimages chosen *)

Section QuotientJoinLattice.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_join (q r : QuotObj x) : QuotObj x :=
  @sub_join (C^op) CC x HI q r.

Definition quot_join_le_l (q r : QuotObj x) : quot_le q (quot_join q r) :=
  @sub_join_le_l (C^op) CC HI x q r.

Definition quot_join_le_r (q r : QuotObj x) : quot_le r (quot_join q r) :=
  @sub_join_le_r (C^op) CC HI x q r.

Definition quot_join_is_lub (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le q w → quot_le r w → quot_le (quot_join q r) w :=
  @sub_join_is_lub (C^op) CC HI x q r.

Definition quot_join_IsJoin (q r : QuotObj x) :
  @IsJoin (C^op) x q r (quot_join q r) :=
  @sub_join_IsJoin (C^op) CC HI x q r.

#[export] Instance quot_join_respects :
  Proper (equiv ==> equiv ==> equiv) quot_join :=
  @sub_join_respects (C^op) CC HI x.

Definition quot_join_comm (q r : QuotObj x) : quot_join q r ≈ quot_join r q :=
  @sub_join_comm (C^op) CC HI x q r.

Definition quot_join_assoc (q r s : QuotObj x) :
  quot_join (quot_join q r) s ≈ quot_join q (quot_join r s) :=
  @sub_join_assoc (C^op) CC HI x q r s.

Definition quot_join_idem (q : QuotObj x) : quot_join q q ≈ q :=
  @sub_join_idem (C^op) CC HI x q.

Definition quot_join_of_le (q r : QuotObj x) :
  quot_le q r → quot_join q r ≈ r :=
  @sub_join_of_le (C^op) CC HI x q r.

Definition quot_le_of_join (q r : QuotObj x) :
  quot_join q r ≈ r → quot_le q r :=
  @sub_le_of_join (C^op) CC HI x q r.

End QuotientJoinLattice.

(** *** Absorption: the two operations make a lattice on the setoid *)

Section QuotientAbsorption.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_meet_absorb (q r : QuotObj x) :
  quot_meet q (quot_join q r) ≈ q :=
  @sub_meet_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

Definition quot_join_absorb (q r : QuotObj x) :
  quot_join q (quot_meet q r) ≈ q :=
  @sub_join_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

End QuotientAbsorption.
