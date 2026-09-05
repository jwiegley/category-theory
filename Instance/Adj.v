Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * The category of adjunctions between two fixed categories *)

(* nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
     "Transformations of Adjoints", book p. 101: display (8) and the
     paragraph that names the category.

   Mac Lane's own sentence, from that page: "For the two given categories
   X and A we thus have a new category A^(adj)X, the CATEGORY OF ADJUNCTIONS
   from X to A; its objects are the adjunctions <F, G; eta, eps>; its arrows
   are the transformations (conjugate pairs) <sigma, tau>, with the
   composition just noted."

   LETTERS.  Mac Lane's adjunction <F, G, phi, eta, eps> : X ⇀ A has
   F : X ⟶ A on the left and G : A ⟶ X on the right, so his X is this
   file's D and his A is this file's C, matching the library's own
   orientation F : D ⟶ C, U : C ⟶ D.  His G is this file's U.

       objects        triples (F, U, F ⊣ U), the type [AdjObj]
       arrows         conjugate pairs, the record [ConjPair]
       identity       the pair (nat_id, nat_id)
       composition    display (8), see below

   This is the hom-category between C and D of the 2-category Adj of
   categories, adjunctions, and their maps; the sibling file
   [Instance.Adjoints] instead bundles categories and adjunctions into a
   1-category (objects are categories, arrows are adjunctions).

   THE CONDITION ON AN ARROW, WHICH THIS FILE NOW IMPOSES.  A morphism of
   this category is not a bare pair of natural transformations: sigma and
   tau are required to be CONJUGATE, that is, to correspond under the two
   hom-set transposes.  That condition is [Conjugate] of
   Adjunction/Conjugate.v, which is Mac Lane's §IV.7 Definition 2 hom-set
   square quantified over every transposable arrow; [conjugate_iff_from]
   there reads the same square through the inverse transposes and
   [conjugate_characterizations] proves the four equivalent pasting forms
   (the two mate formulas and the unit and counit equations).  The record
   [ConjPair] below carries that square as its third field, so the hom is
   the product of the two transformation setoids CUT DOWN by that square,
   and the pair (nat_id, nat_id) and the composite pair have to be PROVED
   to satisfy it.  (That the cut is STRICT is not proved here: no pair of
   transformations that is not conjugate is exhibited.)  This supersedes
   the caveat this file used to carry, which recorded that its hom was the
   bare product setoid ([D,C] × [C,D]) with no such condition, that every
   category obligation therefore discharged with no content, and that
   retyping the hom was future work.  The old
   coarse category is NOT kept: nothing in the tree consumed it, measured
   by USE rather than by name -- before this change no `.v` file anywhere
   Required Category.Instance.Adj (the sibling Instance/Adj/Forgetful.v,
   added alongside, is the first), and every other occurrence of the bare
   token [Adj] in the tree is a local hypothesis of that name or is prose
   (four of them section variables, hence glob-recorded as `var` rather
   than as declarations; the rest are [intros]-bound or prose).
   Adjunction/Map.v's RELATION paragraph described the OLD hom of this
   file; it is corrected in the same commit rather than left stale.

   THE VARIANCE, WHICH IS THE ONE DESIGN DECISION.  Conjugate.v declares

       Conjugate (A : F ⊣ U) (A' : F' ⊣ U') (sigma : F' ⟹ F) (tau : U ⟹ U')

   -- sigma BACKWARD and tau FORWARD relative to the primes.  Mac Lane's
   p. 101 labels the pair the other way: in his forgetful-functor display
   sigma points DOWN, from F to F', and tau points UP, from G' to G, so a
   transformation from the first adjunction to the second is
   sigma : F ⟹ F' together with tau : G' ⟹ G.  That labelling is the same
   relation with its two adjunction arguments EXCHANGED, not a second
   notion, exactly as Conjugate.v's own ORIENTATION note records for
   Riehl.  So the hom from x to y here is

       Conjugate (adjobj_adj y) (adjobj_adj x) sigma tau

   which types sigma : (left of x) ⟹ (left of y) and
   tau : (right of y) ⟹ (right of x).  The positive half of that is pinned
   by [ConjPair]'s own field types below, which typecheck only under this
   reading; the negative half -- that [Conjugate A' A] REJECTS
   sigma : F' ⟹ F at an abstract pair A : F ⊣ U, A' : F' ⊣ U' -- was
   measured out of tree; this file carries no probe, and the fact is
   pinned in Test/ProbeAdjCat395.v, added in the same commit.

   DISPLAY (8), AND WHERE THE CATEGORY LAWS NOW REST.  Mac Lane writes the
   vertical composite of two conjugate pairs as
   <sigma', tau'> ∘ <sigma, tau> = <sigma' · sigma, tau · tau'>: the SECOND
   component composes in the OPPOSITE order.  Read the label precisely: on
   the page (8) sits on the two-arrow CHAIN, and this equation is the
   unnumbered running text just below it; "display (8)" below is shorthand
   for the equation.  Both of the two proof
   obligations that the category's [id] and [compose] fields now generate
   are discharged by naming a theorem that was ALREADY IN TREE before this
   file was retyped, and neither is re-proved here:

       Adjunction/Conjugate.v:471  conjugate_id
         : Conjugate A1 A1 nat_id nat_id
       Adjunction/Conjugate.v:479  conjugate_compose
         : Conjugate A1 A2 sigma tau → Conjugate A2 A3 sigma' tau'
           → Conjugate A1 A3 (sigma ∙ sigma') (tau' ∙ tau)

   Note [(tau' ∙ tau)] in that conclusion: the donor already composes the
   second component backward, which IS display (8), and it already fits
   this category's composition with no rearrangement, since the hom from
   x to y is [Conjugate (adj y) (adj x)] and so the three adjunction
   arguments A1, A2, A3 are the codomain, the middle and the domain in
   that order.  [conj_mate_id] and [conj_mate_compose] sit beside them
   there.

   That those two obligations no longer discharge by themselves is
   MEASURED, not assumed: with four automation attempts inserted ahead of
   each [exact], neither obligation is closed by [cat], by
   [program_simpl], by [simpl; intros; cat] or by [auto], while the
   [exact] itself does close them -- eight rejections against one control,
   checked out of tree, this file carrying no probe of its own.  The
   OTHER five obligations (respectfulness of composition and the four
   category laws) are still componentwise equations between natural
   transformations and still close by the ordinary automation, just as
   they did before the retyping; what changed is that [id] and [compose]
   no longer TYPECHECK at all without the two theorems above.

   COST.  Requiring Adjunction/Conjugate.v grows this file's transitive
   in-project closure from 18 modules to 19, excluding the file itself,
   and the single added module is Adjunction/Conjugate.vo -- everything
   Conjugate.v needs, Instance/Sets included, was already reachable
   through Theory/Adjunction.v.

   THE HOM-SETOID.  Two conjugate pairs are identified when both
   components agree in the transformation setoid.  Comparing only ONE
   component would give the same relation, and that is proved rather than
   asserted: [conj_pair_right_unique] recovers agreement of the tau's from
   agreement of the sigma's, and [conj_pair_left_unique] the converse,
   each in three lines over Conjugate.v's [conj_mate_uniq] /
   [conj_mate_inv_uniq] and the matching respectfulness lemma.  This is
   the reason the third field of [ConjPair] costs nothing at the setoid
   level: a conjugate pair is determined by either of its legs.

   STRENGTHS, MEASURED STRICT FIRST.  Four [Example]s below close by
   [eq_refl] rather than by `≈`, and these are Leibniz equalities of the
   underlying [Transform] values, which is stronger than the hom-setoid's
   own `≈`: the identity's two components ARE [nat_id] on the nose
   ([adj_id_sigma], [adj_id_tau]), and the composite's two components ARE
   the two vertical composites of display (8), in the two opposite orders
   ([adj_compose_sigma], [adj_compose_tau]).  They reduce because
   [ConjPair] has primitive projections, so a projection of a record
   literal reduces whatever the opacity of the third field.

   THE 2-CATEGORICAL STRUCTURE IS NOT HERE, BUT IT EXISTS.  Mac Lane's
   §IV.8 Theorem 2 and Exercise 1 -- horizontal composition of conjugate
   pairs, its bifunctoriality, and the interchange law -- are
   Instance/Adj/Bicategory.v, which assembles [Adj_Bicategory] with the
   categories [Adj C D] built here as its hom-categories (its
   [Adj_bicat_is_Adj] records that at [eq_refl]).  Nothing in THIS file
   consumes or mentions that structure; the sentence this paragraph used
   to carry, that no 2-categorical structure existed at all, is no longer
   true of the tree and has been replaced.

   NOT DELIVERED HERE: no comparison with Theory/Bicategory/Mates.v or
   with Instance/Cat/Bicategory/Conjugate.v; no relation to
   Adjunction/Map.v's maps of adjunctions, whose
   identity-bounding-functor case is this file's hom (that file's
   [map_adj_hom_is_conjugate] records the identification, and nothing here
   consumes it); nothing about limits or colimits of [Adj C D]; and no
   concrete witness at a named pair of categories.  The two forgetful
   functors of the same page are Instance/Adj/Forgetful.v. *)

(* An object of the category: a left adjoint, a right adjoint, and an
   adjunction between them.  `∃` here is [sigT], so the adjunction is data
   and no choice principle is involved. *)
Definition AdjObj (C D : Category) : Type :=
  ∃ (F : D ⟶ C) (U : C ⟶ D), F ⊣ U.

Definition adjobj_left {C D : Category} (x : AdjObj C D) : D ⟶ C := `1 x.
Definition adjobj_right {C D : Category} (x : AdjObj C D) : C ⟶ D := `1 `2 x.
Definition adjobj_adj {C D : Category} (x : AdjObj C D) :
  adjobj_left x ⊣ adjobj_right x := `2 `2 x.

(* An arrow x ⟶ y: Mac Lane's conjugate pair <sigma, tau>, with sigma
   forward on the left adjoints, tau backward on the right adjoints, and
   the hom-set square relating them. *)
Record ConjPair {C D : Category} {x y : AdjObj C D} : Type := {
  conj_left  : adjobj_left x ⟹ adjobj_left y;
  conj_right : adjobj_right y ⟹ adjobj_right x;
  conj_pair_law :
    Conjugate (adjobj_adj y) (adjobj_adj x) conj_left conj_right
}.

(* Two conjugate pairs agree when both components agree; by
   [conj_pair_right_unique] and [conj_pair_left_unique] below, comparing
   either component alone would give the same relation. *)
#[export]
Program Instance ConjPair_Setoid {C D : Category} {x y : AdjObj C D} :
  Setoid (@ConjPair C D x y) := {|
  equiv := fun f g => (conj_left f ≈ conj_left g)
                    ∧ (conj_right f ≈ conj_right g)
|}.
Next Obligation.
  constructor.
  - intros f; split; reflexivity.
  - intros f g [Hl Hr]; split; symmetry; assumption.
  - intros f g h [Hl Hr] [Hl' Hr']; split; etransitivity; eassumption.
Qed.

Program Definition Adj (C D : Category) : Category := {|
  obj     := AdjObj C D;
  hom     := fun x y => @ConjPair C D x y;
  homset  := fun x y => @ConjPair_Setoid C D x y;
  id      := fun x => {| conj_left := nat_id; conj_right := nat_id |};
  compose := fun x y z f g =>
    {| conj_left  := conj_left f ∙ conj_left g
     ; conj_right := conj_right g ∙ conj_right f |}
|}.
(* The identity pair is conjugate: Conjugate.v's [conjugate_id]. *)
Next Obligation. exact (conjugate_id (adjobj_adj x)). Qed.
(* The composite pair is conjugate: Conjugate.v's [conjugate_compose],
   whose conclusion already composes the second component backward. *)
Next Obligation.
  exact (conjugate_compose (adjobj_adj z) (adjobj_adj y) (adjobj_adj x)
           _ _ _ _ (conj_pair_law f) (conj_pair_law g)).
Qed.
Next Obligation. proper; simpl in *; simplify; rewrites; reflexivity. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* Either leg of a conjugate pair determines the other, so the hom-setoid
   above could have compared just one of them. *)
Section Determined.
Context {C D : Category} {x y : AdjObj C D}.

Lemma conj_pair_right_unique (f g : @ConjPair C D x y) :
  conj_left f ≈ conj_left g → conj_right f ≈ conj_right g.
Proof.
  intro H.
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_respects.
Qed.

Lemma conj_pair_left_unique (f g : @ConjPair C D x y) :
  conj_right f ≈ conj_right g → conj_left f ≈ conj_left g.
Proof.
  intro H.
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_inv_respects.
Qed.

End Determined.

(* The identity and Mac Lane's display (8), pinned at Leibniz equality of
   the underlying natural transformations -- strictly stronger than the
   hom-setoid's `≈`.  The second component of a composite is the vertical
   composite taken in the OPPOSITE order, which is the whole content of
   display (8). *)

Example adj_id_sigma (C D : Category) (x : Adj C D) :
  conj_left (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_id_tau (C D : Category) (x : Adj C D) :
  conj_right (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_compose_sigma (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_left (f ∘ g) = conj_left f ∙ conj_left g := eq_refl.

Example adj_compose_tau (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_right (f ∘ g) = conj_right g ∙ conj_right f := eq_refl.
