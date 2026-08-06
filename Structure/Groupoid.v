Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.

Generalizable All Variables.

(** * Groupoids: the property, and the vertex-group structure *)

(* nLab:      https://ncatlab.org/nlab/show/groupoid
   nLab:      https://ncatlab.org/nlab/show/vertex+group
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.5, printed p. 20 (Definition 9 and the remark
              following it)
   Book:      Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
              September 2005), §7.7, printed p. 175
   Book:      Riehl, "Category Theory in Context", Definition 1.1.12 and
              Example 1.1.13(i), printed p. 8
   Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,
              §3.2.5 Exercise 3.32, printed pp. 88-89

   A groupoid is a category in which every morphism is invertible.  This file
   supplies the PREDICATE saying so — [IsGroupoid] — and the local structure
   theory that Mac Lane records immediately after the definition: each object
   x of a groupoid carries a vertex group hom(x, x), and any arrow f : x ~> x'
   conjugates hom(x, x) isomorphically onto hom(x', x').

   Until now the name [Groupoid] was bound in-tree to a CONSTRUCTION —
   Construction/Groupoid.v:103 builds the core (maximal subgroupoid) of a
   category — with no property for it to satisfy.  [core_is_groupoid] below
   closes that gap.

   Contents:

       IsGroupoid C            every morphism of C is an isomorphism
       ginv G f                the chosen inverse of f, with its calculus
       core_is_groupoid        the core of any category is a groupoid
       IsGroupoid_op           C^op is a groupoid whenever C is
       MonInverses M           a two-sided inverse operation on a monoid
       deloop_groupoid_iff     M is a group  <->  B M is a groupoid
       vertex_group G x        hom(x, x) as a group
       MonHom, MonIso          monoid homomorphisms and isomorphisms
       conjugation_iso G f     hom(x, x) ≅ hom(x', x') by conjugation
       deloop_nat_not_groupoid B (ℕ, +) is NOT a groupoid
       deloop_bool_groupoid    B (Z/2) is
       Z3_Grp                  Z/3, the smallest group whose inversion map
                               is not the identity function

   The connectedness predicate and the structure theorem it feeds — a
   connected groupoid is equivalent to the delooping of any one of its vertex
   groups — are in Structure/Groupoid/Connected.v; the inversion isomorphism
   C ≅ C^op is in Structure/Groupoid/Inversion.v. *)

(* Why the vertex group, and what connectedness adds

   nLab:  https://ncatlab.org/nlab/show/groupoid
   nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the
          London Mathematical Society 19, 1987
   Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",
          Notices of the American Mathematical Society 43, 1996

   The history of groupoids — Brandt's 1926/27 paper, Ehresmann's
   differentiable groupoids, Brown's van Kampen theorem, the groupoid model
   of intensional type theory — is told in the essay heading
   Construction/Groupoid.v, and is not repeated here.  What this file adds is
   the ANATOMY: what a groupoid is made of once one knows every arrow
   inverts.

   Mac Lane's §I.5 gives the answer in two sentences.  The endomorphisms at a
   single object form a group, the vertex group (also written Aut(x), or
   π₁(X, x) when the groupoid is a fundamental groupoid); and an arrow
   f : x ~> x' does not merely connect two objects but identifies their vertex
   groups, by a ↦ f ∘ a ∘ f⁻¹.  Both halves are below: [vertex_group] and
   [conjugation_iso].  The conjugation is not canonical — a different arrow
   x ~> x' generally induces a different isomorphism, differing by an inner
   automorphism — which is exactly why the fundamental group of a
   path-connected space is well defined only up to inner automorphism unless
   a base point is chosen, and why Brown's base-point-free fundamental
   groupoid is the more robust invariant (Brown 1987).  The library records
   the dependence honestly: [conjugation_iso] takes the arrow f as an
   argument, and nothing claims the result is independent of it.

   The vertex group does not, by itself, determine the groupoid: a groupoid
   with two objects and no arrow between them has two vertex groups, and is
   not equivalent to the delooping of the one at either object.  That is
   [Two_Discrete_no_deloop_equivalence] in Structure/Groupoid/Connected.v,
   stated there at the object TwoDX; the argument it uses,
   [deloop_equiv_connected], quantifies over the object, so the other case
   costs nothing.  Connectedness is precisely the hypothesis that repairs
   this, and it is the subject of that file.

   Weinstein's survey supplies the reason the extra generality earns its keep:
   many objects display symmetry while having few or no nontrivial
   automorphisms, and the symmetry lives in the arrows BETWEEN objects rather
   than at any one of them (Weinstein 1996).  A group is the degenerate case
   in which there is only one object to move between — the reading this file
   makes precise as [deloop_groupoid_iff] and [vertex_group], the two halves
   of the dictionary between groups and one-object groupoids. *)

(** ** The predicate *)

(* A groupoid is a category in which every morphism has a two-sided inverse.
   This is Mac Lane §I.5 Definition 9, Awodey §7.7, and Riehl Definition
   1.1.12, all three verbatim; the donor is Theory/Isomorphism.v:133's
   [IsIsomorphism], the single-morphism (predicate) reading of `≅`.

   [IsGroupoid] is a plain [Definition], deliberately NOT a [Class] and NOT
   registered for instance resolution: an inhabitant carries a CHOSEN inverse
   for each arrow, in the same way that Theory/Equivalence.v's
   [EquivalenceOfCategories] carries a chosen quasi-inverse, and the same rule
   applies — such a choice is passed explicitly at use sites rather than
   conjured by a proof search.  The choice is nevertheless immaterial:
   [ginv_choice_irrelevant] below shows any two inhabitants give the same
   inverse up to `≈`. *)
Definition IsGroupoid (C : Category) : Type :=
  ∀ (x y : C) (f : x ~> y), IsIsomorphism f.

Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

(* The inverse of f, extracted from the groupoid structure. *)
Definition ginv {x y : C} (f : x ~> y) : y ~> x :=
  two_sided_inverse (IsIsomorphism := G x y f).

(* The two inverse laws, in the orientation [IsIsomorphism] states them. *)
Lemma ginv_right {x y : C} (f : x ~> y) : f ∘ ginv f ≈ id.
Proof. exact (is_right_inverse (IsIsomorphism := G x y f)). Qed.

Lemma ginv_left {x y : C} (f : x ~> y) : ginv f ∘ f ≈ id.
Proof. exact (is_left_inverse (IsIsomorphism := G x y f)). Qed.

(* Any right inverse of f is THE inverse of f, and likewise any left inverse:
   both are Theory/Isomorphism.v's [comp_inverse_unique] (its Eilenberg-Mac
   Lane Lemma 1.4) read at the chosen inverse.  These two lemmas are the
   workhorses of everything below — every identity about [ginv] is proved by
   exhibiting a one-sided inverse rather than by unfolding the choice. *)
Lemma ginv_unique_r {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ≈ id → ginv f ≈ g.
Proof.
  intro H.
  symmetry.
  exact (comp_inverse_unique f g (ginv f) H (ginv_left f)).
Qed.

Lemma ginv_unique_l {x y : C} (f : x ~> y) (g : y ~> x) :
  g ∘ f ≈ id → ginv f ≈ g.
Proof.
  intro H.
  exact (comp_inverse_unique f (ginv f) g (ginv_right f) H).
Qed.

(* Inversion respects `≈`.  Like [grp_inv_respects] in Construction/Deloop.v
   this is derived from uniqueness of inverses, not required as data. *)
#[export] Instance ginv_respects {x y : C} :
  Proper (equiv ==> equiv) (@ginv x y).
Proof.
  intros f g Hfg.
  apply ginv_unique_r.
  rewrite Hfg.
  apply ginv_right.
Qed.

Lemma ginv_involutive {x y : C} (f : x ~> y) : ginv (ginv f) ≈ f.
Proof. apply ginv_unique_l, ginv_right. Qed.

Lemma ginv_id {x : C} : ginv (id[x]) ≈ id.
Proof. apply ginv_unique_r; cat. Qed.

(* Inverses of a composite compose in the opposite order. *)
Lemma ginv_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  ginv (f ∘ g) ≈ ginv g ∘ ginv f.
Proof.
  apply ginv_unique_r.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite ginv_right, id_left.
  apply ginv_right.
Qed.

(* An arrow of a groupoid, packaged as an object-level isomorphism.  This is
   the bridge from the predicate reading back to `≅`. *)
Definition giso {x y : C} (f : x ~> y) : x ≅ y := IsIsoToIso f (G x y f).

(* Moving an inverse across an equation, the two cancellation rules a
   groupoid computation needs: from g ∘ f ≈ h one reads off g ≈ h ∘ f⁻¹ and
   f ≈ g⁻¹ ∘ h.  Each is one rewrite by [ginv_right] or [ginv_left] after
   substituting h. *)
Lemma ginv_move_r {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → g ≈ h ∘ ginv f.
Proof.
  intro H.
  rewrite <- H, <- comp_assoc, ginv_right.
  now rewrite id_right.
Qed.

Lemma ginv_move_l {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → f ≈ ginv g ∘ h.
Proof.
  intro H.
  rewrite <- H, comp_assoc, ginv_left.
  now rewrite id_left.
Qed.

End Groupoid.

Arguments ginv {C} G {x y} f.

(* The groupoid structure is a choice of inverses, but not a choice that
   matters: any two inhabitants of [IsGroupoid C] name the same inverse up to
   `≈`.  (This is why nothing downstream needs to fix one, and why it is safe
   for [conjugation_iso] and the structure theorem to take the structure as an
   argument.) *)
Lemma ginv_choice_irrelevant {C : Category} (G G' : IsGroupoid C)
  {x y : C} (f : x ~> y) : ginv G f ≈ ginv G' f.
Proof. apply ginv_unique_r, ginv_right. Qed.

(** ** The core of a category is a groupoid *)

(* Awodey §7.7 asks for the lemma that every arrow of [Groupoid C] — the core
   construction of Construction/Groupoid.v:103, whose arrows ARE the
   isomorphisms of C — is invertible.  Its inverse is Theory/Isomorphism.v's
   [iso_sym], and the two laws are that file's [iso_sym_right_inverse] and
   [iso_sym_left_inverse].  Construction/Groupoid.v names [iso_sym] in its
   header as the source of the inverses that make its core "a groupoid rather
   than merely a category", but the file itself is 109 lines containing only
   that header and the [Program Definition], and states no invertibility
   lemma; this is that lemma.

   NOT VACUOUS: [Groupoid C] is inhabited for every C, and its arrows x ~> y
   are the isomorphisms of C, of which there is at least one (the identity)
   at every object; so this asserts something about a nonempty family of
   arrows even when C has no nonidentity isomorphism. *)
Definition core_is_groupoid (C : Category) : IsGroupoid (Groupoid C).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (Groupoid C) x y f (iso_sym f) _ _).
  - apply iso_sym_right_inverse.
  - apply iso_sym_left_inverse.
Defined.

(** ** Duality *)

(* The opposite of a groupoid is a groupoid: an arrow of C^op is an arrow of
   C read backwards, and its inverse is the same arrow of C read backwards,
   so the two inverse laws simply exchange places.  This is the fact
   Structure/Groupoid/Inversion.v needs to build the functor C^op ⟶ C. *)
Definition IsGroupoid_op {C : Category} (G : IsGroupoid C) : IsGroupoid (C^op).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (C^op) x y f (ginv G f) _ _).
  - exact (ginv_left G f).
  - exact (ginv_right G f).
Defined.

(* The chosen inverse in C^op is the chosen inverse in C, on the nose: the
   construction moves no data, exactly as [op]/[unop] move none
   (Construction/Opposite.v).  The [=] here is genuinely stronger than `≈` —
   it says the two terms are the same term, not merely equivalent arrows —
   and it holds by [eq_refl]. *)
Example ginv_op_eq {C : Category} (G : IsGroupoid C) {x y : C}
  (f : y ~{C}~> x) : ginv (IsGroupoid_op G) f = ginv G f := eq_refl.

(** ** Groups as one-object groupoids *)

(* Fong and Spivak's Exercise 3.32 asks the reader to decide, of two given
   monoids, whether the delooping is a groupoid.  Stating the exercise needs
   the notion "M is a group" separated from the bundling [GrpObject] of
   Construction/Deloop.v, since the question is about a MONOID that is given
   in advance.  [MonInverses M] is that separation: the inverse operation and
   its two laws, over a fixed monoid.

   As in [GrpObject] no [Proper] field is carried: respectfulness of [minv]
   follows from [mon_inverse_unique] (Construction/Deloop.v) exactly as
   [grp_inv_respects] does there, and is reachable through [GrpObject_of]
   below without restating the argument. *)
Record MonInverses (M : MonObject) := {
  minv : carrier M → carrier M;

  minv_l : ∀ a, mon_op (minv a) a ≈ mon_unit;
  minv_r : ∀ a, mon_op a (minv a) ≈ mon_unit
}.

Arguments minv {M} _ _.
Arguments minv_l {M} _ _.
Arguments minv_r {M} _ _.

(* [MonInverses M] and "M is the underlying monoid of a [GrpObject]" are the
   same data, repackaged; both round trips hold. *)
Definition GrpObject_of {M : MonObject} (I : MonInverses M) : GrpObject := {|
  grp_monoid := M;
  grp_inv    := minv I;
  grp_inv_l  := minv_l I;
  grp_inv_r  := minv_r I
|}.

Definition MonInverses_of (G : GrpObject) : MonInverses (grp_monoid G) := {|
  minv   := grp_inv (g:=G);
  minv_l := grp_inv_l (g:=G);
  minv_r := grp_inv_r (g:=G)
|}.

(* Both round trips hold on the nose, by [eq_refl]: no field is rebuilt, only
   moved.  These [=]s are stronger than any `≈` statement — they are
   equalities of whole records — and they are what justifies treating the two
   packagings as the same data rather than as two notions. *)
Example GrpObject_of_MonInverses_of (G : GrpObject) :
  GrpObject_of (MonInverses_of G) = G := eq_refl.

Example MonInverses_of_GrpObject_of (M : MonObject) (I : MonInverses M) :
  MonInverses_of (GrpObject_of I) = I := eq_refl.

(* One direction of Exercise 3.32, which is Mac Lane's §I.2 construction 4:
   the delooping of a group is a groupoid.  Construction/Deloop.v already
   proves every arrow of [Deloop G] invertible; this is that instance read as
   the predicate. *)
Definition Deloop_IsGroupoid (G : GrpObject) : IsGroupoid (Deloop G) :=
  fun x y f => Deloop_group_invertible G x y f.

(* The converse, which is what makes Exercise 3.32 a CHARACTERISATION rather
   than one implication: if every arrow of B M is invertible then M has
   inverses.  There is only one object, so an [IsIsomorphism] at it is
   literally an inverse element, and the two laws of [IsIsomorphism] are the
   two group laws with composition read as multiplication. *)
Definition Deloop_MonInverses (M : MonObject) (H : IsGroupoid (Deloop M)) :
  MonInverses M := {|
  minv   := fun a => two_sided_inverse (IsIsomorphism := H ttt ttt a);
  minv_l := fun a => is_left_inverse  (IsIsomorphism := H ttt ttt a);
  minv_r := fun a => is_right_inverse (IsIsomorphism := H ttt ttt a)
|}.

(* Fong and Spivak, §3.2.5 Exercise 3.32, as a biconditional: a monoid is a
   group exactly when its delooping is a groupoid.  Both directions are data
   (an inverse operation one way, a family of inverse arrows the other), so
   the statement uses Lib/Foundation.v's Type-valued `↔` ([iffT]) rather than
   propositional [iff]. *)
Theorem deloop_groupoid_iff (M : MonObject) :
  MonInverses M ↔ IsGroupoid (Deloop M).
Proof.
  split.
  - intro I.
    exact (Deloop_IsGroupoid (GrpObject_of I)).
  - intro H.
    exact (Deloop_MonInverses M H).
Defined.

(* The delooping really does have exactly one object: [poly_unit], whose sole
   inhabitant is [ttt].  Together with [deloop_groupoid_iff] this is one half
   of "groups are one-object groupoids" — a group gives a groupoid with one
   object, and a one-object category is a groupoid exactly when its monoid is
   a group.  The other half is [vertex_group] below, which reads a group off
   any object of any groupoid.  (The [=] is an equality of TYPES, stronger
   than any statement about morphisms, and holds by [eq_refl].) *)
Example Deloop_one_object (M : MonObject) : obj[Deloop M] = poly_unit := eq_refl.

(** ** The vertex group *)

(* Mac Lane §I.5: in a groupoid the endomorphism monoid at an object is a
   group.  Construction/Deloop.v's [hom_monoid C x] already exhibits
   hom(x, x) as a monoid in ANY category; a groupoid structure supplies the
   inverses, and the two group laws are [ginv_left] and [ginv_right]
   verbatim.

   This is the converse half of the group/one-object-groupoid dictionary
   asked for by Awodey §7.7 and by Riehl's footnote to Example 1.1.13(i):
   [Deloop_IsGroupoid] turns a group into a one-object groupoid, and
   [vertex_group] reads a group off any object of any groupoid. *)
Definition vertex_group {C : Category} (G : IsGroupoid C) (x : C) : GrpObject := {|
  grp_monoid := hom_monoid C x;
  grp_inv    := fun f => ginv G f;
  grp_inv_l  := fun f => ginv_left G f;
  grp_inv_r  := fun f => ginv_right G f
|}.

(* The two constructions are mutually inverse on data, in the direction where
   that can be said as an equation.  Construction/Deloop.v's
   [hom_monoid_Deloop] already gives the monoid half by [eq_refl]; the
   inverse operation matches on the nose as well, because
   [Deloop_group_invertible] takes [grp_inv] for its [two_sided_inverse]
   field.  The whole records are NOT equal: the law fields of
   [vertex_group ... ] are the opaque obligation proofs of
   [Deloop_group_invertible], not the law fields of G, and [GrpObject] carries
   no proof irrelevance — the same distinction Construction/Deloop.v draws for
   [MonObject_op].  Each [=] below is therefore an equality of a DATA field,
   which is strictly stronger than `≈` on that field and is what [eq_refl]
   can supply. *)
Example vertex_group_Deloop_monoid (G : GrpObject) :
  grp_monoid (vertex_group (Deloop_IsGroupoid G) ttt) = grp_monoid G := eq_refl.

Example vertex_group_Deloop_inv (G : GrpObject) :
  @grp_inv (vertex_group (Deloop_IsGroupoid G) ttt) = @grp_inv G := eq_refl.

(** ** Monoid homomorphisms, and conjugation *)

(* To say that conjugation is a group ISOMORPHISM one needs homomorphisms of
   the [MonObject]s of Construction/Deloop.v, which that file does not define
   (its stated scope stops before the functor-level dictionary).  The two
   records below are the minimum needed.  A homomorphism of GROUPS is not a
   separate notion: [MonHom_grp_inv] shows a monoid homomorphism between
   groups automatically preserves inverses, so [MonIso] between the
   underlying monoids of two groups is exactly a group isomorphism. *)
Record MonHom (M N : MonObject) := {
  mon_map :> carrier M → carrier N;

  mon_map_respects : Proper (equiv ==> equiv) mon_map;

  mon_map_unit : mon_map mon_unit ≈ mon_unit;
  mon_map_op : ∀ a b, mon_map (mon_op a b) ≈ mon_op (mon_map a) (mon_map b)
}.

Arguments mon_map {M N} _ _.
Arguments mon_map_respects {M N} _.
Arguments mon_map_unit {M N} _.
Arguments mon_map_op {M N} _ _ _.

#[export] Existing Instance mon_map_respects.

Record MonIso (M N : MonObject) := {
  moniso_to : MonHom M N;
  moniso_from : MonHom N M;

  moniso_to_from : ∀ b, moniso_to (moniso_from b) ≈ b;
  moniso_from_to : ∀ a, moniso_from (moniso_to a) ≈ a
}.

Arguments moniso_to {M N} _.
Arguments moniso_from {M N} _.
Arguments moniso_to_from {M N} _ _.
Arguments moniso_from_to {M N} _ _.

(* A monoid homomorphism between groups preserves inverses: φ(a⁻¹) is a left
   inverse of φ(a), and [mon_inverse_unique] identifies it with φ(a)⁻¹.  This
   is the classical argument, and it is the reason the file defines no
   separate class of group homomorphisms. *)
Lemma MonHom_grp_inv (G H : GrpObject) (φ : MonHom G H) (a : carrier G) :
  φ (grp_inv a) ≈ grp_inv (φ a).
Proof.
  apply (mon_inverse_unique H (φ a) (φ (grp_inv a)) (grp_inv (φ a))).
  - rewrite <- mon_map_op.
    rewrite grp_inv_l.
    apply mon_map_unit.
  - apply grp_inv_r.
Qed.

Section Conjugation.

Context {C : Category}.
Context (G : IsGroupoid C).
Context {x x' : C}.
Context (f : x ~> x').

(* Conjugation by f, as a map hom(x, x) → hom(x', x'). *)
Definition conjugate (a : x ~> x) : x' ~> x' := f ∘ a ∘ ginv G f.

#[local] Instance conjugate_respects : Proper (equiv ==> equiv) conjugate.
Proof. proper; unfold conjugate; now rewrites. Qed.

Lemma conjugate_id : conjugate id ≈ id.
Proof.
  unfold conjugate.
  rewrite id_right.
  apply ginv_right.
Qed.

Lemma conjugate_comp (a b : x ~> x) :
  conjugate (a ∘ b) ≈ conjugate a ∘ conjugate b.
Proof.
  unfold conjugate.
  rewrite <- !comp_assoc.
  (* on the right-hand side the inner  f⁻¹ ∘ f  cancels *)
  rewrite (comp_assoc (ginv G f) f).
  rewrite ginv_left, id_left.
  reflexivity.
Qed.

(* Built with the constructor applied to explicit monoid arguments rather than
   through record syntax: the field type [carrier (mon_setoid ?M)] does not
   determine ?M from [conjugate]'s type by unification alone. *)
Definition conjugation : MonHom (vertex_group G x) (vertex_group G x') :=
  @Build_MonHom (grp_monoid (vertex_group G x)) (grp_monoid (vertex_group G x'))
    conjugate conjugate_respects conjugate_id conjugate_comp.

End Conjugation.

Arguments conjugate {C} G {x x'} f a.
Arguments conjugation {C} G {x x'} f.

(* Mac Lane §I.5: conjugation by an arrow f : x ~> x' is an ISOMORPHISM of
   vertex groups, inverted by conjugation by f⁻¹.  Both round trips are the
   same three-line cancellation.

   The isomorphism depends on f: a different arrow x ~> x' gives a
   conjugation differing by an inner automorphism, and nothing here claims
   otherwise.  That dependence is the categorical form of the base-point
   dependence of the fundamental group.

   VACUITY.  With x' := x and f := id the statement degenerates to the
   identity automorphism of hom(x, x), so the content is entirely in the
   case of two DISTINCT objects.  That case is witnessed:
   [Bool_Wide_conjugation] in Structure/Groupoid/Connected.v conjugates
   between the vertex groups at [true] and [false] of a two-object
   groupoid. *)
Definition conjugation_iso {C : Category} (G : IsGroupoid C) {x x' : C}
  (f : x ~> x') : MonIso (vertex_group G x) (vertex_group G x').
Proof.
  refine {| moniso_to   := conjugation G f
          ; moniso_from := conjugation G (ginv G f) |}.
  - (* conjugation by f, after conjugation by f⁻¹ *)
    intro b.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_right, id_right.
    rewrite comp_assoc, ginv_right.
    apply id_left.
  - (* and the other way round *)
    intro a.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_left, id_right.
    rewrite comp_assoc, ginv_left.
    apply id_left.
Defined.

(** ** The two witnesses of Exercise 3.32 *)

(* Fong and Spivak ask the reader to decide the exercise for two concrete
   monoids.  Both answers are proved here rather than asserted, and they are
   what keeps [deloop_groupoid_iff] from being an empty biconditional: one
   monoid satisfies it on the left and the right, the other on neither side.

   The hom-setoid of [Deloop Nat_Plus] is Lib/Datatypes.v's [nat_setoid],
   whose [equiv] field IS [eq]; so in the three statements about
   [Deloop Nat_Plus] below, `≈` and `=` are the same relation, and `=` is
   used where the argument is arithmetic.  The same holds of [Z3_Mon] at the
   end of the file, whose carrier setoid is likewise Leibniz equality.

   This remark is scoped to those two carriers, and is not a claim about the
   file as a whole.  Every other [=] here is flagged individually where it
   occurs: [ginv_op_eq] relates two MORPHISMS of an arbitrary category and is
   deliberately stronger than `≈`; the remaining ones equate records, types
   or functions rather than morphisms. *)

(* The only invertible arrow of B (ℕ, +) is the identity: if n + g = 0 then
   n = 0.  (ℕ, +) is the free monoid on one generator, and this is the first
   of the two cases Exercise 3.32 asks the reader to decide. *)
Lemma deloop_nat_iso_is_zero (n : carrier Nat_Plus)
  (H : @IsIsomorphism (Deloop Nat_Plus) ttt ttt n) : n = 0%nat.
Proof.
  pose proof (is_right_inverse (IsIsomorphism := H)) as Hr.
  simpl in Hr.                          (* Hr : (n + two_sided_inverse)%nat = 0%nat *)
  now destruct n.
Qed.

(* Hence B (ℕ, +) is NOT a groupoid.  The witness is the arrow 1, which has
   no inverse: exhibiting a specific non-invertible arrow is the content, an
   appeal to "ℕ is not a group" being a statement about the monoid rather
   than about the category. *)
Theorem deloop_nat_one_not_invertible :
  @IsIsomorphism (Deloop Nat_Plus) ttt ttt 1%nat → False.
Proof.
  intro H.
  pose proof (deloop_nat_iso_is_zero 1%nat H) as Heq.
  discriminate Heq.
Qed.

Theorem deloop_nat_not_groupoid : IsGroupoid (Deloop Nat_Plus) → False.
Proof.
  intro H.
  exact (deloop_nat_one_not_invertible (H ttt ttt 1%nat)).
Qed.

(* Equivalently, through the biconditional: (ℕ, +) has no inverse operation. *)
Corollary nat_plus_no_inverses : MonInverses Nat_Plus → False.
Proof.
  intro I.
  exact (deloop_nat_not_groupoid (fst (deloop_groupoid_iff Nat_Plus) I)).
Qed.

(* The other witness: the delooping of Z/2 IS a groupoid, because Z/2 is a
   group.  Construction/Deloop.v's [Bool_Xor_Grp] is that group. *)
Definition deloop_bool_groupoid : IsGroupoid (Deloop Bool_Xor_Grp) :=
  Deloop_IsGroupoid Bool_Xor_Grp.

(* And its vertex group is Z/2 back again, on the nose in both data fields —
   the round trip of [vertex_group_Deloop_monoid]/[vertex_group_Deloop_inv]
   at a concrete group. *)
Example vertex_group_bool_inv :
  @grp_inv (vertex_group deloop_bool_groupoid ttt) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(** ** A group whose inversion is not the identity *)

(* In Z/2 every element is its own inverse, so any statement about inversion
   degenerates there: the inverse map is the identity function.  Z/3 is the
   smallest group for which it is not, and it is supplied so that the
   inversion functor of Structure/Groupoid/Inversion.v has a witness where it
   genuinely moves an arrow ([Z3_inversion_nontrivial] there).

   The carrier setoid takes Coq's own equality for `≈`, as [Bool_Xor] does,
   so the [mon_op_respects] field is discharged by instance resolution and
   every law below is a finite case check.

   As in Construction/Deloop.v, the global obligation tactic is switched off
   for the rest of the file: every obligation here is a case split, and the
   wide searches [cat_simpl] would run buy nothing. *)
#[local] Obligation Tactic := idtac.

Inductive Z3 : Set := Z3_0 | Z3_1 | Z3_2.

Definition Z3_add (a b : Z3) : Z3 :=
  match a, b with
  | Z3_0, b    => b
  | a,    Z3_0 => a
  | Z3_1, Z3_1 => Z3_2
  | Z3_1, Z3_2 => Z3_0
  | Z3_2, Z3_1 => Z3_0
  | Z3_2, Z3_2 => Z3_1
  end.

Definition Z3_neg (a : Z3) : Z3 :=
  match a with
  | Z3_0 => Z3_0
  | Z3_1 => Z3_2
  | Z3_2 => Z3_1
  end.

Program Definition Z3_Mon : MonObject := {|
  mon_setoid := {| carrier := Z3
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := Z3_0;
  mon_op     := Z3_add
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Program Definition Z3_Grp : GrpObject := {|
  grp_monoid := Z3_Mon;
  grp_inv    := Z3_neg
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Definition deloop_Z3_groupoid : IsGroupoid (Deloop Z3_Grp) :=
  Deloop_IsGroupoid Z3_Grp.

(* Inversion in Z/3 really does move an element.  The [=] is Leibniz equality
   on [Z3], which is exactly the `≈` of [Z3_Mon]'s carrier setoid, so nothing
   weaker is being claimed. *)
Example Z3_inv_1 : grp_inv (g:=Z3_Grp) Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inv_moves : grp_inv (g:=Z3_Grp) Z3_1 <> Z3_1.
Proof. discriminate. Qed.
