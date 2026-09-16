Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.

Generalizable All Variables.

(* The lattice of subobjects of an object

   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/image
   nLab:  https://ncatlab.org/nlab/show/wide+pullback
   nLab:  https://ncatlab.org/nlab/show/well-powered+category

   A subobject of x is a monomorphism into x taken up to the equivalence
   that identifies two monos when each factors through the other.
   Theory/Subobject.v carries that data as [SubObj x] and that order as
   [sub_le] (Theory/Subobject.v:60), a preorder whose mediating arrow is
   itself monic (:86) and unique (:97), and whose induced equivalence is
   exactly the setoid on [SubObj x] (:112, [sub_equiv_iff_mutual]).  What
   that file leaves open, and what this one supplies, is the ORDER
   STRUCTURE of that preorder: binary and indexed greatest lower bounds,
   binary and indexed least upper bounds, and the two end points.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF p. 135), is the source the construction follows.
   Mac Lane observes that a pullback of two monos u : s ↣ x and v : t ↣ x
   is again a pair of monos, and that the composite of either pullback leg
   with the mono below it presents the apex as a subobject of x which is
   contained in both and contains every subobject contained in both: the
   intersection u ∩ v, the greatest lower bound in the factorization
   order.  [sub_meet] below is that composite verbatim, and
   [sub_meet_is_glb] is that greatest-lower-bound claim.  A wide pullback
   of a whole family of monos plays the same role for an indexed
   intersection.  Unions are NOT dual to this in the elementary sense: a
   pushout of two monos is not in general a subobject of x at all, and the
   join has to be built as the IMAGE of the copairing of the two monos out
   of their coproduct.  That is why the join half of this file is
   conditional on an image factorization where the meet half is
   conditional only on pullbacks.

   Riehl, "Category Theory in Context", 2nd ed., §4.7, printed p. 177
   (PDF p. 197), Definition 4.7.9, gives the indexed form.  Riehl defines
   the intersection of a family of subobjects as the LIMIT of the diagram
   consisting of those monomorphisms over their common codomain, and then
   records three facts about it: the legs of the limit cone are monic, the
   induced map from the limit object down to the codomain is monic, and
   the resulting subobject is maximal among the subobjects contained in
   every member of the family.  All three appear below over the
   ELEMENTARY presentation of that limit, the wide pullback of
   Structure/Pullback/Wide.v: the legs are monic by
   [wide_pullback_proj_monic], the induced map is monic by the
   [sub_is_monic] field of [sub_wide_intersection], and maximality is
   [inter_greatest] in [sub_wide_intersection_IsIntersection].

   Fong and Spivak, "Seven Sketches in Compositionality", §1.2.1, printed
   p. 8 (PDF p. 20), meets the same two operations at their most concrete:
   the union and the intersection of subsets of one ambient set, and the
   indexed versions of both over a family.  The unit law they record for
   the union, ∅ ∪ X ≅ X, is [sub_join_bot] below (and [sub_join_via_bot],
   the same law with the image of the copairing handed in), at the level of
   subobjects of an arbitrary object rather than of subsets; its
   intersection counterpart ∅ ∩ X ≅ ∅ is [sub_meet_bot], and the two
   absorption laws that make the pair a lattice are [sub_meet_absorb] and
   [sub_join_absorb].  The merging-versus-tagging contrast that the book
   draws in the same section -- that the union of two subsets of a common
   set merges their overlap where the coproduct tags it -- is exactly the
   distance between [sub_join_via u v I], the image of the copairing, and
   the coproduct [sub_dom u + sub_dom v] it is the image OF.

   In-tree connections, each checked at the cited line in this worktree.

   The order.  Theory/Subobject.v:60 is [sub_le], :86 [sub_le_monic], :97
   [sub_le_unique] and :112 [sub_equiv_iff_mutual]; every antisymmetry
   step below goes through that last one, because [sub_le] is Type-valued
   and the equivalence it induces is the [SubObj] setoid, not Leibniz
   equality.  Note the consequence for how the lattice laws are phrased:
   [SubObj x] is a PREORDER whose setoid identifies mutually-factoring
   subobjects, so the commutativity, associativity, idempotence and
   absorption laws below hold at ≈ and are a lattice ON THAT SETOID, not a
   poset with antisymmetry for Leibniz equality.

   The meet.  Structure/Pullback.v:216 is [HasPullbacks], the chosen-
   pullback class this file's meet is relative to, and
   Theory/Morphisms/Stability.v:226 is [monic_pullback_stable], which is
   what makes the opposite leg monic.  Theory/Subobject/Functor.v:35 is
   [sub_reindex], which packages that same pulled-back leg as a subobject
   of [sub_dom u]; the identification is on the nose, [sub_meet u v] being
   literally [sub_compose u (sub_reindex (sub_mono u) v)] -- the same
   record with the same three fields, including the same [monic_compose]
   proof term.  That is MEASURED, not asserted: with
   Category.Theory.Subobject.Functor added to the requirement list, the
   statement
     [Example e (u v : SubObj x) :
        sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v)
        := eq_refl.]
   compiles, at Leibniz equality and with no tactic -- the one place in
   this development where Leibniz equality is the right relation, because
   the claim is about the DATA of the record and not about its morphism.
   That identification is NOT stated in this file, and the reason is
   NAMESPACE, not cost.  An earlier revision of this paragraph said the
   require was avoided because Theory/Subobject/Functor.v pulls
   Category.Instance.Sets; MEASURED by iterating coqdep to a fixed point,
   that is false as a saving -- this file's own closure (48 files) ALREADY
   contains Instance/Sets.v, through Structure/BiCCC.v,
   Structure/Regular/Factorization.v, Structure/Limit/Coproduct.v and
   Structure/Cartesian/Closed.v, so requiring Functor.v would add exactly
   ONE file.  What the require would add is Functor.v's presheaf [Sub] and
   its reindexing vocabulary alongside the order vocabulary here, and the
   readback is placed in Test/ProbeSubobjectLattice445.v
   ([p445_meet_is_compose_reindex]) by that choice.  The literal Require
   list of this file is instance-free; its closure is not.

   The wide intersection.  Structure/Pullback/Wide.v:182 is
   [IsWidePullback], :202 the chosen form [WidePullback], :257
   [HasWidePullbacks], and :271 [wide_pullback_jointly_monic], the joint
   monicity of the projections that [wide_pullback_proj_monic] below turns
   into monicity of each single projection.  One feature of that file
   governs the shape of the interface here: the record carries NO leg to
   the common codomain, so over an empty index it constrains nothing and
   the wide pullback is the TERMINAL object (:338,
   [wide_pullback_empty_terminal], with the converse at :357).  A terminal
   object is not the top subobject, so [sub_wide_intersection] takes an
   index [j0 : J] and reads the mono into x off the j0-th member.  At
   every nonempty index Riehl's limit-over-the-cospan-shape reading and
   this one agree -- the cospan shape has the codomain as an object, and
   its limit leg to the codomain is the composite this file writes by hand
   -- and they differ only at the empty index, where the intersection of
   the empty family of subobjects is [sub_top] ([IsIntersection_empty]
   below) rather than a terminal object.  Structure/Pullback/Wide.v:453 is
   [binary_wide_pullback]; the binary-from-wide comparison below does not
   route through it, for the reason recorded at that lemma.

   The join.  Structure/Cocartesian.v:175 and :182 are [inl_merge] and
   [inr_merge], the two triangles that put each of u and v below the
   image; Structure/Limit/Coproduct.v:82 and :86 are [IsIndexedCoproduct]
   and [icoprod_desc], the indexed replacements for them.
   Structure/Factorization.v:125 is [Factorization] and :144 [OFS]; an
   (E, Mono) factorization system is precisely a supply of images in the
   sense of the [ImageOf] record below, and [ImageOf_of_OFS] is that
   translation, its minimality clause being the diagonal filler of
   Theory/Orthogonality.v:43 ([Orthogonal], whose [ortho_lift] field
   returns the filler as data).  Theory/Morphisms/Classes.v:31 is
   [MonoClass], which is [fun _ _ f => Monic f] and so matches the
   [sub_is_monic] field with no transport.  Structure/Regular/
   Factorization.v:282 is [Regular_OFS], the (regular epi, mono) system of
   a regular category, with :175 [image_comparison_monic] as its mono leg;
   [Regular_HasImages] below is [HasImages_of_OFS] applied to it.  That
   corollary is CONDITIONAL and stays so: no [Regular] instance exists
   anywhere in this tree, as Instance/Sets/Pullback.v:62 records in terms
   ("a class with no instance anywhere"), and this file adds none.

   The powerset analogue.  Instance/Powerset.v:504 and :522 are
   [subset_inter] and [subset_union], the predicate-level meet and join of
   a family of subsets of a setoid, with their universal properties at
   :535 ([subset_inter_IsGLB]) and :544 ([subset_union_IsLUB]).  This
   file is the SubObj-level analogue of that
   pair in an arbitrary category: the same two universal properties, with
   the powerset's pointwise ∀ and ∃ replaced by a wide pullback and an
   image.  (An earlier revision of this header's source instructions gave
   those two line numbers as :503 and :520; measured in this worktree with
   grep -n '^Definition subset_inter\|^Definition subset_union', they are
   :504 and :522.)

   Where this does NOT go.  Adjunction/SAFT.v:119 packages the
   well-poweredness the special adjoint functor theorem consumes as
   [SubobjectIndex], and :240 builds [SubobjectCover] over it.  Feeding
   the intersections constructed here into that hypothesis list is issue
   #448 and is not attempted in this file; nothing below mentions SAFT,
   and no constant here is named by that development.

   UNIVERSES, measured with [Set Printing Universes. About ...] rather than
   read off the source, which carries no annotation.  Every constant below
   binds its category as [Category@{u u0 u0}] -- the hom universe IDENTIFIED
   with the proof universe.  That collapse is INHERITED, not introduced
   here: Theory/Subobject.v:15's [SubObj] record itself prints as
   [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] → Type@{max(u,u0)}],
   because one record holds both the mono (at the hom level) and its
   [Monic] proof (at the proof level) under two universe variables, and
   [sub_le@{o h p u}] at :60 carries the block [h <= p, h <= u, h = p].
   So the collapse belongs to the FIRST carrier in dependency order,
   Theory/Subobject.v, and every file consuming [SubObj] -- this one,
   Theory/Subobject/Functor.v ([sub_reindex@{u u0}]), and the witnesses in
   Instance/ -- inherits it.  No constant here pins any universe to [Set],
   and none carries a constraint of its own beyond the stdlib
   [prod_rect]/[projections] bounds that come with sigma types.

   NOT DELIVERED.  No distributivity, and no Heyting or Boolean
   structure: the two absorption laws are proved, the distributive law
   relating meet and join is neither proved nor stated, and there is no
   complement, no implication and no negation on [SubObj x].  No
   antisymmetry: every lattice law holds at ≈ and none at Leibniz
   equality, as explained above.  No concrete inhabitant of any of the
   three hypotheses -- this file has no [HasPullbacks], [HasWidePullbacks]
   or [HasImages] instance for any category, and [Regular_HasImages]
   rests on a class with no instance in tree; the whole development is a
   conditional over structure supplied from outside, and docs/
   INHABITATION.md is where the question of which witnesses exist is
   settled.  No limit presentation: [IsIntersection] is a greatest lower
   bound in the factorization preorder, not a limit cone over a shape
   category, and Structure/Pullback/Wide.v carries no limit presentation
   either (its own header says so at :162-165), so Riehl's Definition
   4.7.9 is matched in content and not by a literal [Limit] of a diagram.
   No indexed join over an arbitrary family without an indexed coproduct:
   [sub_wide_join_via] takes the coproduct and the image as arguments and
   nothing here manufactures either.  No union of the empty family without
   an initial object: the empty intersection is [sub_top] unconditionally,
   but its dual needs a least subobject and is therefore stated in the
   Bottom section against [sub_bot].  No functoriality: that reindexing
   along a morphism preserves binary meets belongs to a separate file and
   none is added alongside this one, so neither that statement nor any
   naturality, Galois connection or adjointness claim about reindexing
   appears anywhere in this development.  No computation: no [eq_refl]
   readback of any
   construction at any concrete category, and no enumeration of the Seven
   Sketches examples -- the four-versus-five element contrast, the
   increasing family and its union, and the finite arithmetic -- all of
   which need a concrete model and belong with the witness half of the
   issue.  No strictness result in general: [zero_monic_of_strict] takes
   strictness of the initial object as a HYPOTHESIS and derives no
   instance of it; the one case where the hypothesis is discharged is the
   bicartesian closed one, [biccc_zero_monic] through
   Structure/BiCCC.v:262 ([initial_strict]), and even there no initial
   object of any concrete bicartesian closed category is exhibited. *)

(** ** The order-theoretic vocabulary *)

Section SubobjectOrder.

Context {C : Category}.
Context {x : C}.

(* The top subobject: x itself along the identity. *)
Definition sub_top : SubObj x := {|
  sub_dom := x;
  sub_mono := id;
  sub_is_monic := id_monic x
|}.

Lemma sub_top_greatest (u : SubObj x) : sub_le u sub_top.
Proof. exists (sub_mono u); cat. Defined.

(* Riehl 4.7.9's characterization of the intersection of a family, and its
   dual: the greatest lower bound, respectively least upper bound, of the
   family for the factorization preorder [sub_le]. *)
Record IsIntersection {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  inter_le : ∀ j, sub_le w (S j);
  inter_greatest : ∀ v : SubObj x, (∀ j, sub_le v (S j)) → sub_le v w
}.

Record IsUnion {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  union_ge : ∀ j, sub_le (S j) w;
  union_least : ∀ v : SubObj x, (∀ j, sub_le (S j) v) → sub_le w v
}.

(* A two-element family, for the binary cases. *)
Definition sub_pair (u v : SubObj x) : bool → SubObj x :=
  fun b => if b then u else v.

Definition IsMeet (u v w : SubObj x) : Type := IsIntersection (sub_pair u v) w.
Definition IsJoin (u v w : SubObj x) : Type := IsUnion (sub_pair u v) w.

(** *** Antisymmetry for the induced setoid *)

(* The half of [sub_equiv_iff_mutual] used everywhere below: mutual
   factorization IS equivalence of subobjects.  [SubObj x] has no Leibniz
   antisymmetry; this is its replacement. *)
Lemma sub_le_antisym (u v : SubObj x) : sub_le u v → sub_le v u → u ≈ v.
Proof.
  intros Huv Hvu.
  apply sub_equiv_iff_mutual.
  exact (Huv, Hvu).
Defined.

(* ... and the two projections of the other direction, as named lemmas, so
   that a transport along ≈ reads as one step. *)
Lemma sub_le_of_equiv (u v : SubObj x) : u ≈ v → sub_le u v.
Proof. intros H; exact (fst (fst (sub_equiv_iff_mutual u v) H)). Defined.

Lemma sub_ge_of_equiv (u v : SubObj x) : u ≈ v → sub_le v u.
Proof. intros H; exact (snd (fst (sub_equiv_iff_mutual u v) H)). Defined.

(** *** Uniqueness and transport of the two universal properties *)

(* Two greatest lower bounds of the same family agree: each is below every
   member, so each factors through the other by the other's maximality. *)
Lemma IsIntersection_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsIntersection S w → IsIntersection S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (inter_greatest S w' B w (inter_le S w A)).
  - exact (inter_greatest S w A w' (inter_le S w' B)).
Defined.

Lemma IsUnion_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsUnion S w → IsUnion S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (union_least S w A w' (union_ge S w' B)).
  - exact (union_least S w' B w (union_ge S w A)).
Defined.

(* Being the intersection transports along ≈ of the bound ... *)
Lemma IsIntersection_respects_w {J : Type} (S : J → SubObj x)
  (w w' : SubObj x) : w ≈ w' → IsIntersection S w → IsIntersection S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw) (inter_le S w A j)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (inter_greatest S w A v Hv)
             (sub_le_of_equiv _ _ Hw)).
Defined.

(* ... and pointwise along ≈ of the family. *)
Lemma IsIntersection_respects_family {J : Type} (S S' : J → SubObj x)
  (w : SubObj x) : (∀ j, S j ≈ S' j) →
  IsIntersection S w → IsIntersection S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (inter_le S w A j) (sub_le_of_equiv _ _ (HS j))).
  - intros v Hv.
    apply (inter_greatest S w A).
    intro j.
    exact (sub_le_trans _ _ _ (Hv j) (sub_ge_of_equiv _ _ (HS j))).
Defined.

Lemma IsUnion_respects_w {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  w ≈ w' → IsUnion S w → IsUnion S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (union_ge S w A j) (sub_le_of_equiv _ _ Hw)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw)
             (union_least S w A v Hv)).
Defined.

Lemma IsUnion_respects_family {J : Type} (S S' : J → SubObj x) (w : SubObj x) :
  (∀ j, S j ≈ S' j) → IsUnion S w → IsUnion S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ (HS j)) (union_ge S w A j)).
  - intros v Hv.
    apply (union_least S w A).
    intro j.
    exact (sub_le_trans _ _ _ (sub_le_of_equiv _ _ (HS j)) (Hv j)).
Defined.

(** *** The two degenerate index shapes *)

(* Over an empty index every subobject is vacuously below every member, so
   the greatest lower bound is the greatest subobject.  This is the case
   at which the wide-pullback presentation of the intersection and the
   order-theoretic one part company: the empty wide pullback is a terminal
   object (Structure/Pullback/Wide.v:338), which is not [sub_top]. *)
Lemma IsIntersection_empty {J : Type} (S : J → SubObj x) (Hempty : J → False) :
  IsIntersection S sub_top.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (sub_top_greatest v).
Defined.

(* Dually the union of the empty family is the LEAST subobject, which has
   to be supplied: nothing in the bare preorder produces one.  The Bottom
   section below instantiates [b] at [sub_bot]. *)
Lemma IsUnion_empty_of_least {J : Type} (S : J → SubObj x) (b : SubObj x)
  (Hleast : ∀ u : SubObj x, sub_le b u) (Hempty : J → False) :
  IsUnion S b.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (Hleast v).
Defined.

(* A one-member family is its own bound, on both sides. *)
Lemma IsIntersection_singleton (S : unit → SubObj x) :
  IsIntersection S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

Lemma IsUnion_singleton (S : unit → SubObj x) : IsUnion S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

End SubobjectOrder.

Arguments IsIntersection_unique {C x J} S {w w'} _ _.
Arguments IsUnion_unique {C x J} S {w w'} _ _.

(** ** Pushing a subobject forward along a mono *)

Section Compose.

Context {C : Category}.

(* A subobject of the domain of a subobject is a subobject of the ambient
   object: monos compose. *)
Definition sub_compose {x : C} (u : SubObj x) (w : SubObj (sub_dom u)) :
  SubObj x := {|
  sub_dom := sub_dom w;
  sub_mono := sub_mono u ∘ sub_mono w;
  sub_is_monic := monic_compose (sub_is_monic u) (sub_is_monic w)
|}.

End Compose.

(** ** Binary meets by pullback *)

Section Meet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(* The intersection of two subobjects: the chosen pullback of their monos,
   mapped into x through the first one.  The composite is monic because
   monos are stable under pullback and closed under composition. *)
Definition sub_meet (u v : SubObj x) : SubObj x := {|
  sub_dom := Pull (sub_mono u) (sub_mono v)
               (pullback (sub_mono u) (sub_mono v));
  sub_mono := sub_mono u
              ∘ pullback_fst (sub_mono u) (sub_mono v)
                  (pullback (sub_mono u) (sub_mono v));
  sub_is_monic :=
    monic_compose (sub_is_monic u)
      (monic_pullback_stable (sub_mono u) (sub_mono v) (sub_is_monic v)
         (pullback (sub_mono u) (sub_mono v)))
|}.

(* Below the first factor, by the first projection: the mediating arrow IS
   [pullback_fst] and the triangle is the definition of [sub_meet]. *)
Lemma sub_meet_le_l (u v : SubObj x) : sub_le (sub_meet u v) u.
Proof.
  exists (pullback_fst (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  reflexivity.
Defined.

(* Below the second factor, by the second projection: here the triangle is
   the commuting square of the pullback, read backwards. *)
Lemma sub_meet_le_r (u v : SubObj x) : sub_le (sub_meet u v) v.
Proof.
  exists (pullback_snd (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  symmetry.
  exact (pullback_commutes (sub_mono u) (sub_mono v)
           (pullback (sub_mono u) (sub_mono v))).
Defined.

(* Mac Lane §V.7, book p. 126: the pullback of two monos is the GREATEST
   subobject below both.  A competing w below both supplies a commuting
   square, the universal property supplies the mediator, and the first
   projection triangle turns that mediator into the required
   factorization. *)
Lemma sub_meet_is_glb (u v : SubObj x) :
  ∀ w : SubObj x, sub_le w u → sub_le w v → sub_le w (sub_meet u v).
Proof.
  intros w [k Hk] [l Hl].
  assert (Hsq : sub_mono u ∘ k ≈ sub_mono v ∘ l) by now rewrite Hk, Hl.
  pose proof (ump_pullbacks (sub_mono u) (sub_mono v)
                (pullback (sub_mono u) (sub_mono v)) (sub_dom w) k l Hsq)
    as U.
  exists (unique_obj U).
  simpl.
  rewrite <- comp_assoc.
  rewrite (fst (unique_property U)).
  exact Hk.
Defined.

(* Packaged as the order-theoretic predicate at the two-element family. *)
Lemma sub_meet_IsMeet (u v : SubObj x) : IsMeet u v (sub_meet u v).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_meet_le_l u v).
    + exact (sub_meet_le_r u v).
  - intros w Hw.
    exact (sub_meet_is_glb u v w (Hw true) (Hw false)).
Defined.

(* Respectfulness is proved through the universal property, not through
   the pullback: [sub_meet u v] and [sub_meet u' v'] are greatest lower
   bounds of pointwise-equivalent families, hence equivalent.  Fighting
   the chosen pullback directly would need a comparison isomorphism of
   apexes that this argument never mentions. *)
#[export] Instance sub_meet_respects :
  Proper (equiv ==> equiv ==> equiv) sub_meet.
Proof.
  intros u u' Hu v v' Hv.
  apply (IsIntersection_unique (sub_pair u' v')).
  - apply (IsIntersection_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_meet_IsMeet u v).
  - exact (sub_meet_IsMeet u' v').
Defined.

(** *** The order laws, at ≈ *)

Lemma sub_meet_comm (u v : SubObj x) : sub_meet u v ≈ sub_meet v u.
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r u v)
                           | exact (sub_meet_le_l u v) ].
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r v u)
                           | exact (sub_meet_le_l v u) ].
Defined.

Lemma sub_meet_assoc (u v w : SubObj x) :
  sub_meet (sub_meet u v) w ≈ sub_meet u (sub_meet v w).
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb.
    + exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_l _ _)).
    + apply sub_meet_is_glb.
      * exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_r _ _)).
      * exact (sub_meet_le_r _ _).
  - apply sub_meet_is_glb.
    + apply sub_meet_is_glb.
      * exact (sub_meet_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_l _ _)).
    + exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_r _ _)).
Defined.

Lemma sub_meet_idem (u : SubObj x) : sub_meet u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u u).
  - exact (sub_meet_is_glb u u u (sub_le_refl u) (sub_le_refl u)).
Defined.

(* The top subobject is a unit for the meet. *)
Lemma sub_meet_top (u : SubObj x) : sub_meet u sub_top ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u sub_top).
  - exact (sub_meet_is_glb u sub_top u (sub_le_refl u) (sub_top_greatest u)).
Defined.

(* "u ≤ v iff u ∧ v ≈ u", in two separate lemmas: [sub_le] is Type-valued
   data and the two directions carry different data, so they are not
   packaged as one ↔. *)
Lemma sub_meet_of_le (u v : SubObj x) : sub_le u v → sub_meet u v ≈ u.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u v).
  - exact (sub_meet_is_glb u v u (sub_le_refl u) Huv).
Defined.

Lemma sub_le_of_meet (u v : SubObj x) : sub_meet u v ≈ u → sub_le u v.
Proof.
  intros Hm.
  exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hm) (sub_meet_le_r u v)).
Defined.

End Meet.

(** ** Wide intersections by wide pullback *)

Section WideIntersection.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(* Every projection of a wide pullback of monos is monic: two maps agreeing
   after one projection agree after every projection, by the commutativity
   of the wide square and the monicity of the family, hence agree by joint
   monicity.  This is Riehl 4.7.9's "the legs of the cone are monic". *)
Lemma wide_pullback_proj_monic (W : WidePullback (fun j => sub_mono (S j)))
  (j : J) : Monic (wide_pullback_proj W j).
Proof.
  constructor; intros q g1 g2 Hg.
  apply (wide_pullback_jointly_monic (wide_pullback_is_pullback W)).
  intro i.
  apply (monic (Monic := sub_is_monic (S i))).
  rewrite !comp_assoc.
  rewrite (wide_pullback_commutes W i j).
  rewrite <- !comp_assoc.
  now rewrite Hg.
Qed.

(* The intersection of a family of subobjects, presented at an index j0:
   the wide pullback of the monos, mapped into x through the j0-th member.
   By [wide_pullback_commutes] the mono does not depend on j0 up to ≈.
   The [sub_is_monic] field is Riehl 4.7.9's "the induced map into the
   codomain is again monic". *)
Definition sub_wide_intersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x := {|
  sub_dom := WPull W;
  sub_mono := sub_mono (S j0) ∘ wide_pullback_proj W j0;
  sub_is_monic :=
    monic_compose (sub_is_monic (S j0)) (wide_pullback_proj_monic W j0)
|}.

(* Riehl 4.7.9 in full: the wide pullback presents the greatest subobject
   of x contained in every member of the family.  Containment in the j-th
   member is the j-th projection, with the wide square as its triangle;
   maximality is the wide universal property applied to the family of
   factorizations a competing subobject supplies. *)
Theorem sub_wide_intersection_IsIntersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  IsIntersection S (sub_wide_intersection j0 W).
Proof.
  constructor.
  - (* below every member, by that member's projection *)
    intro j.
    exists (wide_pullback_proj W j).
    exact (wide_pullback_commutes W j j0).
  - (* maximal among the subobjects below every member *)
    intros v Hv.
    pose (q := fun j => `1 (Hv j)).
    assert (Hq : ∀ i j : J, sub_mono (S i) ∘ q i ≈ sub_mono (S j) ∘ q j).
    { intros i j; unfold q.
      rewrite (`2 (Hv i)), (`2 (Hv j)); reflexivity. }
    pose proof (ump_wide_pullbacks W (sub_dom v) q Hq) as U.
    exists (unique_obj U).
    simpl.
    rewrite <- comp_assoc.
    rewrite (unique_property U j0).
    exact (`2 (Hv j0)).
Defined.

(* The chosen index is immaterial, and at the strongest available reading:
   the two subobjects have the SAME domain, so the identity isomorphism
   witnesses the equivalence and only the triangle has to be discharged,
   by the wide square. *)
Lemma sub_wide_intersection_index_irrelevant (j0 j1 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  sub_wide_intersection j0 W ≈ sub_wide_intersection j1 W.
Proof.
  exists iso_id; simpl.
  rewrite id_right.
  exact (wide_pullback_commutes W j1 j0).
Defined.

End WideIntersection.

(** ** The binary meet as a wide intersection *)

Section MeetIsWide.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(* Whenever the pair of monos carries a wide pullback, the wide
   intersection presented at [true] agrees with the chosen binary meet.
   The comparison is made through the two universal properties rather than
   through Structure/Pullback/Wide.v:453 ([binary_wide_pullback]): that
   lemma's family is [two_maps f g] over [two_fam (sub_dom u) (sub_dom v)],
   whereas the family here is [fun b => sub_mono (sub_pair u v b)] over
   [fun b => sub_dom (sub_pair u v b)], and the two index families are
   convertible only at each literal [true] and [false], not as functions
   of a variable b -- so routing through it would cost a transport of the
   whole [IsWidePullback] record along a pointwise-only conversion.  The
   order-theoretic route costs three lines. *)
Theorem sub_meet_is_wide_intersection (u v : SubObj x)
  (W : WidePullback (fun b => sub_mono (sub_pair u v b))) :
  sub_meet u v ≈ sub_wide_intersection (sub_pair u v) true W.
Proof.
  apply (IsIntersection_unique (sub_pair u v)).
  - exact (sub_meet_IsMeet u v).
  - exact (sub_wide_intersection_IsIntersection (sub_pair u v) true W).
Defined.

End MeetIsWide.

(** ** The total form: all wide intersections at once *)

Section TotalIntersection.

Context {C : Category}.
Context `{@HasWidePullbacks C}.
Context {x : C}.

(* With every wide pullback chosen, the intersection of a family is a
   total operation -- still presented at an index, for the reason recorded
   in the header. *)
Definition sub_intersection {J : Type} (j0 : J) (S : J → SubObj x) :
  SubObj x :=
  sub_wide_intersection S j0 (wide_pullback (fun j => sub_mono (S j))).

Theorem sub_intersection_IsIntersection {J : Type} (j0 : J)
  (S : J → SubObj x) : IsIntersection S (sub_intersection j0 S).
Proof.
  exact (sub_wide_intersection_IsIntersection S j0
           (wide_pullback (fun j => sub_mono (S j)))).
Defined.

End TotalIntersection.

(** ** Images as subobjects, and joins by image of the copairing *)

Section Images.

Context {C : Category}.

(* An image of f : y ~> x as a subobject of x: f factors through it, and
   it is the least subobject f factors through.  This is the (E, Mono)
   image of an orthogonal factorization system read as an order-theoretic
   statement; it is what a union of subobjects consumes. *)
Record ImageOf {y x : C} (f : y ~> x) := {
  im_sub : SubObj x;
  im_factor : y ~> sub_dom im_sub;
  im_commutes : sub_mono im_sub ∘ im_factor ≈ f;
  im_least : ∀ (w : SubObj x) (g : y ~> sub_dom w),
    sub_mono w ∘ g ≈ f → sub_le im_sub w
}.

Class HasImages := {
  image_of : ∀ {y x : C} (f : y ~> x), ImageOf f
}.

End Images.

Arguments im_sub {C y x f} _.
Arguments im_factor {C y x f} _.
Arguments im_commutes {C y x f} _.
Arguments im_least {C y x f} _ _ _ _.
Arguments HasImages C : clear implicits.
Arguments image_of {C _ y x} f.

Section Join.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(* The union of two subobjects: the image of the copairing of their monos
   out of the coproduct of their domains, given such an image. *)
Definition sub_join_via (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) : SubObj x := im_sub I.

Definition sub_join `{@HasImages C} (u v : SubObj x) : SubObj x :=
  sub_join_via u v (image_of (merge (sub_mono u) (sub_mono v))).

(* Above the first factor: the mediating arrow is the image factorization
   precomposed with [inl], and the triangle is [inl_merge]
   (Structure/Cocartesian.v:175). *)
Lemma sub_join_via_le_l (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le u (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inl).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inl_merge (sub_mono u) (sub_mono v)).
Defined.

(* ... and above the second, by [inr_merge] (Structure/Cocartesian.v:182). *)
Lemma sub_join_via_le_r (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le v (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inr).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inr_merge (sub_mono u) (sub_mono v)).
Defined.

(* The image is the LEAST subobject above both: a competing w above both
   supplies two factorizations, their copairing factors the copairing of
   the monos through w, and [im_least] is exactly the statement that the
   image is below any subobject the map factors through. *)
Lemma sub_join_via_is_lub (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) (w : SubObj x) :
  sub_le u w → sub_le v w → sub_le (sub_join_via u v I) w.
Proof.
  intros [k Hk] [l Hl].
  apply (im_least I w (merge k l)).
  rewrite <- merge_comp.
  rewrite Hk, Hl.
  reflexivity.
Defined.

Lemma sub_join_via_IsJoin (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  IsJoin u v (sub_join_via u v I).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_join_via_le_l u v I).
    + exact (sub_join_via_le_r u v I).
  - intros w Hw.
    exact (sub_join_via_is_lub u v I w (Hw true) (Hw false)).
Defined.

End Join.

(** ** The join as a lattice operation, with images chosen *)

Section JoinLattice.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

Lemma sub_join_le_l (u v : SubObj x) : sub_le u (sub_join u v).
Proof. exact (sub_join_via_le_l u v _). Defined.

Lemma sub_join_le_r (u v : SubObj x) : sub_le v (sub_join u v).
Proof. exact (sub_join_via_le_r u v _). Defined.

Lemma sub_join_is_lub (u v : SubObj x) :
  ∀ w : SubObj x, sub_le u w → sub_le v w → sub_le (sub_join u v) w.
Proof. intros w Hu Hv; exact (sub_join_via_is_lub u v _ w Hu Hv). Defined.

Lemma sub_join_IsJoin (u v : SubObj x) : IsJoin u v (sub_join u v).
Proof. exact (sub_join_via_IsJoin u v _). Defined.

(* As with the meet: least upper bounds of pointwise-equivalent families
   agree, so the chosen image never has to be compared with itself. *)
#[export] Instance sub_join_respects :
  Proper (equiv ==> equiv ==> equiv) (@sub_join C CC x HI).
Proof.
  intros u u' Hu v v' Hv.
  apply (IsUnion_unique (sub_pair u' v')).
  - apply (IsUnion_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_join_IsJoin u v).
  - exact (sub_join_IsJoin u' v').
Defined.

Lemma sub_join_comm (u v : SubObj x) : sub_join u v ≈ sub_join v u.
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub; [ exact (sub_join_le_r v u)
                           | exact (sub_join_le_l v u) ].
  - apply sub_join_is_lub; [ exact (sub_join_le_r u v)
                           | exact (sub_join_le_l u v) ].
Defined.

Lemma sub_join_assoc (u v w : SubObj x) :
  sub_join (sub_join u v) w ≈ sub_join u (sub_join v w).
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub.
    + apply sub_join_is_lub.
      * exact (sub_join_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_r _ _)).
    + exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_r _ _)).
  - apply sub_join_is_lub.
    + exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_l _ _)).
    + apply sub_join_is_lub.
      * exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_l _ _)).
      * exact (sub_join_le_r _ _).
Defined.

Lemma sub_join_idem (u : SubObj x) : sub_join u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u u u (sub_le_refl u) (sub_le_refl u)).
  - exact (sub_join_le_l u u).
Defined.

(* "u ≤ v iff u ∨ v ≈ v", again in two separate lemmas. *)
Lemma sub_join_of_le (u v : SubObj x) : sub_le u v → sub_join u v ≈ v.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u v v Huv (sub_le_refl v)).
  - exact (sub_join_le_r u v).
Defined.

Lemma sub_le_of_join (u v : SubObj x) : sub_join u v ≈ v → sub_le u v.
Proof.
  intros Hj.
  exact (sub_le_trans _ _ _ (sub_join_le_l u v) (sub_le_of_equiv _ _ Hj)).
Defined.

End JoinLattice.

(** ** Absorption: the two operations make a lattice on the setoid *)

Section Absorption.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

(* u ∧ (u ∨ v) ≈ u.  One direction is the meet's first projection, the
   other is the greatest-lower-bound property applied to u ≤ u and
   u ≤ u ∨ v. *)
Theorem sub_meet_absorb (u v : SubObj x) : sub_meet u (sub_join u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u (sub_join u v)).
  - exact (sub_meet_is_glb u (sub_join u v) u (sub_le_refl u)
             (sub_join_le_l u v)).
Defined.

(* u ∨ (u ∧ v) ≈ u, dually. *)
Theorem sub_join_absorb (u v : SubObj x) : sub_join u (sub_meet u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u (sub_meet u v) u (sub_le_refl u)
             (sub_meet_le_l u v)).
  - exact (sub_join_le_l u (sub_meet u v)).
Defined.

End Absorption.

(** ** Indexed joins *)

Section WideJoin.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(* The union of a family: the image of the induced map out of an indexed
   coproduct of the domains, given such an image. *)
Definition sub_wide_join_via {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  SubObj x := im_sub I.

(* The indexed least upper bound.  Membership is the j-th coproduct
   injection followed by the image factorization; minimality copairs the
   family of factorizations a competing subobject supplies and identifies
   the result with the induced map by the uniqueness half of
   [icoprod_desc]. *)
Theorem sub_wide_join_via_IsUnion {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  IsUnion S (sub_wide_join_via P I).
Proof.
  pose (D := icoprod_desc P (fun j => sub_mono (S j))).
  constructor.
  - (* the j-th member sits below the image *)
    intro j.
    exists (im_factor I ∘ inj j).
    unfold sub_wide_join_via.
    rewrite comp_assoc.
    rewrite (im_commutes I).
    exact (unique_property D j).
  - (* and the image is below every common upper bound *)
    intros v Hv.
    pose proof (icoprod_desc P (fun j => `1 (Hv j))) as E.
    apply (im_least I v (unique_obj E)).
    symmetry.
    apply (uniqueness D).
    intro j.
    rewrite <- comp_assoc.
    rewrite (unique_property E j).
    exact (`2 (Hv j)).
Defined.

End WideJoin.

(** ** The bottom subobject *)

Section Bottom.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(* The least subobject, when the arrow out of the initial object is monic
   (it is whenever the initial object is strict). *)
Definition sub_bot (Hz : Monic (@zero C I x)) : SubObj x := {|
  sub_dom := 0;
  sub_mono := zero;
  sub_is_monic := Hz
|}.

Lemma sub_bot_least (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_le (sub_bot Hz) u.
Proof. exists zero; apply zero_unique. Defined.

(* Strictness supplies the hypothesis.  For g1 g2 : w ~> 0, strictness at
   g1 gives an isomorphism i : w ≅ 0; every map w ~> 0 then agrees with
   [to i], because precomposing it with [from i] lands in the endomorphism
   monoid of the initial object, where [zero_unique] leaves only the
   identity.  The cancellation hypothesis of [Monic] is never consumed:
   in a category with a strict initial object ANY two maps into 0 agree. *)
Lemma zero_monic_of_strict
  (Hstrict : ∀ (y : C) (f : y ~> 0), y ≅ 0) : Monic (@zero C I x).
Proof.
  constructor; intros w g1 g2 _.
  pose proof (Hstrict w g1) as i.
  assert (Hto : ∀ g : w ~> 0, g ≈ to i).
  { intro g.
    transitivity (g ∘ (from i ∘ to i)).
    - rewrite (iso_from_to i); cat.
    - rewrite comp_assoc.
      rewrite (@zero_unique C I 0 (g ∘ from i) id).
      cat. }
  now rewrite (Hto g1), (Hto g2).
Qed.

(* The empty union, at the least subobject. *)
Lemma IsUnion_empty_bot (Hz : Monic (@zero C I x)) {J : Type}
  (S : J → SubObj x) (Hempty : J → False) : IsUnion S (sub_bot Hz).
Proof.
  exact (IsUnion_empty_of_least S (sub_bot Hz) (sub_bot_least Hz) Hempty).
Defined.

End Bottom.

(** ** The bottom in a bicartesian closed category *)

Section BiCCCBottom.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context `{I : @Initial C}.
Context {x : C}.

(* A cartesian closed category with an initial object has a STRICT
   initial object (Structure/BiCCC.v:262, [initial_strict]), so the arrow
   out of it is monic and [sub_bot] applies with no further hypothesis.
   This is the one place in this file where the bottom subobject is
   obtained rather than assumed.  Two measurements govern it.  The
   requirement cost was taken only after being measured, by iterating
   [coqdep -R . Category FILE] to a fixed point over the .v files named
   in its right-hand sides: the two files Structure/BiCCC.v adds to this
   file's requirement closure are itself and Structure/Distributive.v,
   taking that closure from 46 to 48 (the whole file's closure is 48
   files; the interface stub this one replaced measured 37 by the same
   procedure).  And the hypothesis list is exactly the one
   below, NOT the full bicartesian closed one: [initial_strict] is proved
   in Structure/BiCCC.v under a cocartesian context as well, but does not
   consume it, so no [Cocartesian] is declared here and none appears in
   the discharged type of [biccc_zero_monic] -- read off with
   [Check @biccc_zero_monic], whose binders are the category, a
   [Cartesian], a [Closed], a [Terminal] of the opposite (that is the
   [Initial]), and the object. *)
Definition biccc_zero_monic : Monic (@zero C I x) :=
  zero_monic_of_strict (fun y f => initial_strict f).

(* ... and the bottom subobject it names. *)
Definition biccc_sub_bot : SubObj x := sub_bot biccc_zero_monic.

End BiCCCBottom.

(** ** The bottom against the two operations *)

Section BottomMeet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{I : @Initial C}.
Context {x : C}.

(* ∅ ∩ X ≈ ∅. *)
Theorem sub_meet_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_meet (sub_bot Hz) u ≈ sub_bot Hz.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l (sub_bot Hz) u).
  - exact (sub_bot_least Hz (sub_meet (sub_bot Hz) u)).
Defined.

End BottomMeet.

Section BottomJoin.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context `{I : @Initial C}.
Context {x : C}.

(* Fong and Spivak §1.2.1's unit law ∅ ∪ X ≅ X, at the level of
   subobjects, with the image of the copairing handed in: the bottom is
   below u, so u is already a least upper bound of the pair, and least
   upper bounds agree.  Stated first with an explicit [ImageOf], so that a
   category with images for SOME copairings (or a single computed image)
   can use it without a [HasImages] instance; the class form follows.
   [HI] is not consumed by this lemma and is dropped from its discharged
   type -- read it off with [Check @sub_join_via_bot]. *)
Lemma sub_join_via_bot (Hz : Monic (@zero C I x)) (u : SubObj x)
  (Img : ImageOf (merge (sub_mono (sub_bot Hz)) (sub_mono u))) :
  sub_join_via (sub_bot Hz) u Img ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_via_is_lub (sub_bot Hz) u Img u (sub_bot_least Hz u)
             (sub_le_refl u)).
  - exact (sub_join_via_le_r (sub_bot Hz) u Img).
Defined.

Theorem sub_join_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_join (sub_bot Hz) u ≈ u.
Proof.
  exact (sub_join_via_bot Hz u
           (image_of (merge (sub_mono (sub_bot Hz)) (sub_mono u)))).
Defined.

End BottomJoin.

(** ** Images from an orthogonal factorization system *)

Section OFSImages.

Context {C : Category}.
Context {E : MorphismClass C}.

(* The mono leg of an (E, Mono) factorization, read as a subobject.  No
   transport is needed: Theory/Morphisms/Classes.v:31 defines [MonoClass]
   as [fun _ _ f => Monic f], so [fact_m_in] IS the [sub_is_monic]
   field. *)
Definition ofs_image_sub (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  SubObj x := {|
  sub_dom := fact_mid (ofs_factor (OFS := O) f);
  sub_mono := fact_m (ofs_factor (OFS := O) f);
  sub_is_monic := fact_m_in (ofs_factor (OFS := O) f)
|}.

(* Minimality is orthogonality.  A factorization of f through a subobject
   w bounds a commuting square between the E-leg of the factorization and
   the mono of w; the diagonal filler of Theory/Orthogonality.v:43 is the
   arrow exhibiting the image below w, and its second triangle is the
   factorization required by [sub_le]. *)
Lemma ofs_image_least (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x)
  (w : SubObj x) (g : y ~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le (ofs_image_sub O f) w.
Proof.
  pose proof (ofs_orth (OFS := O) (fact_e (ofs_factor (OFS := O) f))
                (sub_mono w) (fact_e_in (ofs_factor (OFS := O) f))
                (sub_is_monic w)) as Ho.
  assert (Hc : sub_mono w ∘ g
               ≈ fact_m (ofs_factor (OFS := O) f)
                   ∘ fact_e (ofs_factor (OFS := O) f)).
  { rewrite (fact_comm (ofs_factor (OFS := O) f)); exact Hg. }
  pose proof (ortho_lift (Orthogonal := Ho) Hc) as U.
  exists (unique_obj U).
  exact (snd (unique_property U)).
Defined.

(* Every (E, Mono) factorization system supplies images. *)
Definition ImageOf_of_OFS (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  ImageOf f := {|
  im_sub := ofs_image_sub O f;
  im_factor := fact_e (ofs_factor (OFS := O) f);
  im_commutes := fact_comm (ofs_factor (OFS := O) f);
  im_least := fun w g Hg => ofs_image_least O f w g Hg
|}.

Definition HasImages_of_OFS (O : OFS E (@MonoClass C)) : HasImages C :=
  {| image_of := fun y x f => ImageOf_of_OFS O f |}.

End OFSImages.

(* A regular category has images, through its (regular epi, mono) system
   Regular_OFS (Structure/Regular/Factorization.v:282).  CONDITIONAL: no
   [Regular] instance exists in this tree (Instance/Sets/Pullback.v:62),
   so this corollary is an implication awaiting a model, and it is the
   only route in this file from an established structure to [HasImages]. *)
Definition Regular_HasImages {C : Category} (R : Regular C) : HasImages C :=
  HasImages_of_OFS (@Regular_OFS C R).
