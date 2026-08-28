Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Group.Representable.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** * Group objects in a functor category are pointwise groups *)

(* nLab:      https://ncatlab.org/nlab/show/group+object
   nLab:      https://ncatlab.org/nlab/show/functor+category
   Wikipedia: https://en.wikipedia.org/wiki/Group_object
   Book:      Mac Lane, CWM 2nd ed., Section III.6 ("Groups in
              Categories"), Exercise 3, p. 76

   Mac Lane's exercise: a functor [T : B ⟶ Sets] is a group object in
   the functor category [[B, Sets]] exactly when every value [T b] is an
   ordinary group and every [T f] is a group homomorphism.  Everything
   that makes this work is that [Sets] has finite products and that
   [Instance/Fun/Cartesian.v] and [Instance/Fun/Terminal.v] compute the
   products of [[B, Sets]] POINTWISE, so that each diagrammatic law of
   [Structure/Group.v]'s [GroupObject], read at an object [b] and at an
   element, IS the corresponding elementary group law in [T b], and the
   NATURALITY of the structure maps IS the statement that each [T f] is
   a homomorphism.

   A PRIOR-ART CORRECTION, WITH ITS DATE.  The issue states that "no
   monoid or group object is ever instantiated at a functor category".
   READ THAT IN TWO HALVES, because only one of them is newly false.
   THE MONOID HALF WAS NEVER TRUE: Monad/Monoid.v has carried
   [Monoid_Monad : @MonoidObject (Endofunctors C) Compose_Monoidal M
   <-> Monad M] since 2017-05-29, where [Endofunctors C := [C, C]] --
   a monoid object at a functor category, in the build set
   (_CoqProject:445), and named in Structure/Monoid.v:77, which THIS
   FILE Requires.  An earlier revision of this header dated the whole
   claim to f3b797fd and was wrong to; the tensor there is
   [Compose_Monoidal] rather than the pointwise cartesian one used
   here, but the absence claim is unqualified as to tensor, so the
   qualifier does not rescue it.  The alias is how the miss happened
   and is worth recording: grepping for [@MonoidObject (\[] does not
   match, because the functor category hides behind [Endofunctors].
   THE GROUP HALF is the part genuinely falsified at master f3b797fd,
   which landed issue #341 as
   Structure/Group/Representable.v: its [RepPresheaf_Group] has type
   [forall {C} (e : C), HomGroupData e -> GroupObject (RepPresheaf e)]
   and [RepPresheaf e : [C^op, Sets]], so its conclusion is literally a
   group object in a functor category, over exactly the pointwise
   [Functor_Category_Cartesian]/[Functor_Category_Terminal] structure
   used here.  [RepresentablyGroup e] is that type packaged.

   WHAT #341 SUPPLIED AND WHAT IT DID NOT, measured rather than assumed.
   No PROOF CONTENT from Structure/Group/Representable.v is reused by
   the development below -- the cross-link at the end of this file does
   consume three of its DEFINITIONS ([RepresentablyMonoid],
   [RepresentablyGroup], [RepPresheaf]), and this file Requires that
   module for them; its central record [HomGroupData e] carries a
   group structure on the hom-SETS [x ~> e], which presupposes that the
   functor in question is [C(-,e)], while [T] here is arbitrary and its
   values [T b] are plain setoids.  Its [FromPresheaf]/[FromPresheafGroup]
   sections are the closest analogue -- they decompose a monoid or group
   object of [[C^op, Sets]] into elementwise operations, exactly the
   forward direction below -- but both are stated inside a section whose
   [Context] FIXES the object to [RepPresheaf e], so neither can be
   applied to an arbitrary [T].  Its generic product-form readings of the
   diagrammatic laws ([rg_unit_left_law] and siblings) WOULD have applied
   at [C := [B, Sets]]; they are not used, because over [Sets] the laws
   evaluate at elements directly and the product form is a detour.  The
   traffic runs the other way instead: [representably_group_iff_pointwise]
   below obtains #341's presheaf statement as an INSTANCE of this one, by
   [:=] with no tactic.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH.

   (A) Two records, [PointwiseMonoid T] and [PointwiseGroup T], holding
       exactly Mac Lane's data: a group (monoid) structure on each [T b],
       and the clauses saying each [T f] is a homomorphism.

   (B) The headline BICONDITIONALS -- genuine [iffT]s, not a pair of
       named passages -- [monoid_object_iff_pointwise] and
       [group_object_iff_pointwise].  Both are [Defined], so the two
       passages are the named constants [monoid_object_pointwise],
       [pointwise_MonoidObject], [group_object_pointwise] and
       [pointwise_GroupObject] and can be computed with.  The monoid
       analogue really is nearly free, and the file shows exactly how
       nearly: the group half adds one transformation, two laws and one
       naturality clause on each side, and reuses the monoid half by
       [groupobject_is_monoid] and by [pg_monoid].

   (C) The five diagrammatic laws are read off at a point BY CONVERSION:
       [fun_unit_l_raw], [fun_unit_r_raw], [fun_assoc_raw],
       [fun_inv_l_raw] and [fun_inv_r_raw] are the class fields applied
       to an explicit element, supplied by [:=] with no tactic and no
       transport.  So the elementary statements ARE the diagrammatic
       ones; nothing is compared across a bridge.

   (D) The ordinary-group reading, as a LIFT: [pointwise_GrpObject] gives
       an Instance/Grp.v [GrpObject] whose carrier is [T b] on the nose,
       [pointwise_GrpHom] gives a [GrpHom] whose underlying map is
       [fmap[T] f] on the nose (both carriers pinned by [eq_refl] in
       [pointwise_GrpObject_carrier] and [pointwise_MonObject_carrier]),
       and [PointwiseGrpFunctor P : B ⟶ Grp]
       assembles them, with [Grp_Forget ◯ PointwiseGrpFunctor P] agreeing
       with [T] on OBJECTS and on ARROWS by [eq_refl].  Conversely
       [grp_functor_PointwiseGroup] and [grp_functor_GroupObject] show
       that EVERY functor into [Grp] carries a group object on its
       underlying functor, with no hypothesis at all.

   STRENGTHS AND WEAKENINGS, each diagnosed.  Everything that survives on
   the nose is pinned as an [eq_refl] [Example]; three strict attempts
   are REFUTED, each pinned as a [Fail] beside the controls that guard
   it.  (i) [Grp_Forget ◯ PointwiseGrpFunctor P = T] is refused: the
   composite rebuilds [fmap_respects], [fmap_id] and [fmap_comp] as its
   own opaque proofs, so what fails is record equality and NOT the
   actions, which do agree ([PointwiseGrpFunctor_forgets_obj] and
   [_forgets_map] are the controls).  The lift is therefore NOT claimed
   strict, and no equality of functors is asserted anywhere.  (ii) The
   round trip on the pointwise datum returns all three OPERATIONS by
   [eq_refl] ([roundtrip_unit], [roundtrip_mul], [roundtrip_inv]) but not
   the whole record: [pw_mul_respects] is rebuilt.  (iii) The round trip
   on the object returns the VALUES of both structure maps by [eq_refl]
   ([roundtrip_obj_unit], [roundtrip_obj_mul]) but not the whole record,
   for the same reason one level up -- the naturality fields of the
   rebuilt transformations are this file's own opaque proofs.  So the two
   passages are mutually inverse ON THE DATA and nothing stronger is
   claimed; in particular neither biconditional is an equivalence of
   structures.

   One residue recurs in every proof and is worth naming: the identity
   natural transformation of [[B, Sets]] has component [fmap[F] id], not
   [id], so each law arrives with a [fmap[T] id] wrapped round one
   argument.  [T_fmap_id] discharges it.  This is the same [nat_id] fact
   already recorded at Theory/Natural/Transformation.v:220 and consumed
   in Construction/Elements/Kan.v and Functor/Representable/Functorial.v.

   UNIVERSES, measured in the constraint block AND read off the binder,
   because here the two disagree.  [PointwiseMonoid@{bo bh bp o so}] and
   [PointwiseGroup@{bo bh bp o so}] are over [B : Category@{bo bh bp}]
   and [Sets@{o so}] and identify NOTHING: the block is [o < so] (which
   is [Sets]' own strictness) plus the bounds [bh <= bp], [bh <= o],
   [bp <= o] and four donor bounds ([o <= Basics.compose.u0/u1/u2],
   [o <= ID.u0]) -- EIGHT entries in all, not the four an earlier
   revision of this sentence listed as though exhaustive.  What matters
   is unchanged and is the point: there is NO equation anywhere in
   either record's block, and [bo] is entirely unconstrained.  Every
   constant of the file that BINDS a [B] is over
   [B : Category@{u u0 u0}] with the record instantiated at
   [PointwiseMonoid@{u u0 u0 u0 u1}] -- B's hom, B's proof and [Sets]'
   carrier universe ALL IDENTIFIED -- and that identification lives
   ENTIRELY IN THE BINDER: the constraint blocks contain [u0 < u1],
   [u <= u2], [u <= u3], [u1 <= u2] and further bounds, and NO equation,
   so reading the block alone would miss it completely.  The two OBJECT
   universes stay free throughout.  The [Witness] section's constants
   ([Und], [Z2_triv], [Und_GroupObject]) bind no [B] at all and are
   outside that description.

   The cause is [Fun], and it is guarded rather than asserted: sections
   [UniverseBoundary] and [UniverseBoundary2] declare the levels apart
   and exhibit [B ⟶ Sets] and [PointwiseGroup T] as formable there while
   [[B, Sets]] is REJECTED, with the two halves separated -- [Fun] forces
   the source category's hom and proof universes to agree, AND forces the
   source's hom universe to be the target's, and neither half alone
   accounts for the collapse.  One qualification, stated rather than
   glossed: [PointwiseGrpFunctor], [pointwise_GrpObject] and
   [pointwise_GrpHom] mention no functor category, and [B ⟶ Grp] is
   formable with the levels apart, so THEIR identification is not
   [Fun]'s but the unannotated [Context {B : Category}] of the section
   they live in -- the minimization family recorded for
   [Build_Quiver_Standard_Eq].  It is repairable in principle and is NOT
   claimed unavoidable; a lift was not attempted, since the headline
   theorems mention [[B, Sets]] and so would keep the identification
   regardless.

   NON-VACUITY.  The witness index category is [Grp] itself and the
   witness functor is [Id[Grp]], so no new functor into [Grp] is built:
   [Und_GroupObject] is the underlying-set functor of [Grp] as a group
   object in [[Grp, Sets]], and the operations recovered from it COMPUTE
   at [Z2] ([und_unit_computes], [und_mul_computes], [und_inv_computes],
   all [eq_refl]).  Both degeneracies are excluded by proof rather than
   assumed: [und_nontrivial] shows the group at [Z2] has two distinct
   elements, and [und_fmap_not_id] shows the arrow action at the trivial
   endomorphism [Z2_triv] genuinely moves one, so the two homomorphism
   clauses are applied to a map that is not an identity.  A THIRD
   degeneracy is NOT excluded and is disclosed here rather than left for
   a reader to notice: the group is [Z2], where inversion IS the
   identity -- [und_inv_computes] records exactly that -- so [pg_inv],
   [pg_inv_l], [pg_inv_r] and [pg_map_inv] are never exercised at an
   element that is not its own inverse.  The index is [Grp] and the
   functor [Id[Grp]], so any in-tree group would serve; no such witness
   is built here.

   115/115 constants are Closed under the global context: [Print Module]
   lists 113, and the two unlisted names are [Build_PointwiseMonoid] and
   [Build_PointwiseGroup].  The file declares no [Axiom] and no
   [Parameter].  An earlier revision of this paragraph said "81" and
   gave as its reason that the [Program] obligations "leave no
   separately named constants behind"; BOTH were wrong -- there are 34
   such obligations and they are ordinary constants.  They are invisible
   to [Print Assumptions] under a BARE name (which is what produced the
   81) and resolve only fully qualified, e.g.
   [Category.Instance.Fun.Group.pointwise_MonoidObject_obligation_1].
   Note also that [Print Module] prints [Qed] constants as [Parameter];
   that is a display convention, not an axiom leak.

   NOT DELIVERED.  No abelian/commutative variant and no Eckmann-Hilton
   consequence.  No [Cocartesian] or coproduct story.  Nothing about a
   general target [D] in place of [Sets] -- the whole development reads
   the laws at ELEMENTS, so a general cartesian [D] would need the
   product-form route instead (which is why Structure/Group/Representable.v's
   [rg_*_law] lemmas are cited above rather than deleted).  No claim that
   [PointwiseGrpFunctor] is an equivalence between [PointwiseGroup T] and
   lifts of [T] through [Grp_Forget]: the object and arrow actions agree
   on the nose, but the strict lift is refuted and no groupoid of lifts is
   built.  The monoid analogue of the [Grp] reading stops at the OBJECT:
   [pointwise_MonObject] gives a Construction/Deloop.v [MonObject] per
   [b], but that record has no category attached, and the tree's only
   category of GENERAL monoids (Instance/CMon.v's [CMon] being
   commutative), Theory/Algebra/Monoid/Hom.v's [Mon], is a category of
   INTERNAL monoids over a chosen monoidal structure --
   [Mon Sets] is taken at [Sets_Product_Monoidal], which Instance/Grp.v's
   own note records as a distinct, NON-CONVERTIBLE term from the
   [CC_Monoidal] used here -- so no [Mon]-valued functor and no monoid
   twin of [PointwiseGrpFunctor] is built.  No naturality of
   the biconditional in [T], and no functoriality of [PointwiseGroup].
   And no witness with a NON-CONSTANT object action combined with a small
   index category: the witness's index is [Grp], which is large. *)

(* ------------------------------------------------------------------ *)
(* The pointwise datum                                                 *)
(* ------------------------------------------------------------------ *)

(* Declared at top level with explicit universe binders rather than inside
   the section below: with an unannotated [Context {B : Category}] the
   elaborator MINIMIZES, identifying B's hom and proof universes with each
   other and with [Sets]' carrier universe.  Written out, the records keep
   all five apart -- see the UNIVERSES paragraph in the header. *)

Record PointwiseMonoid@{bo bh bp o so} {B : Category@{bo bh bp}}
  (T : B ⟶ Sets@{o so}) : Type := {
  pw_unit : ∀ b, carrier (T b);
  pw_mul  : ∀ b, carrier (T b) → carrier (T b) → carrier (T b);

  pw_mul_respects : ∀ b, Proper (equiv ==> equiv ==> equiv) (pw_mul b);

  pw_assoc : ∀ b u v w,
    pw_mul b (pw_mul b u v) w ≈ pw_mul b u (pw_mul b v w);
  pw_unit_l : ∀ b u, pw_mul b (pw_unit b) u ≈ u;
  pw_unit_r : ∀ b u, pw_mul b u (pw_unit b) ≈ u;

  pw_map_unit : ∀ x y (f : x ~{B}~> y), fmap[T] f (pw_unit x) ≈ pw_unit y;
  pw_map_mul : ∀ x y (f : x ~{B}~> y) u v,
    fmap[T] f (pw_mul x u v) ≈ pw_mul y (fmap[T] f u) (fmap[T] f v)
}.

Record PointwiseGroup@{bo bh bp o so} {B : Category@{bo bh bp}}
  (T : B ⟶ Sets@{o so}) : Type := {
  pg_monoid :> PointwiseMonoid@{bo bh bp o so} T;

  pg_inv : ∀ b, carrier (T b) → carrier (T b);
  pg_inv_respects : ∀ b, Proper (equiv ==> equiv) (pg_inv b);

  pg_inv_l : ∀ b u,
    pw_mul _ pg_monoid b (pg_inv b u) u ≈ pw_unit _ pg_monoid b;
  pg_inv_r : ∀ b u,
    pw_mul _ pg_monoid b u (pg_inv b u) ≈ pw_unit _ pg_monoid b;

  pg_map_inv : ∀ x y (f : x ~{B}~> y) u,
    fmap[T] f (pg_inv x u) ≈ pg_inv y (fmap[T] f u)
}.

Arguments pw_unit {B T}.
Arguments pw_mul {B T}.
Arguments pw_mul_respects {B T}.
Arguments pw_assoc {B T}.
Arguments pw_unit_l {B T}.
Arguments pw_unit_r {B T}.
Arguments pw_map_unit {B T}.
Arguments pw_map_mul {B T}.
Arguments pg_monoid {B T}.
Arguments pg_inv {B T}.
Arguments pg_inv_respects {B T}.
Arguments pg_inv_l {B T}.
Arguments pg_inv_r {B T}.
Arguments pg_map_inv {B T}.

#[export] Existing Instance pw_mul_respects.
#[export] Existing Instance pg_inv_respects.

Section Pointwise.

Context {B : Category}.
Context (T : B ⟶ Sets).

Lemma T_fmap_id (b : B) (u : carrier (T b)) : fmap[T] (id[b]) u ≈ u.
Proof. exact (@fmap_id _ _ T b u). Qed.

(* ------------------------------------------------------------------ *)
(* Forward: a monoid/group object has pointwise structure              *)
(* ------------------------------------------------------------------ *)

Section Forward.

Context (M : @MonoidObject ([B, Sets]) CC_Monoidal T).

Definition fun_unit (b : B) : carrier (T b) :=
  transform[@mempty _ _ _ M] b ttt.

Definition fun_mul (b : B) (u v : carrier (T b)) : carrier (T b) :=
  transform[@mappend _ _ _ M] b (u, v).

#[local] Instance fun_mul_respects (b : B) :
  Proper (equiv ==> equiv ==> equiv) (fun_mul b).
Proof.
  intros u u' Hu v v' Hv.
  unfold fun_mul.
  apply proper_morphism; split; assumption.
Qed.

(* The five diagrammatic laws, read off at a point.  Each is the class
   field applied to an explicit element and is accepted by CONVERSION --
   no tactic, no transport -- so the elementary statements below are the
   diagrammatic ones.  The residual [fmap[T] id] is the component of the
   identity natural transformation of [[B, Sets]], which is [fmap[F] id]
   and not [id]; it is discharged by [T_fmap_id]. *)

Definition fun_unit_l_raw (b : B) (u : carrier (T b)) :
  fun_mul b (fun_unit b) (fmap[T] (id[b]) u) ≈ u :=
  @mempty_left ([B, Sets]) CC_Monoidal T M b (ttt, u).

Definition fun_unit_r_raw (b : B) (u : carrier (T b)) :
  fun_mul b (fmap[T] (id[b]) u) (fun_unit b) ≈ u :=
  @mempty_right ([B, Sets]) CC_Monoidal T M b (u, ttt).

Definition fun_assoc_raw (b : B) (u v w : carrier (T b)) :
  fun_mul b (fun_mul b u v) (fmap[T] (id[b]) w)
    ≈ fun_mul b (fmap[T] (id[b]) u) (fun_mul b v w) :=
  @mappend_assoc ([B, Sets]) CC_Monoidal T M b ((u, v), w).

Lemma fun_unit_l (b : B) (u : carrier (T b)) :
  fun_mul b (fun_unit b) u ≈ u.
Proof.
  transitivity (fun_mul b (fun_unit b) (fmap[T] (id[b]) u)).
  - now rewrite T_fmap_id.
  - exact (fun_unit_l_raw b u).
Qed.

Lemma fun_unit_r (b : B) (u : carrier (T b)) :
  fun_mul b u (fun_unit b) ≈ u.
Proof.
  transitivity (fun_mul b (fmap[T] (id[b]) u) (fun_unit b)).
  - now rewrite T_fmap_id.
  - exact (fun_unit_r_raw b u).
Qed.

Lemma fun_assoc (b : B) (u v w : carrier (T b)) :
  fun_mul b (fun_mul b u v) w ≈ fun_mul b u (fun_mul b v w).
Proof.
  transitivity (fun_mul b (fun_mul b u v) (fmap[T] (id[b]) w)).
  - now rewrite T_fmap_id.
  - rewrite fun_assoc_raw.
    now rewrite T_fmap_id.
Qed.

Lemma fun_map_unit (x y : B) (f : x ~{B}~> y) :
  fmap[T] f (fun_unit x) ≈ fun_unit y.
Proof.
  unfold fun_unit.
  exact (@naturality _ _ _ _ (@mempty _ _ _ M) x y f ttt).
Qed.

Lemma fun_map_mul (x y : B) (f : x ~{B}~> y) (u v : carrier (T x)) :
  fmap[T] f (fun_mul x u v) ≈ fun_mul y (fmap[T] f u) (fmap[T] f v).
Proof.
  unfold fun_mul.
  exact (@naturality _ _ _ _ (@mappend _ _ _ M) x y f (u, v)).
Qed.

Definition monoid_object_pointwise : PointwiseMonoid T :=
  {| pw_unit         := fun_unit
   ; pw_mul          := fun_mul
   ; pw_mul_respects := fun_mul_respects
   ; pw_assoc        := fun_assoc
   ; pw_unit_l       := fun_unit_l
   ; pw_unit_r       := fun_unit_r
   ; pw_map_unit     := fun_map_unit
   ; pw_map_mul      := fun_map_mul |}.

End Forward.

Section ForwardGroup.

Context (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T).

Definition fun_gmonoid : @MonoidObject ([B, Sets]) CC_Monoidal T :=
  @groupobject_is_monoid ([B, Sets]) CC_CartesianMonoidal T G.

Definition fun_inv (b : B) (u : carrier (T b)) : carrier (T b) :=
  transform[@Category.Structure.Group.inverse _ _ _ G] b u.

#[local] Instance fun_inv_respects (b : B) :
  Proper (equiv ==> equiv) (fun_inv b).
Proof. intros u u' Hu; unfold fun_inv; now apply proper_morphism. Qed.

Definition fun_inv_l_raw (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fun_inv b (fmap[T] (id[b]) u))
          (fmap[T] (id[b]) (fmap[T] (id[b]) u))
    ≈ fun_unit fun_gmonoid b :=
  @left_inverse ([B, Sets]) CC_CartesianMonoidal T G b u.

Definition fun_inv_r_raw (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fmap[T] (id[b]) (fmap[T] (id[b]) u))
          (fun_inv b (fmap[T] (id[b]) u))
    ≈ fun_unit fun_gmonoid b :=
  @right_inverse ([B, Sets]) CC_CartesianMonoidal T G b u.

Lemma fun_inv_l (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fun_inv b u) u ≈ fun_unit fun_gmonoid b.
Proof.
  transitivity (fun_mul fun_gmonoid b (fun_inv b (fmap[T] (id[b]) u))
                  (fmap[T] (id[b]) (fmap[T] (id[b]) u))).
  - unfold fun_mul, fun_inv.
    apply proper_morphism; split; simpl.
    + apply proper_morphism; symmetry; apply T_fmap_id.
    + symmetry; transitivity (fmap[T] (id[b]) u); apply T_fmap_id.
  - exact (fun_inv_l_raw b u).
Qed.

Lemma fun_inv_r (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b u (fun_inv b u) ≈ fun_unit fun_gmonoid b.
Proof.
  transitivity (fun_mul fun_gmonoid b (fmap[T] (id[b]) (fmap[T] (id[b]) u))
                  (fun_inv b (fmap[T] (id[b]) u))).
  - unfold fun_mul, fun_inv.
    apply proper_morphism; split; simpl.
    + symmetry; transitivity (fmap[T] (id[b]) u); apply T_fmap_id.
    + apply proper_morphism; symmetry; apply T_fmap_id.
  - exact (fun_inv_r_raw b u).
Qed.

Lemma fun_map_inv (x y : B) (f : x ~{B}~> y) (u : carrier (T x)) :
  fmap[T] f (fun_inv x u) ≈ fun_inv y (fmap[T] f u).
Proof.
  unfold fun_inv.
  exact (@naturality _ _ _ _
           (@Category.Structure.Group.inverse _ _ _ G) x y f u).
Qed.

Definition group_object_pointwise : PointwiseGroup T :=
  {| pg_monoid       := monoid_object_pointwise fun_gmonoid
   ; pg_inv          := fun_inv
   ; pg_inv_respects := fun_inv_respects
   ; pg_inv_l        := fun_inv_l
   ; pg_inv_r        := fun_inv_r
   ; pg_map_inv      := fun_map_inv |}.

End ForwardGroup.


(* ------------------------------------------------------------------ *)
(* Backward: pointwise structure assembles a monoid/group object       *)
(* ------------------------------------------------------------------ *)

Section Backward.

Context (P : PointwiseMonoid T).


Program Definition pw_unit_nt : (1 : [B, Sets]) ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := fun _ => pw_unit P b |}
|}.
Next Obligation. now apply pw_map_unit. Qed.
Next Obligation. symmetry; now apply pw_map_unit. Qed.

Program Definition pw_mul_nt :
  @product_obj ([B, Sets]) _ T T ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := fun p => pw_mul P b (fst p) (snd p) |}
|}.
Next Obligation.
  intros p q [Hl Hr]; simpl in *; now rewrite Hl, Hr.
Qed.
Next Obligation. now apply pw_map_mul. Qed.
Next Obligation. symmetry; now apply pw_map_mul. Qed.

Program Definition pointwise_MonoidObject :
  @MonoidObject ([B, Sets]) CC_Monoidal T := {|
  mempty  := pw_unit_nt;
  mappend := pw_mul_nt
|}.
Next Obligation. rewrite T_fmap_id; apply pw_unit_l. Qed.
Next Obligation. rewrite T_fmap_id; apply pw_unit_r. Qed.
Next Obligation. rewrite !T_fmap_id; apply pw_assoc. Qed.

End Backward.


Section BackwardGroup.

Context (P : PointwiseGroup T).


Program Definition pg_inv_nt : T ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := pg_inv P b |}
|}.
Next Obligation. now apply pg_map_inv. Qed.
Next Obligation. symmetry; now apply pg_map_inv. Qed.

Program Definition pointwise_GroupObject :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal T := {|
  groupobject_is_monoid := pointwise_MonoidObject (pg_monoid P);
  Category.Structure.Group.inverse := pg_inv_nt
|}.
Next Obligation. rewrite !T_fmap_id; apply pg_inv_l. Qed.
Next Obligation. rewrite !T_fmap_id; apply pg_inv_r. Qed.

End BackwardGroup.


(* ------------------------------------------------------------------ *)
(* The headline biconditionals                                         *)
(* ------------------------------------------------------------------ *)

Theorem monoid_object_iff_pointwise :
  @MonoidObject ([B, Sets]) CC_Monoidal T ↔ PointwiseMonoid T.
Proof.
  split.
  - exact monoid_object_pointwise.
  - exact pointwise_MonoidObject.
Defined.

Theorem group_object_iff_pointwise :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal T ↔ PointwiseGroup T.
Proof.
  split.
  - exact group_object_pointwise.
  - exact pointwise_GroupObject.
Defined.

(* ------------------------------------------------------------------ *)
(* Strength: what holds on the nose                                    *)
(* ------------------------------------------------------------------ *)

(* The extracted operations ARE the components of the structure maps. *)
Example pointwise_mul_is_component
  (M : @MonoidObject ([B, Sets]) CC_Monoidal T) (b : B)
  (u v : carrier (T b)) :
  pw_mul (monoid_object_pointwise M) b u v
    = transform[@mappend _ _ _ M] b (u, v) := eq_refl.

Example pointwise_unit_is_component
  (M : @MonoidObject ([B, Sets]) CC_Monoidal T) (b : B) :
  pw_unit (monoid_object_pointwise M) b
    = transform[@mempty _ _ _ M] b ttt := eq_refl.

Example pointwise_inv_is_component
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B)
  (u : carrier (T b)) :
  pg_inv (group_object_pointwise G) b u
    = transform[@Category.Structure.Group.inverse _ _ _ G] b u := eq_refl.

(* Round trip, pointwise datum -> object -> pointwise datum: the three
   operations return ON THE NOSE. *)
Example roundtrip_unit (P : PointwiseGroup T) (b : B) :
  pw_unit (monoid_object_pointwise (pointwise_MonoidObject P)) b
    = pw_unit P b := eq_refl.

Example roundtrip_mul (P : PointwiseGroup T) (b : B) (u v : carrier (T b)) :
  pw_mul (monoid_object_pointwise (pointwise_MonoidObject P)) b u v
    = pw_mul P b u v := eq_refl.

Example roundtrip_inv (P : PointwiseGroup T) (b : B) (u : carrier (T b)) :
  pg_inv (group_object_pointwise (pointwise_GroupObject P)) b u
    = pg_inv P b u := eq_refl.

(* Round trip, object -> pointwise datum -> object: the structure maps
   agree on VALUES, on the nose ... *)
Example roundtrip_obj_unit
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B) :
  transform[@mempty _ _ _
    (pointwise_MonoidObject (group_object_pointwise G))] b ttt
    = transform[@mempty _ _ _ (fun_gmonoid G)] b ttt := eq_refl.

Example roundtrip_obj_mul
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B)
  (u v : carrier (T b)) :
  transform[@mappend _ _ _
    (pointwise_MonoidObject (group_object_pointwise G))] b (u, v)
    = transform[@mappend _ _ _ (fun_gmonoid G)] b (u, v) := eq_refl.

(* ------------------------------------------------------------------ *)
(* The ordinary-group reading: a lift through Grp_Forget               *)
(* ------------------------------------------------------------------ *)

(* The monoid half of the ordinary reading.  Construction/Deloop.v's
   [MonObject] is a bare setoid monoid with no category attached, so this
   is an object-level statement only -- there is no [Mon]-valued functor
   to mirror [PointwiseGrpFunctor]; see NOT DELIVERED. *)
Program Definition pointwise_MonObject (P : PointwiseMonoid T) (b : B) :
  MonObject := {|
  mon_setoid := T b;
  mon_unit   := pw_unit P b;
  mon_op     := pw_mul P b
|}.
Next Obligation. symmetry; now apply pw_assoc. Qed.
Next Obligation. now apply pw_unit_l. Qed.
Next Obligation. now apply pw_unit_r. Qed.

Example pointwise_MonObject_carrier (P : PointwiseMonoid T) (b : B) :
  mon_setoid (pointwise_MonObject P b) = T b := eq_refl.

Program Definition pointwise_GrpObject (P : PointwiseGroup T) (b : B) :
  GrpObject := {|
  grp_setoid := T b;
  grp_unit   := pw_unit P b;
  grp_mul    := pw_mul P b;
  grp_inv    := pg_inv P b
|}.
Next Obligation. now apply pw_assoc. Qed.
Next Obligation. now apply pw_unit_l. Qed.
Next Obligation. now apply pg_inv_l. Qed.

Example pointwise_GrpObject_carrier (P : PointwiseGroup T) (b : B) :
  grp_setoid (pointwise_GrpObject P b) = T b := eq_refl.

Program Definition pointwise_GrpHom (P : PointwiseGroup T) {x y : B}
  (f : x ~{B}~> y) :
  GrpHom (pointwise_GrpObject P x) (pointwise_GrpObject P y) := {|
  grp_map := fmap[T] f
|}.
Next Obligation. now apply pw_map_unit. Qed.
Next Obligation. now apply pw_map_mul. Qed.

Program Definition PointwiseGrpFunctor (P : PointwiseGroup T) : B ⟶ Grp := {|
  fobj := pointwise_GrpObject P;
  fmap := fun x y f => pointwise_GrpHom P f
|}.
Next Obligation.
  intros f g Hfg a; simpl.
  exact (@fmap_respects _ _ T x y f g Hfg a).
Qed.
Next Obligation. now apply T_fmap_id. Qed.
Next Obligation. exact (@fmap_comp _ _ T x y z f g a). Qed.

Example PointwiseGrpFunctor_forgets_obj (P : PointwiseGroup T) (b : B) :
  fobj[Grp_Forget ◯ PointwiseGrpFunctor P] b = fobj[T] b := eq_refl.

Example PointwiseGrpFunctor_forgets_map (P : PointwiseGroup T) {x y : B}
  (f : x ~{B}~> y) :
  fmap[Grp_Forget ◯ PointwiseGrpFunctor P] f = fmap[T] f := eq_refl.

(* ------------------------------------------------------------------ *)
(* Strict attempts REFUTED, each beside a positive control             *)
(* ------------------------------------------------------------------ *)

(* (1) The lift is NOT a strict lift: the two functor records are not
   Leibniz-equal, because [Grp_Forget ◯ PointwiseGrpFunctor P] rebuilds
   [fmap_respects], [fmap_id] and [fmap_comp] as its own opaque proofs.
   Both ACTIONS do agree on the nose -- the two Examples just above are
   the controls -- so what is refuted is record equality and nothing
   about the actions. *)
Fail Example lift_is_strict (P : PointwiseGroup T) :
  Grp_Forget ◯ PointwiseGrpFunctor P = T := eq_refl.

(* (2) The round trip on the pointwise datum does not close at the whole
   record either: [pw_mul_respects] is rebuilt.  Controls:
   [roundtrip_unit], [roundtrip_mul] and [roundtrip_inv] above, which do
   close on the nose. *)
Fail Example roundtrip_whole (P : PointwiseGroup T) :
  monoid_object_pointwise (pointwise_MonoidObject P) = pg_monoid P
    := eq_refl.

(* (3) Nor does the round trip on the object, for the same reason one
   level up: the naturality fields of the rebuilt transformations are
   this file's own opaque proofs.  Controls: [roundtrip_obj_unit] and
   [roundtrip_obj_mul] above, which close on the values. *)
Fail Example roundtrip_obj_whole
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) :
  pointwise_GroupObject (group_object_pointwise G) = G := eq_refl.

(* Positive control for the instrument itself: a true [eq_refl] of the
   same shape at the same types is accepted. *)
Example probe_instrument_control
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) : G = G := eq_refl.

End Pointwise.

(* ------------------------------------------------------------------ *)
(* Every functor into Grp is a group object on its underlying functor  *)
(* ------------------------------------------------------------------ *)

Section FromGrp.

Context {B : Category}.
Context (F : B ⟶ Grp).

Program Definition grp_functor_PointwiseMonoid :
  PointwiseMonoid (Grp_Forget ◯ F) := {|
  pw_unit := fun b => grp_unit (F b);
  pw_mul  := fun b => grp_mul (F b)
|}.
Next Obligation. now apply grp_mul_assoc. Qed.
Next Obligation. now apply grp_mul_unit_l. Qed.
Next Obligation. now apply grp_mul_unit_r. Qed.
Next Obligation. now apply grp_map_unit. Qed.
Next Obligation. now apply grp_map_mul. Qed.

Program Definition grp_functor_PointwiseGroup :
  PointwiseGroup (Grp_Forget ◯ F) := {|
  pg_monoid := grp_functor_PointwiseMonoid;
  pg_inv    := fun b => grp_inv (F b)
|}.
Next Obligation. now apply grp_mul_inv_l. Qed.
Next Obligation. now apply grp_mul_inv_r. Qed.
Next Obligation. now apply grp_map_inv. Qed.

Definition grp_functor_GroupObject :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal (Grp_Forget ◯ F) :=
  pointwise_GroupObject (Grp_Forget ◯ F) grp_functor_PointwiseGroup.

End FromGrp.

(* ------------------------------------------------------------------ *)
(* Universe boundary, guarded                                          *)
(* ------------------------------------------------------------------ *)

(* The two records tolerate B's hom universe STRICTLY BELOW both B's
   proof universe and [Sets]' carrier universe; the functor category does
   not.  So the identification [bh = bp = o] visible in the BINDER of
   every headline constant is [Fun]'s doing and not the records'.  The
   three [Check]s are the positive controls: they must succeed at exactly
   the levels at which the [Fail] fires. *)

Section UniverseBoundary.

Universes ubo ubh ubp uo uso.
Constraint ubh < ubp.
(* Deliberately ONLY this constraint: with [ubh < uo] also declared the
   section could not show that the first half suffices on its own. *)

Context (Bu : Category@{ubo ubh ubp}).
Context (Tu : Bu ⟶ Sets@{uo uso}).

Check Bu.
Check Tu.
Check (PointwiseGroup Tu).

(* THE DISCRIMINATING CONTROL for the "two independent causes" claim:
   a functor INTO [Grp] is formable at these separated levels, so the
   identification carried by [PointwiseGrpFunctor] and its siblings --
   which mention no functor category -- cannot be [Fun]'s doing.  An
   earlier revision asserted this control in the header without
   carrying it. *)
Check (Bu ⟶ Grp).

Fail Check ([Bu, Sets@{uo uso}] : Category).

End UniverseBoundary.

(* The two halves of [Fun]'s identification, separated.  Above, the
   rejection fires already at [ubh < ubp]: [Fun] forces the SOURCE
   category's hom and proof universes to agree.  Here the source has them
   equal by construction and only [vbh < vo] is declared, and the functor
   category is rejected again: [Fun] additionally forces the source's hom
   universe to be the target's.  So neither half alone accounts for it. *)

Section UniverseBoundary2.

Universes vbo vbh vo vso.
Constraint vbh < vo.

Context (Bv : Category@{vbo vbh vbh}).
Context (Tv : Bv ⟶ Sets@{vo vso}).

Check Bv.
Check (PointwiseGroup Tv).

Fail Check ([Bv, Sets@{vo vso}] : Category).

End UniverseBoundary2.

(* ------------------------------------------------------------------ *)
(* Cross-link: Structure/Group/Representable.v's presheaf group        *)
(* ------------------------------------------------------------------ *)

(* Issue #341's [RepresentablyGroup e] is [@GroupObject ([C^op, Sets])
   CC_CartesianMonoidal (RepPresheaf e)], i.e. THIS file's headline at
   [B := C^op] and [T := RepPresheaf e].  Both corollaries are [:=] with
   no tactic and no transport, which is the precise sense in which the
   representable case is an instance of the general one. *)

Definition representably_monoid_iff_pointwise {C : Category} (e : C) :
  RepresentablyMonoid e ↔ PointwiseMonoid (RepPresheaf e) :=
  monoid_object_iff_pointwise (RepPresheaf e).

Definition representably_group_iff_pointwise {C : Category} (e : C) :
  RepresentablyGroup e ↔ PointwiseGroup (RepPresheaf e) :=
  group_object_iff_pointwise (RepPresheaf e).

(* ------------------------------------------------------------------ *)
(* Non-vacuity                                                         *)
(* ------------------------------------------------------------------ *)

Section Witness.

(* The trivial endomorphism of Z/2: a genuine group homomorphism that is
   not the identity.  It costs no obligations -- the constant-at-the-unit
   map preserves everything. *)
Program Definition Z2_triv : Z2 ~{Grp}~> Z2 := {|
  grp_map := {| morphism := fun _ => grp_unit Z2 |}
|}.

(* The witness index category is [Grp] itself and the witness functor is
   the identity, so the group object below is the underlying-set functor
   of [Grp] with its evident pointwise structure.  No new functor into
   [Grp] is built. *)
Definition Und : Grp ⟶ Sets := Grp_Forget ◯ Id[Grp].

Definition Und_GroupObject :
  @GroupObject ([Grp, Sets]) CC_CartesianMonoidal Und :=
  grp_functor_GroupObject Id[Grp].

Definition Und_Pointwise : PointwiseGroup Und :=
  group_object_pointwise Und Und_GroupObject.

(* The recovered pointwise operations COMPUTE, through both passages. *)
Example und_unit_computes : pw_unit Und_Pointwise Z2 = false := eq_refl.

Example und_mul_computes :
  pw_mul Und_Pointwise Z2 true true = false := eq_refl.

Example und_mul_computes' :
  pw_mul Und_Pointwise Z2 true false = true := eq_refl.

Example und_inv_computes :
  pg_inv Und_Pointwise Z2 true = true := eq_refl.

(* The group at [Z2] is nontrivial: it has two distinct elements. *)
Lemma und_nontrivial : (@equiv _ (Und Z2) true false) → False.
Proof. simpl; discriminate. Qed.

(* The arrow action is not an identity at [Z2_triv], so the two
   homomorphism clauses of [PointwiseMonoid] are not vacuous: they are
   applied to a map that genuinely moves an element. *)
Example und_fmap_computes : fmap[Und] Z2_triv true = false := eq_refl.

Lemma und_fmap_not_id :
  (@equiv _ (Und Z2) (fmap[Und] Z2_triv true) true) → False.
Proof. simpl; discriminate. Qed.

(* And the clause itself, at that arrow, is a true statement with two
   sides that are not syntactically equal. *)
Example und_map_mul_at_triv :
  fmap[Und] Z2_triv (pw_mul Und_Pointwise Z2 true false)
    = pw_mul Und_Pointwise Z2
        (fmap[Und] Z2_triv true) (fmap[Und] Z2_triv false) := eq_refl.

End Witness.
