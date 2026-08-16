(** * Rep_K(G): K-linear representations of a group *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Grp.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed., §II.4, printed p. 41 (PDF 51) —
              maclane:II.4:construction3
   Book:      Awodey, "Category Theory", 2nd ed., §7.1, printed p. 153 —
              awodey:7.1:construction-linear-representation
   nLab:      https://ncatlab.org/nlab/show/representation
   nLab:      https://ncatlab.org/nlab/show/group+representation
   Wikipedia: https://en.wikipedia.org/wiki/Group_representation

   Mac Lane's third construction in §II.4: for a commutative ring K and
   a group G, a K-linear representation of G is a K-module V together
   with a homomorphism from G into the group of automorphisms of V, an
   intertwiner between two such is a module map commuting with the two
   actions, and the resulting category is the functor category
   [B G, K-Mod].  Awodey states the same identification in §7.1 and
   immediately draws the degenerate consequence: a functor from a group
   into a poset carries every element to an identity, so there are no
   interesting representations of a group in an order.

   This file is Instance/Fun/Action.v's structural twin one door down.
   That file is Mac Lane's construction 2 — actions on SETS, the
   category [MSet M] of M-actions and equivariant maps, and the
   equivalence [MSet_Fun_equiv : [Deloop M, Sets] ≅[Cat] MSet M].  Here
   [Sets] is replaced by [RMod K] and "action by functions" by "action
   by module automorphisms"; the architecture, including how naturality
   over one object collapses to a single commuting square and how the
   functor-side round trip is rebuilt with a transparent component
   family, is that file's and is followed rather than re-invented.

     - [grp_mon]: the monoid underlying a group object, the converter
       that lets Instance/Grp.v's [GrpObject] be delooped
     - [RepObject K G]: a K-module with a homomorphism from G into the
       units of its endomorphism monoid — the issue-literal
       automorphism form
     - [rep_act], [rep_act_unit], [rep_act_mul], [rep_act_iso]: the
       action read off that homomorphism, its two laws, and each
       element acting as an isomorphism of [RMod K]
     - [monhom_of_rep] / [rep_of_monhom]: the passage between the
       automorphism-valued and the endomorphism-valued (working) forms,
       with both round trips definitional
     - [Intertwiner], [Rep K G]: module maps commuting with the actions,
       and the category they form
     - [Rep_Fun_equiv]: the headline —
       [[Deloop (grp_mon G), RMod K] ≅[Cat] Rep K G]
     - [thin_functor_endo_trivial], [thin_group_functor_trivial],
       [proset_group_functor_trivial]: Awodey's degeneracy
     - [trivial_rep], [sign_rep]: the two witnesses

   Design:

   1. THE TWO [GrpObject] RECORDS.  The tree carries two records of that
      name.  Construction/Deloop.v's extends [MonObject] by a two-sided
      inverse and is what [Deloop] and Structure/Groupoid.v's [MonHom]
      machinery consume; Instance/Grp.v's is the object of the official
      category [Grp] (carrier setoid, unit, multiplication, inversion,
      with only the LEFT unit and inverse laws as fields), and is what
      Instance/Matr/GL.v's [UnitsOf] produces.  Since the issue-literal
      statement of a representation names the group of automorphisms —
      i.e. [UnitsOf] — the primitive here is Instance/Grp.v's record,
      imported LAST so that the bare names [GrpObject], [grp_inv],
      [grp_mul], [grp_unit] all refer to it.  [grp_mon] is the one-line
      converter into [MonObject]: carrier, unit and multiplication
      unchanged, associativity flipped (Deloop's [mon_op_assoc] is
      stated in [comp_assoc]'s orientation) and the right unit law taken
      from Instance/Grp.v's derived [grp_mul_unit_r].  Delooping is
      therefore always [Deloop (grp_mon G)].

   2. THE AUTOMORPHISM FORM IS PRIMITIVE, AND THE PASSAGE COSTS
      NOTHING.  [RepObject] carries
      [rep_hom : GrpHom G (UnitsOf (hom_monoid (RMod K) rep_mod))] —
      literally "a homomorphism from G into the automorphisms of V".
      The working form the [Deloop] spine consumes is
      [MonHom (grp_mon G) (hom_monoid (RMod K) V)], an action by bare
      endomorphisms, and the two are interchangeable:

        - [monhom_of_rep] forgets the invertibility witness, its
          [mon_map] being [rep_act] — the FIRST projection of the unit
          datum, so no proof is discarded, only ignored;
        - [rep_of_monhom] supplies it, the inverse of the action of g
          being the action of g⁻¹, by the group laws pushed through the
          homomorphism (this is the automatic-invertibility pattern of
          Construction/Deloop/Functors.v's
          [perm_rep_acts_by_bijections], reached here through
          [UnitsOf] rather than through [fobj_iso]).

      BOTH ROUND TRIPS ARE DEFINITIONAL: [monhom_rep_round] and
      [rep_monhom_round] are [reflexivity], because [UnitsOf]'s
      hom-setoid compares unit data by the underlying element and
      [rep_act] is exactly that projection.  So the choice of primitive
      is one of statement fidelity only, and the equivalence below is
      proved in whichever form is convenient at each step.

   3. NOTHING BELOW USES COMMUTATIVITY OF K.  Mac Lane says commutative
      ring; the parameter here is [RingObject] — defined in
      Theory/Algebra/Rig.v and the object type of Instance/Rng.v's
      [Rng] — because no step consumes commutativity (structurally so:
      the record has no commutativity field) — [RMod K] is a category
      for any
      ring, and every argument is about the endomorphism monoid of one
      of its objects.  Specializing to a commutative K (or to a field,
      once issue #244 supplies one) is instantiation, not a change of
      statement.

   4. THE DEGENERACY IS PROVED IN ITS GENERAL FORM.  Awodey's remark is
      about groups and posets, but neither hypothesis is used: in a thin
      category ANY functor carries ANY endomorphism to an identity
      ([thin_functor_endo_trivial]), since [fmap] of it is parallel to
      [id].  The group statement and the [Proset] instantiation are
      the SAME statement at two instantiations, not further theorems —
      and at [Proset] the conclusion degenerates outright: [Proset]'s
      hom-≈ is the trivial relation ([proset_thin]'s proof is [exact
      I]), so [proset_group_functor_trivial]'s conclusion is inhabited
      by [I] and carries typing content only (the Instance/Proset/
      Limit.v degeneration, disclosed there too).  The instantiation
      is stated at [Proset], not at posets: Instance/Poset.v's [Poset]
      is DEFINED as [Proset P] and discards antisymmetry (the erratum
      recorded in Instance/Proset/Galois.v) — and the coverage is not
      thereby narrowed, since Instance/Pos.v's genuine category of
      posets enters through [PosetAsCategory P := Proset
      (pos_preorder P)], so the corollary covers real posets as well;
      [proset_thin] is the honest donor and is cited, not re-proved.

   5. WHAT IS NOT BUILT.  No category of representations over varying
      K or varying G, and no character theory.  The matrix-valued
      cousin of [RepObject] is Construction/Deloop/Functors.v's
      [MatrixRep] (a dimension plus a homomorphism into the matrix
      monoid, the same spine at [Matr R]); the finite-dimensional
      vector-space reading belongs with issue #237's [FdVect] and is
      deferred to it.  Instance/Fun/Action.v's [MSet_hom_iso] — the
      transformation setoid presented literally as the setoid of
      equivariant maps — has no counterpart here; the hom-level content
      is already carried by [Rep_Fun_equiv]. *)

(** ** From a group object to a monoid object *)

(* Instance/Grp.v's [GrpObject] read as a [MonObject], so that it can be
   delooped.  Carrier, unit and multiplication are the originals; only
   two law fields need any work, and neither is a proof:
   [mon_op_assoc] is stated in the mirrored orientation (Deloop.v
   matches [comp_assoc], Instance/Grp.v matches the usual left-to-right
   reading), and [mon_op_unit_r] is Instance/Grp.v's derived
   [grp_mul_unit_r] rather than a field. *)
Program Definition grp_mon (G : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid G;
  mon_unit   := grp_unit G;
  mon_op     := grp_mul G;

  mon_op_respects := grp_mul_respects G
|}.
Next Obligation.
  intros G a b c; symmetry; apply grp_mul_assoc.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_r.
Qed.

(* The three data fields are the originals, on the nose. *)
Example grp_mon_carrier (G : GrpObject) :
  carrier (grp_mon G) = carrier (grp_setoid G) := eq_refl.

Example grp_mon_unit (G : GrpObject) :
  @mon_unit (grp_mon G) = grp_unit G := eq_refl.

Example grp_mon_op (G : GrpObject) :
  @mon_op (grp_mon G) = grp_mul G := eq_refl.

(* [UnitsOf]'s hom-setoid compares unit data by the underlying element
   alone, so an equation between units is an equation between the
   elements they are built on — the invertibility witnesses are free to
   differ.  Stating that once, as a conversion, keeps every obligation
   below at the level of morphisms of [RMod K]; without it a bare
   [reflexivity] would try to unify the witnesses too. *)
Lemma units_equiv {M : MonObject}
  (x y : carrier (grp_setoid (UnitsOf M))) : `1 x ≈ `1 y → x ≈ y.
Proof. intro H; exact H. Qed.

(** ** Representations *)

(* A K-linear representation of G: a K-module together with a
   homomorphism from G into the group of automorphisms of that module.
   The automorphism group is Instance/Matr/GL.v's [UnitsOf] taken at
   Construction/Deloop.v's endomorphism monoid [hom_monoid (RMod K) V]
   — the same composite that reads GL_n off the matrix monoid there. *)
Record RepObject (K : RingObject) (G : GrpObject) := {
  rep_mod :> RModObject K;

  rep_hom : GrpHom G (UnitsOf (hom_monoid (RMod K) rep_mod))
}.

Arguments rep_mod {K G} _.
Arguments rep_hom {K G} _.

(* The action of a group element, as an endomorphism of the module: the
   underlying element of the unit datum.  Every law below is the
   corresponding homomorphism law read through this projection, which is
   why each of them holds by [exact] with no rewriting. *)
Definition rep_act {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g : carrier G) : rep_mod V ~{RMod K}~> rep_mod V :=
  `1 (grp_map (rep_hom V) g).

Lemma rep_act_respects {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Proper (equiv ==> equiv) (rep_act V).
Proof.
  intros g h Hgh.
  exact (proper_morphism (grp_map (rep_hom V)) g h Hgh).
Qed.

Lemma rep_act_unit {K : RingObject} {G : GrpObject} (V : RepObject K G) :
  rep_act V (grp_unit G) ≈ id.
Proof. exact (grp_map_unit (rep_hom V)). Qed.

Lemma rep_act_mul {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g h : carrier G) :
  rep_act V (grp_mul G g h) ≈ rep_act V g ∘ rep_act V h.
Proof. exact (grp_map_mul (rep_hom V) g h). Qed.

(* Each element acts invertibly, the inverse being the action of the
   inverse element.  This is a consequence of the two laws above, not a
   reading of the unit datum's own witness: the witness stored in
   [rep_hom] is some two-sided inverse, and what is proved here is that
   [rep_act V (grp_inv G g)] is one. *)
Program Definition rep_act_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_mod V ≅[RMod K] rep_mod V := {|
  to   := rep_act V g;
  from := rep_act V (grp_inv G g)
|}.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_r.
  - apply rep_act_unit.
Qed.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_l.
  - apply rep_act_unit.
Qed.

(** ** The two forms of the action datum *)

(* Forgetting the invertibility witness: the working form the [Deloop]
   spine consumes.  Its [mon_map] IS [rep_act]. *)
Program Definition monhom_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  MonHom (grp_mon G) (hom_monoid (RMod K) (rep_mod V)) := {|
  mon_map := rep_act V
|}.
Next Obligation. intros K G V; exact (rep_act_respects V). Qed.
Next Obligation. intros K G V; exact (rep_act_unit V). Qed.
Next Obligation. intros K G V a b; exact (rep_act_mul V a b). Qed.

(* Supplying it back: over a GROUP the invertibility is automatic, the
   inverse of the action of g being the action of g⁻¹.  The two
   obligations are the group's own inverse laws pushed through the
   homomorphism. *)
Program Definition rep_of_monhom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  GrpHom G (UnitsOf (hom_monoid (RMod K) V)) := {|
  grp_map := {| morphism := fun g : carrier G =>
    (mon_map h g; (mon_map h (grp_inv G g); (_, _))) |}
|}.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h g (grp_inv G g)).
    apply (mon_map_respects h).
    apply grp_mul_inv_r.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h (grp_inv G g) g).
    apply (mon_map_respects h).
    apply grp_mul_inv_l.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g g' Hgg'.
  exact (mon_map_respects h g g' Hgg').
Qed.
Next Obligation.
  intros K G V h; exact (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h a b; exact (mon_map_op h a b).
Qed.

(* The packaged representation. *)
Definition RepOfMonHom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  RepObject K G :=
  {| rep_mod := V; rep_hom := rep_of_monhom V h |}.

(* Both round trips are DEFINITIONAL.  Going out and back through the
   invertibility witness recovers the same map because [UnitsOf]'s
   hom-setoid compares unit data by the underlying element, which is
   precisely what [rep_act] projects. *)
Lemma monhom_rep_round {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V))
  (g : carrier G) :
  mon_map (monhom_of_rep (RepOfMonHom V h)) g ≈ mon_map h g.
Proof. reflexivity. Qed.

Lemma rep_monhom_round {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_act (RepOfMonHom (rep_mod V) (monhom_of_rep V)) g ≈ rep_act V g.
Proof. reflexivity. Qed.

(* Stated on the unit datum itself, which is the same equation: the
   round trip is written through [rep_act] because [UnitsOf]'s
   hom-setoid equivalence is that projection, and a bare [reflexivity]
   at the sigma type would have to unify the invertibility witnesses,
   which the two forms are under no obligation to share. *)
Lemma rep_monhom_round_elt {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  `1 (grp_map (rep_of_monhom (rep_mod V) (monhom_of_rep V)) g)
    ≈ `1 (grp_map (rep_hom V) g).
Proof. reflexivity. Qed.

(** ** Intertwiners *)

(* A morphism of representations: a module map commuting with the two
   actions.  The composition is spelled at [RMod K], the actions being
   endomorphisms of the underlying modules. *)
Record Intertwiner {K : RingObject} {G : GrpObject}
       (V W : RepObject K G) := {
  itw_map :> rep_mod V ~{RMod K}~> rep_mod W;

  itw_equivar : ∀ g : carrier G,
    itw_map ∘ rep_act V g ≈ rep_act W g ∘ itw_map
}.

Arguments itw_map {K G V W} _.
Arguments itw_equivar {K G V W} _ _.

(** ** The category of representations *)

Program Definition Rep (K : RingObject) (G : GrpObject) : Category := {|
  obj := RepObject K G;
  hom := fun V W => Intertwiner V W;
  homset := fun V W =>
    {| equiv := fun f g => itw_map f ≈ itw_map g |};
  id := fun V => {| itw_map := id |};
  compose := fun U V W f g => {| itw_map := itw_map f ∘ itw_map g |}
|}.
Next Obligation.
  intros K G V W; constructor.
  - intros f; reflexivity.
  - intros f g Hfg; symmetry; exact Hfg.
  - intros f g h H1 H2; transitivity (itw_map g); assumption.
Qed.
Next Obligation.
  intros K G V g.
  rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G U V W f g gr.
  rewrite <- comp_assoc.
  rewrite (itw_equivar g gr).
  rewrite comp_assoc.
  rewrite (itw_equivar f gr).
  rewrite <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  intros K G U V W f f' Hf g g' Hg.
  exact (@compose_respects (RMod K) (rep_mod U) (rep_mod V) (rep_mod W)
           _ _ Hf _ _ Hg).
Qed.
Next Obligation. intros K G V W f; exact (id_left (itw_map f)). Qed.
Next Obligation. intros K G V W f; exact (id_right (itw_map f)). Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc (itw_map f) (itw_map g) (itw_map h)).
Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc_sym (itw_map f) (itw_map g) (itw_map h)).
Qed.

(** ** The comparison functors *)

(* A functor out of the delooping IS a representation: its value at the
   single object is the module, and its action on arrows is the spine
   homomorphism, made invertible by [rep_of_monhom]. *)
Definition rep_of_functor {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) : RepObject K G :=
  RepOfMonHom (G := G) (F ttt : RModObject K)
    (hom_monoid_of_functor (C := RMod K) F).

(* ...and conversely, through Construction/Deloop/Functors.v's spine. *)
Definition functor_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Deloop (grp_mon G) ⟶ RMod K :=
  functor_of_hom_monoid (C := RMod K) (rep_mod V) (monhom_of_rep V).

(* The action of the representation read off a functor is that functor's
   [fmap], definitionally — the fact every obligation below leans on. *)
Lemma rep_of_functor_act {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) (g : carrier G) :
  rep_act (rep_of_functor F) g ≈ fmap[F] g.
Proof. reflexivity. Qed.

Lemma functor_of_rep_fmap {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  @fmap _ _ (functor_of_rep V) ttt ttt g ≈ rep_act V g.
Proof. reflexivity. Qed.

(* Reading a representation and its intertwiners off a functor: the
   morphism action takes a transformation to its single component,
   whose naturality at g IS the intertwining square. *)
Program Definition Rep_to (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ⟶ Rep K G := {|
  fobj := fun F => rep_of_functor F;
  fmap := fun F F' η => {| itw_map := transform[η] ttt |}
|}.
Next Obligation.
  intros K G F F' η g.
  exact (@naturality_sym _ _ F F' η ttt ttt g).
Qed.
Next Obligation.
  intros K G F F' η θ Hηθ; exact (Hηθ ttt).
Qed.
Next Obligation.
  intros K G F; exact (@fmap_id _ _ F ttt).
Qed.
Next Obligation.
  intros K G F F' F'' η θ; simpl; reflexivity.
Qed.

(* Materializing an intertwiner as the constant transformation family;
   naturality is the intertwining square. *)
Program Definition Rep_from (K : RingObject) (G : GrpObject) :
  Rep K G ⟶ [Deloop (grp_mon G), RMod K] := {|
  fobj := fun V => functor_of_rep V;
  fmap := fun V W h => {| transform := fun _ => itw_map h |}
|}.
Next Obligation.
  intros K G V W h [] [] g.
  symmetry; exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h [] [] g.
  exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h h' Hh []; exact Hh.
Qed.
Next Obligation.
  intros K G V [].
  symmetry; exact (rep_act_unit V).
Qed.
Next Obligation.
  intros K G U V W f g []; simpl; reflexivity.
Qed.

(** ** The equivalence *)

(* The representation-side round trip: the two representations have the
   same module and the same action, so the identity module map is an
   intertwiner in both directions. *)
Program Definition Rep_action_round_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  @Isomorphism (Rep K G) (rep_of_functor (functor_of_rep V)) V := {|
  to   := {| itw_map := id |};
  from := {| itw_map := id |}
|}.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.

(* The functor-side round trip, with a transparent component family: the
   equivalence below has to compute with the components, so the
   in-tree opaque [functor_round] cannot serve (Instance/Fun/Action.v's
   [MSet_round_iso] makes the same move). *)
Program Definition Rep_round_iso {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) :
  @Isomorphism ([Deloop (grp_mon G), RMod K])
    (functor_of_rep (rep_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return
      (functor_of_rep (rep_of_functor F) x ~{RMod K}~> F x)
    with ttt => id end |};
  from := {| transform := fun x =>
    match x return
      (F x ~{RMod K}~> functor_of_rep (rep_of_functor F) x)
    with ttt => id end |}
|}.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry; apply fmap_id.
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry.
    exact (@fmap_id _ _ (functor_of_rep (rep_of_functor F)) ttt).
Qed.

(* Mac Lane's construction 3 at category strength: the category of
   K-linear representations of G IS the functor category out of the
   delooping of G, an isomorphism in Cat and hence — Cat's hom-setoid
   being natural isomorphism (Instance/Cat.v) — an EQUIVALENCE of
   categories.  The orientation is Instance/Fun/Action.v's, with the
   functor category on the left. *)
Program Definition Rep_Fun_equiv (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ≅[Cat] Rep K G := {|
  to   := Rep_to K G;
  from := Rep_from K G
|}.
Next Obligation.
  (* Rep_to ◯ Rep_from ≈ Id, through the representation-side round trip *)
  intros K G.
  exists (fun V => Rep_action_round_iso V).
  intros V W h a; simpl; reflexivity.
Qed.
Next Obligation.
  (* Rep_from ◯ Rep_to ≈ Id, through the transparent functor-side one *)
  intros K G.
  exists (fun F => Rep_round_iso F).
  intros F F' η [] a; simpl; reflexivity.
Qed.

(** ** Awodey's degeneracy *)

(* In a thin category any functor carries any ENDOmorphism to an
   identity: its image is parallel to [id], and thinness identifies
   parallel morphisms.  Neither the group hypothesis nor the one-object
   hypothesis plays any part. *)
Lemma thin_functor_endo_trivial {B C : Category} (T : Thin C)
  (F : B ⟶ C) {x : B} (f : x ~> x) : fmap[F] f ≈ id.
Proof. exact (T (F x) (F x) (fmap[F] f) id). Qed.

(* Awodey's statement: a representation of a group in a thin category
   is trivial — every group element acts as the identity. *)
Theorem thin_group_functor_trivial {G : GrpObject} {C : Category}
  (T : Thin C) (F : Deloop (grp_mon G) ⟶ C) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_functor_endo_trivial T F g). Qed.

(* Instantiated at a preorder.  The statement is about [Proset], not
   about posets: Instance/Poset.v's [Poset] is DEFINED as [Proset P] and
   drops antisymmetry, so nothing here would be strengthened by naming
   it.  [proset_thin] is Instance/Proset/Order.v's, cited. *)
Corollary proset_group_functor_trivial {G : GrpObject} {A : Type}
  {R : relation A} (P : RelationClasses.PreOrder R)
  (F : Deloop (grp_mon G) ⟶ Proset P) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_group_functor_trivial (proset_thin P) F g). Qed.

(** ** Witnesses *)

(* Double negation in an abelian group, the one fact Instance/Ab.v
   leaves unstated among its negation lemmas. *)
Lemma ab_neg_neg (A : AbObject) (a : carrier (cmon_setoid A)) :
  ab_neg A (ab_neg A a) ≈ a.
Proof. symmetry; apply ab_neg_unique; apply ab_neg_right. Qed.

(* The trivial representation of any group on any module: every element
   acts as the identity.  Available at every K and G, so [RepObject] is
   never empty. *)
Program Definition rep_id_unit {K : RingObject} (V : RModObject K) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V))) :=
  (id; (id; (_, _))).
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.

Lemma rep_id_unit_respects {K : RingObject} {G : GrpObject}
  (V : RModObject K) :
  Proper (equiv ==> equiv) (fun _ : carrier G => rep_id_unit V).
Proof. intros g g' Hgg'; apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_is_unit {K : RingObject} (V : RModObject K) :
  rep_id_unit V ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_mul {K : RingObject} (V : RModObject K) :
  rep_id_unit V
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V))
        (rep_id_unit V) (rep_id_unit V).
Proof.
  apply units_equiv; symmetry; exact (id_left (@id (RMod K) V)).
Qed.

(* Spelled as a term for the reason given at [rmod_neg_hom]: the
   obligation numbering is not the field numbering, and every field
   here is already a lemma. *)
Definition trivial_rep {K : RingObject} {G : GrpObject}
  (V : RModObject K) : RepObject K G :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := fun _ : carrier G => rep_id_unit V
                      ; proper_morphism := rep_id_unit_respects V |}
        ; grp_map_unit := rep_id_unit_is_unit V
        ; grp_map_mul := fun a b => rep_id_unit_mul V |} |}.

(* Negation is a module endomorphism: additive because negation
   distributes over addition in an abelian group, K-linear because
   r·(−m) ≈ −(r·m) ([rm_smul_neg_r]). *)
Lemma ab_neg_hom_smul {K : RingObject} (V : RModObject K)
  (r : carrier (rig_setoid (ring_rig K)))
  (m : carrier (cmon_setoid V)) :
  ab_neg V (rm_smul V r m) ≈ rm_smul V r (ab_neg V m).
Proof. symmetry; apply rm_smul_neg_r. Qed.

(* Written as an explicit record literal rather than through [Program]:
   every field is an existing lemma, so there is nothing to defer, and
   Instance/Ab.v's exported [ab_neg_respects] instance would otherwise
   silently discharge one hole and shift the obligation numbering. *)
Definition rmod_neg_hom {K : RingObject} (V : RModObject K) :
  V ~{RMod K}~> V :=
  {| rm_hom :=
       {| cmon_map := {| morphism        := ab_neg V
                       ; proper_morphism := ab_neg_respects V |}
        ; cmon_map_zero := ab_neg_zero V
        ; cmon_map_plus := ab_neg_plus V |}
   ; rm_map_smul := ab_neg_hom_smul V |}.

(* The sign action of Z/2 on any module: the non-unit element acts by
   negation, which is its own inverse. *)
Definition sign_act {K : RingObject} (V : RModObject K) (b : bool) :
  V ~{RMod K}~> V :=
  if b then rmod_neg_hom V else id.

Lemma sign_act_involutive {K : RingObject} (V : RModObject K)
  (b : bool) : sign_act V b ∘ sign_act V b ≈ id.
Proof.
  destruct b.
  - intro a; simpl; apply ab_neg_neg.
  - exact (id_left (@id (RMod K) V)).
Qed.

(* The sign representation.  Instance/Grp.v's [Z2] is (bool, xor,
   false), so [grp_mul Z2] is [xorb] and [grp_unit Z2] is [false]; the
   multiplication law is the four-case check that xor of the signs is
   the composite of the two actions. *)
Definition sign_unit {K : RingObject} (V : RModObject K)
  (b : carrier Z2) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V))) :=
  (sign_act V b;
   (sign_act V b;
    (sign_act_involutive V b, sign_act_involutive V b))).

Lemma sign_unit_respects {K : RingObject} (V : RModObject K) :
  Proper (equiv ==> equiv) (sign_unit V).
Proof.
  intros b b' Hbb'; simpl in Hbb'; subst; reflexivity.
Qed.

Lemma sign_unit_is_unit {K : RingObject} (V : RModObject K) :
  sign_unit V (grp_unit Z2)
    ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma sign_unit_mul {K : RingObject} (V : RModObject K)
  (a b : carrier Z2) :
  sign_unit V (grp_mul Z2 a b)
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V))
        (sign_unit V a) (sign_unit V b).
Proof.
  apply units_equiv; symmetry.
  destruct a, b.
  - exact (sign_act_involutive V true).
  - exact (id_right (rmod_neg_hom V)).
  - exact (id_left (rmod_neg_hom V)).
  - exact (id_left (@id (RMod K) V)).
Qed.

Definition sign_rep {K : RingObject} (V : RModObject K) :
  RepObject K Z2 :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := sign_unit V
                      ; proper_morphism := sign_unit_respects V |}
        ; grp_map_unit := sign_unit_is_unit V
        ; grp_map_mul := sign_unit_mul V |} |}.

(* Non-vacuity, over the integers as a module over themselves: the
   non-unit element of Z/2 acts by an endomorphism that genuinely moves
   a point, so the sign representation is not the trivial one.  (The
   [≈] of [Int_Ring]'s carrier is Leibniz equality on Z, whence
   [discriminate].) *)
Lemma sign_rep_moves_one :
  cmon_map (rm_hom (rep_act (sign_rep Int_RMod) true)) 1%Z ≈ (-1)%Z.
Proof. reflexivity. Qed.

Lemma sign_rep_nontrivial :
  rep_act (sign_rep Int_RMod) true ≈ rep_act (sign_rep Int_RMod) false
    → False.
Proof.
  intro H.
  pose proof (H 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(* The identity module map is not an intertwiner between the two
   witnesses: their actions differ pointwise. *)
Lemma sign_rep_not_trivial_rep :
  (∀ g : carrier Z2,
     rep_act (sign_rep Int_RMod) g ≈ rep_act (trivial_rep Int_RMod) g)
    → False.
Proof.
  intro H.
  pose proof (H true 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(* And the two really are DIFFERENT REPRESENTATIONS in the sense a
   category theorist reads: not merely unequal, but non-isomorphic
   objects of [Rep Int_Ring Z2].  Any intertwiner from the sign
   representation to the trivial one is forced to vanish (equivariance
   at [true] says f(−n) ≈ f(n), additivity says f(−n) ≈ −f(n), so
   2·f(n) = 0 over ℤ), and a vanishing map cannot be half of an
   isomorphism — its round trip at 1 would read 0 = 1. *)
Lemma sign_not_iso_trivial :
  @Isomorphism (Rep Int_Ring Z2) (sign_rep Int_RMod) (trivial_rep Int_RMod)
    → False.
Proof.
  intro iso.
  assert (Hzero : ∀ n : Z, cmon_map (rm_hom (itw_map (to iso))) n = 0%Z).
  { intro n.
    assert (Hf : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = cmon_map (rm_hom (itw_map (to iso))) n)
      by exact (itw_equivar (to iso) true n).
    assert (Hn : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = Z.opp (cmon_map (rm_hom (itw_map (to iso))) n))
      by exact (ab_map_neg (rm_hom (itw_map (to iso))) n).
    lia. }
  assert (H1 : cmon_map (rm_hom (itw_map (to iso)))
                 (cmon_map (rm_hom (itw_map (from iso))) 1%Z) = 1%Z)
    by exact (iso_to_from iso 1%Z).
  rewrite (Hzero _) in H1.
  discriminate H1.
Qed.
