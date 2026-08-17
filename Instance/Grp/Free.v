Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.

(* [Instance/Grp.v] is imported LAST on purpose.  [Construction/Deloop.v]
   also declares a record called [GrpObject] — layered on [MonObject], with
   both unit laws and both inverse laws as fields — and the two names would
   otherwise collide.  With this order, the unqualified [GrpObject],
   [grp_unit], [grp_mul] and [grp_inv] below are always [Instance/Grp.v]'s,
   which is the record [Grp] is the category of and hence the one the
   adjunction must be stated over. *)
Require Import Category.Instance.Grp.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(* The global obligation tactic is [cat_simpl], which would run wide proof
   searches on the group obligations below and has already introduced the
   parameters by the time an obligation is opened.  Switched off here, the
   [Instance/Grp.v:396] idiom, so every obligation starts with an explicit
   [intros]. *)
#[local] Obligation Tactic := idtac.

(** * The free group on a set, and the free-forgetful adjunction

    nLab:      https://ncatlab.org/nlab/show/free+group
    nLab:      https://ncatlab.org/nlab/show/free+groupoid
    nLab:      https://ncatlab.org/nlab/show/free+construction
    Wikipedia: https://en.wikipedia.org/wiki/Free_group
    Wikipedia: https://en.wikipedia.org/wiki/Nielsen%E2%80%93Schreier_theorem
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §II.7, printed p. 51 (Exercise 3, whose closing clause is
          the free group as the one-object free groupoid)
    Book: Riehl, Category Theory in Context, §4.2, printed p. 139 (free ⊣
          forgetful; the unit is the insertion of generators and the counit
          evaluates a word)
    Book: Awodey, Category Theory, §1.7 (the universal mapping property of a
          free structure, worked for monoids) and §9.1 (the adjunction)

    THE POINT OF THE EXERCISE.  A free group on a set S is a group F(S) with
    a map S → |F(S)| through which every map from S into the underlying set
    of a group factors uniquely by a homomorphism.  Nielsen (1921) and
    Schreier (1927) put free groups at the centre of combinatorial group
    theory; the categorical reading — that F is left adjoint to the
    forgetful functor — is the motivating example of an adjunction in
    essentially every textbook, and is the reason "free" is a technical word
    at all.  Mac Lane's §II.7 exercise reaches it the economical way, via
    groupoids: build the free groupoid on a graph, then read the free group
    off the one-node case.  That is what this file does.

    HOW IT IS BUILT.  [Construction/Free/Groupoid.v] supplies the free
    groupoid; this file instantiates it at a quiver with ONE node whose
    edge set is the generating setoid, and reads the endomorphism group of
    that node.  Every group law is then a CATEGORY law by projection —
    associativity is [comp_assoc_sym], the unit law is [id_left], the
    inverse law is [fginv_left] — exactly as [hom_monoid]
    (Construction/Deloop.v) reads a monoid off an endomorphism hom-set, and
    three [eq_refl] Examples below record that the underlying monoid IS
    [hom_monoid] of the free groupoid on all three data fields.

    THE FREE GROUP ON A SETOID, NOT ON A TYPE.  [Grp_Forget] lands in
    [Sets], whose objects are setoids, so the left adjoint is a functor
    [Sets ⟶ Grp] and the generators carry their own [≈], which the word
    relation must respect.  This is the one place where the free-monoid
    precedent does not transfer: in [Instance/Coq/Monoid/Free.v] the
    generators are a bare [Type] and [list X] under Leibniz [=] is already
    free, with no quotient at all.  Here the one-node quiver cannot be
    [Construction/Free/Quiver/Presented.v]'s [OneNodeQuiver], which puts
    Leibniz [=] on its edges; [PointQuiver] is built by hand with the
    generating setoid's own equivalence as the edge setoid, and
    respectfulness of the insertion is then not a new obligation but the
    [fedgemap_respects] field of [FreeGroupoidUnit].

    TWO RECORDS NAMED [GrpObject].  Construction/Deloop.v's is layered on
    [MonObject] and carries both unit laws and both inverse laws as fields;
    Instance/Grp.v's is flat and carries only the left-handed ones, the
    right-handed laws and respectfulness of inversion being derived.  [Grp]
    is the category of the LATTER, so that is the record this adjunction
    must be stated over, and it is why the import order at the top of this
    file is deliberate.  The only bridge between them in tree is
    [Instance/Rep.v]'s [grp_mon], which reads Instance/Grp.v's record as a
    [MonObject]; it drops the inverse, so it does NOT supply
    [Deloop_IsGroupoid]'s hypothesis (that lemma is stated over Deloop's
    [GrpObject]), and its file in any case sits on top of the module and
    matrix stack, which nothing here needs.  [grp_deloop_monoid] and
    [grp_deloop_IsGroupoid] therefore rebuild the two-line bridge directly
    over Instance/Grp.v's record.  Routing the free GROUP through
    [vertex_group] (Structure/Groupoid.v) would have produced a
    Deloop-flavoured record and so would have landed in the wrong category;
    the group is therefore assembled directly from the word quotient.

    MULTIPLICATION IS COMPOSITION, hence right to left: the product of the
    one-letter words a and b is the word "b then a".  That is the house
    convention ([hom_monoid]'s [mon_op] is [fun f g => f ∘ g]) and it is
    what lets [fmap_comp] discharge [grp_map_mul] with no massaging;
    [free_group_mul_is_compose] pins it by [eq_refl].

    STRENGTHS, MEASURED.

      - [eq_refl]: the free functor's object part is the word group
        ([FreeGrp_obj]); the universal arrow is the insertion of generators
        ([free_group_arrow_is_insert]); the UNIT is the one-letter word
        ([free_group_unit_is_insert], [free_group_unit_is_generator]);
        multiplication is composition, the group unit is the identity arrow,
        inversion is word reversal, and the underlying monoid is
        [hom_monoid] on all three data fields.
      - [≈] only: the COUNIT.  It is the other transpose, i.e.
        [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
        (Theory/Universal/Arrow.v) is [Qed]-opaque, so it does not compute
        and no [eq_refl] is claimed on that side.  What is proved is that it
        agrees with word evaluation up to [≈]
        ([free_group_counit_evaluates]), which is the content;
        Test/ProbeFreeGroupoid.v pins the negative side with a [Fail] probe.
      - The triangle identities are [Theory/Adjunction.v]'s derived
        [counit_fmap_unit] and [fmap_counit_unit] instantiated, and are
        named here because the issue asks for them by name.  They are
        derived and not fields, so instantiating them is a genuine check
        that the adjunction is the intended one, not a restatement.

    NON-VACUITY.  A free group on the empty or a one-element generating set
    is abelian and would demonstrate nothing.  The witness therefore has TWO
    generators and is separated by a functor into the delooping of the
    symmetric group on three letters (Structure/Groupoid.v's [S3_Grp], a
    nonabelian group already in tree):
    [free_group_two_generators_nonabelian] and
    [free_group_two_generators_distinct].  Because the delooping of a group
    is a groupoid, the free-GROUPOID universal property applies directly and
    no bridge between the two [GrpObject] records is needed for the witness.

    THIS IS NOT THE ONLY FREE-GROUP ADJUNCTION THE TREE SHOULD HAVE.  Issue
    #442 (maclane:V.6:construction-free-group) reaches a free-group left
    adjoint over [Grp] by the adjoint-functor-theorem route, with no word
    normal form anywhere; Mac Lane presents both routes deliberately, and
    the two are complementary rather than competing — one exhibits the
    object, the other proves it exists from completeness and a solution set.

    WHAT IS NOT DELIVERED.

      - No reduced-word normal form, hence no decision procedure for the
        word problem, no Nielsen-Schreier theorem, and no proof that
        [fg_insert] is injective for a GENERAL generating setoid.  What is
        proved is that it is injective on the two-letter witness
        ([free_group_two_generators_distinct]), by mapping into S3.  A
        general proof needs a separating family of groups, which in the
        constructive setting is essentially the normal-form theorem again.
      - No statement that [FreeGrp] is faithful, and no characterization of
        its image.
      - No free ABELIAN group, no free monoid over [Sets] (the free monoid
        in tree, [Instance/Coq/Monoid/Free.v], is over [Coq]), and no
        comparison functor between them. *)

(** ** The one-node quiver on a setoid

    [Construction/Free/Quiver/Presented.v]'s [OneNodeQuiver] uses
    [Build_Quiver_Standard_Eq], which puts Leibniz [=] on the edges.  That
    will not do here: [Grp_Forget] lands in [Sets], so the free group is the
    free group on a SETOID, and the generators carry their own [≈], which
    the word relation must respect.  Hence the quiver is built by hand, with
    the generating setoid's own equivalence as the edge setoid. *)
Definition PointQuiver (X : SetoidObject) : Quiver := {|
  nodes   := poly_unit;
  edges   := fun _ _ => carrier X;
  edgeset := fun _ _ => is_setoid X
|}.

(** ** The word group

    Mac Lane's §II.7 Ex. 3 read at one object: the free group on [X] is the
    endomorphism group of the unique node of the free groupoid on the
    one-node quiver.  Every group law below is a CATEGORY law by projection
    — associativity is [comp_assoc_sym], the unit law is [id_left], the
    inverse law is [fginv_left] — exactly as [hom_monoid]
    ([Construction/Deloop.v]) reads a monoid off an endomorphism hom-set.

    Multiplication is composition, so it runs right to left: the product of
    the one-letter words [a] and [b] is the word "b then a".  That is the
    house convention ([hom_monoid]'s [mon_op] is [fun f g => f ∘ g]) and it
    is what makes [fmap_comp] discharge [grp_map_mul] with no massaging;
    [free_group_mul_is_compose] pins it by [eq_refl]. *)

Definition FGWord (X : SetoidObject) : Type :=
  ttt ~{FreeGroupoid (PointQuiver X)}~> ttt.

Definition FreeGrpSetoid (X : SetoidObject) : SetoidObject := {|
  carrier   := FGWord X;
  is_setoid := @homset (FreeGroupoid (PointQuiver X)) ttt ttt
|}.

Definition FreeGrpObject (X : SetoidObject) : GrpObject := {|
  grp_setoid := FreeGrpSetoid X;

  grp_unit := @id (FreeGroupoid (PointQuiver X)) ttt;
  grp_mul  := fun a b => a ∘ b;
  grp_inv  := fun a => fginv a;

  grp_mul_respects := @compose_respects (FreeGroupoid (PointQuiver X))
                        ttt ttt ttt;

  grp_mul_assoc := @comp_assoc_sym (FreeGroupoid (PointQuiver X))
                     ttt ttt ttt ttt;
  grp_mul_unit_l := @id_left (FreeGroupoid (PointQuiver X)) ttt ttt;
  grp_mul_inv_l  := fun a => fginv_left a
|}.

(** The multiplication IS composition and the unit IS the identity arrow,
    definitionally. *)
Example free_group_mul_is_compose (X : SetoidObject) (a b : FGWord X) :
  grp_mul (FreeGrpObject X) a b
    = @compose (FreeGroupoid (PointQuiver X)) ttt ttt ttt a b := eq_refl.

Example free_group_unit_is_id (X : SetoidObject) :
  grp_unit (FreeGrpObject X) = @id (FreeGroupoid (PointQuiver X)) ttt
  := eq_refl.

(** Inversion IS word reversal — [Lib/TList.v]'s [tlist_rev] at the sign
    swap — and it is the chosen inverse of the groupoid structure. *)
Example free_group_inv_is_reversal (X : SetoidObject) (a : FGWord X) :
  grp_inv (FreeGrpObject X) a
    = ginv (FreeGroupoid_IsGroupoid (PointQuiver X)) a := eq_refl.

(** The underlying monoid is literally [hom_monoid] of the free groupoid:
    all three data fields agree on the nose. *)
Example free_group_monoid_carrier (X : SetoidObject) :
  carrier (grp_setoid (FreeGrpObject X))
    = carrier (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_op (X : SetoidObject) :
  grp_mul (FreeGrpObject X)
    = @mon_op (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_unit (X : SetoidObject) :
  grp_unit (FreeGrpObject X)
    = @mon_unit (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

(** ** The insertion of generators

    A letter becomes the one-letter positive word.  Respectfulness is not
    reproved: it is the [fedgemap_respects] field of
    [Construction/Free/Groupoid.v]'s [FreeGroupoidUnit], read at the single
    node. *)
Definition fg_insert (X : SetoidObject)
  : X ~{Sets}~> Grp_Forget (FreeGrpObject X) := {|
  morphism        := @fedgemap _ _ (FreeGroupoidUnit (PointQuiver X)) ttt ttt;
  proper_morphism := @fedgemap_respects _ _
                       (FreeGroupoidUnit (PointQuiver X)) ttt ttt
|}.

Example fg_insert_is_generator (X : SetoidObject) (a : carrier X) :
  fg_insert X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(** ** Delooping an [Instance/Grp.v] group

    [Construction/Deloop.v]'s [Deloop_IsGroupoid] is stated over THAT file's
    [GrpObject], and there is no converter in tree from it to this one.
    Both halves are one line each here, so the delooping is rebuilt directly
    over [Instance/Grp.v]'s record rather than routed through a record
    conversion.  ([Instance/Rep.v]'s [grp_mon] is the same monoid bridge,
    but that file sits on top of the module and matrix stack, which nothing
    here needs.) *)

Definition grp_deloop_monoid (H : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid H;

  mon_unit := grp_unit H;
  mon_op   := grp_mul H;

  mon_op_respects := grp_mul_respects H;

  mon_op_assoc  := fun a b c => symmetry (grp_mul_assoc H a b c);
  mon_op_unit_l := grp_mul_unit_l H;
  mon_op_unit_r := grp_mul_unit_r H
|}.

Definition grp_deloop (H : GrpObject) : Category :=
  Deloop (grp_deloop_monoid H).

(** The delooping of a group is a groupoid: the inverse of an arrow is the
    group inverse of the element, and the two [IsIsomorphism] fields are the
    two inverse laws — the left one a field of [GrpObject], the right one
    [Instance/Grp.v]'s derived [grp_mul_inv_r]. *)
Definition grp_deloop_IsGroupoid (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  fun x y a =>
    @Build_IsIsomorphism (grp_deloop H) x y a (grp_inv H a)
      (grp_mul_inv_r H a) (grp_mul_inv_l H a).

(** ** Deliverable 3: the universal property of the free group *)

Section Extension.

Context (X : SetoidObject) (H : GrpObject).
Context (h : X ~{Sets}~> Grp_Forget H).

(** [h], read as a quiver homomorphism into the delooping of [H]. *)
Definition point_hom
  : QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H)) :=
  @Build_QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H))
    (fun _ => ttt)
    (fun _ _ a => h a)
    (fun _ _ => proper_morphism h).

Definition extend_functor : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H :=
  FreeGroupoidFunctor (PointQuiver X) (grp_deloop_IsGroupoid H) point_hom.

(** The extension of [h] to the free group.  Its action is [fmap] of the
    functor just built; the [Build_GrpHom'] smart constructor derives unit
    preservation, and multiplication preservation IS [fmap_comp] — the free
    group's multiplication being composition and the delooping's being the
    group operation, both definitionally. *)
Definition free_grp_extend : FreeGrpObject X ~{Grp}~> H :=
  @Build_GrpHom' (FreeGrpObject X) H
    {| morphism        := fun w => fmap[extend_functor] w;
       proper_morphism := @fmap_respects _ _ extend_functor ttt ttt |}
    (fun a b => @fmap_comp _ _ extend_functor ttt ttt ttt a b).

(** It agrees with [h] on the generators. *)
Lemma free_grp_extend_generators (a : carrier X) :
  free_grp_extend (fg_insert X a) ≈ h a.
Proof using X H h.
  exact (FreeGroupoidFunctor_gen (PointQuiver X) (grp_deloop_IsGroupoid H)
           point_hom (x:=ttt) (y:=ttt) a).
Qed.

(** ...and it evaluates a word: the two structural clauses that pin down
    what "evaluate a word in the group" means, both instances of the
    homomorphism laws. *)
Lemma free_grp_extend_mul (u v : FGWord X) :
  free_grp_extend (grp_mul (FreeGrpObject X) u v)
    ≈ grp_mul H (free_grp_extend u) (free_grp_extend v).
Proof using X H h. exact (grp_map_mul free_grp_extend u v). Qed.

Lemma free_grp_extend_inv (u : FGWord X) :
  free_grp_extend (grp_inv (FreeGrpObject X) u)
    ≈ grp_inv H (free_grp_extend u).
Proof using X H h. exact (grp_map_inv free_grp_extend u). Qed.

(** *** Uniqueness

    Any homomorphism out of the free group agreeing with [h] on the
    generators IS the extension.  The argument is not a fresh induction: the
    competitor is repackaged as a functor into the delooping (its
    [fmap_id] is unit preservation and its [fmap_comp] is multiplication
    preservation, both definitionally), and
    [Construction/Free/Groupoid.v]'s [FreeGroupoidFunctor_unique] finishes.
    In particular the value on an INVERTED letter is never constrained by
    hypothesis — it is forced, which is the whole content of freeness for
    groups as opposed to monoids. *)

Definition functor_of_hom (g : FreeGrpObject X ~{Grp}~> H)
  : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H.
Proof.
  unshelve eapply Build_Functor.
  - exact (fun _ => ttt).
  - intros [] [] w; exact (grp_map g w).
  - intros [] [] u v Huv; exact (proper_morphism (grp_map g) u v Huv).
  - intros []; exact (grp_map_unit g).
  - intros [] [] [] u v; exact (grp_map_mul g u v).
Defined.

Lemma free_grp_extend_unique (g : FreeGrpObject X ~{Grp}~> H)
  (Hg : ∀ a : carrier X, g (fg_insert X a) ≈ h a) (w : FGWord X) :
  g w ≈ free_grp_extend w.
Proof using X H h.
  refine (FreeGroupoidFunctor_unique (PointQuiver X)
            (grp_deloop_IsGroupoid H) point_hom (functor_of_hom g)
            (fun _ => eq_refl) _ ttt ttt w).
  intros [] [] a; exact (Hg a).
Qed.

End Extension.

Arguments free_grp_extend {X H} h.
Arguments extend_functor {X H} h.

(** The universal property, in the shape [Theory/Universal/Arrow.v]'s
    [universal_arrow_from_UMP] consumes. *)
Theorem free_group_universal (X : SetoidObject) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X.
Proof.
  intros H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    symmetry; exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; symmetry; exact (Hg a).
Qed.

(** The free group packaged as a universal arrow.  By
    [Theory/Universal/Arrow.v] this IS an initial object of the comma
    category [=(X) ↓ Grp_Forget]. *)
Definition free_group_universal_arrow (X : Sets)
  : UniversalArrow X Grp_Forget :=
  universal_arrow_from_UMP X Grp_Forget (FreeGrpObject X) (fg_insert X)
    (free_group_universal X).

(** The same content in the direct encoding, where the universal object is
    named rather than projected out of a comma category. *)
Program Definition free_group_AUniversalArrow (X : Sets)
  : AUniversalArrow X Grp_Forget (FreeGrpObject X) := {|
  universal_arrow := fg_insert X
|}.
Next Obligation.
  intros X H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; exact (Hg a).
Qed.

(** ** Deliverable 4: the free-forgetful adjunction

    The functor, the adjunction and both triangle identities come out of the
    generic machinery of [Theory/Universal/Arrow.v] with no further proof —
    the same route [Construction/Free/Quiver.v] and
    [Instance/Coq/Monoid/Free.v] take. *)

Definition FreeGrp : Sets ⟶ Grp :=
  LeftAdjointFunctorFromUniversalArrows Grp_Forget free_group_universal_arrow.

Definition free_group_adjunction : FreeGrp ⊣ Grp_Forget :=
  AdjunctionFromUniversalArrows Grp_Forget free_group_universal_arrow.

(** The free functor's object part is the word group, definitionally. *)
Example FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X := eq_refl.

(** The universal arrow is the insertion of generators on the nose:
    [universal_arrow_from_UMP] stores the supplied morphism as the second
    projection of the comma object it builds, so no proof is involved. *)
Example free_group_arrow_is_insert (X : Sets) :
  @arrow _ _ X Grp_Forget (free_group_universal_arrow X) = fg_insert X
  := eq_refl.

(** ** The unit is the one-letter word

    [unit] is DERIVED in [Theory/Adjunction.v] (it is the transpose of the
    identity), not a field, so what it computes to has to be checked.  It is
    [fmap[U] id ∘ arrow], and [fmap[Grp_Forget] id] is the identity setoid
    map, so the unit is [fg_insert] itself. *)

Definition free_group_unit (X : Sets)
  : X ~{Sets}~> Grp_Forget (FreeGrp X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_group_adjunction X.

Example free_group_unit_is_insert (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

Example free_group_unit_is_generator (X : Sets) (a : carrier X) :
  free_group_unit X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(** ** The counit evaluates a word

    The counit is the OTHER transpose, and it does not compute: it is
    [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
    [Qed]-opaque, so no [eq_refl] is available on this side and none is
    claimed.  What is available — and is the actual content — is that it
    agrees with word evaluation up to [≈], which the uniqueness half of the
    universal property delivers. *)

Definition free_group_counit (H : Grp)
  : FreeGrp (Grp_Forget H) ~{Grp}~> H :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_group_adjunction H.

(** On a generator the counit is the letter itself. *)
Lemma free_group_counit_generator (H : Grp) (a : carrier (Grp_Forget H)) :
  free_group_counit H (fg_insert (Grp_Forget H) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_group_adjunction H a).
Qed.

(** ...and on an arbitrary word it is the evaluation of that word in [H],
    i.e. the extension of the identity map on [H]'s carrier. *)
Theorem free_group_counit_evaluates (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w
    ≈ free_grp_extend (@id Sets (Grp_Forget H)) w.
Proof.
  apply (free_grp_extend_unique (Grp_Forget H) H (@id Sets (Grp_Forget H))
           (free_group_counit H)).
  intro a; exact (free_group_counit_generator H a).
Qed.

(** ** The triangle identities

    Both are instances of [Theory/Adjunction.v]'s derived corollaries; they
    are named here because the issue asks for them by name. *)

Corollary free_group_triangle_left (X : Sets) :
  free_group_counit (FreeGrp X) ∘ fmap[FreeGrp] (free_group_unit X)
    ≈ @id Grp (FreeGrp X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_group_adjunction X). Qed.

Corollary free_group_triangle_right (H : Grp) :
  fmap[Grp_Forget] (free_group_counit H)
    ∘ free_group_unit (Grp_Forget H)
    ≈ @id Sets (Grp_Forget H).
Proof. exact (@fmap_counit_unit _ _ _ _ free_group_adjunction H). Qed.

(** ** The free functor relabels letters

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a word has
    to be proved.  On generators it renames the letter. *)
Lemma free_group_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreeGrp] f (fg_insert X a) ≈ fg_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_group_universal_arrow X)
              (@arrow _ _ Y Grp_Forget (free_group_universal_arrow Y) ∘ f)) a).
Qed.

(** ** Non-vacuity: the free group on two generators is nonabelian

    A free group on the empty or a one-element generating set is abelian and
    would demonstrate nothing.  The witness therefore has TWO generators,
    and it is separated by a functor into the delooping of the symmetric
    group on three letters ([Structure/Groupoid.v]'s [S3_Grp], a nonabelian
    group already in tree) — which is a groupoid, so the free-groupoid
    universal property applies directly and no bridge between the two
    [GrpObject] records is needed. *)

Definition TwoLetters : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_to_S3
  : QuiverHomomorphism (PointQuiver TwoLetters)
      (QuiverOfCat (Deloop S3_Grp)).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (fun _ => ttt).
  - exact (fun _ _ b => if b then S3_r else S3_a).
  - intros u v b b' Hb; simpl in Hb; now rewrite Hb.
Defined.

(* A local abbreviation, purely syntactic, so that the witness proofs below
   fit on a line without disturbing any [rewrite]'s matching. *)
Local Notation FreeTwo := (FreeGroupoid (PointQuiver TwoLetters)).

Definition two_S3 : FreeTwo ⟶ Deloop S3_Grp :=
  FreeGroupoidFunctor (PointQuiver TwoLetters) deloop_S3_groupoid two_to_S3.

Theorem free_group_two_generators_nonabelian :
  grp_mul (FreeGrpObject TwoLetters)
    (fg_insert TwoLetters true) (fg_insert TwoLetters false)
  ≈ grp_mul (FreeGrpObject TwoLetters)
      (fg_insert TwoLetters false) (fg_insert TwoLetters true) → False.
Proof.
  intro Hcomm.
  apply S3_not_abelian.
  assert (Hs : @equiv _ (@homset (Deloop S3_Grp) ttt ttt)
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters true)
                    (fg_insert TwoLetters false)))
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters false)
                    (fg_insert TwoLetters true))))
    by (now rewrite Hcomm).
  rewrite !fmap_comp in Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  exact Hs.
Qed.

(** The two generators are themselves distinct in the free group — the free
    group on two letters does not collapse them. *)
Theorem free_group_two_generators_distinct :
  fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False.
Proof.
  intro Hab.
  pose proof (@fmap_respects _ _ two_S3 ttt ttt _ _ Hab) as Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  discriminate.
Qed.
