(** * Boundary probe for the powerset order and its adjunctions (#382)

    This file exists for what an in-file [Fail] cannot do: survive a
    rename.  A negative written inside the module it guards is renamed in
    lockstep with the constant it names, and so stays green when that
    constant disappears; a negative written HERE breaks loudly.

    The [Require] list below is the UNION of the four target files' own
    lists, plus the four targets.  A short prefix is exactly what makes a
    probe pass for the wrong reason -- a missing coercion or notation can
    turn an intended unification mismatch into an "illegal application" --
    so the list is mirrored rather than trimmed.

    ** THE NEGATIVES, BY KIND

    Eight negatives plus one instrument check.  The kinds are told apart
    by the error TEXT, not by a label, and the labels below were CHANGED
    after reading those texts -- negatives 2 and 3 were drafted as
    "typing" and are not:

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negatives 2, 3, 4 and 5.  Within them the reported
                   bound separates two shapes: 2 and 3 are SORT
                   rejections, "has type Type while it is expected to
                   have type Prop (... Cannot enforce ... <= Prop)",
                   while 4 and 5 are LEVEL rejections between two
                   declared universes ("Cannot enforce X <= o because
                   o < X", "Cannot enforce Set = u").  The tail alone
                   does NOT separate the two shapes.
      CONVERSION   "cannot unify" between two inhabitants of ONE type.
                   Negatives 6, 7 and 8.
      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negative 9.

    Each was stripped ONE AT A TIME and compiled alone, with its whole
    error read.  Every constant a negative names also appears in a
    command OUTSIDE any [Fail], including the donors -- a guard that
    names a constant only inside its own [Fail] is vacuous. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Powerset.

Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.Subobject.
Require Import Category.Instance.FinSet.Subsets.
Require Import Category.Instance.Top.Image.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* If [Fail] were inert -- a missing scope, a stray [Set Silent] -- this
   would pass and every other negative below would be worthless. *)
Fail Check probe382_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @Subsets_Complete.
Check @Subsets_Cartesian.
Check @subset_meet.
Check @DirectImage.
Check @InverseImage.
Check @image_preimage_adjunction.
Check @image_preimage_galois.
Check @image_MonotoneFun.
Check @preimage_MonotoneFun.
Check @direct_image_not_meet_preserving.
Check @powerset_sng0.
Check @sub_image.
Check @sub_reindex_monotone.
Check @sub_image_is_Powerset_Prop_image.
Check @sub_reindex_is_Powerset_Prop_preimage.
Check @Powerset_obj.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @Powerset_subobject_of_subset.
Check @Powerset_subset_of_subobject.
Check @Powerset_Prop_fin_object.
Check @powerset_const0.
Check @powerset_sng1.
Check @Functor_of_monotone.
Check @MonotoneFun.
Check @Opens.
Check @OpenSet.
Check @Opens_preimage.
Check @open_preimage.
Check @open_union.
Check @IsOpen.
Check @nat_inf_point.
Check @nat_inf_no_left_adjoint.
Check @nat_inf_preimage_adjunction.
Check @NatInf_Top.
Check @Point_Top.
Check @TopSpace.
Check @internal_subseteq.
Check @finpow_subseteq.
Check @finpow_le.
Check @FinSubsets.
Check @FinSubsetsToSubsets.
Check @FinSubsetsToSubsets_Full.
Check @FinSubsetsToSubsets_Faithful.
Check @finpow_image.
Check @finpow_dual.
Check @finpow_preimage.
Check @apples.
Check @relation.
Check SetoidObject.
Check Sets.
Check @carrier.
Check @Complete.
Check @Cartesian.
Check @Full.
Check @Faithful.
Check @sub_le.
Check @sub_reindex.
Check @HasPullbacks.
Check @fin_pair.
Check @sub2_10.
Check @sub2_11.
Check @apple0.
Check @finpow_map.
Check @finpow_subseteq_iff.
Check @image_ne_dual_at_apple0.
Check @Subsets_thin.
Check @Thin.
Check @GaloisConnection.
Check @Powerset_Prop_singleton_pred.
Check @nat_inf_right_adjoint.
Check @sub_image_is_Powerset_Prop_image.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 2 and 3: FORMABILITY (sort) -- two Type-valued orders
       that are not [relation]s, hence out of reach of [Proset] and
       [GaloisConnection] *)

(* THE POSITIVE CONTROL FIRST.  Inclusion of Prop-valued subsets IS a
   [relation], which is exactly why Instance/Powerset.v can put a
   [Proset] on it. *)
Definition probe_prop_le@{o} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_Prop_obj@{o} X)) :=
  fun S T => ∀ x, S x → T x.

(* NEGATIVE 2.  Instance/Sets/Powerset.v:238's PROOF-RELEVANT carrier has
   [Type@{o}]-valued members, so inclusion between two of its subsets is
   [Type]-valued and is not a [relation] at all.  This is why the order
   is put on the truncated carrier and not on this one. *)
Fail Definition probe_type_le@{o so} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_obj@{o so} X)) :=
  fun S T => ∀ x, S x → T x.

(* NEGATIVE 3.  The same wall one level up, and the reason
   [nat_inf_no_left_adjoint] quantifies over [Adjunction] rather than
   over [GaloisConnection]: the homs of [Opens X] are [Type]-valued. *)
Fail Definition probe_opens_le (X : TopSpace) : relation (OpenSet X) :=
  fun U V => ∀ x : X, `1 U x → `1 V x.

(* ... and the control that the SAME expression IS the hom of [Opens X]. *)
Definition probe_opens_hom (X : TopSpace) (U V : OpenSet X) : Type :=
  U ~{Opens X}~> V.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 4 and 5: FORMABILITY (level) *)

(* NEGATIVE 4.  The GENERAL right adjoint of [Opens_preimage] is the
   interior of a predicate: the union of all opens contained in it.  That
   union is indexed by [OpenSet X], which sits one universe ABOVE the
   points, while [open_union] indexes only at the points' level.  This is
   why Instance/Top/Image.v delivers the right adjoint at its witness and
   not in general. *)
Fail Definition probe_interior@{o} (X : TopSpace@{o}) (P : X → Type@{o}) :
  X → Type@{o} :=
  fun x => { V : OpenSet X & prod (∀ y : X, `1 V y → P y) (`1 V x) }.

(* The control: at a SMALL index the very same union does form, so the
   rejection is about the index's universe and not about the shape. *)
Definition probe_small_union@{o} (X : TopSpace@{o}) (I : Type@{o})
  (U : I → (X → Type@{o})) (HU : ∀ i, IsOpen X (U i)) :
  IsOpen X (fun x => { i : I & U i x }) := open_union X I U HU.

(* NEGATIVE 5.  The [Set] pin of the RAPL route, made visible.
   [Subsets_Complete] goes through [Proset_Limit] and hence through
   Instance/Discrete.v's unannotated [DiscreteCat_Functor], which fixes
   the shape at [DiscreteCat@{u Set Set}] while [IsALimit] identifies the
   shape's hom-and-proof universe with the ambient's.  So completeness is
   available at hom level [Set] and nowhere else. *)
Fail Definition probe_complete_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Complete (Subsets@{o u} X) :=
  Subsets_Complete.

(* The control at [Set], which is what Instance/Powerset.v states. *)
Definition probe_complete_at_Set@{o +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o Set} X) := Subsets_Complete.

(* And the control that the CARTESIAN structure, which does NOT route
   through the discrete diagram, carries no such pin. *)
Definition probe_cartesian_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Cartesian (Subsets@{o u} X) :=
  Subsets_Cartesian.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 6, 7 and 8: CONVERSION *)

(* NEGATIVE 6.  The direct image does not preserve meets, so the two
   sides are not the same term -- and they are not merely
   non-convertible, they are provably distinct, which is
   Instance/Powerset.v's [direct_image_not_meet_preserving]. *)
Fail Example probe_image_meet@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  := eq_refl.

(* The control: the corresponding statement for the PREIMAGE, which does
   preserve meets, is not merely true but definitional -- substitution
   commutes with a universal quantifier on the nose. *)
Example probe_preimage_meet@{o so +} :
  Powerset_Prop_preimage@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng0@{o})
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng1@{o})
  → True.
Proof. intros _; exact I. Qed.

(* NEGATIVE 7.  The monotone-map reading and the Galois reading of the
   direct image agree on OBJECTS but are not the same functor record:
   [Functor_of_monotone] is a [Program Definition] whose three law fields
   are its own opaque obligations, while [GaloisFunctor_l]'s are its own.
   The two [eq_refl] object Examples in Instance/Powerset.v are the
   controls that the difference touches neither data field. *)
Fail Example probe_monotone_functor@{o so u}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  Functor_of_monotone (subset_le_preorder@{o} X)
    (subset_le_preorder@{o} Y) (image_MonotoneFun f)
  = DirectImage f := eq_refl.

Example probe_monotone_functor_obj@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) (image_MonotoneFun f)] S
  = fobj[DirectImage f] S := eq_refl.

(* NEGATIVE 8.  The subobject bridge holds at [≈] and not at [eq_refl]:
   the two truncated existentials are bracketed differently, one
   quantifying over image points and the other over elements of the
   domain. *)
Fail Example probe_sub_image_bridge@{o so}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
  = Powerset_Prop_image@{o} f S := eq_refl.

(* The control: the same comparison at [≈] is Instance/Powerset/
   Subobject.v's own lemma. *)
Example probe_sub_image_bridge_equiv@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S
  := sub_image_is_Powerset_Prop_image f S.

(* ------------------------------------------------------------------------ *)
(** ** Positive checks that the headline artifacts exist and apply *)

Definition probe_adjunction_exists@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.

Definition probe_no_left_adjoint_exists
  (L : Opens Point_Top ⟶ Opens NatInf_Top)
  (A : L ⊣ Opens_preimage nat_inf_point) : False :=
  nat_inf_no_left_adjoint L A.

Definition probe_right_adjoint_exists :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint :=
  nat_inf_preimage_adjunction.

Definition probe_finset_full (n : nat) : Full (FinSubsetsToSubsets n) :=
  FinSubsetsToSubsets_Full n.

Definition probe_finset_faithful (n : nat) :
  Faithful (FinSubsetsToSubsets n) := FinSubsetsToSubsets_Faithful n.

Definition probe_reindex_monotone {C : Category} `{@HasPullbacks C}
  {x y : C} (f : y ~> x) (u v : SubObj x) :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v) :=
  sub_reindex_monotone f.

Example probe_internal_subseteq_computes :
  internal_subseteq 2 (fin_pair sub2_10 sub2_11) = fin_true := eq_refl.

Example probe_finpow_image_ne_dual :
  finpow_image apples apple0 = finpow_dual apples apple0 → False :=
  fun H => image_ne_dual_at_apple0 H.

Example probe_finpow_preimage_is_map (T : Fin.t (finpow 2)) :
  finpow_preimage apples T = finpow_map apples T := eq_refl.

Example probe_finpow_subseteq_iff (n : nat) (S T : Fin.t (finpow n)) :
  finpow_subseteq S T = true ↔ finpow_le S T := finpow_subseteq_iff n S T.

Example probe_sub_reindex_bridge@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T
  := sub_reindex_is_Powerset_Prop_preimage f T.

Example probe_subsets_thin (X : SetoidObject) : Thin (Subsets X) :=
  Subsets_thin X.

Example probe_open_preimage_obj {X Y : TopSpace} (g : Y ~{Top}~> X)
  (U : OpenSet X) : fobj[Opens_preimage g] U = open_preimage g U := eq_refl.

Example probe_galois_exists@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  image_preimage_galois f.

Example probe_preimage_monotonefun@{o so +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  preimage_MonotoneFun f.

Example probe_powerset_sng0_is_singleton@{o +} :
  powerset_sng0@{o}
    = Powerset_Prop_singleton_pred@{o}
        (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1 := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Negative 9: TYPING -- the adjunction has a handedness *)

(* Mac Lane's sentence is that the DIRECT image is LEFT adjoint to the
   inverse image.  The swapped reading is not a false equation, it is a
   different type, and the error says so with no "cannot unify" and no
   universe clause: a plain "has type ... while it is expected to have
   type ...". *)
Fail Definition probe_wrong_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  InverseImage f ⊣ DirectImage f := image_preimage_adjunction f.

(* The control at the correct handedness. *)
Definition probe_right_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.
