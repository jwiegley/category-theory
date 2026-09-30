(** * R ⊗ (−) is a left adjoint: the premises of Riehl's Corollary 5.6.10 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Additive.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.BaseChange.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.TensorMonad.

Generalizable All Variables.

(* Book: Riehl, "Category Theory in Context", 2nd ed., Corollary
         5.6.10, printed p. 212 (PDF p. 232) — riehl:5.6:cor10; with
         her Example 4.4.15, printed p. 154 (PDF p. 174), Theorem 4.6.2,
         printed p. 165, Theorem 5.6.5, printed pp. 210–211, and
         Exercise 5.6.ii, printed p. 217
   nLab: https://ncatlab.org/nlab/show/tensor-hom+adjunction
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/created+limit

   Riehl proves her Corollary 5.6.10 — the forgetful functor U : _R Mod → Ab
   creates every colimit that Ab has, in this header's paraphrase — in one
   short paragraph.  U is monadic with monad R ⊗_ℤ −.  "By Example 4.4.15, for
   any pair of abelian groups A and B, there is a natural isomorphism"
   involving "the abelian group Hom_ℤ(R, B) of group homomorphisms R → B.  In
   particular, the monad R ⊗_ℤ − : Ab → Ab has a right adjoint Hom_ℤ(R, −)."
   And "By Theorem 4.6.2, R ⊗_ℤ − preserves all colimits and so Theorem
   5.6.5(ii) applies to all diagrams in Ab."  Theorem 4.6.2 (printed p. 165)
   is "Right adjoints preserve limits, and left adjoints preserve colimits";
   Theorem 5.6.5 (printed p. 210) says that a monadic functor creates "(ii)
   any colimits that C has and the monad and its square preserve", and its
   proof asks, on printed p. 211, "the additional hypothesis that T and T²
   preserve the colimit cone in C under consideration".  This file delivers
   the premises that proof consumes and stops before the theorem it feeds,
   which the tree does not have.

   WHICH READING OF THE DISPLAY.  The natural isomorphism is displayed on
   printed p. 212 as Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, A′)), and the sentence
   that follows names the group on the right Hom_ℤ(R, B).  The tree implements
   the B reading, Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, B)), the shape of her
   Example 4.4.15's own display (4.4.16) (printed p. 154), Ab(A ⊗_ℤ B,
   C) ≅ Ab(A, Hom(B, C)), with the fixed factor R written on the left as the
   corollary writes it.

   THE TENSOR–HOM ADJUNCTION IS A COMPOSITE, NOT A NEW CONSTRUCTION.
   Instance/Mod/TensorMonad.v's [TensorF R] is U ◯ ZExt R, whose value at A is
   Instance/Ab/Tensor.v's [AbTensor (ring_ab R) A], R ⊗ A.
   [TensorF_left_adjoint] composes (Adjunction/Compose.v's
   [Adjunction_Compose]) Instance/Mod/BaseChange.v's
   [zext_adjunction R : ZExt R ⊣ U] with Instance/Mod/Coextension.v's
   [coex_adjunction R : U ⊣ Coextension R], so TensorF R ⊣ U ◯ Coextension R,
   and the right adjoint IS Hom_ℤ(R, −): [TensorF_right_adjoint_obj] reads U
   (Coextension R B) back, by [eq_refl], as Adjunction/Additive.v's
   [hom_ab Ab_AbEnriched (ring_ab R) B], the additive maps R → B under
   pointwise addition.  The bijection is Riehl's correspondence between
   homomorphisms out of the tensor and bilinear maps, read at generators.  The
   transpose of φ : R ⊗ A → B sends a to r ↦ φ ((r · 1) ⊗ a) ([tensor_hom_to],
   by [eq_refl]) — the unit enters through ZExt's own action — and so
   is ≈ r ↦ φ (r ⊗ a) ([tensor_hom_to_gen], by [rig_mul_one_r] under
   Instance/Ab/Tensor.v's [te_gen]).  The inverse transpose of
   ψ : A → Hom_ℤ(R, B) sends r ⊗ a to ψ a (1 · r) ([tensor_hom_from], by
   [eq_refl]), evaluation at 1 after Coextension's action by translation, and
   so is ≈ ψ a r ([tensor_hom_from_gen], by [rig_mul_one_l]).  Without the
   unit, both are refused at [eq_refl] (C5 and C6 of
   Test/ProbeTensorMonad465.v), at a variable scalar: r · 1 or 1 · r against
   r is a propositional law at an abstract ring, and even at [Int_Ring] the
   product is stuck on a variable integer (C5Z, C6Z), while over ℤ at the
   scalar 3 both hold by [eq_refl] (that probe's controls).

   THE SQUARE, AND BOTH FORMS OF COCONTINUITY.  [TensorF2_left_adjoint]
   composes the adjunction with itself, so T² = TensorF R ◯ TensorF R is a
   left adjoint too.  Adjunction/Continuity.v then gives
   [TensorF_cocontinuous] and [TensorF2_cocontinuous], at
   Structure/Limit/Preservation.v's [CocontinuousFunctor]: every colimiting
   COCONE is carried to a colimiting cocone, which is the form Riehl's proof
   of 5.6.5(ii) asks for ("preserve the colimit cone"); and
   [TensorF_preserves_colimits] and [TensorF2_preserves_colimits], at
   [PreservesAllColimits], the apex-level form, to which
   Structure/Limit/Preservation.v's [Cocontinuous_PreservesAllColimits]
   descends from the first.

   ONLY AT [RingObject@{c c c}], MEASURED.  Every constant of the tensor–hom
   part binds [@{c o x}] (or [@{c o x t l l0 s}]) with the ring's three
   universes one.  That is Coextension's, not this file's: About on
   [Coextension] and [coex_adjunction] prints the block equations u = u0 and
   u = u1 over [RingObject@{u u0 u1}], and Instance/Mod/Coextension.v's header
   traces them to reading a ring's additive group as the source of a
   homomorphism of abelian groups and, independently, to Instance/Mod.v's
   [Ring_RMod].  Stated at a general [RingObject@{a c p}] under an extensible
   binder, the composite elaborates with the equations a = c and a = p (that
   probe's control [p465c_ctl_ring_open]); with c < a declared in the same
   binder it is refused, "Universe inconsistency. Cannot enforce a = c because
   c < a." (C8 of that probe), and with p < a likewise on a = p (C8a).
   Instance/Mod/TensorMonad.v's monad and Instance/Mod/Colimit/Creation.v's
   direct creation hold at [RingObject@{a c p}]; this restriction is the
   monadic route's alone.

   THE THIRD TRANSPORT'S PREMISE.  Riehl's route reaches U through the
   Eilenberg–Moore forgetful functor, and U is not that functor on the nose.
   [rmod_forget_comparison_obj] and [rmod_forget_comparison_map] show, by
   [eq_refl], that EM_Forget (TensorF R) ◯ EM_Comparison (zext_adjunction R)
   agrees with RMod_Forget_Ab R on objects and arrows, at a general
   [RingObject@{a c p}]; the two functor RECORDS are refused as one term
   (C7), each of the three law fields separating on its own
   ([fmap_respects], [fmap_id], [fmap_comp]; C7a, C7b, C7c);
   and [rmod_forget_comparison] is the isomorphism of functors, in
   Theory/Functor.v's [Functor_Setoid], with identity components.

   NOT DELIVERED: RIEHL'S ROUTE ITSELF.  The step all of this feeds is her
   Theorem 5.6.5(ii) at an Eilenberg–Moore forgetful functor, issue #1008,
   OPEN; the tree has no [CreatesColimit] at [EM_Forget], only the limit
   clause (Monad/Eilenberg/Moore/Limit.v's [em_forget_StrictlyCreatesLimit]).
   The statement of the corollary is delivered directly, without the monad, by
   Instance/Mod/Colimit/Creation.v's [RMod_Forget_Ab_creates_colimits].  A
   follow-up finishing the monadic route must: (1) prove #1008's clause (ii)
   for [EM_Forget T], for a diagram K of T-algebras and a colimiting cocone
   under EM_Forget T ◯ K whose images under T and T ◯ T are colimiting (the
   [PreservesColimitCocone] form [TensorF_cocontinuous] and
   [TensorF2_cocontinuous] supply), with the structure map on the nadir
   induced by the colimit under T ◯ EM_Forget T ◯ K, as Riehl sketches; (2)
   instantiate it at Instance/Mod/TensorMonad.v's [TensorMonad R], whose
   functor is [TensorF R], at [RingObject@{c c c}]; (3) carry the creation
   back along the comparison equivalence [RMod_comparison_equivalence] of that
   file, through Theory/Equivalence/Creation.v's [equivalence_CreatesLimit] at
   the opposite equivalence (Theory/Equivalence/Limit.v's
   [EquivalenceOfCategories_op]) and Structure/Limit/Creation.v's
   [CreatesLimit_compose], repackaging the opposite of a composite as that
   file's colimit section does; (4) move it from EM_Forget ◯ EM_Comparison to
   [RMod_Forget_Ab R] along [rmod_forget_comparison], read in the opposite
   categories, with Instance/Cat/Creation.v's [CreatesLimit_transport]; and
   (5) compare the result with the direct [RMod_Forget_Ab_CreatesColimit], by
   [creates_lift_unique], recording the restriction to [RingObject@{c c c}]
   that (2) inherits.

   STRENGTHS.  By [eq_refl]: the right adjoint's value
   ([TensorF_right_adjoint_obj]); the two transposes at generators, with the
   unit ([tensor_hom_to], [tensor_hom_from]); U^T ◯ K against U on objects and
   arrows ([rmod_forget_comparison_obj], [rmod_forget_comparison_map]).
   At ≈ only: the transposes without the unit ([tensor_hom_to_gen],
   [tensor_hom_from_gen]); U^T ◯ K against U as functors
   ([rmod_forget_comparison]).  Refused, each pinned in
   Test/ProbeTensorMonad465.v beside its positive half: the transposes
   without the unit at [eq_refl] (C5, C6, and over ℤ at a variable integer
   C5Z, C6Z), the two functor records as one (C7) and each of their three law
   fields (C7a-C7c), by conversion; the tensor–hom adjunction at a ring whose
   carrier or proof universe is declared strictly below its auxiliary one
   (C8, C8a), by universes.

   WHY C5-C7 ARE REFUSED.  Not by opacity: in the copy of this file, its
   sibling, Instance/Mod/TensorMonad.v and their joint closure of 95 files
   with every [Qed] made [Defined] (Instance/Sets.v too),
   [Transparent Obligations] set and [abstract] made [transparent_abstract],
   described in Instance/Mod/Colimit/Creation.v's header, all of C5-C7, C5Z,
   C6Z and C7a-C7c stand, each stripped copy stopping with "cannot unify"
   inside its command.  C5 and C6 compare r · 1 or 1 · r with r at a variable
   scalar (propositional at an abstract ring; stuck on a variable integer
   even at [Int_Ring], C5Z and C6Z);
   C7 compares the composite functor's derived law proofs with
   [RMod_Forget_Ab]'s own.

   TRANSPARENCY, MEASURED.  Counted by token as in the sibling, 2 [Qed] and 1
   [Defined].  The [Defined] of [rmod_forget_comparison] is NOT load-bearing
   here — made [Qed] in a copy of the whole file, the file compiles — and is
   kept so that a transport along it computes with its identity components.

   UNIVERSES, read off [About] on all 14 constants.  The tensor–hom constants
   bind [@{c o x}]: R : RingObject@{c c c}, Ab@{o c}, RMod@{o x c c c}, pinned
   as Coextension@{c c c o x}, coex_adjunction@{c c c o x c},
   zext_adjunction@{c c c o o x c c} and Adjunction@{o c c o c c c c x c o}.
   The four cocontinuity constants add t (the class's level), l and l0 (the
   colimit predicate's) and s (the shape's objects).  The three comparison
   constants bind [@{a c p o x}] as Instance/Mod/TensorMonad.v does.  The
   strict bounds are Set < o, c < o and c < x everywhere, and c < t, s < t on
   the cocontinuity constants; the rest are c <= l0, s <= l0, l0 <= l, o <= l,
   l <= t and o <= t there, and a <= o, c <= a, p <= a on the comparison.
   There is no equation and no other [Set].  First carriers, by [About] on the
   donors: Set < o and c < o, Instance/Ab.v's [Ab]; c < x, Instance/Mod.v's
   [RMod]; c < t and s < t, Structure/Limit/Preservation.v's
   [CocontinuousFunctor] (u4 < u, u5 < u) and [PreservesAllColimits] (u3 < u,
   u5 < u).  Two donors carry levels outside their statements, and each
   such level is pinned rather than left outside the closed binder:
   [left_adjoint_Cocontinuous@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10}]'s u5,
   which neither its type nor its block mentions, is written c, and
   [left_adjoint_preserves_colimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}]'s u4,
   likewise unmentioned, is written c and its u5, bounded only from below,
   t.  Made a placeholder in a copy of the whole file, each of the three is
   refused with "Universe ... is unbound"; the u6 of each, in its type but
   unconstrained by its block, compiles as a placeholder, the adjunction
   argument's last level fixing it, and is written o.  The stdlib caps are
   inherited, each placed by [About] on every constant of its donor's
   dependency cone, as [Print All Dependencies] lists it, at its topmost
   carrier: compose and ID on Instance/Sets.v's [setoid_morphism_compose]
   and [setoid_morphism_id], through Instance/CMon.v's [cmon_hom_compose]
   and [cmon_hom_id] and so through [Ab]; prod_rect on two setoid rewrites,
   Instance/Ab.v's [ab_cancel_l], through BaseChange.v's [ZExtObj] on the
   constants that name [TensorF] and through Coextension.v's [coex_group]
   and Structure/AbCategory.v's [Ab_AbEnriched] on
   [TensorF_right_adjoint_obj], and Theory/Isomorphism.v's [iso_to_monic],
   through Theory/Adjunction.v's [Build_Adjunction'] in both adjunctions;
   Logic_lemmas.equality on Lib/Setoid.v's [eq_equivalence] and projections
   (the pair projections) on [Build_Adjunction'], both through
   [zext_adjunction] and [coex_adjunction]; and Projections (the sigma
   projections) on Monad/Eilenberg/Moore.v's [EilenbergMoore], through
   [EM_Forget], on the comparison constants.

   NOT DELIVERED, FURTHER.  No cocontinuity of R ⊗ (−) at a general ring, by
   this or any other route.  No naturality of the bijection is restated beyond
   what [Adjunction] carries.  No comparison with the hom–tensor bijections of
   Instance/Mod/HomTensor.v and Instance/Mod/Closed.v, which tensor over R
   rather than over ℤ.  Nothing registered as an [Instance]. *)

(** ** The tensor–hom adjunction *)

(* Ab(R ⊗ A, B) ≅ Ab(A, Hom_ℤ(R, B)): extension of scalars, then
   coextension, composed. *)

Definition TensorF_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R)
    (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R) :=
  Adjunction_Compose (zext_adjunction@{c c c o o x c c} R)
    (coex_adjunction@{c c c o x c} R).

Example TensorF_right_adjoint_obj@{c o x} (R : RingObject@{c c c})
  (B : obj[Ab@{o c}]) :
  fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B
  = hom_ab Ab_AbEnriched (ring_ab R) B := eq_refl.

Example tensor_hom_to@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  = cmon_map φ (@ts_gen (ring_ab R) A
                  (rig_mul (ring_rig R) r (rig_one (ring_rig R))) a)
  := eq_refl.

Lemma tensor_hom_to_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  ≈ cmon_map φ (@ts_gen (ring_ab R) A r a).
Proof.
  apply (proper_morphism (cmon_map φ)).
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_r (ring_rig R) r) (reflexivity a)).
Qed.

Example tensor_hom_from@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  = @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a)
      (rig_mul (ring_rig R) (rig_one (ring_rig R)) r) := eq_refl.

Lemma tensor_hom_from_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  ≈ @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a) r.
Proof.
  apply (proper_morphism
           (@cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a))).
  exact (rig_mul_one_l (ring_rig R) r).
Qed.

(** ** The square of the monad is a left adjoint *)

Definition TensorF2_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R)
    ((RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)
       ◯ (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)) :=
  Adjunction_Compose (TensorF_left_adjoint@{c o x} R)
    (TensorF_left_adjoint@{c o x} R).

(** ** Cocontinuity, cone-level and apex-level *)

(* Left adjoints preserve colimits: Riehl's Theorem 4.6.2, here
   Adjunction/Continuity.v. *)

Definition TensorF_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x} (TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF2_left_adjoint@{c o x} R).

Definition TensorF_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o} (TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF2_left_adjoint@{c o x} R).

(** ** The forgetful functor against U^T ◯ K *)

(* EM_Forget ◯ EM_Comparison agrees with U on objects and arrows on the
   nose, and is isomorphic to it with identity components. *)

Example rmod_forget_comparison_obj@{a c p o x} (R : RingObject@{a c p})
  (M : obj[RMod@{o x a p c} R]) :
  fobj[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M
  = fobj[RMod_Forget_Ab@{x o o a p c} R] M := eq_refl.

Example rmod_forget_comparison_map@{a c p o x} (R : RingObject@{a c p})
  (M N : obj[RMod@{o x a p c} R]) (f : M ~{RMod@{o x a p c} R}~> N) :
  fmap[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] f
  = fmap[RMod_Forget_Ab@{x o o a p c} R] f := eq_refl.

Definition rmod_forget_comparison@{a c p o x} (R : RingObject@{a c p}) :
  EM_Forget (TensorF@{a c p o x} R)
    ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)
  ≈ RMod_Forget_Ab@{x o o a p c} R.
Proof.
  exists (fun M => @iso_id Ab@{o c} (fobj[RMod_Forget_Ab@{x o o a p c} R] M)).
  intros M N f.
  simpl. intros m. reflexivity.
Defined.
