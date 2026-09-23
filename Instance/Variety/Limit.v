Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.

Generalizable All Variables.

(** * Limits in the setoid variety are computed on underlying sets *)

(* nLab:      https://ncatlab.org/nlab/show/created+limit
   nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
   Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)
   Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
              §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)

   A limit of algebras is computed on the underlying sets: its carrier is
   the limit of the carriers, its operations act coordinatewise, and it
   satisfies every equation the components satisfy because each
   coordinate does.  Mac Lane's §V.1 proves this for groups (the forgetful
   functor creates limits, Theorem 2, so the category is complete,
   Theorem 3); Instance/Grp/Limit.v formalises that case.  This file does
   the same for the SETOID VARIETY [SVariety E] of
   Instance/Variety/Free.v, uniformly in the operation signature and the
   set of equations.  It supplies completeness, which every application
   of the adjoint functor theorem (Adjunction/GAFT.v's [GAFT]) at this
   category takes, and the continuity of the forgetful functor, which the
   application at that functor takes.  Instance/Variety/Colimit.v makes
   both applications: at the diagonal, for Mac Lane's colimits of
   algebras (§V.7 Exercise 4, §IX.1 Exercise 2), where the preservation
   input is Adjunction/Diagonal/Limit.v's [Diagonal_continuous]; and at
   the forgetful functor, for Mac Lane's own route to the free algebra
   (§V.6), where it is [SVariety_Forget_continuous] below.

   CONSUMED, not rebuilt: Instance/Sets/Complete.v's compatible families
   ([Sets_limit_obj], [Sets_limit_carrier]); Instance/Sets/Propositional.v's
   [limit_PropEquiv], the propositional mirror of a limit of setoids,
   which supplies the [soa_prop] field Instance/Variety/Free.v's record
   carries since #450 with no hypothesis on the limit; and
   Instance/Comp.v's [lhs_natural] and [rhs_natural], CONSUMED along
   evaluation at a coordinate exactly as Free.v's [soa_prod_satisfies]
   consumes them along a projection -- never proved, so nothing here pays
   the functional extensionality some [EqSignature]s cost to BUILD.

   BUILT:

     - [svlim_soa]/[svlim_alg], the limit algebra over any shape and any
       diagram; [svlim_eval d], evaluation at a coordinate as a LEIBNIZ
       homomorphism of Instance/Comp.v, whose [op_commute] is
       [reflexivity]; [svlim_satisfies], the equations coordinatewise.
     - [svlim_cone], [svlim_med] and [SVariety_Limit : Limit F], the cone
       with its mediator and uniqueness read off pointwise, as
       [Sets_Limit] does; [SVariety_Complete : @Complete (SVariety E)].
     - [SVariety_Forget_continuous : ContinuousFunctor (SVariety_Forget
       E)], cone-level preservation of EVERY limit, not only of the
       computed one: for a limiting cone [N] the comparison [svf_to] from
       the computed limit is a retraction of [svlim_med] ([svf_to_med]),
       both composites being mediators out of [N] into itself, and the
       mediator out of a cone of setoids is the compatible family of its
       legs followed by [svf_to].

   STRENGTH, STRICTEST FIRST.  At the limit [SVariety_Complete] chooses,
   the carrier IS the compatible families, the operation at coordinate [d]
   IS the component's operation, and the leg at [d] IS evaluation:
   [svariety_complete_carrier], [svariety_complete_op] and
   [svariety_complete_leg] are three [eq_refl] Examples at an arbitrary
   signature, set of equations, shape and diagram.  They compare carriers
   and elements, the sanctioned exception to comparing morphisms by `≈`;
   every law, mediator and uniqueness clause is stated with `≈`.  NOT
   delivered at any strength is CREATION in the sense of
   Structure/Limit/Creation.v -- no [CreatesLimits] or
   [StrictlyCreatesLimit] instance, and no statement that the algebra
   structure on a limit of carriers is UNIQUE (Mac Lane's Theorem 2 has
   that clause; Instance/Grp/Limit.v's [glim_structure_unique] states it
   for groups).  What is delivered is computation plus continuity, which
   is exactly what [GAFT] consumes.

   UNIVERSES, measured with [About] under [Set Printing Universes], the
   stdlib-global bounds ([Projections], [compose], [eq_rect_r], [ID])
   dropped:

     SVariety_Complete@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} :
       ∀ {S : UA.OpSignature@{u0 u1}} (E : UA.EqSignature@{u2 u3 u u u0 u1} S),
       Complete@{u u4 u u5}
     (* Set < u6 / u < u6 / u < u9 / u <= u7 / u0 <= u / u1 <= u /
        u2 <= u7 / u3 <= u7 / u4 <= u / u6 <= u5 / u7 <= u5 / u8 <= u *)

   So the result and hom universes of [Complete@{r so h o}] are the
   carrier universe [u], shapes may have objects at or below it
   ([u4 <= u]), and the category's objects sit strictly above it -- more
   permissive than [Sets_Complete@{u u0} : Complete@{u u u u0}], whose
   shapes have their objects AT the carrier universe ([Category] is not
   cumulative), and at [u4 := u] exactly the [Complete@{h h h cobj}]
   instance [GAFT] needs with [h] the carrier.
   No universe is instantiated at [Set]; the one [Set] is the lower bound
   [Set < u6] that [soa_prop] puts on the object universe
   (Instance/Variety/Free.v's header).  No binder is annotated by hand:
   minimization collapsed nothing, measured by the readback above.

   NON-VACUITY.  Nothing here is specific to a witness category: the
   three readbacks hold for every diagram, and
   Instance/Variety/Colimit.v instantiates [SVariety_Complete] at #440's
   [CommEq], whose [EqSignature] is built without extensionality, in
   closed constants of its own.

   TRANSPARENCY, measured by flipping each of the four [Defined] to [Qed]
   in a scratch copy of this file: all four are load-bearing.  [svlim_op]
   opaque stops [svlim_soa], whose respect field needs the operation to
   reduce at a coordinate; [svlim_eval] opaque stops [svlim_satisfies],
   which needs its map to reduce to evaluation; [svlim_med_map] opaque
   stops the respect obligation of [svlim_med], and [svf_family] opaque
   stops that of [svf_med], each needing the family to reduce at a
   coordinate.  The [Program] obligations and the lemmas end in [Qed].

   PORTABILITY.  [svlim_op], [svlim_med_map] and [svf_family] are
   written as tactic proofs, the first component given by [exists] and
   the second proved by tactics against the goal it leaves, not as
   anonymous-constructor terms [(a; b)]: measured by a Nix build
   on Coq 8.20.1 of the first revision of this file, the term form of
   [svlim_med_map] is refused there although Rocq 9.1 accepts it (the
   comment above that definition quotes the refusal).

   ASSUMPTIONS, measured: [Print Assumptions] on every constant of the
   module, enumerated by [Print Module] (heads and [Program] obligations,
   which [.glob] heads omit) returns "Closed under the global context"
   for each.

   NOT delivered: creation and uniqueness of the lifted structure, as
   above; no identification of [soa_prod] (Instance/Variety/Free.v) with
   the binary product computed here; no colimits (Instance/Variety/Colimit.v);
   and nothing about #440's Leibniz [Variety E], whose limits are not
   touched. *)

Module UA := Category.Instance.Comp.UniversalAlgebra.

#[local] Obligation Tactic := idtac.

Section SVarietyLimit.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (F : J ⟶ SVariety E).

(* The underlying diagram of setoids. *)
Definition svlim_UF : J ⟶ Sets := SVariety_Forget E ◯ F.

(* The carrier: the compatible families of Instance/Sets/Complete.v. *)
Definition svlim_obj : SetoidObject := Sets_limit_obj svlim_UF.

(* The operations, pointwise in the shape.  Compatibility of the result is
   the homomorphism law of each [fmap[F] f] followed by respect for `≈`
   of the target's operation, applied to the compatibility of each
   argument. *)
Definition svlim_op (o : UA.operation S)
  (k : UA.arity o → carrier svlim_obj) : carrier svlim_obj.
Proof.
  exists (fun d => soa_op (`1 (F d)) o (fun i => `1 (k i) d)).
  intros d d' f; simpl.
  transitivity (soa_op (`1 (F d')) o
                  (fun i => salg_map (`1 (fmap[F] f)) (`1 (k i) d))).
  - exact (salg_commute (`1 (fmap[F] f)) o (fun i => `1 (k i) d)).
  - apply (soa_op_respects (`1 (F d')) o); intro i.
    exact (`2 (k i) d d' f).
Defined.

(* The propositional equality is Instance/Sets/Propositional.v's limit
   transport, supplied from the components' own [soa_prop] with no
   hypothesis on the limit. *)
Definition svlim_soa : SetoidOpAlgebra S := {|
  soa_obj := svlim_obj;
  soa_op := svlim_op;
  soa_op_respects := fun o k1 k2 H d =>
    soa_op_respects (`1 (F d)) o _ _ (fun i => H i d);
  soa_prop := limit_PropEquiv svlim_UF (fun d => soa_prop (`1 (F d)))
|}.

(* Evaluation at [d] is a LEIBNIZ homomorphism of Instance/Comp.v: the
   limit's operation at [d] is the component's operation on the nose, so
   [op_commute] is [eq_refl]. *)
Definition svlim_eval (d : J) :
  UA.AlgHom (soa_alg svlim_soa) (soa_alg (`1 (F d))).
Proof. exists (fun p => `1 p d). intros o args; reflexivity. Defined.

(* The equations hold pointwise: each component is [F d]'s own
   satisfaction transported along [svlim_eval d] by [lhs_natural] and
   [rhs_natural], consuming those fields and never proving one. *)
Lemma svlim_satisfies : ssatisfies E svlim_soa.
Proof.
  intros e args d.
  assert (HL : `1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
               = @UA.lhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.lhs_natural S E _ _ (svlim_eval d) e args).
  assert (HR : `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d
               = @UA.rhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.rhs_natural S E _ _ (svlim_eval d) e args).
  change (`1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
          ≈ `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d).
  rewrite HL, HR.
  exact (`2 (F d) e (fun i => `1 (args i) d)).
Qed.

Definition svlim_alg : SVariety E := (svlim_soa; svlim_satisfies).

Program Definition svlim_leg (d : J) : svlim_alg ~{SVariety E}~> F d :=
  ({| salg_map := fun p : carrier svlim_obj => `1 p d |}; I).
Next Obligation. intros d p q H; exact (H d). Qed.
Next Obligation. intros d o args; simpl; reflexivity. Qed.

Program Definition svlim_cone : Cone F := {|
  vertex_obj := svlim_alg;
  coneFrom := {| vertex_map := svlim_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(* Written as a tactic proof, the coherence component closed by [exact],
   and NOT as an anonymous-constructor term: its expected type states
   compatibility with [fmap[SVariety_Forget E ◯ F]], which [cone_coherence]
   matches only after unfolding the composite.  Measured by a Nix build
   of this file's first revision on Coq 8.20.1, the term form
   [(fun d => … ; fun d d' f => @cone_coherence … x)] is refused there
   with "The term … has type "∃ _ : ∀ x0 : obj[J], soa_obj (projT1
   (fobj[F] x0)), …" while it is expected to have type "carrier
   svlim_obj"", although Rocq 9.1 accepts it. *)
Definition svlim_med_map (N : Cone F)
  (x : carrier (soa_obj (`1 (vertex_obj[N])))) : carrier svlim_obj.
Proof.
  exists (fun d => salg_map (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f x).
Defined.

Program Definition svlim_med (N : Cone F) :
  vertex_obj[N] ~{SVariety E}~> svlim_alg :=
  ({| salg_map := svlim_med_map N |}; I).
Next Obligation.
  intros N x y H d; simpl.
  exact (salg_respects (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x y H).
Qed.
Next Obligation.
  intros N o args d; simpl.
  exact (salg_commute (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) o args).
Qed.

Program Definition SVariety_Limit : Limit F := {|
  limit_cone := svlim_cone;
  ump_limits := fun N => {| unique_obj := svlim_med N |}
|}.
Next Obligation. intros N d x; simpl; reflexivity. Qed.
Next Obligation. intros N v Hv x d; simpl; symmetry; exact (Hv d x). Qed.

End SVarietyLimit.

Arguments svlim_UF {_} _ {_} _.
Arguments svlim_obj {_} _ {_} _.
Arguments svlim_op {_} _ {_} _ _ _.
Arguments svlim_soa {_} _ {_} _.
Arguments svlim_eval {_} _ {_} _ _.
Arguments svlim_satisfies {_} _ {_} _ _ _ _.
Arguments svlim_alg {_} _ {_} _.
Arguments svlim_leg {_} _ {_} _ _.
Arguments svlim_cone {_} _ {_} _.
Arguments svlim_med_map {_} _ {_} _ _ _.
Arguments svlim_med {_} _ {_} _ _.
Arguments SVariety_Limit {_} _ {_} _.

Definition SVariety_Complete {S : UA.OpSignature} (E : UA.EqSignature S) :
  @Complete (SVariety E) := fun J F => SVariety_Limit E F.

(* The limit [SVariety_Complete] chooses IS the computed one on the nose:
   its carrier is the compatible families of Instance/Sets/Complete.v,
   its operation at a coordinate is the component's operation, and its
   legs are evaluation. *)

Example svariety_complete_carrier {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) :
  carrier (soa_obj (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])))
    = Sets_limit_carrier (svlim_UF E F) := eq_refl.

Example svariety_complete_op {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (o : UA.operation S)
  (k : UA.arity o → carrier (svlim_obj E F)) (d : J) :
  `1 (soa_op (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])) o k) d
    = soa_op (`1 (F d)) o (fun i => `1 (k i) d) := eq_refl.

Example svariety_complete_leg {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (d : J) (p : carrier (svlim_obj E F)) :
  salg_map (`1 (@vertex_map _ _ _ _
                 (@coneFrom _ _ _ (@limit_cone _ _ _ (SVariety_Complete E J F))) d)) p
    = `1 p d := eq_refl.

(** ** The forgetful functor is continuous

    The image under [SVariety_Forget] of ANY limiting cone -- not only
    of [svlim_cone] -- is limiting in [Sets].  Given a limiting [N] and a
    cone [M] of setoids, the mediator is the compatible family of [M]'s
    legs followed by the comparison [svf_to] from the computed limit to
    [N]; uniqueness goes back through the comparison [svlim_med] the
    other way, which composes with [svf_to] to the identity by [N]'s own
    uniqueness clause. *)

Section ForgetContinuous.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (G : J ⟶ SVariety E).
Context (N : Cone G) (HN : IsLimitCone N).
Context (M : Cone (SVariety_Forget E ◯ G)).

(* The comparison from the computed limit to [N]. *)
Definition svf_to : svlim_alg E G ~{SVariety E}~> vertex_obj[N] :=
  unique_obj (HN (svlim_cone E G)).

Lemma svf_to_legs (d : J) (p : carrier (svlim_obj E G)) :
  salg_map (`1 (cone_leg N d)) (salg_map (`1 svf_to) p) ≈ `1 p d.
Proof. exact (unique_property (HN (svlim_cone E G)) d p). Qed.

(* It is a retraction of [svlim_med]: [svf_to ∘ svlim_med N] and the
   identity are both mediators from [N] to itself. *)
Lemma svf_to_med (y : carrier (soa_obj (`1 (vertex_obj[N])))) :
  salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) y) ≈ y.
Proof.
  assert (Hid : unique_obj (HN N) ≈ id[vertex_obj[N]]).
  { apply (uniqueness (HN N)); intros d x; reflexivity. }
  assert (Hcomp : unique_obj (HN N) ≈ svf_to ∘ svlim_med E G N).
  { apply (uniqueness (HN N)); intros d x; simpl.
    exact (svf_to_legs d (svlim_med_map E G N x)). }
  exact (transitivity (symmetry (Hcomp y)) (Hid y)).
Qed.

(* The compatible family of the legs of [M]. *)
Definition svf_family (x : carrier (vertex_obj[M])) : carrier (svlim_obj E G).
Proof.
  (* Tactic form for the reason given at [svlim_med_map]. *)
  exists (fun d => cone_leg M d x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) d d' f x).
Defined.

Program Definition svf_med :
  vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N]) := {|
  morphism := fun x => salg_map (`1 svf_to) (svf_family x)
|}.
Next Obligation.
  intros x y Hxy.
  apply (salg_respects (`1 svf_to)).
  intro d; simpl.
  exact (proper_morphism (cone_leg M d) x y Hxy).
Qed.

Lemma svf_med_legs (d : J) :
  cone_leg (FCone (SVariety_Forget E) N) d ∘ svf_med ≈ cone_leg M d.
Proof. intro x; exact (svf_to_legs d (svf_family x)). Qed.

Lemma svf_med_unique
  (v : vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N])) :
  (∀ d : J, cone_leg (FCone (SVariety_Forget E) N) d ∘ v ≈ cone_leg M d) →
  svf_med ≈ v.
Proof.
  intros Hv x; simpl.
  transitivity (salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) (v x))).
  - apply (salg_respects (`1 svf_to)).
    intro d; simpl; symmetry; exact (Hv d x).
  - exact (svf_to_med (v x)).
Qed.

End ForgetContinuous.

Arguments svf_to {_} _ {_} _ _ _.
Arguments svf_to_legs {_} _ {_} _ _ _ _ _.
Arguments svf_to_med {_} _ {_} _ _ _ _.
Arguments svf_family {_} _ {_} _ _ _.
Arguments svf_med {_} _ {_} _ _ _ _.
Arguments svf_med_legs {_} _ {_} _ _ _ _ _ _.
Arguments svf_med_unique {_} _ {_} _ _ _ _ _ _ _.

Definition SVariety_Forget_continuous {S : UA.OpSignature}
  (E : UA.EqSignature S) : ContinuousFunctor (SVariety_Forget E) :=
  fun J G N HN M =>
    {| unique_obj := svf_med E G N HN M
     ; unique_property := svf_med_legs E G N HN M
     ; uniqueness := svf_med_unique E G N HN M |}.
