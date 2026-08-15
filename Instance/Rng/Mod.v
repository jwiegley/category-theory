(** * Restriction of scalars, and the category of all modules

    Mac Lane's §II.2 pairs contravariance with a worked algebraic
    example.  Construction 8 is restriction of scalars: a homomorphism of
    rings ρ : R → S turns every S-module into an R-module, by letting r
    act as ρ r does, and the assignment is CONTRAVARIANT — ρ points from
    R to S while the induced functor points from S-modules to R-modules.
    Construction 9 collects the fibres into a single category of all
    modules over all rings, whose objects are pairs (R, M) and whose
    morphisms carry a ring map alongside a map of the underlying groups
    (Categories for the Working Mathematician, 2nd ed., §II.2, printed
    p. 35, [maclane:II.2:construction8] and [maclane:II.2:construction9];
    the locations follow issue jwiegley/category-theory#256's convention,
    and as there the printed text was not consulted while writing this
    file).
    nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
    nLab: https://ncatlab.org/nlab/show/Grothendieck+construction
    Wikipedia: https://en.wikipedia.org/wiki/Restriction_of_scalars

    WHAT IS BUILT ON.  Instance/Mod.v supplies [RModObject]/[RModHom] and
    the categories [RMod R]; Instance/Rng.v and Theory/Algebra/Rig.v
    supply [Rng], whose objects are [RingObject] and whose morphisms are
    [RigHom]s of the underlying rigs.  Nothing about modules is restated:
    [RestrictObj] keeps [rm_ab] LITERALLY the same term, so every module
    fact — the group laws, [rm_smul_zero_l], [ab_map_neg] — transfers
    unchanged, and each of the five module obligations is M's own law
    with ρ's preservation of the relevant operation spliced in front.
    Distributing over a sum of scalars spends [rig_map_add],
    associativity spends [rig_map_mul], unitality spends [rig_map_one],
    and distributing over a sum of vectors spends nothing at all.

    LEFT AND RIGHT.  Mac Lane's modules are right modules, so his
    construction 8 reads "for a right S-module".  The tree's primitive is
    the LEFT module ([RModObject] of Instance/Mod.v), with right modules
    defined there as left modules over the opposite ring,
    [ModR R := RMod (Ring_op R)].  The right-hand reading therefore costs
    one observation and no second construction: a ring homomorphism is
    its own homomorphism of the opposite rings, since ρ (b · a) ≈ ρ b · ρ a
    IS ρ's multiplicativity read backwards ([RigHom_op]), and
    [RestrictR ρ := Restrict (RigHom_op ρ)].  The two are the same
    construction at different rings, by definition rather than by a
    separate proof.

    THE FIRST INDEXED CATEGORY INSTANTIATED AT A CONCRETE VARYING
    FAMILY.  Three [IndexedCat] values existed before [ModIndexed], and
    the claim must be measured against them precisely.  Two are GENERAL
    CONSTRUCTORS that do discharge all fifteen coherence fields for
    varying fibres — Construction/Grothendieck/RoundTrip.v's
    [RT_Indexed] (from a split cleaving, with real coherence proofs)
    and Construction/Grothendieck/Strict.v's
    [IndexedCat_of_StrictFunctor] (from a [StrictCat]-valued functor
    under fibrewise UIP) — but neither is APPLIED to a concrete family
    anywhere outside its own file.  The third, that same file's
    [Constant_IndexedCat], is the one concrete Grothendieck the tree
    instantiates, and it has every fibre the SAME category, every
    reindexing the identity functor and every mediator [iso_id].  So
    what is new here is the INSTANTIATION: [ModIndexed] is the first
    [IndexedCat] whose fifteen fields are discharged at a concrete
    family whose fibres genuinely vary with the base object.  The
    fields still come cheap, for one structural
    reason worth stating because it is what makes the exercise tractable:
    EVERY structural isomorphism of [ModIndexed] is an identity-carrier
    one.  Reindexing never touches the abelian group, only the action, so
    the comparison morphisms are all the identity map of a shared group
    and are built by the single smart constructor [rmod_iso_of_ab].  Two
    of the three even have DEFINITIONALLY equal actions — [idx_id]
    because the identity ring map is the identity function, [idx_comp]
    because [rig_hom_compose] is function composition — so their
    obligations close by [reflexivity]; only [idx_resp] does any work,
    and that work is one application of [rm_smul_respects].  The ten law
    fields are then pointwise identities and close by [reflexivity] as
    well.

    TWO TOTAL CATEGORIES, AND WHICH ONE IS MAC LANE'S.  Construction 9's
    category of all modules over all rings is [ModFibred], fibred over
    [Rng], and its morphisms are Mac Lane's on the nose: a morphism
    (R; M) ~> (S; N) is a pair (ρ; f) with ρ : R ~> S a homomorphism of
    rings — running WITH the total arrow — and f an R-module map
    [M ~> RestrictObj ρ N], that is, an additive f : M → N with
    f (r · m) ≈ ρ r · f m.  That condition is the standard notion of a
    SEMILINEAR map, and the word is reserved for it here
    ([ModFibred_semilinear] one way, [mod_semilinear_hom] back).
    Composition is Mac Lane's pasting: ring legs compose as ρ' ∘ ρ
    ([ModFibred_compose_ring]) and fibre legs as (Restrict ρ f') ∘ f
    ([ModFibred_compose_fibre]).

    [ModTotal] is the OPFIBRED companion, and it is what the tree's
    covariant [IndexedCat] together with [Grothendieck] yields DIRECTLY,
    which is why it is built first and keeps its name.  Its morphisms are
    pairs (ρ; g) with ρ : S ~> R — running OPPOSITE to the total arrow —
    and g an S-module map [RestrictObj ρ M ~> N], that is, an additive
    g : M → N with g (ρ s · m) ≈ s · g m.  That is the mirror condition,
    called COSEMILINEAR here so the standard word stays with Mac Lane's
    ([ModTotal_cosemilinear], [mod_cosemilinear_hom]).  The two
    categories are NOT opposite to one another: comparing the two hom
    types shows that passing to the opposite reverses the fibre leg as
    well as the base, so each has to be built rather than derived from
    the other by [Opposite].

    How [ModFibred] is reached costs no new mathematics.  [OpModIndexed]
    is the same assignment with the fibres read backwards —
    [idx_fib R := (RMod R)^op], reindexing by [Opposite_Functor] of the
    same [Restrict], every structural isomorphism
    Construction/Opposite.v's [Isomorphism_Opposite] of the same
    identity-carrier isomorphism — and
    [ModFibred := (Grothendieck OpModIndexed)^op].  Extension of scalars,
    the left adjoint of restriction, is a different matter and is NOT
    built: the tree has no tensor product for it.

    What is definitional and what is up to ≈, stated exactly, and it is
    the same on both sides.  The OBJECT and HOM TYPES are definitional:
    [ModTotal_obj_unfold], [ModTotal_hom_unfold], [ModFibred_obj_unfold]
    and [ModFibred_hom_unfold] are all [eq_refl], as are the ring legs of
    composites ([ModTotal_compose_ring], [ModFibred_compose_ring]) and
    the collapse [(Rng^op)^op = Rng] that lets [ModFibredProj] be typed
    at [Rng] with no transport.  (Those ring-leg [eq_refl] Examples DO
    compare Rng morphisms with [=] — a deliberate strengthening, sound
    exactly because the two sides are convertible; the ≈-only
    discipline governs statements about morphisms that are not, which
    is why the MODULE leg of a composite is stated up to ≈.)  On
    the fibred side the mediating comparison is genuinely present rather
    than absent — [RestrictObj ρ (RestrictObj ρ' P)] and
    [RestrictObj (ρ' ∘ ρ) P] have the same action but different law
    fields, so they are distinct records — and
    [ModFibred_compose_fibre] displays it, while
    [ModFibred_compose_carrier] shows it is invisible on carriers.  Here
    the ≈ carries real weight and is not standing in for [=]: the two
    morphism terms of [ModFibred_compose_fibre] are NOT convertible, a
    whole-term [reflexivity] being refused, and the equation closes
    pointwise instead.  The carrier-level statements
    ([ModTotal_compose_carrier], [ModFibred_compose_carrier]) do close by
    whole-term [reflexivity].  No claim is made anywhere that two
    morphisms with ≈-equal components are [eq];
    the hom-setoid of [Total] compares base arrows by ≈ and transports
    fibre arrows along that proof.

    FIBRATION STATUS.  The in-tree [IndexedCat] is COVARIANT and its
    Grothendieck construction produces an OPfibration whose canonical
    opcleaving satisfies the split laws — Construction/Grothendieck/
    Fibration.v, cited and not re-proved here, and cited at the strength
    it delivers: that file's own header records that the split laws are
    standalone lemmas ([Grothendieck_Split]) rather than an instance of
    Theory/Fibration.v's strict [SplitCleaving] record.  So [ModProj] is
    that opfibration over [Rng^op].  Nothing here re-derives the dual
    statement for [ModFibredProj]: that it is a fibration over [Rng]
    follows from the same citation read through the opposite, and is not
    formalized.

    THE FIBRES.  [ModTotal_fibre] instantiates
    Construction/Grothendieck/Fiber.v's [fiber_grothendieck_equiv] at
    [ModIndexed]: the fibre of [ModTotal] over a ring R is equivalent to
    [RMod R], by an equivalence that is the identity on objects, and the
    target is [RMod R] on the nose ([ModTotal_fibre_target], [eq_refl]).
    On the fibred side the same instantiation at [OpModIndexed] lands at
    [(RMod R)^op] ([ModFibred_fibre_op]), and [ModFibred_fibre] carries
    it across by Theory/Equivalence/Limit.v's
    [EquivalenceOfCategories_op] to land at [RMod R], the double opposite
    collapsing definitionally.  Disclosed: [ModFibred] is not itself
    presented as the total category of a displayed category over [Rng],
    so [Fiber] is applied to the underlying Grothendieck and transported,
    rather than computed for [ModFibred] directly.

    WITNESS.  ℤ is initial in [Rng] (Instance/Rng.v's [Rng_Initial_Z]),
    so restriction along the unique map ℤ → R makes every R-module a
    ℤ-module: [ZRestrict].  The same datum is an arrow in each category,
    pointing opposite ways: [mod_to_Z] runs out of every object of
    [ModTotal], and [mod_from_Z] runs into every object of [ModFibred],
    both with ring leg the unique map ℤ → R and identity fibre leg.  At ℤ
    itself the action computes, [3 · 4 = 12] by [eq_refl]. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.
Require Import Category.Construction.Grothendieck.Fiber.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

(* Both [C^op] on categories and [F^op] on functors are notations for
   [_ ^op] at level 7, in [category_scope] and [functor_scope]
   respectively, and Functor/Opposite.v opens the latter; reopening
   [category_scope] here keeps [Rng^op] and [(RMod R)^op] reading as
   categories.  Opposite FUNCTORS are therefore written out as
   [Opposite_Functor], which is what Instance/Cat/Opposite.v does
   throughout for the same reason. *)
Open Scope category_scope.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Restriction of scalars: Mac Lane's construction 8 *)

(** Along ρ : R → S, an S-module M becomes an R-module with r acting as
    ρ r does.  The underlying abelian group is UNCHANGED — [rm_ab] is
    [rm_ab M], the same term — which is what makes every comparison
    further down an identity-carrier one. *)
Definition RestrictObj {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject S) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab   := rm_ab M;
    rm_smul := fun r m => rm_smul M (rig_map rho r) m
  |}.
  - (* rm_smul_respects *)
    intros r r' Hr m m' Hm.
    now rewrite Hr, Hm.
  - (* rm_smul_distr_l: no property of ρ is spent *)
    intros r m n.
    apply rm_smul_distr_l.
  - (* rm_smul_distr_r: ρ is additive *)
    intros r r' m.
    rewrite (rig_map_add rho r r').
    apply rm_smul_distr_r.
  - (* rm_smul_assoc: ρ is multiplicative *)
    intros r r' m.
    rewrite (rig_map_mul rho r r').
    apply rm_smul_assoc.
  - (* rm_smul_one: ρ preserves the unit *)
    intros m.
    rewrite (rig_map_one rho).
    apply rm_smul_one.
Defined.

(** A map of S-modules IS a map of the restricted R-modules: the same
    homomorphism of abelian groups, its linearity read at the scalar
    ρ r. *)
Program Definition RestrictHom {R S : RingObject} (rho : R ~{Rng}~> S)
  {M N : RModObject S} (f : M ~{RMod S}~> N) :
  RestrictObj rho M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := rm_hom f
|}.
Next Obligation.
  intros R S rho M N f r m.
  exact (rm_map_smul f (rig_map rho r) m).
Qed.

(** Restriction of scalars as a functor.  Both functor laws hold because
    the arrow part changes nothing: identities and composites of module
    maps ARE identities and composites of the underlying group maps. *)
Program Definition Restrict {R S : RingObject} (rho : R ~{Rng}~> S) :
  RMod S ⟶ RMod R := {|
  fobj := RestrictObj rho;
  fmap := fun M N f => RestrictHom rho f
|}.
Next Obligation. intros R S rho M N f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R S rho M a; reflexivity. Qed.
Next Obligation. intros R S rho M N P f g a; reflexivity. Qed.

(** ** The right-module reading *)

(** A ring homomorphism is its own homomorphism of the OPPOSITE rings:
    ρ (b ·op a) = ρ (a · b) ≈ ρ a · ρ b = ρ b ·op ρ a, which is
    [rig_map_mul] with its two arguments exchanged.  Everything else is
    the original field, since Instance/Mod.v's [Rig_op] keeps the setoid,
    the zero, the addition and the unit as the very same terms.  The
    constructor is named explicitly for the reason Instance/Mod.v's
    [bimodule_right_RMod] records: a record literal here would elaborate
    the first field's type against [R] and infer the parameters to be
    [R] and [S] rather than their opposites, the two being convertible,
    and the multiplication clause would then be checked in the wrong
    argument order. *)
Definition RigHom_op {R S : RingObject} (rho : R ~{Rng}~> S) :
  Ring_op R ~{Rng}~> Ring_op S :=
  @Build_RigHom (Rig_op (ring_rig R)) (Rig_op (ring_rig S))
    (rig_map rho) (rig_map_zero rho) (rig_map_add rho)
    (rig_map_one rho) (fun a b => rig_map_mul rho b a).

(** Restriction of scalars for RIGHT modules — Mac Lane's own statement
    of construction 8.  It is [Restrict] at the opposite rings, by
    definition; no obligation is discharged a second time. *)
Definition RestrictR {R S : RingObject} (rho : R ~{Rng}~> S) :
  ModR S ⟶ ModR R := Restrict (RigHom_op rho).

(** ** The comparison isomorphisms, all identity-carrier *)

(** The smart constructor.  A pair of mutually inverse homomorphisms of
    the UNDERLYING abelian groups, each commuting with the two actions,
    is an isomorphism of modules.  Stating the hypotheses through an
    explicit [AbHom] rather than through the carriers is what keeps the
    constructor usable at arbitrary M and N: at every call site below the
    two groups are the same term and both maps are the identity, so the
    inverse laws close by [reflexivity] and only the two action clauses
    carry content. *)
Program Definition rmod_iso_of_ab {R : RingObject} {M N : RModObject R}
  (h : AbHom (rm_ab M) (rm_ab N)) (k : AbHom (rm_ab N) (rm_ab M))
  (Hh : ∀ r m, cmon_map h (rm_smul M r m) ≈ rm_smul N r (cmon_map h m))
  (Hk : ∀ r n, cmon_map k (rm_smul N r n) ≈ rm_smul M r (cmon_map k n))
  (Hhk : ∀ n, cmon_map h (cmon_map k n) ≈ n)
  (Hkh : ∀ m, cmon_map k (cmon_map h m) ≈ m) :
  M ≅[RMod R] N := {|
  to   := {| rm_hom := h; rm_map_smul := Hh |};
  from := {| rm_hom := k; rm_map_smul := Hk |}
|}.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh n; exact (Hhk n).
Qed.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh m; exact (Hkh m).
Qed.

(** Reindexing, packaged with the op-direction fixed once: a morphism
    x ~> y of [Rng^op] IS a ring map y → x, and restriction along it
    carries x-modules to y-modules. *)
Definition mod_map {x y : RingObject} (f : x ~{Rng^op}~> y) :
  RMod x ⟶ RMod y := Restrict f.

(** ≈-equal ring maps reindex isomorphically.  The one comparison of the
    three that does any work, and the work is one application of
    [rm_smul_respects] to the pointwise equality of the two ring maps. *)
Definition mod_resp_iso {x y : RingObject} {f g : x ~{Rng^op}~> y}
  (e : f ≈ g) (a : RMod x) : mod_map f a ≅[RMod y] mod_map g a.
Proof.
  (* The two modules are pinned explicitly: both comparison maps being
     the identity of ONE group, the elaborator would otherwise identify
     the source and target modules with each other. *)
  unshelve notypeclasses refine
    (@rmod_iso_of_ab y (mod_map f a) (mod_map g a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m.
    exact (rm_smul_respects a _ _ (e r) m m (reflexivity m)).
  - intros r n.
    exact (rm_smul_respects a _ _ (symmetry (e r)) n n (reflexivity n)).
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(** Reindexing along the identity is the identity ON THE ACTION, not
    merely up to isomorphism: the identity ring map is the identity
    function, so the two actions are the same term and all four
    obligations close by [reflexivity]. *)
Definition mod_id_iso {x : RingObject} (a : RMod x) :
  mod_map (@id (Rng^op) x) a ≅[RMod x] a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab x (mod_map (@id (Rng^op) x) a) a
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(** Reindexing twice is reindexing along the composite, again on the
    action: composition in [Rng] is composition of the underlying
    functions, so ρ₂ (ρ₁ s) · m is literally the same term on both
    sides. *)
Definition mod_comp_iso {x y z : RingObject} (f : y ~{Rng^op}~> z)
  (g : x ~{Rng^op}~> y) (a : RMod x) :
  mod_map f (mod_map g a) ≅[RMod z] mod_map (f ∘ g) a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab z (mod_map f (mod_map g a)) (mod_map (f ∘ g) a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(** ** The indexed category of modules *)

(** Modules indexed by rings, contravariantly — that is, covariantly over
    [Rng^op], which is what Construction/Indexed.v's covariant
    [IndexedCat] asks for.  The ten law fields are pointwise identities:
    every comparison above is the identity map of a shared abelian group,
    and [fmap] of a restriction functor changes no underlying map, so
    each equation is an identity of carrier functions. *)
Definition ModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => RMod R)
       (fun x y f => mod_map f)
       (fun x y f g e a => mod_resp_iso e a)
       _ _ _
       (fun x a => mod_id_iso a)
       _
       (fun x y z f g a => mod_comp_iso f g a)
       _ _ _ _ _ _).
  - (* idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle *)
    intros w x y z f g h a m; reflexivity.
Defined.

(** ** The category of all modules: Mac Lane's construction 9 *)

(** Objects are pairs (R; M) with M an R-module; morphisms are described
    below.  The name is the issue's. *)
Definition ModTotal : Category := Grothendieck ModIndexed.

(** The projection to rings, contravariantly.  By
    Construction/Grothendieck/Fibration.v it is an opfibration whose
    canonical opcleaving satisfies the split laws — cited at that
    strength, not re-proved here. *)
Definition ModProj : ModTotal ⟶ Rng^op := Grothendieck_Proj ModIndexed.

(** *** What the objects and morphisms are, on the nose *)

Example ModTotal_obj_unfold :
  obj[ModTotal] = (∃ R : RingObject, RModObject R) := eq_refl.

(** A morphism (R; M) ~> (S; N) is a ring map ρ : S → R — running
    OPPOSITE to the total arrow, which is what [Rng^op] as the base
    means — together with an S-module map out of the restriction of M
    along ρ.  This is an equality of TYPES, by [eq_refl]. *)
Example ModTotal_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModTotal}~> (S; N))
    = (∃ rho : S ~{Rng}~> R, RestrictObj rho M ~{RMod S}~> N) := eq_refl.

(** The fibre leg unfolded: g is additive and satisfies
    g (ρ s · m) ≈ s · g m.  That is the MIRROR of Mac Lane's condition,
    not Mac Lane's own, so the standard word "semilinear" is reserved for
    [ModFibred] below and this one is called COSEMILINEAR. *)
Lemma ModTotal_cosemilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : S ~{Rng}~> R)
  (g : RestrictObj rho M ~{RMod S}~> N)
  (s : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom g) (rm_smul M (rig_map rho s) m)
    ≈ rm_smul N s (cmon_map (rm_hom g) m).
Proof. exact (rm_map_smul g s m). Qed.

(** And back: that equation is all a fibre leg is. *)
Program Definition mod_cosemilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : S ~{Rng}~> R)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ s m, cmon_map h (rm_smul M (rig_map rho s) m)
                 ≈ rm_smul N s (cmon_map h m)) :
  RestrictObj rho M ~{RMod S}~> N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs s m.
  exact (Hs s m).
Qed.

(** *** Composition is Mac Lane's (ρ, f)·(ρ', f') *)

(** The ring components compose in [Rng] in the REVERSE order, on the
    nose. *)
Example ModTotal_compose_ring {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 a ∘[Rng] `1 b := eq_refl.

(** The module components compose directly.  Stated up to ≈ because it
    is an equation between morphisms; the proof is [reflexivity], the
    mediating [from (idx_comp …)] being the identity map of the shared
    group. *)
Lemma ModTotal_compose_carrier {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

(** The projection really does take first components. *)
Example ModProj_fobj (X : ModTotal) : ModProj X = `1 X := eq_refl.

Example ModProj_fmap {X Y : ModTotal} (a : X ~> Y) :
  fmap[ModProj] a = `1 a := eq_refl.

(** *** The fibres *)

Example ModTotal_fibre_target (R : RingObject) :
  idx_fib ModIndexed R = RMod R := eq_refl.

(** The fibre of [ModTotal] over R is equivalent to [RMod R], by
    Construction/Grothendieck/Fiber.v's equivalence — which is the
    identity on objects, both of its cells carrying identity
    components. *)
Definition ModTotal_fibre (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To ModIndexed R) :=
  fiber_grothendieck_equiv ModIndexed R.

(** ** The fibred reading: Mac Lane's (ρ, f) on the nose *)

(** The same assignment of modules to rings, with the fibres read
    BACKWARDS.  Restriction of scalars is not touched: every reindexing
    functor here is [Opposite_Functor] of the very one [ModIndexed]
    uses, and every structural isomorphism is Construction/Opposite.v's
    [Isomorphism_Opposite] of the very identity-carrier isomorphism
    [ModIndexed] uses.  Reversing the fibres is exactly what turns the
    opfibred morphisms of [ModTotal] into the fibred ones Mac Lane
    writes; the ten law fields close by [reflexivity] for the same reason
    they do there, composition in the opposite fibre being the same
    identity map of the same abelian group read the other way. *)
Definition OpModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => (RMod R)^op)
       (fun x y f => Opposite_Functor (mod_map f))
       (fun x y f g e a => Isomorphism_Opposite (mod_resp_iso e a))
       _ _ _
       (fun x a => Isomorphism_Opposite (mod_id_iso a))
       _
       (fun x y z f g a => Isomorphism_Opposite (mod_comp_iso f g a))
       _ _ _ _ _ _).
  - (* idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle *)
    intros w x y z f g h a m; reflexivity.
Defined.

(** Mac Lane's category of all modules over all rings, fibred over
    [Rng]. *)
Definition ModFibred : Category := (Grothendieck OpModIndexed)^op.

(** The projection to rings, COVARIANTLY.  No transport is needed to
    type it at [Rng] rather than at [(Rng^op)^op]: the double opposite
    collapses definitionally in this tree, by the auto-duality
    Construction/Opposite.v is built for. *)
Definition ModFibredProj : ModFibred ⟶ Rng :=
  Opposite_Functor (Grothendieck_Proj OpModIndexed).

Example ModFibred_double_op_collapses : (Rng^op)^op = Rng := eq_refl.

(** *** Mac Lane's (ρ, f), definitionally *)

Example ModFibred_obj_unfold :
  obj[ModFibred] = (∃ R : RingObject, RModObject R) := eq_refl.

(** A morphism (R; M) ~> (S; N) is a ring map ρ : R → S running WITH the
    total arrow, together with an R-module map from M into the
    restriction of N along ρ.  This is Mac Lane's (ρ, f) exactly, and it
    is an equality of TYPES, by [eq_refl]. *)
Example ModFibred_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModFibred}~> (S; N))
    = (∃ rho : R ~{Rng}~> S, M ~{RMod R}~> RestrictObj rho N) := eq_refl.

(** The fibre leg unfolded: f is additive and SEMILINEAR in the standard
    sense, f (r · m) ≈ ρ r · f m.  This is Mac Lane's condition, which is
    why the word sits here rather than on [ModTotal_cosemilinear]. *)
Lemma ModFibred_semilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : R ~{Rng}~> S)
  (f : M ~{RMod R}~> RestrictObj rho N)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom f) (rm_smul M r m)
    ≈ rm_smul N (rig_map rho r) (cmon_map (rm_hom f) m).
Proof. exact (rm_map_smul f r m). Qed.

(** And back: that equation is all a fibre leg is. *)
Program Definition mod_semilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : R ~{Rng}~> S)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ r m, cmon_map h (rm_smul M r m)
                 ≈ rm_smul N (rig_map rho r) (cmon_map h m)) :
  M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs r m.
  exact (Hs r m).
Qed.

(** *** Composition is Mac Lane's pasting *)

(** The ring legs compose in [Rng] in Mac Lane's order, ρ' ∘ ρ, on the
    nose. *)
Example ModFibred_compose_ring {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 b ∘[Rng] `1 a := eq_refl.

(** The fibre legs paste as Mac Lane's (Restrict ρ f') ∘ f, with the one
    canonical comparison made visible: the composite lands in
    [RestrictObj ρ (RestrictObj ρ' P)] and the target is
    [RestrictObj (ρ' ∘ ρ) P], and those are DISTINCT records — their
    actions are the same term but their law fields are not — so the
    identity-carrier [mod_comp_iso] is what mediates.  The ≈ is doing
    real work: the two sides are NOT convertible as terms — a whole-term
    [reflexivity] is refused — so the equation is closed pointwise, which
    is what ≈ asks for in this hom-setoid. *)
Lemma ModFibred_compose_fibre {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `2 (b ∘ a)
    ≈ to (mod_comp_iso (`1 a) (`1 b) (`2 Z))
        ∘ fmap[mod_map (`1 a)] (`2 b) ∘ `2 a.
Proof. intro m; reflexivity. Qed.

(** On carriers the comparison is invisible and the fibre legs simply
    compose. *)
Lemma ModFibred_compose_carrier {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

Example ModFibredProj_fobj (X : ModFibred) :
  ModFibredProj X = `1 X := eq_refl.

Example ModFibredProj_fmap {X Y : ModFibred} (a : X ~> Y) :
  fmap[ModFibredProj] a = `1 a := eq_refl.

(** *** The fibres *)

(** What is straightforwardly available, and exactly how far it goes.
    [ModFibred] is NOT itself presented as the total category of a
    displayed category over [Rng] — it is the opposite of one over
    [Rng^op] — so Construction/Grothendieck/Fiber.v's [Fiber] is applied
    to the underlying Grothendieck, where it lands at [(RMod R)^op], and
    the result is carried across by Theory/Equivalence/Limit.v's
    [EquivalenceOfCategories_op].  The double opposite collapses
    definitionally, so the transported equivalence lands at [RMod R] with
    no further work and no new general machinery. *)
Example ModFibred_fibre_target (R : RingObject) :
  (idx_fib OpModIndexed R)^op = RMod R := eq_refl.

Definition ModFibred_fibre_op (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To OpModIndexed R) :=
  fiber_grothendieck_equiv OpModIndexed R.

Definition ModFibred_fibre (R : RingObject) :
  EquivalenceOfCategories
    (Opposite_Functor (Fiber_Grothendieck_To OpModIndexed R)) :=
  EquivalenceOfCategories_op (fiber_grothendieck_equiv OpModIndexed R).

(** ** Every module is a ℤ-module: the witness *)

(** ℤ is initial in [Rng], so there is exactly one ring map ℤ → R, and
    restriction along it is the underlying-abelian-group functor read as
    a change of base. *)
Example rng_from_Z_is_initial_arrow (R : RingObject) :
  rng_from_Z R = @zero Rng Rng_Initial_Z R := eq_refl.

Definition ZRestrict (R : RingObject) : RMod R ⟶ RMod Int_Ring :=
  Restrict (rng_from_Z R).

(** The arrow of [ModTotal] this produces, out of EVERY object: its ring
    leg is the unique map ℤ → R and its module leg is the identity,
    because the restriction is the target on the nose. *)
Definition mod_to_Z (R : RingObject) (M : RModObject R) :
  (R; M) ~{ModTotal}~> (Int_Ring; ZRestrict R M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_to_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModProj] (mod_to_Z R M) = rng_from_Z R := eq_refl.

(** The same datum read in [ModFibred], where the ring leg runs forward
    and the arrow therefore points the other way: Mac Lane's (ρ, f) with
    ρ the unique map ℤ → R and f the identity, exhibiting each module as
    its own underlying abelian group with the R-action added along ρ. *)
Definition mod_from_Z (R : RingObject) (M : RModObject R) :
  (Int_Ring; ZRestrict R M) ~{ModFibred}~> (R; M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_from_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModFibredProj] (mod_from_Z R M) = rng_from_Z R := eq_refl.

(** At ℤ itself the action computes: restriction along ℤ → ℤ leaves
    multiplication of integers where it was. *)
Example int_ZRestrict_smul :
  rm_smul (ZRestrict Int_Ring Int_RMod) 3%Z 4%Z = 12%Z := eq_refl.

Example int_ZRestrict_group :
  rm_ab (ZRestrict Int_Ring Int_RMod) = rm_ab Int_RMod := eq_refl.

(** The right-module reading unfolds on the nose: restricting a right
    S-module along ρ makes r act as ρ r acted.  This is the statement
    that carries the content; the ℤ computation below does not, ℤ being
    commutative, and is recorded only as evidence that the opposite-ring
    plumbing computes.  The argument exchange itself is what
    [RigHom_op]'s multiplication clause asserts, and the elaborator
    checks it against [Rig_op]'s definition. *)
Example RestrictR_action {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject (Ring_op S))
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  rm_smul (RestrictR rho M) r m = rm_smul M (rig_map rho r) m := eq_refl.

Example int_RestrictR_smul :
  rm_smul (RestrictR (rng_from_Z Int_Ring) (Ring_RMod (Ring_op Int_Ring)))
          3%Z 4%Z = 12%Z := eq_refl.
