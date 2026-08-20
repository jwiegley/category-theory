Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Kan's form of the coyoneda lemma over the category of elements. *)

(* nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma
   nLab: https://ncatlab.org/nlab/show/category+of+elements

   BOOK LOCATION.  Recorded from the statement of issue #319: Mac Lane,
   "Categories for the Working Mathematician" (2nd ed.), III.2,
   Exercise 3, book p. 62.  That text was not consulted while writing
   this file; the location is given so a reader can look the exercise
   up, and nothing beyond the location is reproduced here.  No claim is
   made about the wording or numbering at that place.

   THE STATEMENT.  For K : D ⟶ Sets with category of elements
   [Elements K] and projection Q := [Elements_proj K], and for an object
   a of D, there is a bijection between

     - natural transformations K ⟹ [Hom a,─] into the covariant
       representable at a, and
     - cones from the constant functor at a to Q,

   natural in a.  Maps out of K into a representable are the same thing
   as cones over the elements projection.

   A SAME-NAME TRAP, FLAGGED BY THE ISSUE ITSELF.  Theory/Coend/Yoneda.v
   carries a [coyoneda_reduction] — the coend formula
   ∫^x C(x,c) × F x ≅ F c.  That is a DIFFERENT theorem which happens to
   share the name "coyoneda"; it is about coends, mentions no category
   of elements, and neither statement is derived from the other here.
   Nothing below refers to it.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH
   ---------------------------------------

   (1) The two passages, as plain [Definition]s applying the record
   constructor to named lemmas — no [Program], hence no obligation, in
   either passage or in the Δ bridge, so the terms whose conversion
   behaviour is measured below are transparent and the measurements mean
   what they say.  ([Program] is used for the three isomorphism
   definitions, whose obligations are respectfulness and the inverse
   laws and are opaque; nothing is claimed at [eq_refl] about those.
   The fourth isomorphism, [kan_iso_transform], is a plain [Definition]
   composing two of them.)

       [kan_cone_of_nat]  : (K ⟹ [Hom a,─]) → ACone a Q
       [kan_nat_of_cone]  : ACone a Q → (K ⟹ [Hom a,─])

   (2) Both round trips at `≈` — [kan_nat_cone_nat] in the hom-setoid of
   [D, Sets], which closes by [reflexivity] outright, and
   [kan_cone_nat_cone] in [AConeEquiv], which must first destruct the
   sigma object.  Whole-record Leibniz equality is REFUTED for both and
   pinned in Test/ProbeCoyoneda.v; see "Strict attempts" below.

   (3) The pointwise isomorphism of setoids
   [kan_iso_at : KanNat K a ≅[Sets] KanCone K a], and

   (4) the naturality-in-a upgrade
   [kan_coyoneda : KanNat K ≅[[D^op, Sets]] KanCone K],
   an isomorphism in the functor category, which is the "natural
   isomorphism" reading the exercise asks for.  Its two components ARE
   the legs of [kan_iso_at] by [eq_refl] ([kan_coyoneda_to_component],
   [kan_coyoneda_from_component]), so (4) is an upgrade of (3) and not a
   parallel construction.

   (5) The literal Δ-reading, [Transform (Δ[Elements K](a)) Q], related
   to the [ACone] form in both directions with both round trips, and the
   composite [kan_iso_transform] delivering Mac Lane's own phrasing
   Nat(K, D(a,−)) ≅ Nat(Δa, Q) as an isomorphism of setoids in Sets.

   THE DESIGN DECISION: WHY [ACone] AND NOT [Transform (Δ a) Q]
   -----------------------------------------------------------

   The two are the same data — [ACone c F] is an apex-indexed leg family
   [vertex_map] plus [cone_coherence], and a [Transform] out of a
   constant functor is that same family plus a naturality square — but
   they are NOT the same record, and they are not convertible: the cone
   law reads [fmap[F] f ∘ ψ x ≈ ψ y] while naturality against Δa reads
   [fmap[F] f ∘ τ x ≈ τ y ∘ id], so the two differ by an [id_right] and
   a [Transform] additionally carries [naturality_sym].  A choice had to
   be made and it is [ACone], for one reason that is not a matter of
   taste: Structure/Cone.v:79 already builds [ConePresheaf F : C^op ⟶
   Sets], the presheaf of cones over F, whose reindexing along
   g : a' ~> a precomposes every leg with g.  That IS the right-hand
   side of the exercise AS A FUNCTOR OF a, already assembled, with its
   functor laws already proved.  Taking the Δ-reading as primary would
   have required building that presheaf again by hand for no gain.

   The Δ-reading is therefore not dropped, it is delivered as a proved
   bridge ([kan_transform_of_cone], [kan_cone_of_transform]) with both
   round trips and packaged as [kan_cone_transform_iso].  What the
   bridge costs is exactly one [id_right] in each direction, which is
   the measurement, not a guess: both round trips are REFUTED at
   [eq_refl] and hold at `≈` by [reflexivity], the leg family surviving
   on the nose in both directions and only the law fields being rebuilt.

   THE CRUX OF THE BACKWARD PASSAGE
   --------------------------------

   Objects of [Elements K] are pairs (d, x) compared by LEIBNIZ equality
   — [obj] carries no setoid in this library — while the elements x
   themselves live in a setoid.  So when x ≈ y in K d without x = y, the
   pairs (d, x) and (d, y) are two DIFFERENT objects.  A cone therefore
   assigns them two legs, a priori unrelated, whereas the transformation
   it is supposed to become must have a component at d that RESPECTS `≈`
   on K d.

   That respectfulness is not assumed and is not an extra hypothesis: it
   is DERIVED, in [kan_leg_respects], from cone coherence alone.  The
   witness is [elements_same], the morphism (d, x) ~> (d, y) whose
   underlying D-morphism is the identity — it exists precisely because
   [fmap[K] id x ≈ x ≈ y] — and coherence at it gives
   [id ∘ ψ (d,x) ≈ ψ (d,y)].  This is the same phenomenon
   Theory/Natural/Transformation/Arrows.v records for the arrows-only
   presentation of a natural transformation, where respectfulness in the
   arrow argument is likewise derivable rather than carried; the
   mechanism there is a detour through [f ∘ id] and here it is the
   identity-carried morphism between two elements, so it is an analogy
   of shape and not a reuse of that file, which is not imported.

   UNIVERSES (measured in the constraint blocks with [Set Printing
   Universes], not read off the binders)
   --------------------------------------------------------------------

   Everything below lives over a category [D : Category@{u u0 u0}] with
   [K : D ⟶ Sets@{u0 _}].  The measured facts:

     - [KanNat@{u u0 u1 u2 u3}] and [KanCone@{u u0 u1 u2}] EACH carry
       [u <= u0] — D's objects at or below D's homs — and so therefore do
       [kan_iso_at], [kan_coyoneda] and [kan_iso_transform];
     - [kan_cone_of_nat@{u u0 u1 u2 u3 u4}] and
       [kan_nat_of_cone@{u u0 u1 u2 u3 u4}] DO NOT.  Each block bounds
       [u] and [u0] below [Elements K]'s own object universe — which is
       [u2] in the first block and [u3] in the second, the two constants
       numbering their binders differently — with nothing forcing that
       universe below [u0].  (Read the binder names from the block you
       are looking at: [kan_nat_of_cone]'s [u2] is a DIFFERENT universe,
       carrying [u1 <= u2].)

   So the restriction is real but it enters at the PACKAGING, not at the
   mathematics: the two passages are formable over a category whose
   objects sit strictly ABOVE its homs, and it is the presheaf and the
   setoid of transformations that refuse there.  That is not inferred
   from the blocks — it is pinned, at one universe setting, by
   formability negatives 8-10 against positive controls 6 and 7 of
   Test/ProbeCoyoneda.v, which differ from the negatives in exactly which
   constant is named.

   Where each pin comes from, and that the two are INDEPENDENT:

     - RHS.  [ConePresheaf@{u0 u1 u2 u3 u4 u5 u}] carries [u0 <= u4], its
       index category's OBJECT universe below its target category's HOM
       universe (a cone's leg family is indexed by the objects of the
       index category and lands in homs of the target).  The index here
       is [Elements K], whose object universe is bounded below by both
       [u] and [u0].  Chaining gives [u <= u0].
     - LHS.  Independently: [KanNat K a] must be an OBJECT of
       [Sets@{u0 _}], hence a [Type@{u0}], and it is a type of natural
       transformations, i.e. of families indexed by [obj[D] : Type@{u}].
       So again [u <= u0].  Negative 9 pins this half on its own.

   The restriction is stated rather than worked around; it is NOT
   introduced by the comparison, it is what each side costs on its own,
   and for the same underlying reason — a set of natural transformations,
   or of cones, is a family indexed by objects, so the objects must fit
   where hom-sets live.  Nothing here is claimed unavoidable, and no
   attempt is made to restate the theorem at a coarser level.

   Two further donor pins are inherited and named so a consumer is not
   surprised.  Instance/Fun.v's [Fun] identifies its source and target
   hom levels ([u0 = u2] in its own block) and demands hom = proof in
   both, so [D, Sets] and [D^op, Sets] pin D's hom and proof levels
   together at [Sets]' carrier level.  Theory/Functor.v's [Compose]
   demands ONE shared hom-and-proof level across its three categories,
   which is what [KanNat]'s assembly spends.  Both pins are recorded in
   Functor/Construction/Postcompose.v's Universes section; neither is
   introduced here.

   AN ENGINEERING FINDING, RECORDED BECAUSE IT COST TIME
   -----------------------------------------------------

   The two inverse laws of [kan_coyoneda] need an [id_right] that the
   corresponding laws of [kan_iso_at] do not, and the reason is not about
   this construction at all: Theory/Natural/Transformation.v defines
   [nat_id]'s component as [fmap[F] id], not as [id].  So the identity of
   a FUNCTOR CATEGORY reindexes, and the goal carries an [∘ id] that must
   be discharged — whereas in [Sets] the identity is
   [setoid_morphism_id] and no such factor appears.  (Neither side closes
   by a bare [reflexivity]: [kan_iso_at]'s laws go through
   [kan_cone_nat_cone], which must itself destruct the sigma object, per
   (2) above.  The contrast is the [id_right], not the tactic.)  The same
   [nat_id] fact is recorded twice in this tree — at
   Functor/Representable.v:319-321, about [repr_induced_id], and at
   Functor/Representable/Functorial.v:239-244, about the comparison with
   [repr_pair_iso] (which is itself declared in
   Functor/Hom/Yoneda/Iso.v:162, not in Functor/Representable.v).  It is
   restated here because a reader comparing the two isomorphism proofs
   below would otherwise take the asymmetry for an accident.

   Strict attempts, measured and refuted
   -------------------------------------

   Every comparison was tried at [eq_refl] first.  SEVEN were REFUTED,
   each with its cause diagnosed, and all seven are pinned as CONVERSION
   negatives in Test/ProbeCoyoneda.v (which also carries the three
   FORMABILITY negatives above and twelve positive controls).  The
   causes, which are three and not seven:

     - REBUILT LAW FIELDS.  [kan_nat_of_cone (kan_cone_of_nat τ) = τ] and
       its component-family and single-component variants.  [Transform]
       and [SetoidMorphism] both carry primitive projections with eta
       conversion (measured, not assumed), so record equality reduces to
       field equality — and the [naturality], [naturality_sym] and
       [proper_morphism] fields of the rebuilt records are this file's
       own lemmas rather than τ's.  `≈` is [crelation]-valued, so there
       is no definitional proof irrelevance to close the gap.  Positive
       control 2 shows the UNDERLYING FUNCTIONS do agree on the nose, so
       the obstruction is located exactly at the proofs.
     - MISSING sigT ETA.  The leg family of
       [kan_cone_of_nat (kan_nat_of_cone ψ)] is [fun j => ψ (`1 j; `2 j)],
       and stdlib [sigT] has no eta rule here — Lib/Foundation.v's
       [Set Primitive Projections] governs this library's own records,
       not [sigT].  This cause is INDEPENDENT of the first: it defeats
       even the bare leg family at a variable object (negative 4), which
       is why [kan_cone_nat_cone] destructs the pair before closing by
       [reflexivity], and positive control 3 is that same statement with
       the pair destructed.
     - THE Δ-BRIDGE [id_right].  Both bridge round trips at the whole
       record.  Here the sigma plays no part and the DATA returns on the
       nose in BOTH directions at a variable object (positive controls 4
       and 5), so the only remaining obstruction is the law field, which
       is rebuilt through the [id_right] described above.

   What DOES hold strictly: the object actions of both functors
   ([kan_nat_obj], [kan_cone_obj]), the identification of the two
   components of the natural isomorphism with the legs of the pointwise
   one ([kan_coyoneda_to_component], [kan_coyoneda_from_component]), the
   leg family of the forward passage read at a pair
   ([kan_cone_of_nat_leg]), the component of the backward passage read
   at an element ([kan_nat_of_cone_component]), and both leg families of
   the Δ bridge ([kan_transform_of_cone_component],
   [kan_cone_of_transform_leg]).

   AXIOMS.  All 46 constants of this module — the 32 named ones plus the
   14 [Program] obligations of the three isomorphism definitions,
   enumerated with [Print Module] per the methodology of docs/AXIOMS.md —
   report "Closed under the global context".  Twelve of them are wired into the
   [print-assumptions] gate of the Makefile; the names were checked
   against the whole tree first and collide with nothing, which matters
   because the gate [Require]s everything into one scope and a later
   [Require] would silently win.

   PRIOR ART, SCOPED TO WHAT WAS SEARCHED
   --------------------------------------

   Theory/Universal/Element/Elements.v is a DIFFERENT theorem over the
   same construction — universal elements are initial objects of the
   category of elements, its eight constants all of the
   [Elements_Initial] family — and is neither used nor generalized here.

   [rg ACone --glob '*.v'] over the tree returns twenty files — the glob
   matters, since the unrestricted [rg ACone] returns forty-nine, the
   difference being CLAUDE.md, the planning ledger and the per-chapter
   coverage JSON.  One (Structure/Cone.v)
   declares the class; two are this file and its probe; one
   (Theory/Diagram/Examples.v) mentions it in PROSE only, in a note about
   a shape match, and constructs no cone.  The remaining sixteen —
   Adjunction/Continuity.v, Construction/Comma/{Creation,Limit}.v,
   Instance/Top/Forgetful.v, Monad/Eilenberg/Moore/Limit.v,
   Structure/{Coequalizer,Limit}.v, Structure/Equalizer/Fork.v,
   Structure/Limit/{Kan/Pointwise,Preservation,Preservation/Separation,
   Product,Weighted}.v, Structure/UniversalProperty/Limit.v,
   Theory/Adamek.v and Theory/Equivalence/Limit.v — are every one of them
   limit- or colimit-related, and none has this shape.  That is a
   statement about that grep and not a survey of the tree.

   NOT DELIVERED
   -------------

     - no presheaf (contravariant) orientation: nothing is stated for
       [PElements P] and the contravariant representable, and the
       transport of the isomorphism along opposites is not performed;
     - no identification of either side with a limit or a Kan extension,
       and in particular no claim that Q is a discrete opfibration or
       that the exercise's bijection is an instance of the pointwise Kan
       formula of Structure/Limit/Kan/Pointwise.v;
     - no naturality in K: only the variable a is varied, K being fixed
       throughout, so the two sides are not exhibited as functors of the
       pair;
     - no statement in [StrictCat] and no Leibniz equality of the two
       functors [KanNat K] and [KanCone K] — [kan_coyoneda] is an
       isomorphism in [D^op, Sets], which is the honest strength;
     - no bijection of the underlying TYPES: both isomorphisms are of
       setoids, and the round trips are up to `≈`;
     - the Δ-reading is NOT upgraded to a naturality statement: [KanDelta]
       is a [SetoidObject] and is never exhibited as a functor
       [D^op ⟶ Sets], so [kan_iso_transform] is pointwise in a and is not
       shown natural.  Only the [ACone] side carries the naturality, which
       is exactly why [ConePresheaf] was taken as primary; the cost is that
       Mac Lane's own phrasing is delivered one strength below the headline. *)

Section Kan.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* The passages and the Δ bridge are built by applying the record
   constructor to named lemmas, so they carry no obligation and stay
   transparent — which is what the [eq_refl] measurements below rest on.
   [Program] is used only for the three isomorphism definitions, and
   there the obligation tactic is set to [idtac] so that the goals arrive
   in a predictable shape rather than partially discharged under
   generated names. *)

#[local] Obligation Tactic := idtac.

(* Explicit spellings of the two [ACone] projections at the data of this
   file.  Both are class projections whose instance argument is found by
   typeclass search, and search cannot see which cone is meant when two
   cones over the same diagram are in scope; naming them here keeps every
   statement below unambiguous. *)

Notation leg psi j :=
  (@vertex_map (Elements K) D _ (Elements_proj K) psi j).

Notation coh psi f :=
  (@cone_coherence (Elements K) D _ (Elements_proj K) psi _ _ f).

(** ** From a map into a representable to a cone *)

(* Cone coherence for the leg family j ↦ τ (`1 j) (`2 j).  A morphism of
   [Elements K] is a D-morphism together with a witness that it carries
   the element; naturality of τ supplies the equation at the D-morphism
   and the carried witness moves the answer onto the target element. *)

Lemma kan_cone_coherence {a : D} (tau : K ⟹ [Hom a,─])
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[tau] (`1 x) (`2 x)
    ≈ transform[tau] (`1 y) (`2 y).
Proof.
  rewrite <- (`2 f).
  exact (naturality[tau] _ _ (`1 f) (`2 x)).
Qed.

Definition kan_cone_of_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[tau] (`1 j) (`2 j))
    (fun x y f => kan_cone_coherence tau f).

(* The leg at a pair is the component of τ evaluated at the element, on
   the nose. *)
Example kan_cone_of_nat_leg {a : D} (tau : K ⟹ [Hom a,─])
        (d : D) (x : K d) :
  leg (kan_cone_of_nat tau) ((d; x) : Elements K) = transform[tau] d x
  := eq_refl.

(** ** From a cone to a map into a representable *)

(* Two `≈`-equal elements over one object of D are DIFFERENT objects of
   [Elements K] — objects are compared by Leibniz equality — but they are
   connected by the morphism whose underlying D-morphism is the identity.
   This is the witness that makes the backward passage possible. *)

Lemma elements_same_cond {d : D} (x y : K d) (H : x ≈ y) :
  fmap[K] (id[d]) x ≈ y.
Proof. now rewrite (elements_id_cond K x). Qed.

Definition elements_same {d : D} (x y : K d) (H : x ≈ y) :
  ((d; x) : Elements K) ~{Elements K}~> (d; y) :=
  (id[d]; elements_same_cond x y H).

(* Respectfulness of a cone's leg family in the ELEMENT argument, derived
   from cone coherence at [elements_same] rather than assumed. *)

Lemma kan_leg_respects {a : D} (psi : ACone a (Elements_proj K))
      {d : D} (x y : K d) (H : x ≈ y) :
  leg psi ((d; x) : Elements K) ≈ leg psi ((d; y) : Elements K).
Proof.
  pose proof (coh psi (elements_same x y H)) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  now rewrite id_left.
Qed.

(* The naturality square of the transformation to be built, in both
   orientations.  Each is cone coherence at the chosen lift of f, whose
   image under the projection is f itself definitionally
   ([Elements_lift_over]). *)

Lemma kan_nat_naturality {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  f ∘ leg psi ((d; x) : Elements K)
    ≈ leg psi ((d'; fmap[K] f x) : Elements K).
Proof. exact (coh psi (Elements_lift K x f)). Qed.

Lemma kan_nat_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {d d' : D} (f : d ~> d') (x : K d) :
  leg psi ((d'; fmap[K] f x) : Elements K)
    ≈ f ∘ leg psi ((d; x) : Elements K).
Proof. symmetry; exact (coh psi (Elements_lift K x f)). Qed.

Definition kan_nat_of_cone {a : D} (psi : ACone a (Elements_proj K)) :
  K ⟹ [Hom a,─] :=
  @Build_Transform D Sets K ([Hom a,─])
    (fun d => @Build_SetoidMorphism (K d) _ (@hom D a d) _
                (fun x => leg psi ((d; x) : Elements K))
                (fun x y H => kan_leg_respects psi x y H))
    (fun d d' f => kan_nat_naturality psi f)
    (fun d d' f => kan_nat_naturality_sym psi f).

(* The component at d, evaluated at an element, is the leg at the pair,
   on the nose. *)
Example kan_nat_of_cone_component {a : D} (psi : ACone a (Elements_proj K))
        (d : D) (x : K d) :
  transform[kan_nat_of_cone psi] d x = leg psi ((d; x) : Elements K)
  := eq_refl.

(** ** The two round trips *)

(* Both hold at `≈` and neither holds at [eq_refl]; the negatives are
   pinned in Test/ProbeCoyoneda.v.  The cone side must destruct the pair
   first, stdlib [sigT] having no eta rule here. *)

Lemma kan_nat_cone_nat {a : D} (tau : K ⟹ [Hom a,─]) :
  kan_nat_of_cone (kan_cone_of_nat tau) ≈ tau.
Proof. intros d x; reflexivity. Qed.

Lemma kan_cone_nat_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_nat (kan_nat_of_cone psi)) psi.
Proof. intros [d x]; reflexivity. Qed.

(** ** The two sides as functors of the apex *)

(* The left-hand side is a PURE ASSEMBLY of in-tree parts: the covariant
   hom-functor of the functor category [D, Sets] taken at K, composed
   with the Yoneda embedding of D.  It is a plain [Definition] with no
   obligations, so all three functor laws are inherited. *)

Definition KanNat : D^op ⟶ Sets :=
  Curried_Hom ([D, Sets]) K ◯ Curried_Hom D.

(* The right-hand side is Structure/Cone.v's presheaf of cones, taken at
   the elements projection.  Also pure reuse. *)

Definition KanCone : D^op ⟶ Sets :=
  ConePresheaf (Elements_proj K).

(* Both object actions are the setoids the exercise names, on the nose. *)

Example kan_nat_obj (a : D) :
  KanNat a = {| carrier   := K ~{[D, Sets]}~> [Hom a,─]
              ; is_setoid := @homset ([D, Sets]) K [Hom a,─] |}
  := eq_refl.

Example kan_cone_obj (a : D) :
  KanCone a = {| carrier   := ACone a (Elements_proj K)
               ; is_setoid := AConeEquiv a (Elements_proj K) |}
  := eq_refl.

(** ** The pointwise isomorphism *)

Program Definition kan_iso_at (a : D) : KanNat a ≅[Sets] KanCone a := {|
  to   := {| morphism := fun tau => kan_cone_of_nat tau |};
  from := {| morphism := fun psi => kan_nat_of_cone psi |}
|}.
Next Obligation. intros a tau tau' H [d z]; exact (H d z). Qed.
Next Obligation. intros a psi psi' H d z; exact (H (d; z)). Qed.
Next Obligation. intros a psi; apply kan_cone_nat_cone. Qed.
Next Obligation. intros a tau; apply kan_nat_cone_nat. Qed.

(** ** Naturality in the apex *)

(* The reindexing on both sides is precomposition of every leg (resp. of
   every component's value) with g, so all four naturality obligations
   close by [reflexivity].  The two INVERSE laws do not, and the reason
   is not this construction: [nat_id]'s component is [fmap[F] id] rather
   than [id] (Theory/Natural/Transformation.v), so the identity of a
   functor category reindexes and leaves an [∘ id] behind — see the
   engineering note in the header.  In [Sets] the identity is
   [setoid_morphism_id] and [kan_iso_at]'s corresponding obligations need
   no such step. *)

Program Definition kan_coyoneda : KanNat ≅[[D^op, Sets]] KanCone := {|
  to   := {| transform := fun a => to   (kan_iso_at a) |};
  from := {| transform := fun a => from (kan_iso_at a) |}
|}.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g tau [d z]; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a a' g psi d z; reflexivity. Qed.
Next Obligation. intros a psi [d z]; simpl; now rewrite id_right. Qed.
Next Obligation. intros a tau d z; simpl; now rewrite id_right. Qed.

(* The upgrade is an upgrade: the components ARE the pointwise legs. *)

Example kan_coyoneda_to_component (a : D) :
  transform[to kan_coyoneda] a = to (kan_iso_at a) := eq_refl.

Example kan_coyoneda_from_component (a : D) :
  transform[from kan_coyoneda] a = from (kan_iso_at a) := eq_refl.

(** ** The literal Δ-reading *)

(* Mac Lane writes the right-hand side as Nat(Δa, Q).  A [Transform] out
   of the constant functor is the same leg family as an [ACone] with the
   coherence law read against [fmap[Δa] f = id]; the passages below cost
   exactly one [id_right] each. *)

Lemma kan_transform_naturality {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ leg psi x
    ≈ leg psi y ∘ fmap[Δ[Elements K](a)] f.
Proof. rewrite id_right; exact (coh psi f). Qed.

Lemma kan_transform_naturality_sym {a : D} (psi : ACone a (Elements_proj K))
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  leg psi y ∘ fmap[Δ[Elements K](a)] f
    ≈ fmap[Elements_proj K] f ∘ leg psi x.
Proof. rewrite id_right; symmetry; exact (coh psi f). Qed.

Definition kan_transform_of_cone {a : D}
           (psi : ACone a (Elements_proj K)) :
  Δ[Elements K](a) ⟹ Elements_proj K :=
  @Build_Transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
    (fun j => leg psi j)
    (fun x y f => kan_transform_naturality psi f)
    (fun x y f => kan_transform_naturality_sym psi f).

Lemma kan_cone_of_transform_coherence {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K)
      {x y : Elements K} (f : x ~{Elements K}~> y) :
  fmap[Elements_proj K] f ∘ transform[theta] x ≈ transform[theta] y.
Proof.
  rewrite <- (id_right (transform[theta] y)).
  exact (naturality[theta] _ _ f).
Qed.

Definition kan_cone_of_transform {a : D}
           (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  ACone a (Elements_proj K) :=
  @Build_ACone (Elements K) D a (Elements_proj K)
    (fun j => transform[theta] j)
    (fun x y f => kan_cone_of_transform_coherence theta f).

Example kan_transform_of_cone_component {a : D}
        (psi : ACone a (Elements_proj K)) (j : Elements K) :
  transform[kan_transform_of_cone psi] j = leg psi j := eq_refl.

Example kan_cone_of_transform_leg {a : D}
        (theta : Δ[Elements K](a) ⟹ Elements_proj K) (j : Elements K) :
  leg (kan_cone_of_transform theta) j = transform[theta] j := eq_refl.

Lemma kan_cone_transform_cone {a : D} (psi : ACone a (Elements_proj K)) :
  @equiv _ (AConeEquiv a (Elements_proj K))
         (kan_cone_of_transform (kan_transform_of_cone psi)) psi.
Proof. intro j; reflexivity. Qed.

Lemma kan_transform_cone_transform {a : D}
      (theta : Δ[Elements K](a) ⟹ Elements_proj K) :
  kan_transform_of_cone (kan_cone_of_transform theta) ≈ theta.
Proof. intro j; reflexivity. Qed.

(* The setoid of Δ-transformations, named so the two isomorphisms below
   can mention it without repeating the packaging. *)

Definition KanDelta (a : D) : SetoidObject :=
  {| carrier   := Δ[Elements K](a) ~{[Elements K, D]}~> Elements_proj K
   ; is_setoid := @homset ([Elements K, D])
                          Δ[Elements K](a) (Elements_proj K) |}.

Program Definition kan_cone_transform_iso (a : D) :
  KanCone a ≅[Sets] KanDelta a := {|
  to   := {| morphism := fun psi   => kan_transform_of_cone psi |};
  from := {| morphism := fun theta => kan_cone_of_transform theta |}
|}.
Next Obligation. intros a psi psi' H j; exact (H j). Qed.
Next Obligation. intros a th th' H j; exact (H j). Qed.
Next Obligation. intros a th; apply kan_transform_cone_transform. Qed.
Next Obligation. intros a psi; apply kan_cone_transform_cone. Qed.

(* Mac Lane's own phrasing: Nat(K, D(a,−)) ≅ Nat(Δa, Q). *)

Definition kan_iso_transform (a : D) : KanNat a ≅[Sets] KanDelta a :=
  iso_compose (kan_cone_transform_iso a) (kan_iso_at a).

End Kan.
