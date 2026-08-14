(** * Open(X) and the presheaf of continuous real-valued functions *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.2, printed p. 35 (PDF p. 45) — maclane:II.2:construction7
   Book:      Riehl, "Category Theory in Context", Example 1.3.7,
              clauses (iii)–(v), printed pp. 18–19 (PDF pp. 38–39)
   Book:      Fong–Spivak, "Seven Sketches in Compositionality", §7.3.2,
              printed p. 236 (PDF p. 248)
   nLab:      https://ncatlab.org/nlab/show/presheaf
   nLab:      https://ncatlab.org/nlab/show/sheaf
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   Mac Lane's §II.2 example: for a topological space X the open sets,
   ordered by inclusion, form a thin category, and assigning to each open U
   the set of continuous real-valued functions on U — with restriction along
   an inclusion as the arrow action — is a contravariant functor into Set,
   the standard first example of a presheaf (and, classically, of a sheaf).
   Riehl's Example 1.3.7 spreads the story across three clauses: (iii)
   the open-set functor with preimage as arrow action, together with its
   closed-set companion — both already in tree as Instance/Top/Closed.v's
   [OpensF], [ClosedsF] and the complementation natural isomorphism
   [complement_natural], with [Opens X] the thin inclusion category
   itself; (iv) Spec, the prime spectrum of a commutative ring with the
   Zariski topology, which stays OUT OF SCOPE here (design note 7); and
   (v) the sheaf of continuous real-valued functions as the typifying
   presheaf.  This file delivers clause (v), Mac Lane's construction:

     [ContinuousPresheaf X : Presheaf (Opens X) Sets]

   sending an open U to the setoid of continuous maps from U (as a subspace)
   to the real line, and an inclusion V ⊆ U to restriction, which is
   precomposition with the continuous inclusion of subspaces.

   Seven Sketches §7.3.2 builds the same [Opens X] preorder and adds its
   ROLE: it is the site over which presheaves and sheaves on a space are
   defined.  That role is visible here in the type of [ContinuousPresheaf];
   the sheaf CONDITION is deliberately not stated (design note 4).

   Contents:
     - [R_Top]: the real line as a topological space (metric topology)
     - [OpenSub U]: an open set as a subspace, with [sub_incl] and the
       restriction morphisms [sub_map]
     - [ContinuousPresheaf X]: the presheaf of continuous real-valued
       functions, with constant sections as inhabitants
     - [OpenSub_whole_iso], [global_sections_iso]: the subspace on the
       whole-space open is the space itself, and its sections are the
       continuous maps X → R — "Γ(X, C(−,ℝ)) = C(X,ℝ)"

   Design:

   1. AN OPEN SUBSPACE IS A SPACE WHOSE OPENS CARRY PROPERNESS.  The
      carrier of [OpenSub U] is the sigma type { x : X & `1 U x } compared
      on first components, and a predicate on it is open when (a) it
      respects that comparison and (b) its extension along the projection —
      the predicate "some membership witness lands in V" — is open in X.
      Conjunct (a) is not decoration: the membership component of a point
      of the subspace is proof DATA, and a bare predicate could distinguish
      two witnesses of the same point, which no topology on the subspace
      setoid may do.  This is the same move Instance/Top.v makes for
      [Discrete_Top], whose opens are EXACTLY the respectful predicates.
      Because U itself is open, the extension-openness conjunct gives the
      standard subspace topology, and the identification is machine-checked
      rather than asserted: the opens of [OpenSub U] correspond to the
      opens of X contained in U ([sub_ext_contained], [sub_ext_recovers],
      [sub_open_of_open], [sub_ext_of_open] below).

   2. THE REAL LINE IS A BALL SPACE.  [R_Top] is Instance/Top/Interval.v's
      [BallTop] applied to R with distance [Rabs (x − y)] — the metric
      topology, with the radius of each interior ball carried as DATA, so
      the union axiom is discharged without any choice principle.  The
      interval file stops at [0,1] because paths need endpoints; the line
      itself is the three-lemma instance below.

   3. RESTRICTION IS PRECOMPOSITION.  An inclusion V ⊆ U induces a
      continuous map of subspaces [sub_map : OpenSub V ~> OpenSub U], and
      the presheaf's arrow action is precomposition with it.  Functoriality
      is thereby inherited from the category laws of [Top] — up to the
      subspace setoid's indifference to membership witnesses — rather than
      proved against a bespoke notion of "restriction of a function".

   4. THE SHEAF CONDITION IS NOT STATABLE HERE.  Two independent
      obstructions, and the universe one bites first: Theory/Sheaf.v's
      [Sheaf] class carries its own inferred universe signature, which
      constrains its presheaf argument exactly the way the un-annotated
      [Presheaf] alias used to, so [Sheaf (ContinuousPresheaf X)] is a
      universe inconsistency, not a statement a reader could weaken — and
      the still-minimized [Presheaves] alias likewise cannot receive
      [ContinuousPresheaf] as an object.  Structurally, even at shared
      levels, the class records a per-object, per-leg gluing condition
      over the single covering family its [Site] supplies, which
      Theory/Sheaf/Category.v discloses as vacuous beyond subsingleton
      fibres — a donor erratum whose matching-family re-founding is
      deferred with sheafification (ledger item 1).  That re-founding
      will need the same universe generality [Presheaf] now has;
      verifying gluing for this presheaf belongs there.  What Mac Lane's
      p. 35 example asserts is the presheaf, which is delivered in full.
      The smooth-manifold variant (C^∞ functions on a manifold) is
      likewise out of tree: there are no manifolds here, and the example
      would need them before it needs anything categorical.

   5. WHAT IT COSTS.  This is the third file in the tree to import
      Coq.Reals (after Instance/Top/Interval.v and its consumer
      Instance/Top/FundamentalGroupoid.v), and it inherits the axiom set
      of the standard library's construction of R — principally
      [ClassicalDedekindReals.sig_forall_dec] and
      [FunctionalExtensionality.functional_extensionality_dep] — exactly
      as docs/AXIOMS.md's "Stdlib axioms" section documents for the other
      two; the section enumerates this file alongside them.  Constants
      that never touch R (the subspace machinery) remain closed under the
      global context.

   6. UNIVERSES.  [Top]'s hom-sets live strictly above its points
      (Instance/Top.v's header), so a setoid of sections is an object of
      Sets one level up — the same placement Instance/Top/Forgetful.v
      gives [Top_Forget] and Instance/Top/Closed.v gives [OpensF].  The
      polymorphic [Sets] absorbs this silently: [ContinuousPresheaf X]
      lands in the Sets whose objects are section setoids, not the Sets
      whose objects are point setoids.

   7. SPEC STAYS OUT OF SCOPE.  Riehl's clause (iv) is the prime-spectrum
      functor from commutative rings (opposite) to spaces, a ring going to
      its set of prime ideals under the Zariski topology.  The tree now
      has commutative rings (Instance/Rng.v's [CRng]) and, with this
      file, enough topology to state the target — but no ideals, no
      primality, and no spectrum construction: Spec is a development of
      its own (prime ideals as setoid predicates, Zariski opens generated
      by ring elements, contravariant functoriality along ring maps), not
      an increment of the presheaf example, and no in-tree issue currently
      tracks it. *)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.
Require Import Category.Instance.Top.Interval.
Require Import Category.Theory.Sheaf.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The real line as a topological space *)

Definition R_equiv (x y : R) : Type := x = y.

Lemma R_equiv_Equivalence : Equivalence R_equiv.
Proof.
  constructor; unfold R_equiv.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition R_Setoid : Setoid R := {|
  equiv        := R_equiv;
  setoid_equiv := R_equiv_Equivalence
|}.

Definition R_Object : SetoidObject := {|
  carrier   := R;
  is_setoid := R_Setoid
|}.

(* Registered for downstream setoid tactics at real points; the proofs in
   this file use explicit terms instead. *)
#[export] Existing Instance R_equiv_Equivalence.

Lemma BS_R_zero (x y : R_Object) : x ≈ y → Rabs (x - y) = 0.
Proof.
  intro H.
  assert (Heq : x = y :> R) by exact H.
  Rlin.
Qed.

Lemma BS_R_sym (x y : R_Object) : Rabs (x - y) = Rabs (y - x).
Proof. Rlin. Qed.

Lemma BS_R_tri (x y z : R_Object) :
  Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof. Rlin. Qed.

Definition BS_R : BallSpace := {|
  ball_carrier := R_Object;
  bdist        := fun x y => Rabs (x - y);
  bdist_zero   := BS_R_zero;
  bdist_sym    := BS_R_sym;
  bdist_tri    := BS_R_tri
|}.

(* The real line with the metric topology (design note 2). *)
Definition R_Top : TopSpace := BallTop BS_R.

(** ** An open set as a subspace *)

Section OpenSubspace.

Context (X : TopSpace) (U : OpenSet X).

(* Points of the subspace: a point of X together with a membership
   witness.  The setoid compares first components only, so the witness is
   invisible to everything downstream — the discipline that design note 1
   then forces on the opens. *)
Definition SubCar : Type := { x : X & `1 U x }.

Definition sub_equiv (s t : SubCar) : Type := `1 s ≈ `1 t.

Lemma sub_equiv_Equivalence : Equivalence sub_equiv.
Proof.
  constructor; unfold sub_equiv.
  - intro s; reflexivity.
  - intros s t H; now symmetry.
  - intros s t u H1 H2; now transitivity (`1 t).
Qed.

Definition Sub_Setoid : Setoid SubCar := {|
  equiv        := sub_equiv;
  setoid_equiv := sub_equiv_Equivalence
|}.

Definition SubOb : SetoidObject := {|
  carrier   := SubCar;
  is_setoid := Sub_Setoid
|}.

(* The extension of a subspace predicate along the projection: it holds at
   a point of X when some membership witness lands in V. *)
Definition sub_ext (V : SubCar → Type) : X → Type :=
  fun x => { h : `1 U x & V (x; h) }.

(* Openness in the subspace: respect for the point comparison, plus
   openness of the extension in X (design note 1). *)
Definition sub_open (V : SubCar → Type) : Type :=
  (∀ (x y : X) (hx : `1 U x) (hy : `1 U y),
      x ≈ y → V (x; hx) → V (y; hy)) ∧
  IsOpen X (sub_ext V).

Lemma sub_respects (V W : SubCar → Type) :
  (∀ s, V s ↔ W s) → sub_open V → sub_open W.
Proof.
  intros HVW [Vprop Vext]; split.
  - intros x y hx hy Hxy w.
    exact (fst (HVW (y; hy)) (Vprop x y hx hy Hxy (snd (HVW (x; hx)) w))).
  - apply (open_respects X (sub_ext V)); [ | exact Vext ].
    intro x; split.
    + intros [h v]; exact (h; fst (HVW (x; h)) v).
    + intros [h w]; exact (h; snd (HVW (x; h)) w).
Qed.

Lemma sub_proper (V : SubCar → Type) :
  sub_open V → ∀ s t : SubOb, s ≈ t → V s → V t.
Proof.
  intros [Vprop _] [x hx] [y hy] Hst v.
  exact (Vprop x y hx hy Hst v).
Qed.

Lemma sub_union (I : Type) (V : I → (SubCar → Type)) :
  (∀ i, sub_open (V i)) → sub_open (fun s => { i : I & V i s }).
Proof.
  intro HV; split.
  - intros x y hx hy Hxy [i v].
    exact (i; fst (HV i) x y hx hy Hxy v).
  - apply (open_respects X (fun x => { i : I & sub_ext (V i) x })).
    + intro x; split.
      * intros [i [h v]]; exact (h; (i; v)).
      * intros [h [i v]]; exact (i; (h; v)).
    + apply open_union.
      intro i; exact (snd (HV i)).
Qed.

Lemma sub_whole : sub_open (fun _ => poly_unit).
Proof.
  split.
  - intros x y hx hy Hxy w; exact ttt.
  - apply (open_respects X (`1 U)); [ | exact (`2 U) ].
    intro x; split.
    + intro h; exact (h; ttt).
    + intros [h _]; exact h.
Qed.

Lemma sub_inter (V W : SubCar → Type) :
  sub_open V → sub_open W → sub_open (fun s => V s ∧ W s).
Proof.
  intros [Vprop Vext] [Wprop Wext]; split.
  - intros x y hx hy Hxy [v w].
    exact (Vprop x y hx hy Hxy v, Wprop x y hx hy Hxy w).
  - apply (open_respects X (fun x => sub_ext V x ∧ sub_ext W x)).
    + intro x; split.
      * intros [[h v] [k w]].
        exact (h; (v, Wprop x x k h (reflexivity _) w)).
      * intros [h [v w]]; exact ((h; v), (h; w)).
    + exact (open_inter X (sub_ext V) (sub_ext W) Vext Wext).
Qed.

(* The subspace, as a topological space. *)
Definition OpenSub : TopSpace := {|
  top_carrier   := SubOb;
  IsOpen        := sub_open;
  open_respects := sub_respects;
  open_proper   := sub_proper;
  open_union    := sub_union;
  open_whole    := sub_whole;
  open_inter    := sub_inter
|}.

(* The inclusion of the subspace, continuous because the preimage of an
   open W of X is its intersection with U, transported to the subspace. *)
Program Definition sub_incl : ContinuousMorphism OpenSub X := {|
  continuous_map := {| morphism := fun s : SubCar => `1 s |}
|}.
Next Obligation.
  intros s t Hst; exact Hst.
Qed.
Next Obligation.
  intros W HW; split.
  - intros x y hx hy Hxy w.
    exact (open_proper X W HW x y Hxy w).
  - apply (open_respects X (fun x => `1 U x ∧ W x)).
    + intro x; split.
      * intros [h w]; exact (h; w).
      * intros [h w]; exact (h, w).
    + exact (open_inter X (`1 U) W (`2 U) HW).
Qed.

(* The identification promised by design note 1: subspace opens are
   exactly the opens of X contained in U, pulled back along the
   projection.  Forward: the extension of a subspace open is an open of X
   ([sub_open]'s second conjunct), it is contained in U, and — by the
   properness conjunct — the open it came from is pointwise equivalent to
   its pullback.  Backward: the pullback of any open of X contained in U
   is a subspace open, and its extension recovers the original. *)

Lemma sub_ext_contained (V : SubCar → Type) (x : X) :
  sub_ext V x → `1 U x.
Proof.
  intros [h _]; exact h.
Qed.

Lemma sub_ext_recovers (V : SubCar → Type) :
  sub_open V → ∀ (x : X) (h : `1 U x), V (x; h) ↔ sub_ext V x.
Proof.
  intros [Vprop _] x h; split.
  - intro v; exact (h; v).
  - intros [k v]; exact (Vprop x x k h (reflexivity _) v).
Qed.

Lemma sub_open_of_open (W : X → Type) :
  IsOpen X W → (∀ x : X, W x → `1 U x) →
  sub_open (fun s => W (`1 s)).
Proof.
  intros HW Hsub; split.
  - intros x y hx hy Hxy w; exact (open_proper X W HW x y Hxy w).
  - apply (open_respects X W); [ | exact HW ].
    intro x; split.
    + intro w; exact (Hsub x w; w).
    + intros [h w]; exact w.
Qed.

Lemma sub_ext_of_open (W : X → Type)
  (Hsub : ∀ x : X, W x → `1 U x) (x : X) :
  sub_ext (fun s => W (`1 s)) x ↔ W x.
Proof.
  split.
  - intros [h w]; exact w.
  - intro w; exact (Hsub x w; w).
Qed.

End OpenSubspace.

Arguments SubCar {X} U.
Arguments sub_ext {X} U V x.
Arguments sub_open {X} U V.
Arguments OpenSub {X} U.
Arguments sub_incl {X} U.

(* Registered for downstream setoid tactics at subspace points, as with
   [R_equiv_Equivalence] above. *)
#[export] Existing Instance sub_equiv_Equivalence.

(** ** Restriction along an inclusion *)

Section Restriction.

Context {X : TopSpace} (V U : OpenSet X).
Context (i : ∀ x : X, `1 V x → `1 U x).

(* An inclusion of opens induces a continuous map of subspaces: transport
   the membership witness.  Continuity re-runs the design-note-1
   bookkeeping: properness of the preimage is properness of the source
   open, and its extension is (V ∩ extension), open in X. *)
Program Definition sub_map : ContinuousMorphism (OpenSub V) (OpenSub U) := {|
  continuous_map :=
    {| morphism := fun s : SubCar V => (`1 s; i (`1 s) (`2 s)) |}
|}.
Next Obligation.
  intros s t Hst; exact Hst.
Qed.
Next Obligation.
  intros P [Pprop Pext]; split.
  - intros x y hx hy Hxy p.
    exact (Pprop x y (i x hx) (i y hy) Hxy p).
  - apply (open_respects X (fun x => `1 V x ∧ sub_ext U P x)).
    + intro x; split.
      * intros [h [k p]].
        exact (h; Pprop x x k (i x h) (reflexivity _) p).
      * intros [h p]; exact (h, (i x h; p)).
    + exact (open_inter X (`1 V) (sub_ext U P) (`2 V) Pext).
Qed.

End Restriction.

(** ** The presheaf of continuous real-valued functions *)

(* The setoid of sections over an open: continuous maps from the subspace
   to the real line, compared pointwise — [Top]'s own hom-setoid, packaged
   as an object of Sets (design note 6). *)
Definition SectionsOb (X : TopSpace) (U : OpenSet X) : obj[Sets] := {|
  carrier   := ContinuousMorphism (OpenSub U) R_Top;
  is_setoid := ContinuousMorphism_Setoid
|}.

(* Mac Lane's presheaf: U ↦ continuous real-valued functions on U,
   inclusions to restriction, i.e. precomposition with [sub_map].  The
   Opens-side hom-setoid is trivial, and honestly so: two parallel
   inclusions may differ as functions on witnesses, but the subspace
   setoid does not see witnesses, so their restrictions agree. *)
Program Definition ContinuousPresheaf (X : TopSpace) :
  Presheaf (Opens X) Sets := {|
  fobj := fun U => SectionsOb X U;
  fmap := fun U V (f : U ~{(Opens X)^op}~> V) =>
    {| morphism := fun s : ContinuousMorphism (OpenSub U) R_Top =>
         top_compose s (sub_map V U f) |}
|}.
Next Obligation.
  (* precomposition respects pointwise equality of sections *)
  intros X U V f s t Hst p; exact (Hst (sub_map V U f p)).
Qed.
Next Obligation.
  (* any two parallel inclusions restrict identically *)
  intros X U V f g _ s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
Next Obligation.
  (* restriction along the identity inclusion is the identity *)
  intros X U s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
Next Obligation.
  (* restriction along a composite is the composite of restrictions *)
  intros X U V W f g s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.

(** ** Constant sections *)

(* Every hom-setoid of the presheaf is inhabited: the constant functions
   are continuous, because the preimage of an open is constantly true or
   constantly false — [open_const]'s union trick, run through the subspace
   packaging. *)
Program Definition const_section (X : TopSpace) (U : OpenSet X) (c : R) :
  ContinuousMorphism (OpenSub U) R_Top := {|
  continuous_map := {| morphism := fun _ => c |}
|}.
Next Obligation.
  intros X U c s t Hst; reflexivity.
Qed.
Next Obligation.
  intros X U c W HW; split.
  - intros x y hx hy Hxy w; exact w.
  - apply (open_respects X (fun x => `1 U x ∧ W c)).
    + intro x; split.
      * intros [h w]; exact (h; w).
      * intros [h w]; exact (h, w).
    + exact (open_inter X (`1 U) (fun _ => W c) (`2 U) (open_const X (W c))).
Qed.

(* Restriction of a constant is the constant — the presheaf's arrow action
   computes on the nose here. *)
Example const_restrict (X : TopSpace) (U V : OpenSet X)
  (f : U ~{(Opens X)^op}~> V) (c : R) :
  fmap[ContinuousPresheaf X] f (const_section X U c) ≈ const_section X V c.
Proof.
  intro p; reflexivity.
Qed.

(** ** Global sections *)

(* The whole space, as an object of [Opens X]. *)
Definition whole_open (X : TopSpace) : OpenSet X :=
  ((fun _ => poly_unit); open_whole X).

(* The subspace on the whole-space open is the space itself: the inclusion
   is an isomorphism of [Top], the inverse adjoining the trivial witness. *)
Program Definition OpenSub_whole_iso (X : TopSpace) :
  OpenSub (whole_open X) ≅[Top] X := {|
  to   := sub_incl (whole_open X);
  from := {| continuous_map := {| morphism := fun x : X => (x; ttt) |} |}
|}.
Next Obligation.
  intros X x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros X P [Pprop Pext].
  apply (open_respects X (sub_ext (whole_open X) P)); [ | exact Pext ].
  intro x; split.
  - intros [h p].
    exact (Pprop x x h ttt (reflexivity _) p).
  - intro p; exact (ttt; p).
Qed.
Next Obligation.
  intros X x; simpl; reflexivity.
Qed.
Next Obligation.
  intros X s; simpl.
  exact (reflexivity (`1 s)).
Qed.

(* The continuous maps X → R, as an object of Sets. *)
Definition Maps_to_R (X : TopSpace) : obj[Sets] := {|
  carrier   := ContinuousMorphism X R_Top;
  is_setoid := ContinuousMorphism_Setoid
|}.

(* Sections over the whole space ARE the continuous real-valued functions
   on X — the "Γ(X, C(−,ℝ)) = C(X,ℝ)" sanity theorem, an isomorphism of
   section setoids in Sets by conjugation with [OpenSub_whole_iso]. *)
Program Definition global_sections_iso (X : TopSpace) :
  SectionsOb X (whole_open X) ≅[Sets] Maps_to_R X := {|
  to   := {| morphism := fun s =>
               top_compose s (from (OpenSub_whole_iso X)) |};
  from := {| morphism := fun m =>
               top_compose m (to (OpenSub_whole_iso X)) |}
|}.
Next Obligation.
  intros X s t Hst x; exact (Hst (x; ttt)).
Qed.
Next Obligation.
  intros X m n Hmn s; exact (Hmn (`1 s)).
Qed.
Next Obligation.
  intros X m x; simpl; reflexivity.
Qed.
Next Obligation.
  intros X s p; simpl.
  apply (proper_morphism (continuous_map s)).
  exact (reflexivity (`1 p)).
Qed.
