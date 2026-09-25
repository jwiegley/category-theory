Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Spaces with Prop-valued opens *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, book p. 132 (PDF p. 141), read from the page image: the
     category Top and its faithful underlying-set functor G : Top → Set
     (catalog id maclane:V.9:construction1)
   Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
     Definition 7.25, printed p. 234 (PDF p. 246): a topology is a set of
     subsets containing the whole set and closed under binary intersections
     and under unions of families indexed by any set, as the catalogue
     under doc/plan/books summarizes it (that book was not consulted)
   nLab: https://ncatlab.org/nlab/show/Top
   nLab: https://ncatlab.org/nlab/show/topological+space
   nLab: https://ncatlab.org/nlab/show/initial+topology

   BACKGROUND.  A topology on a set is a family of its subsets, so a
   type-theoretic encoding has to decide what a subset is.  Instance/Top.v
   takes a subset of the points to be a Type-valued predicate at the
   points' universe [o], and its header (point 2) draws the consequence:
   the predicate on predicates [IsOpen] lives above the points, and
   [Continuous], which quantifies over the opens of the codomain, puts the
   hom-sets of [Top@{h o}] strictly above them, [o < h].  Three
   measurements downstream trace back to that one choice.
     - Instance/Top/Forgetful.v: the underlying-set functor cannot land in
       [Sets@{o so}], the Sets whose objects ARE the point setoids; it
       lands in the lifted [Sets@{h so}], so no [Adjunction] record joins
       it to a functor out of [Sets@{o so}] (that file's header).
     - Test/ProbeStoneCech455.v's N6: [ContinuousMorphism X Y] ascribed at
       [Type@{o}] is refused, and Instance/Top/StoneCech.v's header traces
       the refutation of [CompHaus]'s completeness under [IEM] to the
       homs sitting above the points.
     - Mac Lane's subspace predicate, "V is the preimage of an open of X",
       quantifies over the opens of X; over [Top] it is refused at
       [Type@{o}] and lives one universe up (Instance/Top/Subspace/
       TypeValued.v's [tsub_open]).
   The standard way out is impredicativity: a Prop-valued predicate on
   Prop-valued predicates, and a quantification over all the opens of a
   space, are again propositions.  That is this file's encoding.  Opens are
   predicates [pt_carrier X → Prop], [POpen X] is a predicate on them, and
   continuity [PCont] is a proposition, so a continuous map [PMor X Y] is a
   setoid map with a proof attached and lives at the points' universe,
   exactly as a [Sets] arrow does.  The subspace predicate is then an
   ordinary proposition and the subspace an ordinary [PTop@{o}]
   (Instance/Top/Subspace.v's [PSub], with an empty constraint block), and
   the underlying-set functor [PForget] lands in [Sets@{o so}] itself, so
   Mac Lane's sliced adjunctions of §V.9 are formable as [Adjunction]
   records (Instance/Top/Subspace.v).  What Prop costs is the usual
   restriction on eliminating a proof into data: membership in an open
   carries no computational witness, [ex] where Instance/Top.v has a
   dependent sum; nothing in this file or in Instance/Top/Subspace.v
   eliminates membership into data.

   PROVENANCE.  This file is #1328's item 1, "a Prop-valued
   topological-space record and category, with homs at the points'
   universe", landed under #457 by the maintainer's decision of 2026-09-24
   at the path #1328 suggested.  It sits beside Instance/Top.v, not in its
   place: [Top] and its consumers are unchanged.  What stays for #1328:
   [PCompHaus] (its suggested Instance/Top/Prop/CompHaus.v), the comparison
   functors between [Top] and [PTopCat] (item 2), the limit structure the
   adjoint functor theorems need, products and completeness (item 3; its
   equalizers and coequalizers are Instance/Top/Subspace.v's
   [PTop_HasEqualizers] and [PTop_HasCoequalizers]), and the re-run of
   #455's refutations against this encoding (item 4).  CORRECTION
   (#458): item 3 is delivered for [PTopCat] and item 4 for its
   completeness and cocompleteness: Instance/Top/Complete.v builds its
   products ([PTop_HasIndexedProducts]) and proves it complete
   ([PTop_Complete]), Instance/Top/Cocomplete.v builds its coproducts
   ([PTop_HasIndexedCoproducts]) and proves it cocomplete
   ([PTop_Cocomplete]), both at every shape universe at or below the
   points', and Instance/Top/Complete/Refutations.v and
   Instance/Top/Cocomplete/Refutations.v refute both above the points
   under informative excluded middle; [PCompHaus], the comparison
   functors and the rest of item 4 stay for #1328.  The
   record completes Test/ProbeStoneCech455.v's control [p455_TopP], which
   has a union axiom only, in form (a) below: it adds the other four
   axioms and restates the union axiom as (b).  Instance/Top/StoneCech.v's
   header cites that control as the encoding's first measurement.

   THE UNION AXIOM, MEASURED BOTH WAYS.  Two statements of "arbitrary
   unions" are available for Prop-valued opens:
     (a) over an index type at the points' universe,
         [∀ (I : Type@{o}) (U : I → X → Prop), (∀ i, POpen (U i)) →
          POpen (fun x => ex (fun i => U i x))], [p455_TopP]'s form;
     (b) over a family of opens given as a Prop-valued predicate on
         predicates, [∀ F, (∀ U, F U → POpen U) →
          POpen (fun x => ex (fun U => F U /\ U x))], this file's
         [popen_union].
   Both were compiled, in a scratch file carrying this file,
   Instance/Top/Subspace.v and a copy of the record with (a) in place of
   (b).  Under (a) the subspace's union is witnessed by the union of all
   the witnessing opens, indexed by pairs (index, open of X); that index
   type reads back at [Type@{max(Set+1,o)}] (About), and used as a union
   index at [o := Set] it is refused, "Cannot enforce Set+1 <= Set", while
   under a declared [Set < o] it is accepted; so the subspace built from
   that pair-indexed witness, the only route tried, carries [Set < o].
   Deriving (b) from (a) needs the index [{ U | F U }] and is refused at
   [Set] the same way, accepted under [Set < o].  Under (b)
   Instance/Top/Subspace.v's [PSub] is accepted at [PTop@{Set}] (the
   same scratch file, an empty constraint block), and (a) follows at
   EVERY index universe:
   [popen_union_indexed@{o i}], whose constraint block is empty.  (b) is
   therefore the field, for three reasons: it closes the opens under the
   union of any family of opens, with no index type to bound; it implies
   (a) at every index universe, so Seven Sketches' unions over an index
   set hold as stated (Instance/Top/Subspace.v's [ex732_part2] uses
   them); and it frees the subspace of the [Set < o] bound.  Nothing here
   shows (b) strictly stronger than (a) at [o := Set]; only the direct
   derivation is refused there.

   STRENGTHS.  [PForget_fobj] and [PForget_fmap] hold at [eq_refl]: the
   underlying setoid of a space IS its point setoid and the underlying map
   of an arrow IS its setoid map.  [PForget_Faithful] is the identity on
   hom-setoid proofs: [PMor_Setoid] compares exactly the underlying maps,
   pointwise, and ignores the continuity proofs.  [popen_const] makes every
   constant proposition open, the Prop analogue of Instance/Top.v's
   [open_const], and [popen_empty] is its case [False].  Of the concrete
   spaces below, [PDiscrete_carrier], [PDiscrete_open] and
   [pdisc_mor_map] hold at [eq_refl] as well.

   CONCRETE SPACES.  [PDiscrete S] is the discrete topology on a setoid
   [S]: its opens are the predicates respecting the points' equality
   ([pdisc_open]), which under the setoid discipline is the whole
   condition, [popen_proper] asking it of every open.  It is a record
   literal over five [Qed] lemmas, so its points and its opens read back
   at [eq_refl] ([PDiscrete_carrier], [PDiscrete_open]).  Built instead in
   proof mode by [refine] and closed [Qed], as #457's review prototyped
   it, the points' readback at [eq_refl] is refused (Coq: cannot unify
   "pt_carrier (PDiscreteQ S)" and "S", the Qed copy named [PDiscreteQ]
   in a scratch file carrying this file); measured, not pinned.  Every
   setoid map out of a discrete space is continuous ([pdisc_cont]), so
   [pdisc_mor S Y f] is [f] as an arrow of [PTopCat] ([pdisc_mor_map], at
   [eq_refl]); [pconst S Y y] is the constant setoid map at a point [y]
   of a space.  [PPoint] and [PBool] are the discrete spaces on
   Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object], and
   [PBool_points_distinct] refutes [false ≈ true] in [PBool], its
   equality being Leibniz.  They are the tree's first named [PTop]s: a
   grep of the tree's .v files for [Build_PTop] and for [pt_carrier :=]
   finds that, besides [PDiscrete], only Instance/Top/Subspace.v's [PSub]
   and [PQuot] define a space with them, both built from variables.
   Instance/Top/Subspace.v takes an equalizer and a coequalizer of two
   different maps between them.

   UNIVERSES, read by [About] under [Set Printing Universes].
     - [PTop@{o} : Type@{max(Set+1,o+1)}], empty block.  The [Set+1] is
       the sort of the type of Prop-valued predicates; since [Set <= o]
       the sort is [o+1], and [PTop@{Set} : Type@{Set+1}] is accepted.
     - [PMor@{o} : PTop@{o} → PTop@{o} → Type@{o}], empty block: the homs
       sit at the points' universe, where Test/ProbeStoneCech455.v's N6
       refuses [ContinuousMorphism].  [PCont@{o}], [PMor_Setoid@{o}] (a
       [Setoid@{o o}]), [pcont_respects@{o}], [popen_const@{o}] and
       [popen_union_indexed@{o i}] have empty blocks too.
     - [pid@{o}] carries [o <= ID.u0] and [pcompose@{o}] the three
       [o <= compose.u*] caps: the stdlib caps of Instance/Sets.v's
       [setoid_morphism_id] and [setoid_morphism_compose], which carry
       them in their own blocks, and which [Sets@{o so}] carries too.
     - [PTopCat@{o so} : Category@{so o o}], block [Set < so], [o < so]
       and those four caps: [Sets@{o so}]'s block plus [Set < so], which
       [o < so] implies and which records [PTop]'s sort.
     - [PForget@{o so} : PTopCat@{o so} ⟶ Sets@{o so}], the same block;
       [PForget_Faithful@{o so} : Faithful@{so o so} PForget@{o so}].
     - [PDiscrete@{o} : SetoidObject@{o o} → PTop@{o}], empty block, as
       are [pdisc_open@{o}], its five lemmas, [PDiscrete_carrier],
       [PDiscrete_open], [pdisc_cont@{o}], [pdisc_mor@{o}],
       [pdisc_mor_map] and [pconst@{o}].  [PPoint@{o} : PTop@{o}],
       [PBool@{o} : PTop@{o}] and [PBool_points_distinct@{o}] carry the
       one cap [o <= Logic_lemmas.equality.u0], which Instance/Sets.v's
       [unit_setoid_object] and [bool_setoid_object] carry in their own
       blocks.
   No universe of this file is pinned at [Set].  Over the [About] output
   of all 51 of this file's constants (the 49 names of its [Print Module]
   listing, obligations included, and the two record constructors), the
   word [Set] occurs in [PTop]'s sort and as [Set < so] in 12 blocks:
   [PTopCat], [PForget], their seven obligations, [PForget_fobj],
   [PForget_fmap] and [PForget_Faithful].

   NOT DELIVERED.  No comparison with [Top], no [PCompHaus], and no limits
   or colimits of [PTopCat] in this file: its equalizers and coequalizers
   are Instance/Top/Subspace.v's [PTop_HasEqualizers] and
   [PTop_HasCoequalizers], and its products are not built; no
   indiscrete, empty or other non-discrete named space (the named spaces
   are discrete); no discrete or indiscrete functors and no adjoint
   triple, the analogue of
   Instance/Top/Forgetful.v, over [PTopCat]; no separation or compactness
   notions; and no claim that (b) is strictly stronger than (a) at
   [o := Set].  CORRECTION (#458): those limits, colimits and functors
   are no longer absent from the tree, only from this file.  The products
   and all small limits of [PTopCat] are Instance/Top/Complete.v's
   ([PProd], [PTop_Complete]), its coproducts and all small colimits
   Instance/Top/Cocomplete.v's ([PSigma], [PTop_Cocomplete]), both at
   every shape universe at or below the points'.  The discrete and
   indiscrete functors are [PDisc] (Instance/Top/Complete.v) and
   [PIndisc] (Instance/Top/Cocomplete.v), with the adjoint triple
   [PDisc ⊣ PForget ⊣ PIndisc] as two adjunctions, [PDisc_PForget] and
   [PForget_PIndisc], as Instance/Top/Forgetful.v states its own.  Named
   spaces that are not discrete exist there as well: the indiscrete space
   on a setoid [PIndiscrete] and the indiscrete two-point [PTwoIndisc]
   (Instance/Top/Cocomplete.v), their sum [PTwoIndiscSum], whose topology
   is neither discrete nor indiscrete ([PTwoIndiscSum_not_discrete],
   [PTwoIndiscSum_not_indiscrete]), and Instance/Top/Complete.v's
   convergent sequence [PConv], whose limit point is not open
   ([pconv_limit_point_not_open]). *)

#[local] Obligation Tactic := idtac.

(** ** Spaces *)

(* A space: a setoid of points and a Prop-valued predicate on its
   Prop-valued predicates, closed under the book's operations.  The union
   field takes a FAMILY of opens, itself a Prop-valued predicate on
   predicates, and forms its union; see the header for why it is not stated
   over an index type. *)
Record PTop@{o} := {
  pt_carrier :> SetoidObject@{o o};    (* the setoid of points *)

  (* the topology: which predicates on the points are open *)
  POpen : (pt_carrier → Prop) → Prop;

  (* being open is invariant under pointwise equivalence of predicates *)
  popen_respects (U V : pt_carrier → Prop) :
    (∀ x, U x <-> V x) → POpen U → POpen V;

  (* every open respects the carrier's own equality on points *)
  popen_proper (U : pt_carrier → Prop) :
    POpen U → ∀ x y : pt_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary unions: the union of every family of opens *)
  popen_union (F : (pt_carrier → Prop) → Prop) :
    (∀ U, F U → POpen U) → POpen (fun x => ex (fun U => F U /\ U x));

  (* the whole space is open *)
  popen_whole : POpen (fun _ => True);

  (* closure under binary intersection *)
  popen_inter (U V : pt_carrier → Prop) :
    POpen U → POpen V → POpen (fun x => U x /\ V x)
}.

(* The union of a family indexed by a type, at ANY universe [i]: the family
   of the predicates pointwise equivalent to some [U k] is a Prop-valued
   family of opens, and its union is the indexed one. *)
Lemma popen_union_indexed@{o i} (X : PTop@{o}) (I : Type@{i})
  (U : I → pt_carrier X → Prop) :
  (∀ k, POpen X (U k)) → POpen X (fun x => ex (fun k => U k x)).
Proof.
  intro HU.
  apply (popen_respects X
           (fun x => ex (fun W => ex (fun k => ∀ y, W y <-> U k y) /\ W x))).
  - intro x; split.
    + intros [W [[k Hk] w]]. exists k. exact (proj1 (Hk x) w).
    + intros [k u]. exists (U k). split; [|exact u].
      exists k. intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [k Hk].
    apply (popen_respects X (U k)); [|exact (HU k)].
    intro y; exact (iff_sym (Hk y)).
Qed.

(* Every constant proposition is open: the union of the family holding of
   the whole space exactly when [P] does. *)
Lemma popen_const@{o} (X : PTop@{o}) (P : Prop) : POpen X (fun _ => P).
Proof.
  apply (popen_respects X
           (fun x => ex (fun W => (P /\ ∀ y, W y <-> True) /\ W x))).
  - intro x; split.
    + intros [W [[p _] _]]; exact p.
    + intro p. exists (fun _ => True). split; [split; [exact p|]|exact I].
      intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [_ HW].
    apply (popen_respects X (fun _ => True)); [|exact (popen_whole X)].
    intro y; exact (iff_sym (HW y)).
Qed.

(* The empty predicate is open: [popen_const] at [False]. *)
Corollary popen_empty@{o} (X : PTop@{o}) : POpen X (fun _ => False).
Proof. exact (popen_const X False). Qed.

(** ** Continuous maps *)

(* Continuity: the preimage of every open is open.  It is a proposition, so
   a continuous map is a setoid map with a proof attached, at the level of
   the points. *)
Definition PCont@{o} {X Y : PTop@{o}} (f : SetoidMorphism@{o o o} X Y) :
  Prop :=
  ∀ U : Y → Prop, POpen Y U → POpen X (fun x => U (f x)).

(* Continuity depends on the map only up to pointwise [≈]: every open
   respects the codomain's equality. *)
Lemma pcont_respects@{o} {X Y : PTop@{o}} (f g : SetoidMorphism@{o o o} X Y) :
  (∀ x, f x ≈ g x) → PCont f → PCont g.
Proof.
  intros Hfg Hf U HU.
  apply (popen_respects X (fun x => U (f x))); [|exact (Hf U HU)].
  intro x; split; intro u.
  - exact (popen_proper Y U HU (f x) (g x) (Hfg x) u).
  - exact (popen_proper Y U HU (g x) (f x) (symmetry (Hfg x)) u).
Qed.

Record PMor@{o} (X Y : PTop@{o}) : Type@{o} := {
  pmap :> SetoidMorphism@{o o o} X Y;
  pcont : PCont pmap
}.

Arguments pmap {X Y} _.
Arguments pcont {X Y} _ _ _.

(* The hom-setoid compares the map parts pointwise, as [Sets] does; the
   continuity proofs are not compared. *)
Program Definition PMor_Setoid@{o} (X Y : PTop@{o}) :
  Setoid@{o o} (PMor@{o} X Y) := {|
  equiv := fun f g => ∀ x, pmap f x ≈ pmap g x
|}.
Next Obligation.
  intros X Y; constructor.
  - intros f x; reflexivity.
  - intros f g H x; symmetry; exact (H x).
  - intros f g k H1 H2 x; transitivity (pmap g x); [exact (H1 x)|exact (H2 x)].
Qed.

Definition pid@{o} (X : PTop@{o}) : PMor@{o} X X :=
  {| pmap := setoid_morphism_id@{o o o}; pcont := fun U H => H |}.

Definition pcompose@{o} {X Y Z : PTop@{o}} (g : PMor@{o} Y Z)
  (f : PMor@{o} X Y) : PMor@{o} X Z :=
  {| pmap := setoid_morphism_compose@{o o o} g f;
     pcont := fun U H => pcont f _ (pcont g U H) |}.

Lemma pcompose_respects@{o} {X Y Z : PTop@{o}} :
  Proper@{o o} (@equiv _ (PMor_Setoid@{o} Y Z)
                ==> @equiv _ (PMor_Setoid@{o} X Y)
                ==> @equiv _ (PMor_Setoid@{o} X Z)) (@pcompose@{o} X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  transitivity (pmap g1 (pmap f2 x)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category and its underlying-set functor *)

Program Definition PTopCat@{o so | o < so +} : Category@{so o o} := {|
  obj     := PTop@{o};
  hom     := PMor@{o};
  homset  := PMor_Setoid@{o};
  id      := pid@{o};
  compose := @pcompose@{o};

  compose_respects := @pcompose_respects@{o}
|}.
Solve All Obligations with (intros; simpl; intros; reflexivity).

(* The points, into the Sets whose objects ARE the point setoids. *)
Program Definition PForget@{o so | o < so +} :
  PTopCat@{o so} ⟶ Sets@{o so} := {|
  fobj := fun X => pt_carrier X;
  fmap := fun X Y f => pmap f
|}.
Next Obligation. intros X Y f g H x; exact (H x). Qed.
Next Obligation. intros X x; reflexivity. Qed.
Next Obligation. intros X Y Z f g x; reflexivity. Qed.

Example PForget_fobj@{o so | o < so +} (X : PTop@{o}) :
  fobj[PForget@{o so}] X = pt_carrier X := eq_refl.

Example PForget_fmap@{o so | o < so +} {X Y : PTop@{o}}
  (f : X ~{PTopCat@{o so}}~> Y) :
  fmap[PForget@{o so}] f = pmap f := eq_refl.

#[export] Instance PForget_Faithful@{o so | o < so +} :
  Faithful PForget@{o so}.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(** ** Concrete spaces: the discrete topology, the point and two points *)

(* The discrete topology on a setoid: every predicate respecting the
   points' equality is open.  The setoid discipline makes that respect the
   whole condition: without it [popen_proper] could not hold. *)
Definition pdisc_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) : Prop :=
  ∀ x y : S, x ≈ y → U x → U y.

Lemma pdisc_open_respects@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  (∀ x, U x <-> V x) → pdisc_open S U → pdisc_open S V.
Proof.
  intros HUV HU x y Hxy v.
  apply (proj1 (HUV y)), (HU x y Hxy), (proj2 (HUV x)), v.
Qed.

Lemma pdisc_open_proper@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  pdisc_open S U → ∀ x y : S, x ≈ y → U x → U y.
Proof. intro HU; exact HU. Qed.

Lemma pdisc_open_union@{o} (S : SetoidObject@{o o})
  (F : (S → Prop) → Prop) :
  (∀ U, F U → pdisc_open S U) →
  pdisc_open S (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x y Hxy [U [FU u]]. exists U; split; [exact FU|].
  exact (HF U FU x y Hxy u).
Qed.

Lemma pdisc_open_whole@{o} (S : SetoidObject@{o o}) :
  pdisc_open S (fun _ => True).
Proof. intros x y _ t; exact t. Qed.

Lemma pdisc_open_inter@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  pdisc_open S U → pdisc_open S V → pdisc_open S (fun x => U x /\ V x).
Proof.
  intros HU HV x y Hxy [u v]; exact (conj (HU x y Hxy u) (HV x y Hxy v)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens
   read back at [eq_refl]. *)
Definition PDiscrete@{o} (S : SetoidObject@{o o}) : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pdisc_open S;
  popen_respects := pdisc_open_respects S;
  popen_proper   := pdisc_open_proper S;
  popen_union    := pdisc_open_union S;
  popen_whole    := pdisc_open_whole S;
  popen_inter    := pdisc_open_inter S
|}.

Example PDiscrete_carrier@{o} (S : SetoidObject@{o o}) :
  pt_carrier (PDiscrete S) = S := eq_refl.

Example PDiscrete_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  POpen (PDiscrete S) U = (∀ x y : S, x ≈ y → U x → U y) := eq_refl.

(* Every setoid map out of a discrete space is continuous: the preimage of
   an open respects the domain's equality because the map and the open
   do. *)
Lemma pdisc_cont@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : @PCont (PDiscrete S) Y f.
Proof.
  intros U HU x y Hxy u.
  exact (popen_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) u).
Qed.

Definition pdisc_mor@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : PMor@{o} (PDiscrete S) Y :=
  @Build_PMor (PDiscrete S) Y f (pdisc_cont S Y f).

Example pdisc_mor_map@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : pmap (pdisc_mor S Y f) = f := eq_refl.

(* The constant map at a point [y] of a space, as a setoid map from any
   setoid. *)
Definition pconst@{o} (S : SetoidObject@{o o}) (Y : PTop@{o}) (y : Y) :
  SetoidMorphism@{o o o} S Y :=
  {| morphism := fun _ => y; proper_morphism := fun _ _ _ => reflexivity y |}.

(* The one-point space and the two-point discrete space, on
   Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object]. *)
Definition PPoint@{o} : PTop@{o} := PDiscrete unit_setoid_object@{o o}.

Definition PBool@{o} : PTop@{o} := PDiscrete bool_setoid_object@{o o}.

(* The two points of [PBool] are distinct: its equality is Leibniz. *)
Lemma PBool_points_distinct@{o} : @equiv _ PBool@{o} false true → False.
Proof. intro H; discriminate H. Qed.
