Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.

Generalizable All Variables.

(** * Quotient objects of a setoid: the witness half of Mac Lane §V.7
      Definition 3 *)

(* nLab:      https://ncatlab.org/nlab/show/quotient+object
   nLab:      https://ncatlab.org/nlab/show/quotient+set
   nLab:      https://ncatlab.org/nlab/show/coimage
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF p. 135), Definition 3, is the source.  Dually to
   the subobjects of Definition 2, a quotient object of x is an
   equivalence class of epimorphisms OUT of x, ordered by factorization,
   and Mac Lane's whole point is that in a category where the epis are
   the onto maps these are the familiar quotients.  Theory/Subobject/
   Quotient.v carries the definition -- [QuotObj x] is [@SubObj (C^op) x]
   and nothing more -- and this file is the first half of the answer to
   "and where epis ARE onto?", at [Sets].  The [FinSet] and [Grp] halves
   are Instance/FinSet/QuotObj.v and Instance/Grp/QuotObj.v.

   WHAT IS DELIVERED.

   (1) The onto clause, in both directions and with nothing assumed.
   [Sets_quot_epi_surjective] says the epimorphism of a quotient object
   is a surjection and [Sets_quot_of_surjection] says every surjection
   presents a quotient object; both are Instance/Sets.v's
   [surjectivity_is_epic] read through the accessors of the interface
   stub, one leg apiece.  No stability or decidability
   hypothesis appears, and none is hidden: `≈` is [Type]-valued in this
   library, so the biconditional's backward leg RETURNS the preimage as
   data.  This is the point at which [Sets] and [Grp] part company --
   Instance/Grp/QuotObj.v has to take the double-negation stability of
   image membership as a hypothesis, and says so.

   (2) The element-level quotient as a quotient object.
   [SetsQuotient_QuotObj] packages Instance/Sets/Quotient.v's
   [SetsQuotient A R HR] -- the SAME CARRIER under a coarser `≈` -- with
   its projection.  The surjectivity witness is
   [Equivalence_Reflexive] and nothing else, the projection being the
   identity function.  The [SetoidCoarser] argument [HC] is carried
   explicitly and is not optional: the projection does not exist without
   it.

   (3) The COIMAGE, as an [ImageOf] in [Sets^op].  Read
   Theory/Subobject/Lattice.v's record at [C := Sets^op] and each
   field turns over: [im_sub] is a quotient object OF THE DOMAIN,
   [im_factor] is the map from that quotient to the codomain,
   [im_commutes] is the triangle, and [im_least] says the coimage is
   COARSER than every quotient through which f factors.  The coimage is
   the quotient by the kernel relation [sets_coimage_rel a b := f a ≈ f b],
   whose object-level twin is Instance/Sets/Pullback.v's [sets_ker]
   (the kernel pair).  [Sets_HasCoimages] is the class form at [Sets^op],
   registered as an [#[export] Instance] so that [HasImages (Sets^op)]
   resolves by class search (an audit found the first draft a plain
   [Definition], which resolution cannot see).
   One expectation was WRONG and is recorded rather than smoothed over:
   [im_least] is NOT [sets_quot_med]'s job.  That mediator maps OUT of a
   quotient; [im_least] needs a map INTO the coimage from a competing
   quotient's codomain, and since the coimage's carrier is the carrier of
   X such a map must CHOOSE a preimage.  The choice is free here because
   surjectivity is data, and it is well defined into the coimage (though
   not into X) because two preimages of `≈`-equal points have equal
   f-values, which is exactly equality in the coimage.

   (4) A worked binary MEET, at the stub's [quot_meet] -- which at [Sets]
   is the PUSHOUT of the two epis, Instance/Sets/Pushout.v supplying
   it.  The pair is the parity quotient of the discrete setoid on [nat]
   (Instance/Sets/Quotient.v, already in tree) and the residue-mod-3
   quotient defined here, and the answer is the TOTAL quotient
   (Instance/Sets/Quotient.v's [TotalRelT]):
   [Sets_quot_meet_parity_mod3].  The proof never touches
   the pushout apex.  Both sides are greatest lower bounds of the same
   two-element family, so Theory/Subobject/Lattice.v's
   [IsIntersection_unique] identifies them, and the only arithmetic is
   [Sets_meet_collapse]: a quotient coarser than both identifies m with
   m+3 (same residue) and m+3 with m+1 (same parity), hence consecutive
   naturals, hence everything.  Both invariant equations hold by
   [eq_refl] -- [Nat.even (S (S k)) = Nat.even k] by the stdlib
   fixpoint's own reduction, and [nat_tri (S (S (S k))) = nat_tri k]
   because [nat_tri] is written as a three-step fixpoint here for exactly
   that reason, in place of [Nat.modulo], which would have cost an
   arithmetic lemma.  [Sets_quot_meet_collapses] then reads the same fact
   off the apex itself, with no comparison isomorphism in sight.

   (5) The BOTTOM quotient object, and the measurement of its hypothesis.
   The stub's [quot_bot] asks for [Epic (one : X ~> 1)], and in [Sets]
   that is exactly inhabitedness of the carrier: [Sets_one_epic_of_inhabited]
   discharges it from a point in three lines with nothing assumed, so
   [Sets_quot_bot] is the coarsest quotient object X ↠ 1 of every
   inhabited setoid, and [Sets_one_not_epic_empty] refutes it at the empty
   setoid (the two constant maps [Sets_pick true]/[Sets_pick false] out of
   the singleton agree after ∅ → 1 for free and differ at [ttt]).  This
   is what makes the hypothesis object-dependent rather than rare, the
   claim Theory/Subobject/Quotient.v's header makes and cites here.

   STRENGTHS, and what they are NOT.  Everything about quotient objects
   here is stated at ≈, never at Leibniz equality: [QuotObj x] inherits
   [SubObj]'s setoid (Theory/Subobject.v) and has no antisymmetry, so
   [Sets_quot_meet_parity_mod3] is an equivalence of quotient objects and
   the same statement at `=` is REFUSED (measured: CONVERSION, "cannot
   unify quot_meet Sets_Q_parity Sets_Q_mod3 and Sets_Q_total").  Nothing
   in this file computes by [eq_refl]; the computing readbacks of this
   development are in Instance/FinSet/QuotObj.v, where the objects are
   natural numbers.

   MEASUREMENTS, each re-runnable.  33 constants
   (grep -E '^(def|prf|thm|ind|constr|proj|class|inst|meth|rec|corec|ax|
   defax) ' on the .glob), no [Program] anywhere so
   [strings … .vo | grep obligation] returns nothing, and all 33 report
   "Closed under the global context" under [Print Assumptions] -- the
   [Sets] layer is often a place where stdlib axioms enter (docs/
   AXIOMS.md), and here none does.  5 [Defined] and 7 [Qed] (grep -c on
   '^Defined\.' / '^Qed\.'; a first draft of this paragraph said 28
   constants, 3 [Defined] and 8 [Qed], figures stale by the time it was
   committed and corrected here); flipping each [Defined] to [Qed] in
   turn, exactly TWO are required to be transparent: [sets_coimage_med],
   whose underlying function the [change] in [sets_coimage_least] must
   see ("Error: Not convertible"), and [Sets_pick], whose morphism the
   [cbn]/[discriminate] in [Sets_one_not_epic_empty] must reduce ("Not a
   discriminable equality"); the other three recompile green as [Qed]
   and are kept [Defined] because [sub_le], `≈` on [QuotObj] and an
   [Epic] proof consumed by [quot_bot] are data.  The requirement
   closure is 75 files COUNTING THIS FILE (iterated over .Makefile.coq.d;
   74 before Structure/Initial.v joined it).  No name introduced here occurs
   anywhere else in the tree (swept over all .glob files with
   '^[a-z]+ [0-9:]+ [^ ]* NAME$', instrument-checked on [sub_le]; a first
   draft called the kernel relation [sets_ker] and the sweep found
   Instance/Sets/Pullback.v, hence [sets_coimage_rel]).

   UNIVERSES, measured with [Set Printing Universes. About …].  Every
   constant here is [@{o so}] with [o < so], the idiom of
   Instance/Powerset/Subobject.v, and binds its category as
   [Sets@{o so}], which Instance/Sets.v declares as
   [Category@{so o o}] -- hom level and proof level are the SAME
   universe, which is what [SubObj] demands.  That identification is
   INHERITED and is not introduced here: Theory/Subobject.v's record
   itself prints as [∀ {C : Category@{u u0 u0}}, …], as the header of
   Theory/Subobject/Lattice.v records, and [Sets] happens to satisfy it
   on the nose.  No constant here pins any universe to [Set].

   NOT DELIVERED.  No WORKED join: [Sets_quot_join] is delivered as the
   one-line transport of [quot_join] at [Sets_Cartesian] and
   [Sets_HasCoimages] (an earlier revision of this paragraph said the
   join needed "a product instance not assembled here", which an audit
   refuted -- the instance was Instance/Sets/Cartesian.v all along),
   but no pair of quotients has its join computed, unlike the meet.
   No lattice laws: commutativity, associativity,
   idempotence and absorption for [quot_meet] are not restated at [Sets],
   being transports of Theory/Subobject/Lattice.v and not facts about
   setoids.  No top quotient object.  The BOTTOM one IS delivered, at
   every inhabited setoid ([Sets_quot_bot], through
   [Sets_one_epic_of_inhabited]; [Sets_one_not_epic_empty] shows the
   hypothesis is exactly inhabitedness), and the total quotient of
   [NatDiscrete] is shown below every quotient of it directly
   ([Sets_Q_total_below]) -- an argument specific to an inhabited
   carrier for the same reason, the constant map it builds having to
   name an element.  No indexed meet.  No claim that the coimage agrees with
   Instance/Sets/Image.v's image: the two are related by the
   epi-mono factorization of [Sets] and nothing here states it.  No
   [eq_refl] readback of any construction.  No uniqueness of the
   coimage's mediating map ([sub_le_unique] dualized), which would need
   the epi of the competing quotient cancelled on the right and is not
   stated. *)

Section SetsQuotObj.

Universe o so.
Constraint o < so.

(** ** Mac Lane's "where epis are onto" clause, both ways *)

(* The epimorphism of a quotient object of [Sets] is a surjection.  This
   is [Instance/Sets.v]'s [epic_implies_surjective] -- the backward
   leg of [surjectivity_is_epic] -- applied to the [Epic] the
   accessor [quot_is_epic] reads off the [Monic] in [Sets^op].  The
   preimage is DATA: `≈` is [Type]-valued, so [∃] is [sigT] and `1 of
   this is an honest element of the carrier. *)
Definition Sets_quot_epi_surjective {X : SetoidObject@{o o}}
  (q : @QuotObj Sets@{o so} X) :
  ∀ b : carrier (quot_cod q), ∃ a : carrier X, quot_epi q a ≈ b :=
  fun b => epic_implies_surjective (quot_epi q) (quot_is_epic q) b.

(* ... and conversely every surjection of setoids presents a quotient
   object, by the forward leg and [mk_quot]. *)
Definition Sets_quot_of_surjection {X B : SetoidObject@{o o}}
  (h : X ~{Sets@{o so}}~> B)
  (Hs : ∀ b : carrier B, ∃ a : carrier X, h a ≈ b) :
  @QuotObj Sets@{o so} X :=
  mk_quot h (surjective_implies_epic h Hs).

(** ** The quotient of a setoid by an equivalence relation, as a
       quotient object *)

(* [Instance/Sets/Quotient.v]'s [SetsQuotient A R HR] is A with a
   coarser `≈`; its projection is the IDENTITY FUNCTION, so it is
   surjective with the element itself as preimage and the surjectivity
   witness is [Equivalence_Reflexive] and nothing more.  [HC] is not
   decoration: the projection does not exist without it, its
   respectfulness clause being convertible with [SetoidCoarser R]
   (Instance/Sets/Quotient.v). *)
Definition SetsQuotient_QuotObj (A : SetoidObject@{o o})
  (R : crelation (carrier A)) (HR : Equivalence R) (HC : SetoidCoarser R) :
  @QuotObj Sets@{o so} A :=
  Sets_quot_of_surjection (sets_quot_proj A R HR HC)
    (fun b => (b; @Equivalence_Reflexive _ R HR b)).

(** ** The coimage of a setoid map *)

Section Coimage.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* The kernel relation of f, as a coarsening of X's own `≈`.  The
   OBJECT-level counterpart is Instance/Sets/Pullback.v's [sets_ker],
   the kernel pair; this is the same information as a relation on the
   carrier, which is what Instance/Sets/Quotient.v's quotient consumes. *)
Definition sets_coimage_rel : crelation (carrier X) := fun a b => f a ≈ f b.

Lemma sets_coimage_rel_Equivalence : Equivalence sets_coimage_rel.
Proof.
  constructor; unfold sets_coimage_rel.
  - intro a; reflexivity.
  - intros a b H; now symmetry.
  - intros a b c H1 H2; now transitivity (f b).
Qed.

(* Coarser than `≈` because f is a setoid map: this IS [proper_morphism]. *)
Definition sets_coimage_rel_coarser : SetoidCoarser sets_coimage_rel :=
  fun a b H => proper_morphism f a b H.

Definition Sets_coimage : @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_rel_coarser.

(* f itself respects its own kernel relation, by the IDENTITY
   implication, so the descended map is [sets_quot_med] at that witness. *)
Definition sets_coimage_resp : RespMap sets_coimage_rel Y :=
  existT (SetsRespects sets_coimage_rel Y) f
    (fun a b (H : sets_coimage_rel a b) => H).

Definition sets_coimage_factor :
  Y ~{Sets@{o so}^op}~> quot_cod Sets_coimage :=
  sets_quot_med sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_resp.

(* The triangle, read in [Sets^op]: composition there is composition in
   [Sets] with the arguments swapped, so this is
   [sets_coimage_factor ∘ quot_epi Sets_coimage ≈ f] and the projection
   being the identity function leaves nothing to compute. *)
Lemma sets_coimage_commutes :
  sub_mono Sets_coimage ∘[Sets@{o so}^op] sets_coimage_factor ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

(* Minimality needs a map OUT of a competing quotient INTO the coimage,
   whose carrier is the carrier of X -- so it has to choose a preimage.
   [sets_quot_med] is the wrong donor here: it maps out of the quotient,
   not into it.  Choosing is free, the preimage being data. *)
Definition sets_coimage_pick (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) : carrier X :=
  `1 (Sets_quot_epi_surjective w p).

Lemma sets_coimage_pick_eq (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) :
  quot_epi w (sets_coimage_pick w p) ≈ p.
Proof. exact (`2 (Sets_quot_epi_surjective w p)). Qed.

(* The choice is well defined INTO THE COIMAGE, though not into X: two
   preimages of `≈`-equal points have the same value under f, which is
   exactly equality in the coimage. *)
Definition sets_coimage_med (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  quot_cod Sets_coimage ~{Sets@{o so}^op}~> quot_cod w.
Proof.
  unshelve refine {| morphism := sets_coimage_pick w |}.
  intros p q Hpq.
  change (f (sets_coimage_pick w p) ≈ f (sets_coimage_pick w q)).
  transitivity (g (quot_epi w (sets_coimage_pick w p))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w (sets_coimage_pick w q))).
    + apply proper_morphism.
      rewrite !sets_coimage_pick_eq; exact Hpq.
    + exact (Hg _).
Defined.

Lemma sets_coimage_least (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  @sub_le (Sets@{o so}^op) X Sets_coimage w.
Proof.
  exists (sets_coimage_med w g Hg).
  intro a.
  change (f (sets_coimage_pick w (quot_epi w a)) ≈ f a).
  unfold sets_coimage_pick.
  transitivity
    (g (quot_epi w (`1 (Sets_quot_epi_surjective w (quot_epi w a))))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w a)).
    + apply proper_morphism.
      exact (`2 (Sets_quot_epi_surjective w (quot_epi w a))).
    + exact (Hg a).
Qed.

(* Theory/Subobject/Lattice.v's [ImageOf], instantiated at [Sets^op]:
   [im_sub] is a quotient object of the DOMAIN, [im_factor] the map from
   the quotient to the codomain, [im_commutes] the triangle, and
   [im_least] says the coimage is BELOW (that is, coarser than) every
   quotient through which f factors. *)
Definition Sets_CoimageOf : @ImageOf (Sets@{o so}^op) Y X f := {|
  im_sub := Sets_coimage;
  im_factor := sets_coimage_factor;
  im_commutes := sets_coimage_commutes;
  im_least := fun w g Hg => sets_coimage_least w g Hg
|}.

End Coimage.

(* The class form.  The anonymous record literal [{| image_of := … |}] is
   REFUSED here -- it elaborates the field against [C := Sets] and reports
   "has type @ImageOf Sets^op X Y f while it is expected to have type
   @ImageOf Sets Y X f" -- so the constructor is named and its category
   argument given explicitly. *)
#[export] Instance Sets_HasCoimages : @HasImages (Sets@{o so}^op) :=
  @Build_HasImages (Sets@{o so}^op) (fun Y X f => @Sets_CoimageOf X Y f).

(* The JOIN of two quotient objects at Sets, by transport and nothing
   else: Theory/Subobject/Quotient.v's [quot_join] wants a [Cartesian]
   structure on the category -- Instance/Sets/Cartesian.v's
   [Sets_Cartesian], which IS a [@Cocartesian (Sets^op)] on the nose
   (Structure/Cocartesian.v makes [Cocartesian C] notation for
   [@Cartesian (C^op)], and [Sets^op^op] is [Sets] by reflexivity) -- and
   the coimages just registered.  The join is the coimage of the pairing
   of the two epis into the product of their codomains.  An earlier
   revision of this file said the join "needs a product instance not
   assembled here"; an audit refuted that by compiling this one line, so
   it is landed rather than left as a false obstruction.  Its least-
   upper-bound property and the lattice laws are [quot_join_is_lub],
   [quot_join_comm] and their siblings, read at [Sets]; none is restated
   here. *)
Definition Sets_quot_join {X : SetoidObject@{o o}}
  (q r : @QuotObj Sets@{o so} X) : @QuotObj Sets@{o so} X :=
  quot_join q r.

(** ** A worked meet: parity ∧ residue-mod-3 on the naturals *)

(* The residue mod 3, by a three-step fixpoint rather than by [Nat.modulo],
   so that [nat_tri (S (S (S m))) = nat_tri m] holds by [eq_refl] and the
   collapse argument below needs no arithmetic lemma.  Its parity
   counterpart, [Nat.even (S (S m)) = Nat.even m], holds by [eq_refl] for
   the same reason. *)
Fixpoint nat_tri (n : nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S O) => 2
  | S (S (S m)) => nat_tri m
  end.

Definition nat_mod3 : crelation (carrier NatDiscrete@{o}) :=
  fun m n => nat_tri m = nat_tri n.

Lemma nat_mod3_Equivalence : Equivalence nat_mod3.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (nat_tri n).
Qed.

Definition nat_mod3_coarser : SetoidCoarser nat_mod3 :=
  fun m n (H : m = n) => f_equal nat_tri H.

(* The three quotient objects of the discrete setoid on [nat]:
   Instance/Sets/Quotient.v's parity, the residue mod 3, and that
   file's total relation. *)
Definition Sets_Q_parity : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_parity nat_parity_Equivalence
    nat_parity_coarser.

Definition Sets_Q_mod3 : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_mod3 nat_mod3_Equivalence
    nat_mod3_coarser.

Definition Sets_Q_total : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} (TotalRelT NatDiscrete@{o})
    (TotalRelT_Equivalence NatDiscrete@{o})
    (TotalRelT_coarser NatDiscrete@{o}).

(* The total quotient is the BOTTOM of the factorization order on
   quotient objects of [NatDiscrete]: it factors through every quotient
   (every quotient has it below), by the constant map out of that
   quotient's codomain, whose respectfulness is [ttt].  An earlier
   revision of this comment said "every quotient factors through it",
   the reverse direction; the statement below was always the right one. *)
Lemma Sets_Q_total_below (w : @QuotObj Sets@{o so} NatDiscrete@{o}) :
  @sub_le (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_total w.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun _ : carrier (quot_cod w) => 0%nat |}.
    intros p q Hpq; exact ttt.
  - intro a; exact ttt.
Defined.

(* The arithmetic of the meet, done once: a quotient coarser than both
   parity and residue-mod-3 identifies EVERY pair of naturals.  m and
   m+3 agree mod 3, m+3 and m+1 agree in parity, so consecutive
   naturals are identified and induction finishes.  Both steps are
   [eq_refl] at the two invariants. *)
Lemma Sets_meet_collapse (v : @QuotObj Sets@{o so} NatDiscrete@{o})
  (H1 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_parity)
  (H2 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_mod3)
  (m n : nat) : quot_epi v m ≈ quot_epi v n.
Proof.
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  assert (step : ∀ p : nat, quot_epi v p ≈ quot_epi v (S p)).
  { intro p.
    transitivity (k2 p); [ symmetry; exact (Hk2 p) | ].
    transitivity (k2 (S (S (S p)))).
    { exact (proper_morphism k2 p (S (S (S p)))
               (eq_refl : nat_tri p = nat_tri p)). }
    transitivity (quot_epi v (S (S (S p)))); [ exact (Hk2 _) | ].
    transitivity (k1 (S (S (S p)))); [ symmetry; exact (Hk1 _) | ].
    transitivity (k1 (S p)).
    { exact (proper_morphism k1 (S (S (S p))) (S p)
               (eq_refl : Nat.even (S p) = Nat.even (S p))). }
    exact (Hk1 _). }
  assert (zero : ∀ p : nat, quot_epi v 0%nat ≈ quot_epi v p).
  { induction p as [| p IH]; [ reflexivity | now rewrite IH ]. }
  now rewrite <- (zero m), <- (zero n).
Qed.

Lemma Sets_Q_total_IsMeet :
  @IsMeet (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3
    Sets_Q_total.
Proof.
  constructor.
  - intro b; destruct b; exact (Sets_Q_total_below _).
  - intros v Hv.
    unshelve eexists.
    + unshelve refine
        {| morphism :=
             fun p : carrier (quot_cod Sets_Q_total) => quot_epi v p |}.
      intros p q _.
      exact (Sets_meet_collapse v (Hv true) (Hv false) p q).
    + intro a; reflexivity.
Defined.

(* The stub's [quot_meet] at [Sets], evaluated.  Both sides are greatest
   lower bounds of the same two-element family, so they agree -- at ≈ on
   [QuotObj], which is the strongest relation available here ([QuotObj]
   has no Leibniz antisymmetry, exactly as [SubObj] has none). *)
Theorem Sets_quot_meet_parity_mod3 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 ≈ Sets_Q_total.
Proof.
  apply (@IsIntersection_unique (Sets@{o so}^op) NatDiscrete@{o} bool
           (sub_pair Sets_Q_parity Sets_Q_mod3)).
  - exact (@sub_meet_IsMeet (Sets@{o so}^op)
             (HasPullbacks_op_of_HasPushouts Sets_HasPushouts)
             NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3).
  - exact Sets_Q_total_IsMeet.
Qed.

(* The same fact read on elements of the pushout apex itself, with no
   comparison isomorphism in sight: in the pushout of the two
   projections every natural is identified with every other. *)
Corollary Sets_quot_meet_collapses (m n : nat) :
  quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
              Sets_Q_parity Sets_Q_mod3) m
    ≈ quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
                  Sets_Q_parity Sets_Q_mod3) n.
Proof.
  exact (Sets_meet_collapse _ (sub_meet_le_l _ _) (sub_meet_le_r _ _) m n).
Qed.

(** ** The bottom quotient object: [Epic one] is inhabitedness *)

(* Theory/Subobject/Quotient.v's [quot_bot] is conditional on
   [Epic (one : X ~> 1)].  In [Sets] that hypothesis is EXACTLY
   inhabitedness of the carrier, both ways.  Given a point [x0], two maps
   out of the singleton that agree after [one] agree at their only
   argument, because [one x0] IS that argument -- three lines and
   nothing assumed.  At the empty setoid the two constant maps 1 → bool
   agree after ∅ → 1 for free (there is nothing to check) and differ at
   [ttt], so [one] is not epic there.  Hence the coarsest quotient
   object, X ↠ 1, exists at every inhabited setoid and the theory's
   hypothesis is not a gap at [Sets]; it is object-dependent, and this
   pair of constants is the measurement. *)
Definition Sets_one_epic_of_inhabited {X : SetoidObject@{o o}}
  (x0 : carrier X) : Epic (@one Sets@{o so} Sets_Terminal X).
Proof.
  constructor; intros Z g1 g2 H u.
  destruct u.
  exact (H x0).
Defined.

Definition Sets_quot_bot {X : SetoidObject@{o o}} (x0 : carrier X) :
  @QuotObj Sets@{o so} X :=
  @quot_bot Sets@{o so} Sets_Terminal X (Sets_one_epic_of_inhabited x0).

(* The two constant maps 1 → bool, without [Program] (this file has no
   obligations and the measurements below say so). *)
Definition Sets_pick (b : bool) :
  @terminal_obj Sets@{o so} Sets_Terminal ~{Sets@{o so}}~>
    bool_setoid_object@{o o}.
Proof.
  unshelve refine {| morphism := fun _ => b |}.
  proper.
Defined.

Lemma Sets_one_not_epic_empty :
  Epic (@one Sets@{o so} Sets_Terminal
          (@initial_obj Sets@{o so} Sets_Initial)) → False.
Proof.
  intros [He].
  assert (H : Sets_pick true
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial)
              ≈ Sets_pick false
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial))
    by (intro u; contradiction).
  pose proof (He _ _ _ H ttt) as E.
  cbn in E.
  discriminate E.
Qed.

End SetsQuotObj.
