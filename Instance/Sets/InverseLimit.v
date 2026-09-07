Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.

Generalizable All Variables.

(* Category.Functor.Opposite opens [functor_scope], after which a bare
   [Omega^op] in an ASCRIPTION (no expected type to bind the scope)
   parses as [Opposite_Functor Omega] and dies naming neither culprit.
   Reopening [category_scope] is the tree's guard for this. *)
Open Scope category_scope.

(* Obligations are written out rather than left to the tree default, so
   that each [intros] pattern is predictable -- the Instance/Sets/Cone.v
   idiom. *)
#[local] Obligation Tactic := idtac.

(** * Inverse limits of towers of sets *)

(* Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
   Springer 1998, §V.1, book p. 109 (PDF pp. 118-119), construction 1.
   Riehl, _Category Theory in Context_, Dover 2016, §3.1 Definition 3.1.21
   (printed p. 88) and §3.2 Example 3.2.8 (printed p. 95).

   nLab:      https://ncatlab.org/nlab/show/inverse+limit
   Wikipedia: https://en.wikipedia.org/wiki/Inverse_limit

   A TOWER of sets is a diagram indexed by the opposite of the ordinal
   omega,

       F 0  <--  F 1  <--  F 2  <--  ...

   and Mac Lane's inverse (projective) limit of it is the set of MATCHING
   STRINGS: sequences [x] with [x n : F n] whose successive entries are
   carried to one another by the transition maps.  His observation is that
   a matching string is exactly a cone from the one-point set, which is
   why the general cone-set formula of §V.1 Theorem 1 specialises to the
   familiar description.  Both halves are delivered here: the matching
   strings as an object with its projections and universal property, and
   the identification with the cone set.

   WHAT WAS ALREADY IN TREE, AND THE ISSUE'S OWN SURVEY IS STALE ON THREE
   COUNTS.  Issue #408's "Current state" says (a) that [Sets] has no
   indexed products and that [HasIndexedProducts] "has zero instances
   tree-wide", (b) that the compatible-family idiom "exists only at the
   end/wedge shape", and (c) that no functor out of [Omega^op] into [Sets]
   is anywhere shown to have a limit.  Re-measured at 067ee4eb: (a) and
   (b) are FALSE and (c) is accurate but answered by one application.
   [Instance/Sets/Products.v:302] declares
   [Sets_HasIndexedProducts : @HasIndexedProducts Sets] -- one of THREE
   UNCONDITIONAL inhabitants at a named category, with
   [Two_Sets_HasIndexedProducts] and [One_HasIndexedProducts]; the
   criterion matters, since a fourth constant,
   [Instance/Fun/Terminal.v]'s [Fun_HasIndexedProducts], concludes
   [HasIndexedProducts] CONDITIONALLY on one.  [Instance/Sets/Complete.v:128]
   and [:144] are the compatible-family predicate and setoid AT ARBITRARY
   SHAPE, not only at the end/wedge.  And (c) is right about what the tree
   STATES -- no constant of type [Limit F] for [F : Omega^op ⟶ Sets]
   existed -- but it costs NO WORK, [Sets_Complete (Omega^op) F]
   elaborating as it stands.

   SO THE INCREMENT IS NOT EXISTENCE, IT IS THE PRESENTATION.  What no
   in-tree statement had was the tower's own description -- compatibility
   at the SUCCESSOR STEPS ONLY -- and the theorem that it agrees with the
   general one, which quantifies over EVERY arrow of [Omega^op], i.e. over
   every proof of an inequality.  That bridge is [tower_compat_all], one
   induction on [Instance/Omega.v:28]'s [le_t], and it is the exact
   analogue of Instance/Sets/Cone.v's [tuple_compat_paths] (generators to
   paths) one shape along.

   READ THAT AT ITS SCOPE.  It is the only proof with content in sections
   (A)-(D) EXCEPT for [tower_obj]'s own [Equivalence] obligation, which is
   a short script and not an evident map; and section (H) adds two further
   inductions of its own, [stream_trunc_compat] and
   [stream_trunc_respects].  Counted by tactic, exactly FOUR scripts in
   the file run to more than three tactics and every other one is a single
   [exact] or [reflexivity].  An "only new proof content in the file"
   claim would be false, and the sibling file Instance/Sets/Cone.v carried
   exactly that defect until an audit caught it.

   THE STEP DECOMPOSITION IS DEFINITIONAL, WHICH IS WHY THE BRIDGE IS
   SHORT.  [Omega]'s composition is [le_t_trans g f] and [le_t_trans]
   recurses on its SECOND argument, so in [Omega^op] the composite
   [f' ∘ tower_step k] reduces by two iota steps to [le_t_S f'] -- the
   very constructor the induction is peeling.  [fmap_comp] therefore
   applies with no rewriting of the index, and the successor case is one
   [fmap_comp], one step hypothesis and the induction hypothesis.

   [Cochain] STOPS BEING DEAD CODE.  Construction/Chain.v:78 declares
   [Cochain F := (Chain (F^op))^op : Omega^op ⟶ C], the tower
   [1 <- F 1 <- F² 1 <- ...] of an endofunctor with a terminal object, and
   before this file it was used NOWHERE -- [rg -l Cochain] returned that
   file alone.  Section (E) gives it its first consumer.

   WHAT IS NOT SPECIAL ABOUT TOWERS, said plainly so no reader infers
   otherwise: nothing below uses any property of [Omega] except that its
   arrows are generated by the steps.  The general limit
   [Sets_Limit F : Limit F] applies at every shape, this one included; the
   tower case adds a presentation, not a construction.  The corresponding
   statement at an ARBITRARY index category is [Sets_Limit] itself, and
   [tower_iso] is the comparison between the two presentations at this
   shape.

   STREAMS, AND WHAT IS AND IS NOT CLAIMED ABOUT THEM.  Riehl's §3.2
   Example 3.2.8 names the compatible-sequence description; the canonical
   instance of it is the stream tower [1 <- A <- A² <- ...], which is
   [Cochain (StreamF A)].  Section (H) builds that tower's inverse limit
   and the comparison map [stream_to_tower], a stream to its string of
   truncations, with its coordinates read back at [eq_refl].  It is NOT
   proved invertible: the inverse is a corecursive assembly of a stream
   from a matching string plus two round trips up to bisimilarity, a
   larger development, so nothing here says the inverse limit IS
   Instance/Sets/Streams.v:231's final coalgebra [Stream_final].  The
   closure cost of reaching the streams at all is THREE modules (89 to
   92, measured), so the deferral is about proof content and not about
   dependencies.

   THREE SCOPE NOTES, each recording a reading NOT delivered.

   * Riehl's Definition 3.1.21 phrases a cone over a tower as a diagram of
     shape [(ω+1)^op], the tower extended by a new bottom object.  That
     reading is NOT built here: the library's generic [Cone]/[ACone]
     (Structure/Cone.v) is used instead, whose apex is an object of the
     target rather than an extra index.  The two agree in the sense that a
     cone in either sense is the same data -- an apex with a leg at each
     [n] commuting with the transitions -- but no functor [(ω+1)^op ⟶ Sets]
     is formed and no comparison is proved, because [Instance/Omega.v]
     carries no [ω+1].

   * Riehl adds that the same holds for any limit ordinal in place of ω.
     [Instance/Omega.v] is nat-indexed only and the tree has no
     TRANSFINITE machinery -- [Instance/Ordinal.v:282]'s [Ordinal n] is the
     FINITE ordinals and [Omega] is omega, so the issue's own "no ordinal
     machinery", which an earlier revision of this note copied, is too
     broad -- and the generalisation is not statable here, nor attempted.

   * The tower is over [Sets].  Nothing here is claimed for a general
     target category: the construction reads elements, which is what the
     compatible-family presentation of [Instance/Sets/Complete.v] gives
     and what an arbitrary category does not. *)

(** ** (A) The tower's own compatibility condition *)

Section Tower.

Context (F : Omega^op ⟶ Sets).

(* The generating arrow of the tower, read in [Omega^op]: it runs DOWN,
   from stage [S n] to stage [n].  It IS [Instance/Omega.v:85]'s
   [omega_step], the same proof term read in the opposite category. *)
Definition tower_step (n : nat) : @hom (Omega^op) (S n) n := omega_step n.

(* Read this at its true strength: [tower_step] is DEFINED as
   [omega_step], so the readback holds by DELTA and pins that the
   definition is unchanged, not that anything computes.  It is kept as
   that guard, on the Theory/Universal/Element.v:1002 precedent
   ([setsone_is_terminal], disclosed there the same way). *)
Example tower_step_is_omega_step (n : nat) :
  tower_step n = omega_step n := eq_refl.

(* THE MECHANISM THE BRIDGE BELOW TURNS ON, MACHINE-CHECKED RATHER THAN
   ASSERTED: composing an arrow of [Omega^op] with the step is the [le_t_S]
   constructor, ON THE NOSE.  [Omega]'s composition is [le_t_trans g f] and
   [le_t_trans] recurses on its SECOND argument, so two iota steps do it. *)
Example step_is_le_t_S (m k : nat) (f : @hom (Omega^op) k m) :
  @compose (Omega^op) (S k) k m f (tower_step k) = le_t_S f := eq_refl.

(* Mac Lane's matching-string condition: successive entries are carried to
   one another.  Compare [Sets_limit_compatible] (Instance/Sets/
   Complete.v:128), which quantifies over EVERY arrow of the shape. *)
Definition tower_compat (x : Sets_iprod_obj (fun n : nat => F n)) : Type :=
  ∀ n : nat, fmap[F] (tower_step n) (x (S n)) ≈ x n.

(* The product the two presentations are cut out of is one and the same. *)
Example tower_inner_strict :
  Sets_iprod_obj (fun d : Omega^op => F d)
  = Sets_iprod_obj (fun n : nat => F n) := eq_refl.

(* THE BRIDGE -- see the header for its scope: it is the only proof with
   content in sections (A)-(D) apart from [tower_obj]'s setoid obligation,
   and section (H) adds two more.  A family
   family matching at each step matches along every arrow.  The successor
   case turns on the definitional identity
   [f' ∘ tower_step k = le_t_S f'] described in the header. *)
Lemma tower_compat_all (x : Sets_iprod_obj (fun n : nat => F n))
  (H : tower_compat x) {m n : nat} (f : @hom (Omega^op) n m) :
  fmap[F] f (x n) ≈ x m.
Proof.
  induction f as [| k f' IH].
  - exact (@fmap_id _ _ F m (x m)).
  - transitivity (fmap[F] f' (fmap[F] (tower_step k) (x (S k)))).
    + exact (@fmap_comp _ _ F (S k) k m f' (tower_step k) (x (S k))).
    + transitivity (fmap[F] f' (x k)).
      * apply proper_morphism; exact (H k).
      * exact IH.
Qed.

(** ** (B) The set of matching strings, and its projections *)

Program Definition tower_obj : obj[Sets] := {|
  carrier   := { x : Sets_iprod_obj (fun n : nat => F n) & tower_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p n; reflexivity.
  - intros p q Hpq n; symmetry; exact (Hpq n).
  - intros p q r Hpq Hqr n; transitivity (`1 q n);
    [exact (Hpq n)|exact (Hqr n)].
Qed.

(* "with the coordinate projections as the legs". *)
Program Definition tower_proj (n : nat) : tower_obj ~{Sets}~> F n := {|
  morphism := fun p => `1 p n
|}.
Next Obligation. intros n p q Hpq; exact (Hpq n). Qed.

(* An element of the inverse limit is determined by its coordinates: this
   is the definition of [tower_obj]'s setoid, restated in the form a
   consumer wants. *)
Lemma tower_ext (p q : tower_obj) :
  (∀ n : nat, tower_proj n p ≈ tower_proj n q) → p ≈ q.
Proof. intros Hn n; exact (Hn n). Qed.

(** ** (C) The two presentations agree *)

Program Definition tower_fwd :
  Sets_limit_obj F ~{Sets}~> tower_obj := {|
  morphism := fun p => (`1 p ; fun n => _)
|}.
Next Obligation. intros p n; exact (`2 p (S n) n (tower_step n)). Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

Program Definition tower_bwd :
  tower_obj ~{Sets}~> Sets_limit_obj F := {|
  morphism := fun p => (`1 p ; fun m n f => _)
|}.
Next Obligation.
  intros p m n f; exact (tower_compat_all (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

(* The compatible-family limit IS the set of matching strings. *)
Program Definition tower_iso :
  @Isomorphism Sets (Sets_limit_obj F) tower_obj := {|
  to := tower_fwd; from := tower_bwd
|}.
Next Obligation. intros p n; reflexivity. Qed.
Next Obligation. intros p n; reflexivity. Qed.

(** ** (D) The matching strings are a limit *)

Program Definition tower_acone : ACone tower_obj F := {|
  vertex_map := tower_proj
|}.
Next Obligation. intros m n f p; exact (tower_compat_all (`1 p) (`2 p) f). Qed.

Definition tower_cone : Cone F :=
  {| vertex_obj := tower_obj; coneFrom := tower_acone |}.

(* The mediator out of a competing cone: bundle its legs at a point, whose
   step compatibility is the cone's own coherence read at [tower_step]. *)
Program Definition tower_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> tower_obj := {|
  morphism := fun e =>
    (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n e;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (S n) n
                (tower_step n) e)
|}.
Next Obligation.
  intros N e e' Hee' n.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n)
                         e e' Hee').
Qed.

Lemma tower_med_commutes (N : Cone F) (n : nat) :
  tower_proj n ∘ tower_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n.
Proof. intros e; reflexivity. Qed.

Lemma tower_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> tower_obj)
  (Hv : ∀ n : nat,
          tower_proj n ∘ v ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n) :
  v ≈ tower_med N.
Proof. intros e n; exact (Hv n e). Qed.

Program Definition Sets_tower_limit : IsALimit F tower_obj := {|
  limit_acone := tower_acone;
  ump_limit := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

Program Definition Sets_tower_Limit : Limit F := {|
  limit_cone := tower_cone;
  ump_limits := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

(* Mac Lane's own sentence: a matching string IS a cone from the one-point
   set.  The cone set is Instance/Sets/Complete.v's [cone_apex]; the two
   are identified by the general essential-uniqueness theorem, so this
   carries both leg families rather than being a bare isomorphism. *)
Definition Sets_tower_limit_iso_cone_limit : tower_obj ≅ cone_apex F :=
  limit_unique_iso Sets_tower_limit (cone_set_IsALimit F).

End Tower.

(** ** (E) The named notion, its notation, and [Cochain]'s first consumer *)

Definition inverse_limit (F : Omega^op ⟶ Sets) : SetoidObject := tower_obj F.

(* By DELTA, like [tower_step_is_omega_step] above: [inverse_limit] is
   defined as [tower_obj], so this guards the name against drift and
   measures nothing. *)
Example inverse_limit_is_tower (F : Omega^op ⟶ Sets) :
  inverse_limit F = tower_obj F := eq_refl.

(* An OPT-IN scope, on the [power_scope] precedent of
   Structure/Limit/Power.v: the token is not forced on any consumer. *)
Declare Scope inverse_limit_scope.
Delimit Scope inverse_limit_scope with invlim.
Notation "'lim←' F" := (inverse_limit F)
  (at level 9, format "'lim←'  F") : inverse_limit_scope.

(* [Construction/Chain.v:78]'s [Cochain G] is the tower
   [1 <- G 1 <- G² 1 <- ...] of an endofunctor with a terminal object, and
   before this file NOTHING in the tree consumed it ([rg -l Cochain]
   returned that file alone).  It is a tower, so it has an inverse limit.

   A DONOR UNIVERSE PIN, MEASURED AND DISCLOSED.  [Cochain] is declared
   without universe annotations and minimizes to

     Cochain@{u u0} : forall {C : Category@{u0 Set Set}},
       Terminal@{u0 Set} -> C ⟶ C -> Omega@{u Set Set}^op ⟶ C

   -- C's hom AND proof universes pinned to the literal [Set] -- where
   [Chain@{u u0 u1}], one line above it, leaves its TARGET category FREE
   ([C : Category@{u u0 u0}]) where [Cochain] pins it.  Read that
   precisely: [Chain] is NOT free of [Set] -- its own printed type carries
   [Omega@{u1 Set Set}] -- so BOTH constants pin [Omega]'s hom and proof to
   [Set], and what separates them is the TARGET alone.  [Omega@{o h p}]
   itself is free in all three.  So the consumer below is
   confined to [Sets@{Set su}], setoids whose CARRIER lives in [Set]; the
   general section (A)-(D) above carries no [Set] at all
   ([tower_obj@{u u0 u1 u2 u3 u4} : Omega@{u u0 u0}^op ⟶ Sets@{u0 u1} ->
   obj[Sets@{u4 u2}]]).  The pin is the donor's, is NOT repaired here, and
   is NOT claimed unavoidable. *)

Definition cochain_inverse_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) : obj[Sets@{Set su}] :=
  inverse_limit (Cochain G).

Definition cochain_tower_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  IsALimit (Cochain G) (cochain_inverse_limit G) :=
  Sets_tower_limit (Cochain G).

(* The tower's stages are the iterated images of the terminal object. *)
Example cochain_stage_zero@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  fobj[Cochain G] 0%nat = @terminal_obj Sets@{Set su} Sets_Terminal
  := eq_refl.

Example cochain_stage_succ@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su})
  (n : nat) : fobj[Cochain G] (S n) = G (fobj[Cochain G] n) := eq_refl.

(** ** (F) What the two identifications read back *)

(* The legs of the tower limit ARE the coordinate projections. *)
Example tower_limit_leg (F : Omega^op ⟶ Sets) (n : nat) :
  limit_leg (Sets_tower_limit F) n = tower_proj F n := eq_refl.

(* And the comparison with the cone set is not a bare [≅]: it carries both
   leg families, by the general essential-uniqueness theorem. *)
Definition Sets_tower_limit_iso_cone_limit_legs (F : Omega^op ⟶ Sets) :
  (∀ n : nat, cone_leg_at F n ∘ to (Sets_tower_limit_iso_cone_limit F)
                ≈ tower_proj F n) *
  (∀ n : nat, tower_proj F n ∘ from (Sets_tower_limit_iso_cone_limit F)
                ≈ cone_leg_at F n) :=
  limit_unique_iso_legs (Sets_tower_limit F) (cone_set_IsALimit F).

(* Both legs of [tower_iso] are the identity on the underlying family: the
   two presentations differ in what they CARRY (a step condition against a
   condition at every arrow), never in the string itself. *)
Example tower_fwd_underlying (F : Omega^op ⟶ Sets)
  (p : Sets_limit_obj F) : `1 (tower_fwd F p) = `1 p := eq_refl.

Example tower_bwd_underlying (F : Omega^op ⟶ Sets)
  (p : tower_obj F) : `1 (tower_bwd F p) = `1 p := eq_refl.

(** ** (G) A tower whose limit is not a singleton *)

(* The constant tower.  Its transitions are identities, so a matching
   string is an arbitrary constant sequence and the limit has exactly as
   many points as the stage.  Read the scope: this witness shows the
   inverse limit does NOT collapse, and exercises the projections and the
   mediator on closed input.  THIS witness's transitions are identities
   and so lose nothing; section (H)'s [StreamTower] is genuinely lossy (two
   distinct stage-2 points share a stage-1 image), so the FILE does contain
   a lossy tower and it is only this section's witness that does not.  What
   no witness here has is an EMPTY inverse limit: that phenomenon is not
   exhibited and is not claimed. *)

(* The constant tower is [Functor/Diagonal.v:33]'s diagonal at the shape,
   consumed rather than rebuilt: its arrow action is [id] at every arrow,
   which is exactly the identity system. *)
Definition ConstTower (X : obj[Sets]) : Omega^op ⟶ Sets :=
  Diagonal (Omega^op) X.

Example const_tower_fmap (X : obj[Sets]) (n : nat) :
  fmap[ConstTower X] (tower_step n) = id[X] := eq_refl.

(* The compatibility witness is proved as a lemma rather than written
   inline as [fun _ => reflexivity _]: the bare [_] leaves the relation an
   unresolved implicit on Coq 8.19 and 8.20 (it elaborates on Rocq 9.1),
   where the TACTIC [reflexivity] has the goal to work from.  Measured on
   both legacy versions. *)
Lemma const_string_compat (b : bool) :
  tower_compat (ConstTower bool_setoid_object) (fun _ : nat => b).
Proof. intros n; reflexivity. Qed.

Definition const_string (b : bool) :
  inverse_limit (ConstTower bool_setoid_object) :=
  (fun _ => b; const_string_compat b).

Example const_string_coord (b : bool) (n : nat) :
  tower_proj (ConstTower bool_setoid_object) n (const_string b) = b
  := eq_refl.

(* Two provably distinct points of the inverse limit. *)
Lemma const_string_separates :
  const_string true ≈ const_string false → False.
Proof. intros H; specialize (H 0%nat); discriminate H. Qed.

(** ** (H) Streams: the classical tower, and the comparison map *)


Section StreamTower.

Context (A : SetoidObject@{Set Set}).

Definition StreamTower : Omega^op ⟶ Sets@{Set _} := Cochain (StreamF A).

Example stream_tower_zero :
  fobj[StreamTower] 0%nat = @terminal_obj Sets Sets_Terminal := eq_refl.

Example stream_tower_succ (n : nat) :
  fobj[StreamTower] (S n)
  = @product_obj Sets Sets_Cartesian A (fobj[StreamTower] n) := eq_refl.

Fixpoint stream_trunc (n : nat) (s : Stream A) : fobj[StreamTower] n :=
  match n as m return fobj[StreamTower] m with
  | O   => ttt
  | S k => (shead A s, stream_trunc k (stail A s))
  end.

Lemma stream_trunc_compat (s : Stream A) :
  tower_compat StreamTower (fun n => stream_trunc n s).
Proof.
  intros n; revert s.
  induction n as [| k IH]; intros s; simpl.
  - destruct (fmap[StreamTower] (tower_step 0%nat) (stream_trunc 1%nat s)).
    reflexivity.
  - split; [reflexivity | exact (IH (stail A s))].
Qed.

Lemma stream_trunc_respects (n : nat) (s t : Stream A)
  (H : bisim A s t) : stream_trunc n s ≈ stream_trunc n t.
Proof.
  revert s t H.
  induction n as [| k IH]; intros s t H; simpl.
  - destruct (stream_trunc 0%nat s), (stream_trunc 0%nat t); reflexivity.
  - split; [exact (bisim_head A H) | exact (IH _ _ (bisim_tail A H))].
Qed.

(* The comparison map: a stream to its string of truncations.  Read its
   strength exactly -- this is a MORPHISM, and it is NOT proved
   invertible.  The inverse would be a corecursive assembly of a stream
   from a matching string together with two round trips up to
   bisimilarity, which is a different and larger development; nothing here
   claims the inverse limit IS [Instance/Sets/Streams.v:231]'s final
   coalgebra, only that the canonical map exists. *)
Program Definition stream_to_tower :
  Stream_SO A ~{Sets}~> inverse_limit StreamTower := {|
  morphism := fun s => (fun n => stream_trunc n s ; stream_trunc_compat s)
|}.
Next Obligation. intros s t Hst n; exact (stream_trunc_respects n s t Hst). Qed.

(* Its coordinates are the truncations, on the nose. *)
Example stream_to_tower_coord (s : Stream A) (n : nat) :
  tower_proj StreamTower n (stream_to_tower s) = stream_trunc n s := eq_refl.

Example stream_to_tower_one (s : Stream A) :
  tower_proj StreamTower 1%nat (stream_to_tower s) = (shead A s, ttt)
  := eq_refl.

End StreamTower.
