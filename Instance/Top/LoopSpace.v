Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Instance.Top.FundamentalGroupoid.
Require Import Category.Instance.Top.Presheaf.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(* Lib.v sets [Default Proof Using "Type"], which keeps only the Section
   variables occurring in a lemma's STATEMENT.  Several proofs below consume
   Section hypotheses that their statements do not mention -- the
   multiplication's continuity certificate above all -- and the narrower
   setting would discard them.  This is the same declaration
   Instance/Top/Interval.v, Instance/Top/FundamentalGroupoid.v and
   Instance/Top/Homotopy.v make, for the same reason. *)
Set Default Proof Using "All".

(** * Loops in a topological group, and the abelian fundamental group *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.5 Exercises 4 and 6 (printed p. 45)
   Paper:     Eckmann, Hilton, "Group-like structures in general categories
              I. Multiplications and comultiplications", Mathematische
              Annalen 145, 1962
   Paper:     Eckmann, Hilton, "Structure maps in group theory", Fundamenta
              Mathematicae 50, 1961 (Theorem 1.12)
   nLab:      https://ncatlab.org/nlab/show/topological+group
   nLab:      https://ncatlab.org/nlab/show/loop+space
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Topological_group

   Mac Lane's Exercise 4 asks for the interchange law between the two
   operations that loops at the unit of a topological group carry, and
   Exercise 6 asks for the consequence: the fundamental group of a
   topological group is abelian.  Both are proved here, over the two donor
   developments the tree already has -- Instance/Top/FundamentalGroupoid.v
   for paths, homotopy rel endpoints and π(X), and Theory/EckmannHilton.v
   for the abstract argument.

   The two operations.  A loop at the unit e is a path α : [0,1] → G with
   α(0) = α(1) = e.  Two such loops can be composed in two unrelated ways:

     - CONCATENATION, [path_concat] -- run α on the first half of the
       interval and β on the second.  This is the operation of the
       fundamental groupoid (Instance/Top/FundamentalGroupoid.v:1045), and
       its unit up to homotopy is the constant loop.

     - POINTWISE MULTIPLICATION, [loop_mult] below -- multiply the two
       values in the group at each instant, (α · β)(t) = α(t) · β(t).  This
       operation exists only because the ambient space is a group (or, as
       below, only an H-space); it has the constant loop at the unit as a
       STRICT unit, no homotopy needed.

   Exercise 4 is that they INTERCHANGE:

       (α ∗ β) · (γ ∗ δ)  ≈  (α · γ) ∗ (β · δ),

   and the proof is a computation, not a homotopy: at a parameter t ≤ 1/2
   both sides evaluate to α(2t) · γ(2t), and at t ≥ 1/2 both evaluate to
   β(2t−1) · δ(2t−1), because the pointwise product commutes with the split
   at 1/2 that concatenation performs.  The two maps are therefore EQUAL AT
   EVERY POINT, and [pointwise_homotopic]
   (Instance/Top/FundamentalGroupoid.v:1127) upgrades that to a homotopy rel
   endpoints with no surgery of squares anywhere.  This is [loop_interchange]
   below.

   Exercise 6 is then Eckmann and Hilton's: two unital operations that
   interchange coincide, and the one operation that remains is commutative
   and associative.  Theory/EckmannHilton.v proves that over a bare setoid;
   this file instantiates it at the hom-setoid of loops, whose `≈` IS
   homotopy rel endpoints ([Path_Setoid]).  The conclusion transported back
   to π₁ is [pi1_topgroup_abelian].

   THE ORIENTATION, worked out and pinned.  Theory/EckmannHilton.v takes its
   interchange law in the shape

       f (g a b) (g c d)  ≈  g (f a c) (f b d),

   so f is applied LAST on the left and FIRST on the right.  Matching
   against the displayed law above forces

       f := pointwise multiplication      g := concatenation.

   The swapped assignment is NOT false -- the interchange law is self-dual
   under swapping f and g together with a transposition of its middle two
   arguments, so the swapped law is [loop_interchange] with b and c
   exchanged, and instantiating the abstract theorem the other way round
   would deliver the same conclusions with the f- and g-sides exchanged.
   The matching above is forced only in the weak sense that it reads
   Exercise 4's displayed law variable-for-variable; under it the theorem's
   f-side conclusions ([eh_comm], [eh_assoc]) are about POINTWISE
   MULTIPLICATION, and the statement a reader wants about π₁ -- which is a
   group under CONCATENATION -- comes out as the g-side corollary
   [eh_g_comm].  Both are recorded below ([loop_mult_comm] and
   [loop_concat_comm]).

   WHAT THE HYPOTHESES ACTUALLY ARE, and why the record is not [TopGroup].
   Reading the argument off, the multiplication is used exactly three times:
   it must respect `≈`, it must be jointly continuous (so that the pointwise
   product of two paths is again a path, and the pointwise product of two
   homotopies again a homotopy), and it must have a STRICT two-sided unit at
   the base point (so that the pointwise product of two loops at e is again
   a loop at e, and so that the constant loop is a strict unit for it).
   Neither associativity nor inverses are used anywhere.  The record below,
   [HTopMonoid], carries exactly those three requirements and nothing else;
   it is the classical sharpening of the exercise -- the fundamental group
   of an H-SPACE with a strict unit is abelian -- and it is what
   [pi1_topgroup_abelian] is stated over.  [TopGroup] then extends it with
   an inverse, its two laws and its continuity, so that Mac Lane's named
   object exists in the tree; [pi1_TopGroup_abelian] is his literal
   statement and is one line.  DISCLOSURE: nothing on the path to the
   theorem consumes the inverse, either of its laws, or its continuity.
   [tg_inv_cont] has exactly one consumer, [tg_inv_nbhd], which restates it
   and is itself consumed by nothing; [tg_inv_left] and [tg_inv_right] have
   no consumer at all.  They are carried because the exercise names a group,
   not because the theorem needs one.

   A COMPANION NON-CLAIM, since the two operations are visibly different
   constructions (one splits the interval at 1/2, the other does not):
   [loop_mult_concat_agree] says they agree UP TO HOMOTOPY, which is
   Eckmann and Hilton's [eh_ops] and is a conclusion, not an assumption.  It
   does not say the two maps are pointwise equal, and no witness here
   separates them pointwise -- separating them would be a statement about
   chosen representatives rather than about π₁, which is why none is built.

   WHY THE CONTINUITY OF THE MULTIPLICATION IS A CERTIFICATE.  Instance/Top.v
   builds no products, so there is no space G × G whose opens could be
   quantified over and no arrow G × G ⟶ G to be called continuous.  Joint
   continuity is therefore carried in the two-open form directly -- for every
   open V containing m(x, y), opens U ∋ x and W ∋ y with m(U × W) ⊆ V --
   which is the same accommodation Instance/Top/Homotopy.v makes for the
   cylinder (its [htpy_cont] field, :208, states the rectangle condition
   pointwise for exactly this reason).  The inverse is not affected: with
   one variable the ordinary preimage form is available, and [tg_inv_cont]
   below is the unfolded form of [Continuous G G] for the inversion map
   (the constant itself expects a bundled [SetoidMorphism], which [tg_inv]
   deliberately is not).  [tg_inv_nbhd] restates it in the pointwise form
   for symmetry with the multiplication.

   WHAT IS DEFERRED, disclosed.  (1) No space in this tree has a nontrivial
   fundamental group -- Instance/Top/FundamentalGroupoid.v says so in its own
   header, and both of its witnesses have trivial vertex groups at every base
   point -- so the witness below, the additive reals, exercises the
   HYPOTHESES and the derivation, not the strength of the conclusion.  π₁(ℝ)
   is trivial, hence abelian for a reason that has nothing to do with this
   theorem.  The circle, whose π₁ is ℤ and whose case would be the honest
   test, needs covering-space theory.  (2) [open_of_nbhds] below is a fact
   about every topological space and belongs in Instance/Top.v; it is proved
   here rather than upstream to keep this file's change surface to one new
   file, and it is an upstreaming candidate.  (3) The loop space Ω(G, e) is
   not built as a SPACE (that needs the compact-open topology, hence
   function spaces, which Instance/Top.v does not have); what is built is
   the two operations on its points, which is all the exercises ask for. *)

(** ** Topological monoids and topological groups *)

(* An H-space with a strict unit, in the exact strength the exercises
   consume.  [htm_mult_cont] is joint continuity in the two-open form
   forced by the absence of products (header). *)
Record HTopMonoid := {
  htm_space :> TopSpace;

  htm_unit : htm_space;
  htm_mult : htm_space → htm_space → htm_space;

  htm_mult_proper : Proper (equiv ==> equiv ==> equiv) htm_mult;

  htm_unit_left : ∀ x : htm_space, htm_mult htm_unit x ≈ x;
  htm_unit_right : ∀ x : htm_space, htm_mult x htm_unit ≈ x;

  htm_mult_cont : ∀ V : htm_space → Type, IsOpen htm_space V →
    ∀ x y : htm_space, V (htm_mult x y) →
      { U : htm_space → Type &
        ((IsOpen htm_space U) ∧ (U x) ∧
         { W : htm_space → Type &
           ((IsOpen htm_space W) ∧ (W y) ∧
            (∀ x' y' : htm_space,
               U x' → W y' → V (htm_mult x' y')))%type })%type }
}.

(* Mac Lane's named object: a group in [Top].  The inverse's continuity is
   stated in the ordinary preimage form, which for a map of one variable is
   available and is literally [Continuous]. *)
Record TopGroup := {
  tg_monoid :> HTopMonoid;

  tg_inv : tg_monoid → tg_monoid;

  tg_inv_proper : Proper (equiv ==> equiv) tg_inv;

  tg_inv_left : ∀ x : tg_monoid,
    htm_mult tg_monoid (tg_inv x) x ≈ htm_unit tg_monoid;
  tg_inv_right : ∀ x : tg_monoid,
    htm_mult tg_monoid x (tg_inv x) ≈ htm_unit tg_monoid;

  tg_inv_cont : ∀ V : tg_monoid → Type,
    IsOpen (htm_space tg_monoid) V →
    IsOpen (htm_space tg_monoid) (fun x => V (tg_inv x))
}.

(* The pointwise reading of the inverse's continuity, for symmetry with the
   multiplication's certificate.  Nothing below consumes it; it is here so
   that the two continuity conditions can be compared in one shape. *)
Lemma tg_inv_nbhd (G : TopGroup) (V : G → Type)
      (HV : IsOpen (htm_space (tg_monoid G)) V) (x : G) (Hx : V (tg_inv G x)) :
  { U : G → Type &
    ((IsOpen (htm_space (tg_monoid G)) U) ∧ (U x) ∧
     (∀ y : G, U y → V (tg_inv G y)))%type }.
Proof.
  exists (fun z => V (tg_inv G z)).
  split; [ | split ].
  - exact (tg_inv_cont G V HV).
  - exact Hx.
  - intros y Hy; exact Hy.
Qed.

(** ** A predicate with an open neighbourhood at each of its points is open *)

(* The union of the neighbourhoods, indexed by the points at which the
   predicate holds.  Radius-free and choice-free: the neighbourhood is DATA,
   supplied by the hypothesis, exactly as the radius is data in
   Instance/Top/Interval.v's [ball_open].  This is a fact about every
   [TopSpace] and is an upstreaming candidate for Instance/Top.v (header,
   deferral 2). *)
Lemma open_of_nbhds (X : TopSpace) (P : X → Type)
      (H : ∀ x : X, P x →
             { U : X → Type &
               ((IsOpen X U) ∧ (U x) ∧ (∀ y : X, U y → P y))%type }) :
  IsOpen X P.
Proof.
  apply (open_respects X
           (fun x => { w : { z : X & P z } &
                       projT1 (H (projT1 w) (projT2 w)) x })
           P).
  - intro x; split.
    + intros [w Hw].
      exact (snd (snd (projT2 (H (projT1 w) (projT2 w)))) x Hw).
    + intro Px.
      exact ((x; Px); fst (snd (projT2 (H x Px)))).
  - apply open_union.
    intro w.
    exact (fst (projT2 (H (projT1 w) (projT2 w)))).
Qed.

(** ** The pointwise product of two arrows into a topological monoid *)

(* Developed once for an ARBITRARY domain, because it is needed twice: at the
   interval, where it multiplies two paths, and at the square, where it
   multiplies two homotopies.  Nothing in the construction mentions either
   domain. *)
Section PointwiseProduct.

Context (G : HTopMonoid).
Context {D : TopSpace}.
Context (p q : D ~{Top}~> G).

Definition mult_fun (z : D) : G := htm_mult G (p z) (q z).

Lemma mult_fun_proper : Proper (equiv ==> equiv) mult_fun.
Proof.
  intros z w Hzw.
  apply (htm_mult_proper G); apply proper_morphism; exact Hzw.
Qed.

Definition mult_setoid_map : SetoidMorphism (top_carrier D) (top_carrier G) := {|
  morphism        := mult_fun;
  proper_morphism := mult_fun_proper
|}.

(* Continuity.  Given an open V containing the product at z, the certificate
   supplies opens U ∋ p z and W ∋ q z whose product lands in V; the two
   preimages are open by continuity of p and of q, and their intersection is
   the neighbourhood of z that [open_of_nbhds] asks for.  No metric, no
   radius, no reals: the argument is the abstract one. *)
Lemma mult_open (V : G → Type) (HV : IsOpen (htm_space G) V) :
  IsOpen D (fun z => V (mult_fun z)).
Proof.
  apply open_of_nbhds.
  intros z Hz.
  destruct (htm_mult_cont G V HV (p z) (q z) Hz)
    as [U [HU [Uz [W [HW [Wz Hprod]]]]]].
  exists (fun w : D => U (p w) ∧ W (q w)).
  split; [ | split ].
  - apply open_inter.
    + exact (continuity p U HU).
    + exact (continuity q W HW).
  - split; [ exact Uz | exact Wz ].
  - intros w Hw; exact (Hprod (p w) (q w) (fst Hw) (snd Hw)).
Qed.

Definition mult_arrow : D ~{Top}~> G := {|
  continuous_map := mult_setoid_map;
  continuity     := mult_open
|}.

(* The defining equation, by [reflexivity]: the arrow's value IS the product
   of the two values. *)
Lemma mult_arrow_eval (z : D) : mult_arrow z ≈ htm_mult G (p z) (q z).
Proof. reflexivity. Qed.

End PointwiseProduct.

Arguments mult_fun G {D} p q z.
Arguments mult_arrow G {D} p q.

(** ** Pointwise multiplication of loops *)

Section Loops.

Context (G : HTopMonoid).

(* Both endpoint conditions come from the same computation: the value at an
   endpoint is the product of the two endpoint values, which are both the
   unit, and the unit is strict. *)
Lemma loop_mult_src (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_zero ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_src p) | exact (path_src q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

Lemma loop_mult_tgt (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_one ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_tgt p) | exact (path_tgt q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

(* The pointwise product of two loops at the unit, as a loop at the unit. *)
Definition loop_mult (p q : Path G (htm_unit G) (htm_unit G)) :
  Path G (htm_unit G) (htm_unit G) := {|
  path_map := mult_arrow G (path_map p) (path_map q);
  path_src := loop_mult_src p q;
  path_tgt := loop_mult_tgt p q
|}.

Lemma loop_mult_eval (p q : Path G (htm_unit G) (htm_unit G)) (t : Ipt) :
  path_map (loop_mult p q) t ≈ htm_mult G (path_map p t) (path_map q t).
Proof. reflexivity. Qed.

(** ** Pointwise multiplication respects homotopy *)

(* The square is the pointwise product of the two squares, which is
   [mult_arrow] again -- at the square rather than at the interval.  Its four
   edges are the products of the corresponding edges: the bottom and top by
   respectfulness, the two sides because the product of the unit with itself
   is the unit. *)
Definition loop_mult_respects
           {p p' q q' : Path G (htm_unit G) (htm_unit G)}
           (H1 : PathHomotopy p p') (H2 : PathHomotopy q q') :
  PathHomotopy (loop_mult p q) (loop_mult p' q').
Proof.
  unfold PathHomotopy.
  refine {| ah_map := mult_arrow G (ah_map H1) (ah_map H2) |}.
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_bot H1 t) | exact (ah_bot H2 t) ].
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_top H1 t) | exact (ah_top H2 t) ].
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G); [ exact (ah_left H1 s) | exact (ah_left H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G);
        [ exact (ah_right H1 s) | exact (ah_right H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
Defined.

(** ** The constant loop is a STRICT unit for pointwise multiplication *)

(* Strict at the level of points; the homotopy is then [pointwise_homotopic]
   and nothing is deformed. *)
Definition loop_mult_unit_left (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (const_path (htm_unit G)) p) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_left G (path_map p t)).
Defined.

Definition loop_mult_unit_right (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p (const_path (htm_unit G))) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_right G (path_map p t)).
Defined.

(** ** Mac Lane §II.5 Exercise 4: the interchange law *)

(* Both sides split the interval at 1/2 in the same place and agree on each
   half, so they agree at every point.  On the first half both reduce to
   a(2t) · c(2t), on the second to b(2t−1) · d(2t−1). *)
Theorem loop_interchange (a b c d : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (path_concat a b) (path_concat c d))
               (path_concat (loop_mult a c) (loop_mult b d)).
Proof.
  apply pointwise_homotopic.
  intro t.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - transitivity (path_map (loop_mult a c) (I_dbl t)).
    + apply (htm_mult_proper G).
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
    + symmetry.
      apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (loop_mult b d) (I_dbl' t)).
    + apply (htm_mult_proper G).
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
    + symmetry.
      apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
Qed.

(** ** Mac Lane §II.5 Exercise 6: Eckmann–Hilton at the loops *)

(* The seven hypotheses of Theory/EckmannHilton.v, assembled.  The carrier is
   the set of loops at the unit and the setoid is [Path_Setoid], whose `≈` IS
   homotopy rel endpoints; f is pointwise multiplication and g is
   concatenation, in the orientation the header derives.  The two [Proper]
   arguments are supplied as lambdas rather than as instances, because
   [Path_Setoid] is deliberately not registered for resolution
   (Instance/Top/FundamentalGroupoid.v:1028) and the expected type unfolds to
   exactly the shape [loop_mult_respects] and [path_concat_respects]
   already have.

   The g-side unit laws come from the fundamental groupoid's own two unit
   homotopies -- note the sides: [unit_left_homotopy] concatenates the
   CONSTANT loop first, so it is [g_unit_left], and [unit_right_homotopy]
   concatenates it last, so it is [g_unit_right]. *)

Definition loops_eckmann_hilton :
  (const_path (htm_unit G) ≈ const_path (htm_unit G))
    ∧ (∀ a b, loop_mult a b ≈ path_concat a b)
    ∧ (∀ a b, loop_mult a b ≈ loop_mult b a)
    ∧ (∀ a b c, loop_mult (loop_mult a b) c ≈ loop_mult a (loop_mult b c)) :=
  @eckmann_hilton
    (Path G (htm_unit G) (htm_unit G))
    (Path_Setoid (htm_unit G) (htm_unit G))
    loop_mult (@path_concat G _ _ _)
    (const_path (htm_unit G)) (const_path (htm_unit G))
    (fun p p' E1 q q' E2 => loop_mult_respects E1 E2)
    (fun p p' E1 q q' E2 => path_concat_respects E1 E2)
    loop_mult_unit_left loop_mult_unit_right
    (fun p => unit_left_homotopy p) (fun p => unit_right_homotopy p)
    loop_interchange.

(* The three substantive conclusions, read off individually.  Each is the
   corresponding lemma of Theory/EckmannHilton.v at the same seven
   hypotheses; they are restated here so that a consumer need not unfold the
   nested pair. *)

(* The two operations agree up to homotopy. *)
Theorem loop_mult_concat_agree (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (path_concat p q).
Proof.
  exact (fst (snd loops_eckmann_hilton) p q).
Qed.

(* Pointwise multiplication is commutative up to homotopy (the f-side
   conclusion). *)
Theorem loop_mult_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (loop_mult q p).
Proof.
  exact (fst (snd (snd loops_eckmann_hilton)) p q).
Qed.

(* Pointwise multiplication is associative up to homotopy. *)
Theorem loop_mult_assoc (p q r : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (loop_mult p q) r) (loop_mult p (loop_mult q r)).
Proof.
  exact (snd (snd (snd loops_eckmann_hilton)) p q r).
Qed.

(* THE LOOP-LEVEL FORM of Exercise 6: concatenation of loops at the unit is
   commutative up to homotopy rel endpoints.  This is the g-side corollary
   [eh_g_comm], and it is the statement π₁ is about -- the fundamental group's
   operation is concatenation, not the pointwise product. *)
Theorem loop_concat_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (path_concat p q) (path_concat q p).
Proof.
  exact (@eh_g_comm
           (Path G (htm_unit G) (htm_unit G))
           (Path_Setoid (htm_unit G) (htm_unit G))
           loop_mult (@path_concat G _ _ _)
           (const_path (htm_unit G)) (const_path (htm_unit G))
           (fun a a' E1 b b' E2 => loop_mult_respects E1 E2)
           (fun a a' E1 b b' E2 => path_concat_respects E1 E2)
           loop_mult_unit_left loop_mult_unit_right
           (fun a => unit_left_homotopy a) (fun a => unit_right_homotopy a)
           loop_interchange p q).
Qed.

End Loops.

Arguments loop_mult {G} p q.
Arguments loop_interchange {G} a b c d.
Arguments loop_concat_comm {G} p q.

(** ** The headline: π₁ of a topological group is abelian *)

(* The group-level statement.  [fundamental_group G e] is the vertex group of
   π(G) at e (Instance/Top/FundamentalGroupoid.v:1100), whose multiplication
   is [hom_monoid]'s -- that is, composition in π(G), which
   Instance/Top/FundamentalGroupoid.v:1045 defines as
   [compose q p := path_concat p q].  So [mon_op p q] IS
   [path_concat q p], and commutativity of the group operation is
   [loop_concat_comm] with its two arguments in the other order.

   THE NAME is the one issue #286 pins, and it names Mac Lane's object; the
   theorem is stated over the weaker [HTopMonoid] because that is all the
   proof consumes (header).  [pi1_TopGroup_abelian] just below is Mac Lane's
   literal statement, over a genuine topological group. *)
Theorem pi1_topgroup_abelian (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (loop_concat_comm q p).
Qed.

(* What the group operation and its unit ARE, recorded by [eq_refl] so that
   the statement above cannot be misread: the multiplication of
   [fundamental_group] is concatenation -- in the order π(G)'s composition
   puts it, the SECOND argument running first -- and its unit is the
   constant loop.  Neither is an artefact of this file: both are read off
   Construction/Deloop.v's [hom_monoid] at
   Instance/Top/FundamentalGroupoid.v:1045. *)
Example pi1_mon_op_is_concat (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q = path_concat q p := eq_refl.

Example pi1_mon_unit_is_const (G : HTopMonoid) :
  @mon_unit (fundamental_group G (htm_unit G)) = const_path (htm_unit G)
  := eq_refl.

(* Mac Lane §II.5 Exercise 6 as stated: the fundamental group of a
   topological group, at its unit, is abelian. *)
Corollary pi1_TopGroup_abelian (G : TopGroup)
          (p q : fundamental_group (tg_monoid G) (htm_unit (tg_monoid G))) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian (tg_monoid G) p q).
Qed.

(** ** Witness: the additive reals *)

(* Instance/Top/Presheaf.v:202's [R_Top] -- the real line with the metric
   topology, over Instance/Top/Interval.v's ball spaces -- carries the
   additive group structure, and both continuity conditions are the ordinary
   ε/2 and ε arguments with the radius carried as data.

   DISCLOSURE (header, deferral 1): π₁(ℝ) is trivial, ℝ being contractible,
   so this witness demonstrates that the hypotheses of [HTopMonoid] and
   [TopGroup] are simultaneously satisfiable by a genuine space -- and that
   the certificate field is dischargeable in practice -- and NOT that the
   conclusion has content at it.  No space in this tree has a nontrivial
   fundamental group. *)

(* Instance/Top/Presheaf.v registers [R_equiv_Equivalence] but deliberately
   not [R_Setoid] (its note at :175), so `≈` does not resolve at a bare [R].
   Registering it FILE-LOCALLY is what lets the two [Proper] obligations
   below be stated in the ordinary shape; it is the same setoid the record
   fields ask for, [is_setoid (top_carrier R_Top)] reducing to it. *)
#[local] Existing Instance R_Setoid.

(* A metric ball of the real line is open: at any interior point the slack
   radius witnesses openness, radius as data, no choice.  Instance/Top/
   Interval.v's [Rlin] splits absolute values in the GOAL only, and the
   estimate here carries one in a hypothesis, so the triangle inequality is
   applied by name rather than by case analysis; that also avoids adding a
   third copy of Instance/Top/ContinuousRing.v's [RlinH] to the tree. *)
Lemma R_ball_open (c d : R) :
  (0 < d)%R → IsOpen R_Top (fun r : R => (Rabs (c - r) < d)%R).
Proof.
  intros Hd r Hr.
  exists (d - Rabs (c - r))%R; split.
  - lra.
  - intros y Hy; simpl in Hy.
    pose proof (Rabs_triang (c - r) (r - y)) as Ht.
    replace (c - r + (r - y))%R with (c - y)%R in Ht by ring.
    lra.
Qed.

Lemma R_plus_proper : Proper (equiv ==> equiv ==> equiv) Rplus.
Proof.
  intros a b Hab c d Hcd.
  assert (Ha : a = b :> R) by exact Hab.
  assert (Hc : c = d :> R) by exact Hcd.
  rewrite Ha, Hc.
  reflexivity.
Qed.

(* Joint continuity of addition, in the two-open form: split the target
   radius in half between the two factors. *)
Lemma R_plus_cont (V : R_Top → Type) (HV : IsOpen R_Top V)
      (x y : R_Top) (Hxy : V (Rplus x y)) :
  { U : R_Top → Type &
    ((IsOpen R_Top U) ∧ (U x) ∧
     { W : R_Top → Type &
       ((IsOpen R_Top W) ∧ (W y) ∧
        (∀ x' y' : R_Top, U x' → W y' → V (Rplus x' y')))%type })%type }.
Proof.
  destruct (HV (Rplus x y) Hxy) as [d [Hd Hball]].
  exists (fun u : R => (Rabs (x - u) < d / 2)%R).
  split; [ | split ].
  - apply R_ball_open; lra.
  - replace (x - x)%R with 0%R by ring; rewrite Rabs_R0; lra.
  - exists (fun w : R => (Rabs (y - w) < d / 2)%R).
    split; [ | split ].
    + apply R_ball_open; lra.
    + replace (y - y)%R with 0%R by ring; rewrite Rabs_R0; lra.
    + intros u w Hu Hw.
      apply Hball.
      pose proof (Rabs_triang (x - u) (y - w)) as Ht.
      replace (x - u + (y - w))%R with (x + y - (u + w))%R in Ht by ring.
      simpl; lra.
Qed.

Definition R_TopMonoid : HTopMonoid := {|
  htm_space  := R_Top;
  htm_unit   := 0%R;
  htm_mult   := Rplus;

  htm_mult_proper := R_plus_proper;

  htm_unit_left  := Rplus_0_l;
  htm_unit_right := Rplus_0_r;

  htm_mult_cont := R_plus_cont
|}.

Lemma R_opp_proper : Proper (equiv ==> equiv) Ropp.
Proof.
  intros a b Hab.
  assert (Ha : a = b :> R) by exact Hab.
  rewrite Ha; reflexivity.
Qed.

(* Negation is continuous: the same radius works, negation being an
   isometry. *)
Lemma R_opp_cont (V : R_Top → Type) (HV : IsOpen R_Top V) :
  IsOpen R_Top (fun x : R => V (Ropp x)).
Proof.
  intros x Hx.
  destruct (HV (Ropp x) Hx) as [d [Hd Hball]].
  exists d; split; [ exact Hd | ].
  intros y Hy.
  apply Hball.
  simpl in *.
  replace (- x - - y)%R with (- (x - y))%R by ring.
  rewrite Rabs_Ropp.
  exact Hy.
Qed.

Definition R_TopGroup : TopGroup := {|
  tg_monoid := R_TopMonoid;

  tg_inv := Ropp;

  tg_inv_proper := R_opp_proper;

  tg_inv_left  := Rplus_opp_l;
  tg_inv_right := Rplus_opp_r;

  tg_inv_cont := R_opp_cont
|}.

(* Acceptance: the record's data are the additive ones on the nose, and the
   pointwise product of two loops is pointwise addition. *)
Example R_unit_is_zero : htm_unit R_TopMonoid = 0%R := eq_refl.

Example R_mult_is_plus : htm_mult R_TopMonoid = Rplus := eq_refl.

Example R_inv_is_opp : tg_inv R_TopGroup = Ropp := eq_refl.

Example R_loop_mult_eval
        (p q : Path R_TopMonoid (htm_unit R_TopMonoid) (htm_unit R_TopMonoid))
        (t : Ipt) :
  path_map (loop_mult p q) t ≈ (path_map p t + path_map q t)%R.
Proof. reflexivity. Qed.

(* And the headline instantiated at the reals. *)
Corollary pi1_R_abelian
          (p q : fundamental_group R_TopMonoid (htm_unit R_TopMonoid)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian R_TopMonoid p q).
Qed.
