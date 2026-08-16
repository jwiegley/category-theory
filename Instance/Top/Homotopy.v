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
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

Open Scope R_scope.

(* The sections below quantify over the two homotopies being pasted, which
   their proofs genuinely use but which do not occur in every statement.
   Lib.v's [Default Proof Using "Type"] would discard them; this is the same
   setting, for the same reason, as Instance/Top/Interval.v:23 and
   Instance/Top/FundamentalGroupoid.v:32. *)
Set Default Proof Using "All".

(** * Homotopy, the homotopy category, and their pointed forms *)

(* nLab:      https://ncatlab.org/nlab/show/homotopy+category
   nLab:      https://ncatlab.org/nlab/show/homotopy
   nLab:      https://ncatlab.org/nlab/show/pointed+topological+space
   Wikipedia: https://en.wikipedia.org/wiki/Homotopy_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.7, printed pp. 25-26 (PDF pp. 35-36) -- the two
              constructions formalized here, [Toph] and [Toph_*], from the
              roll-call of large categories that opens at printed p. 24
   Book:      Mac Lane, ibid., §II.8 "Quotient Categories", printed p. 51
              (PDF p. 61) -- the remark that [Toph] IS a quotient of [Top]
              by a congruence on its hom-sets, which is how it is built
   Book:      Riehl, "Category Theory in Context", §1.1 Exercise 1.1.iv,
              printed p. 3 ff. (PDF p. 23 ff.)

   Two continuous maps are homotopic when one can be deformed continuously
   into the other; homotopy is an equivalence relation on each hom-set of
   [Top] and is compatible with composition, so the quotient is a category
   -- the homotopy category [Toph], where the arrows are deformation
   classes.  The pointed forms keep a chosen point and deform only through
   maps that fix it.

   Every claim below about what a printed source says is a paraphrase; no
   book was opened for this file and nothing here quotes one.  The
   printed/PDF page pairs come from the in-tree page maps
   doc/plan/books/maclane/pagemap.md (whose offset over the printed range
   7-53 is +10, and which is expressly NOT uniform across that book) and
   doc/plan/books/riehl/pagemap.md (a uniform +20).

   Contents:

       Homotopy               a homotopy of two continuous maps, as data
       homotopy_const/_sym
         /_trans/_comp        the four congruence clauses
       homotopic              the relation, at [HomRelT Top]
       homotopy_congruence    it is a [HomCongruence]
       Toph, TophProj         the quotient category and its projection
       PointedTop, PointedMap
         Top_pointed          Mac Lane's [Top_*]
       BasedHomotopy          a homotopy constant at the basepoint
       based_homotopy_congruence, Toph_pointed
       homotopy_of_square     square arrows are homotopies of interval maps
       interval_contraction   the straight-line contraction of [0,1]
       HomotopyEquivalence    and its coincidence with [Toph]-isomorphism
       interval_iso_point_in_Toph
                              the interval IS the point in [Toph] ...
       interval_not_iso_point_in_Top
                              ... and is not, in [Top]

   THE CYLINDER, AND WHY THERE IS NOT ONE.  A homotopy is classically a
   continuous map out of the cylinder `X × [0,1]`, and this tree has no
   such object to map out of: [Top] carries no products here (only
   [Top_Terminal] and [Top_Initial] are instantiated, and Instance/Top.v's
   own header scopes the remark that the product topology is the
   categorical product to the mathematics at large, "none of it formalized
   here").  Supplying the cylinder directly does not rescue the plan
   either, and the obstruction is a universe obstruction rather than a
   matter of labour.  Writing the product topology out -- W is open when
   every `(x, t)` in it carries an open `U ∋ x` of X and a radius `r > 0`
   with `U × B(t, r) ⊆ W` -- the condition existentially quantifies over an
   OPEN of X, and the opens of X live one universe above its points,
   whereas the [IsOpen] field of [TopSpace@{o}] must land at the universe
   of the points.  Measured rather than assumed, with the carrier
   `Cyl_pt X := X × Ipt`:

       Cyl_pt X : Type@{o}                                    ACCEPTED
       cyl_open X : (Cyl_pt X → Type@{o}) → Type@{o}          REJECTED
       cyl_open X : (Cyl_pt X → Type@{o}) → Type@{o2}, o < o2 ACCEPTED

   So the cylinder object exists, one universe up, as a [TopSpace@{o2}] --
   an object of a DIFFERENT [Top] from the one X belongs to.  The
   inclusions `X ~> Cyl X` are then not arrows of any single category, the
   relation "there is a map out of the cylinder restricting to f and g"
   is not a relation on a hom-set of [Top], and it could not be a
   [HomRelT Top] at all.  This is the same stratification Top/Forgetful.v
   documents for the underlying-set functor, met here from the other side.

   The packaging taken instead carries the certificate directly: a
   [Homotopy] is a function `X → Ipt → Y` respecting `≈`, with the joint
   continuity condition stated as the rectangle condition it would have
   satisfied, plus the two endpoint equations.  Everything then stays in
   one [Top].  The cost is that cylinder functoriality is not available as
   a lemma, which is why [cong_comp] below is the DIAGONAL homotopy rather
   than the textbook two-step composite; the diagonal needs no cylinder,
   its certificate being the two given certificates chained through each
   other, and it is the shorter proof besides.  For maps out of the
   interval the cylinder does exist -- it is the unit square of
   Instance/Top/Interval.v -- and [homotopy_of_square] is the bridge, which
   is how the witnesses at the end of the file are obtained.

   HOMOTOPY IS DATA.  [HomRelT] (Construction/Quotient.v) is the
   [Type]-valued relation family, so [homotopic] carries the chosen
   homotopy rather than its bare existence, and no truncation is applied
   anywhere.  This settles the presentational point of Riehl's Exercise
   1.1.iv in the strong direction: the relation whose quotient is taken is
   at the level of witnesses, and reflexivity, symmetry, transitivity and
   the composition clause are CONSTRUCTIONS on those witnesses --
   respectively the constant track, the reversed track, the concatenated
   track and the diagonal -- not proofs that something exists.

   THE CONGRUENCE IS NAMED, AND Toph IS THE QUOTIENT.  Mac Lane's §II.8
   remark is formalized as such: [homotopy_congruence] is a
   [HomCongruence homotopic] instance and [Toph] is literally
   `Quotient Top homotopic`, not a hand-built category that happens to
   look like one.  Everything the quotient machinery already proves is
   thereby inherited rather than restated -- the category laws, the
   projection functor with its fullness ([TophProj_Full]) and its
   identity-on-objects action, and the descent of isomorphisms.  The
   coincidence of homotopy equivalences with the isomorphisms of [Toph]
   needs no proof at all for the same reason: the composites of an
   isomorphism of the quotient ARE homotopies, by the definition of the
   quotient's hom-setoid.

   BASED MEANS BASED THROUGHOUT.  A based homotopy is not merely a
   homotopy between two based maps: its whole track at the basepoint must
   be the basepoint, `H(x₀, t) ≈ y₀` for EVERY t, which is the field
   [bhtpy_base].  The weaker reading -- endpoints based -- is already
   implied by the two endpoint equations of [Homotopy] and would not give
   a congruence on [Top_*] in the sense the classes of based maps need.
   Each of the four clauses is checked at the basepoint: constant,
   reversed, concatenated (by cases on which half of the time interval t
   falls in) and diagonal.

   WHAT IS NOT HERE.  The standard example of a [Toph]-arrow that is not
   monic despite being monic in [Top] -- the inclusion of the circle in
   the disc, non-monic in [Toph] because the disc is contractible -- is
   DEFERRED: it needs the circle and the disc as spaces and a genuine
   piece of algebraic topology to see that the two maps it separates are
   not homotopic.  Neither space is in this tree.  What is delivered
   instead is the contractibility of the interval, which is the same
   phenomenon at a shape where the tree can prove it: `I_Top` and
   `Point_Top` are isomorphic in [Toph] ([interval_iso_point_in_Toph]) and
   are provably not isomorphic in [Top] ([interval_not_iso_point_in_Top]),
   the two categories having the same objects and the same arrows.  Also
   not here: any cylinder functor, any comparison of [Toph] with the
   fundamental groupoid of Instance/Top/FundamentalGroupoid.v (whose
   [ArrowHomotopy] is homotopy REL ENDPOINTS of maps out of the interval,
   a different and finer relation than the free homotopy of this file),
   and the homotopy-extension property.

   THE AXIOM FOOTPRINT.  No axiom is declared here, and no classical
   principle is invoked beyond what the standard library's reals already
   spend through Instance/Top/Interval.v's kit.  Measured per constant
   with [Print Assumptions], not sampled from the headlines: over the 69
   constants the `.glob` records as def/prf/proj/inst entries, the four
   record types it records as `rec` entries, and the four [Program]
   obligations of [Top_pointed] that genuinely appear in no `.glob`
   entry of any kind -- 77 in all -- the split is

        17 closed under the global context: the whole [Top_pointed] spine
           ([PointedTop] and [PointedMap] with their four projections,
           the hom-setoid and its [Equivalence], [ptop_id], [ptop_compose]
           and its respectfulness, [Top_pointed] itself and its four
           obligations) together with [top_const]
        60 carry exactly [ClassicalDedekindReals.sig_forall_dec] and
           [FunctionalExtensionality.functional_extensionality_dep], the
           two the standard library's own construction of R carries
         0 carry [ClassicalDedekindReals.sig_not_dec]

   The four obligations were measured DIRECTLY:
   [Print Assumptions Category.Instance.Top.Homotopy.Top_pointed_obligation_1]
   (and _2 .. _4, under the fully qualified names -- the short names do
   not resolve after Import) each reports closed under the global
   context.

   The third axiom is the one picked up by anything routed through the
   least-upper-bound property; nothing here is, the interval entering only
   as a parameter domain.  That [Top_pointed] is closed while [Toph] is
   not is exactly right and worth reading off: the category of pointed
   spaces mentions no interval, and only the homotopy relation does. *)

(** ** Homotopy of continuous maps *)

Record Homotopy {X Y : TopSpace} (f g : X ~{Top}~> Y) := {
  htpy_map :> X → Ipt → Y;

  htpy_proper : ∀ (x x' : X) (t t' : Ipt),
    x ≈ x' → ival t = ival t' → htpy_map x t ≈ htpy_map x' t';

  htpy_cont : ∀ V : Y → Type, IsOpen Y V →
    ∀ (x : X) (t : Ipt), V (htpy_map x t) →
      { r : R & ((0 < r) ∧
        { U : X → Type & ((IsOpen X U) ∧ (U x) ∧
          (∀ (y : X) (s : Ipt),
             U y → Rabs (ival t - ival s) < r →
             V (htpy_map y s)))%type })%type };

  htpy_zero : ∀ x : X, htpy_map x I_zero ≈ f x;
  htpy_one : ∀ x : X, htpy_map x I_one ≈ g x
}.

Arguments htpy_map {X Y f g} _ _ _.
Arguments htpy_proper {X Y f g} _ _ _ _ _ _ _.
Arguments htpy_cont {X Y f g} _ _ _ _ _ _.
Arguments htpy_zero {X Y f g} _ _.
Arguments htpy_one {X Y f g} _ _.

(** ** Reflexivity: the constant homotopy *)

Definition homotopy_const {X Y : TopSpace} {f g : X ~{Top}~> Y}
           (E : f ≈ g) : Homotopy f g.
Proof.
  refine {| htpy_map := fun (x : X) (_ : Ipt) => f x |}.
  - intros x x' t t' Hx _.
    exact (proper_morphism f x x' Hx).
  - intros V HV x t Vx.
    exists 1; split; [ lra | ].
    exists (fun y => V (f y)); split; [ | split ].
    + exact (continuity f V HV).
    + exact Vx.
    + intros y s Uy _; exact Uy.
  - intro x; reflexivity.
  - exact E.
Defined.

(** ** Symmetry: run the track backwards *)

Definition homotopy_sym {X Y : TopSpace} {f g : X ~{Top}~> Y}
           (H : Homotopy f g) : Homotopy g f.
Proof.
  refine {| htpy_map := fun (x : X) (t : Ipt) => htpy_map H x (I_rev t) |}.
  - intros x x' t t' Hx Ht.
    apply (htpy_proper H); [ exact Hx | ].
    rewrite !I_rev_eval, Ht; reflexivity.
  - intros V HV x t Vx.
    destruct (htpy_cont H V HV x (I_rev t) Vx)
      as [r [Hr [U [HU [Ux Hball]]]]].
    exists r; split; [ exact Hr | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    apply (Hball y (I_rev s) Uy).
    rewrite !I_rev_eval.
    revert Hs; Rlin.
  - intro x.
    transitivity (htpy_map H x I_one); [ | exact (htpy_one H x) ].
    apply (htpy_proper H); [ reflexivity | ].
    rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
  - intro x.
    transitivity (htpy_map H x I_zero); [ | exact (htpy_zero H x) ].
    apply (htpy_proper H); [ reflexivity | ].
    rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Defined.

(** ** Transitivity: concatenation in the time direction *)

Section HomotopyTrans.

Context {X Y : TopSpace}.
Context {f g h : X ~{Top}~> Y}.
Context (H1 : Homotopy f g).
Context (H2 : Homotopy g h).

(* The concatenated track: the first homotopy at double speed on the first
   half of the time interval, the second on the other half.  Both halves are
   defined on ALL of the interval -- [I_dbl] and [I_dbl'] are clamped, not
   partial -- so nothing here needs a subspace, exactly as in
   Instance/Top/Interval.v's [paste_arrow]. *)
Definition htrans_fun (x : X) (t : Ipt) : Y :=
  if Rle_dec (ival t) (1/2)
  then htpy_map H1 x (I_dbl t)
  else htpy_map H2 x (I_dbl' t).

Lemma htrans_left (x : X) (t : Ipt) :
  ival t <= 1/2 → htrans_fun x t = htpy_map H1 x (I_dbl t).
Proof.
  intro Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - reflexivity.
  - exfalso; exact (Hnle Ht).
Qed.

Lemma htrans_right (x : X) (t : Ipt) :
  1/2 < ival t → htrans_fun x t = htpy_map H2 x (I_dbl' t).
Proof.
  intro Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - exfalso; lra.
  - reflexivity.
Qed.

(* At the seam the two halves agree, both being the middle map g. *)
Lemma htrans_agree (x : X) (t : Ipt) : ival t = 1/2 →
  htpy_map H1 x (I_dbl t) ≈ htpy_map H2 x (I_dbl' t).
Proof.
  intro Ht.
  transitivity (g x).
  - transitivity (htpy_map H1 x I_one); [ | exact (htpy_one H1 x) ].
    apply (htpy_proper H1); [ reflexivity | ].
    rewrite I_dbl_eval, ival_I_one, Ht; Rlin.
  - symmetry.
    transitivity (htpy_map H2 x I_zero); [ | exact (htpy_zero H2 x) ].
    apply (htpy_proper H2); [ reflexivity | ].
    rewrite I_dbl'_eval, ival_I_zero, Ht; Rlin.
Qed.

Lemma htrans_proper (x x' : X) (t t' : Ipt) :
  x ≈ x' → ival t = ival t' → htrans_fun x t ≈ htrans_fun x' t'.
Proof.
  intros Hx Ht; unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle],
           (Rle_dec (ival t') (1/2)) as [Hle' | Hnle'].
  - apply (htpy_proper H1); [ exact Hx | ].
    rewrite !I_dbl_eval, Ht; reflexivity.
  - exfalso; apply Hnle'; lra.
  - exfalso; apply Hnle; lra.
  - apply (htpy_proper H2); [ exact Hx | ].
    rewrite !I_dbl'_eval, Ht; reflexivity.
Qed.

(* Joint continuity of the concatenation.  This is the pasting argument of
   [paste_open] redone one level down, on certificates rather than on a
   domain that is a ball space: away from the seam the rectangle of the
   relevant half is shrunk so as to stay on its own side, and AT the seam
   both rectangles are available -- the base opens are intersected and the
   two radii halved -- because the two halves agree there. *)
Lemma htrans_cont (V : Y → Type) (HV : IsOpen Y V) (x : X) (t : Ipt) :
  V (htrans_fun x t) →
  { r : R & ((0 < r) ∧
    { U : X → Type & ((IsOpen X U) ∧ (U x) ∧
      (∀ (y : X) (s : Ipt),
         U y → Rabs (ival t - ival s) < r →
         V (htrans_fun y s)))%type })%type }.
Proof.
  intro Vx.
  destruct (total_order_T (ival t) (1/2)) as [[Hlt | Heq] | Hgt].
  - (* strictly inside the first half *)
    assert (Ht2 : ival t <= 1/2) by lra.
    rewrite (htrans_left x t Ht2) in Vx.
    destruct (htpy_cont H1 V HV x (I_dbl t) Vx)
      as [r [Hr [U [HU [Ux Hb]]]]].
    exists (Rmin (r/2) (1/2 - ival t)); split; [ Rlin | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    assert (Hs2 : ival s <= 1/2) by (revert Hs; Rlin).
    rewrite (htrans_left y s Hs2).
    apply (Hb y (I_dbl s) Uy).
    rewrite !I_dbl_eval.
    revert Hs; Rlin.
  - (* exactly at the seam: both halves are available, and they agree *)
    assert (Ht2 : ival t <= 1/2) by lra.
    rewrite (htrans_left x t Ht2) in Vx.
    assert (Vx2 : V (htpy_map H2 x (I_dbl' t)))
      by exact (open_proper Y V HV _ _ (htrans_agree x t Heq) Vx).
    destruct (htpy_cont H1 V HV x (I_dbl t) Vx)
      as [r1 [Hr1 [U1 [HU1 [Ux1 Hb1]]]]].
    destruct (htpy_cont H2 V HV x (I_dbl' t) Vx2)
      as [r2 [Hr2 [U2 [HU2 [Ux2 Hb2]]]]].
    exists (Rmin (r1/2) (r2/2)); split; [ Rlin | ].
    exists (fun y => U1 y ∧ U2 y); split;
      [ exact (open_inter X U1 U2 HU1 HU2)
      | split; [ exact (Ux1, Ux2) | ] ].
    intros y s Uy Hs.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + rewrite (htrans_left y s Hle).
      apply (Hb1 y (I_dbl s) (fst Uy)).
      rewrite !I_dbl_eval.
      revert Hs; rewrite Heq; Rlin.
    + apply Rnot_le_lt in Hnle.
      rewrite (htrans_right y s Hnle).
      apply (Hb2 y (I_dbl' s) (snd Uy)).
      rewrite !I_dbl'_eval.
      revert Hs; rewrite Heq; Rlin.
  - (* strictly inside the second half *)
    rewrite (htrans_right x t Hgt) in Vx.
    destruct (htpy_cont H2 V HV x (I_dbl' t) Vx)
      as [r [Hr [U [HU [Ux Hb]]]]].
    exists (Rmin (r/2) (ival t - 1/2)); split; [ Rlin | ].
    exists U; split; [ exact HU | split; [ exact Ux | ] ].
    intros y s Uy Hs.
    assert (Hs2 : 1/2 < ival s) by (revert Hs; Rlin).
    rewrite (htrans_right y s Hs2).
    apply (Hb y (I_dbl' s) Uy).
    rewrite !I_dbl'_eval.
    revert Hs; Rlin.
Defined.

Definition homotopy_trans : Homotopy f h.
Proof.
  refine {| htpy_map := htrans_fun |}.
  - exact htrans_proper.
  - exact htrans_cont.
  - intro x.
    assert (Hz : ival I_zero <= 1/2) by (rewrite ival_I_zero; lra).
    rewrite (htrans_left x I_zero Hz).
    transitivity (htpy_map H1 x I_zero); [ | exact (htpy_zero H1 x) ].
    apply (htpy_proper H1); [ reflexivity | ].
    rewrite I_dbl_eval, ival_I_zero; Rlin.
  - intro x.
    assert (Ho : 1/2 < ival I_one) by (rewrite ival_I_one; lra).
    rewrite (htrans_right x I_one Ho).
    transitivity (htpy_map H2 x I_one); [ | exact (htpy_one H2 x) ].
    apply (htpy_proper H2); [ reflexivity | ].
    rewrite I_dbl'_eval, ival_I_one; Rlin.
Defined.

(* The concatenated track computes, which is what the based refinement of
   this construction below reads off. *)
Lemma htrans_eval (x : X) (t : Ipt) :
  htpy_map homotopy_trans x t = htrans_fun x t.
Proof. reflexivity. Qed.

End HomotopyTrans.

(** ** Compatibility with composition *)

Section HomotopyComp.

Context {X Y Z : TopSpace}.
Context {f f' : Y ~{Top}~> Z}.
Context {g g' : X ~{Top}~> Y}.
Context (H1 : Homotopy f f').
Context (H2 : Homotopy g g').

(* The DIAGONAL track: deform the inner map and the outer one at the same
   time.  The two-step route -- first [f ∘ g ~ f ∘ g'] by postcomposition,
   then [f ∘ g' ~ f' ∘ g'] by precomposition, then concatenate -- would need
   the cylinder functoriality that the packaging below deliberately does not
   build; the diagonal needs neither, and its certificate is exactly the two
   given certificates chained through each other. *)
Definition hcomp_fun (x : X) (t : Ipt) : Z :=
  htpy_map H1 (htpy_map H2 x t) t.

Definition homotopy_comp : Homotopy (f ∘ g) (f' ∘ g').
Proof.
  refine {| htpy_map := hcomp_fun |}.
  - intros x x' t t' Hx Ht; unfold hcomp_fun.
    apply (htpy_proper H1); [ | exact Ht ].
    exact (htpy_proper H2 x x' t t' Hx Ht).
  - intros V HV x t Vx; unfold hcomp_fun in *.
    (* the outer certificate supplies an open of the middle space ... *)
    destruct (htpy_cont H1 V HV (htpy_map H2 x t) t Vx)
      as [r1 [Hr1 [U1 [HU1 [Ux1 Hb1]]]]].
    (* ... which is exactly what the inner certificate consumes *)
    destruct (htpy_cont H2 U1 HU1 x t Ux1)
      as [r2 [Hr2 [U2 [HU2 [Ux2 Hb2]]]]].
    exists (Rmin r1 r2); split; [ Rlin | ].
    exists U2; split; [ exact HU2 | split; [ exact Ux2 | ] ].
    intros y s Uy Hs.
    apply (Hb1 (htpy_map H2 y s) s).
    + apply (Hb2 y s Uy); revert Hs; Rlin.
    + revert Hs; Rlin.
  - intro x.
    transitivity (htpy_map H1 (g x) I_zero).
    + apply (htpy_proper H1); [ exact (htpy_zero H2 x) | reflexivity ].
    + exact (htpy_zero H1 (g x)).
  - intro x.
    transitivity (htpy_map H1 (g' x) I_one).
    + apply (htpy_proper H1); [ exact (htpy_one H2 x) | reflexivity ].
    + exact (htpy_one H1 (g' x)).
Defined.

Lemma hcomp_eval (x : X) (t : Ipt) :
  htpy_map homotopy_comp x t = hcomp_fun x t.
Proof. reflexivity. Qed.

End HomotopyComp.

(** ** Homotopy is a hom-congruence, and Toph is the quotient by it *)

(* The relation itself, at [HomRelT] -- the [Type]-valued family of
   Construction/Quotient.v, so the chosen homotopy is DATA and nothing is
   truncated away. *)
Definition homotopic : HomRelT Top :=
  fun (X Y : TopSpace) (f g : X ~{Top}~> Y) => Homotopy f g.

#[export]
Instance homotopy_congruence : HomCongruence homotopic.
Proof.
  constructor.
  - intros W Z p q E; exact (homotopy_const E).
  - intros W Z p q H; exact (homotopy_sym H).
  - intros W Z p q r H H'; exact (homotopy_trans H H').
  - intros W Z V p p' q q' H H'; exact (homotopy_comp H H').
Defined.

(* Mac Lane's [Toph]: the same spaces, the same continuous maps, with the
   hom-setoid coarsened to homotopy. *)
Definition Toph : Category := Quotient Top homotopic.

Definition TophProj : Top ⟶ Toph :=
  @QuotientProj Top homotopic homotopy_congruence.

(* The projection is full -- it adds no arrows -- but deliberately not
   faithful; that is the whole content of the quotient. *)
Definition TophProj_Full : Full TophProj :=
  @QuotientProj_Full Top homotopic homotopy_congruence.

Lemma TophProj_obj (X : TopSpace) : fobj[TophProj] X = X.
Proof. reflexivity. Qed.

(** ** Pointed spaces *)

(* A pointed space, and a based map: the pattern of Instance/Sets/Pointed.v
   with [SetoidObject] replaced by [TopSpace]. *)
Record PointedTop := {
  ptop_space :> TopSpace;
  ptop_pt : carrier (top_carrier ptop_space)
}.

Record PointedMap (X Y : PointedTop) := {
  ptop_map :> ptop_space X ~{Top}~> ptop_space Y;
  ptop_preserves : ptop_map (ptop_pt X) ≈ ptop_pt Y
}.

Arguments ptop_map {X Y} _.
Arguments ptop_preserves {X Y} _.

(* The hom-setoid is Top's own, read on the underlying maps.  Stating it
   again pointwise would place the relation at the universe of the POINTS'
   equality, one step below where [Category] needs a hom-setoid to live
   (Instance/Top.v:219-225 annotates [ContinuousMorphism_equiv] for exactly
   this reason); inheriting the donor's setoid inherits its placement.  It
   also makes `p ≈ q` in [Top_pointed] definitionally `ptop_map p ≈ ptop_map
   q` in [Top], which is what lets the based constructions below hand their
   hypothesis straight to the unbased ones. *)
Lemma PointedMap_equiv_Equivalence {X Y : PointedTop} :
  Equivalence (fun p q : PointedMap X Y => ptop_map p ≈ ptop_map q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; symmetry; exact Hpq.
  - intros p q r Hpq Hqr.
    transitivity (ptop_map q); [ exact Hpq | exact Hqr ].
Qed.

#[export]
Instance PointedMap_Setoid {X Y : PointedTop} : Setoid (PointedMap X Y) := {|
  equiv := fun p q => ptop_map p ≈ ptop_map q;
  setoid_equiv := PointedMap_equiv_Equivalence
|}.

Definition ptop_id {X : PointedTop} : PointedMap X X.
Proof.
  refine {| ptop_map := @id Top (ptop_space X) |}.
  reflexivity.
Defined.

Definition ptop_compose {X Y Z : PointedTop}
           (p : PointedMap Y Z) (q : PointedMap X Y) : PointedMap X Z.
Proof.
  refine {| ptop_map := ptop_map p ∘[Top] ptop_map q |}.
  simpl.
  transitivity (ptop_map p (ptop_pt Y)).
  - apply proper_morphism; exact (ptop_preserves q).
  - exact (ptop_preserves p).
Defined.

Lemma ptop_compose_respects {X Y Z : PointedTop} :
  Proper (equiv ==> equiv ==> equiv) (@ptop_compose X Y Z).
Proof.
  intros p p' Hp q q' Hq x; simpl.
  transitivity (ptop_map p (ptop_map q' x)).
  - apply proper_morphism; exact (Hq x).
  - exact (Hp (ptop_map q' x)).
Qed.

(* Mac Lane's [Top_*].

       objects: pointed spaces          (a space with a chosen point)
        arrows: based continuous maps   (f (pt X) ≈ pt Y)
      identity: the identity map
   composition: composition of continuous maps *)
Program Definition Top_pointed : Category := {|
  obj     := PointedTop;
  hom     := PointedMap;
  homset  := @PointedMap_Setoid;
  id      := @ptop_id;
  compose := @ptop_compose;

  compose_respects := @ptop_compose_respects
|}.

(** ** Based homotopy *)

(* A based homotopy is a homotopy whose whole TRACK at the basepoint is the
   basepoint -- not merely one whose endpoints are based maps, which the two
   endpoint equations of [Homotopy] already give.  This is the condition that
   makes the based classes compose. *)
Record BasedHomotopy {X Y : PointedTop} (p q : X ~{Top_pointed}~> Y) := {
  bhtpy :> Homotopy (ptop_map p) (ptop_map q);
  bhtpy_base : ∀ t : Ipt, htpy_map bhtpy (ptop_pt X) t ≈ ptop_pt Y
}.

Arguments bhtpy {X Y p q} _.
Arguments bhtpy_base {X Y p q} _ _.

Definition based_const {X Y : PointedTop} {p q : X ~{Top_pointed}~> Y}
           (E : p ≈ q) : BasedHomotopy p q.
Proof.
  refine {| bhtpy := homotopy_const (f:=ptop_map p) (g:=ptop_map q) E |}.
  intro t; exact (ptop_preserves p).
Defined.

Definition based_sym {X Y : PointedTop} {p q : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p q) : BasedHomotopy q p.
Proof.
  refine {| bhtpy := homotopy_sym (bhtpy H) |}.
  intro t; exact (bhtpy_base H (I_rev t)).
Defined.

Definition based_trans {X Y : PointedTop} {p q r : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p q) (H' : BasedHomotopy q r) :
  BasedHomotopy p r.
Proof.
  refine {| bhtpy := homotopy_trans (bhtpy H) (bhtpy H') |}.
  intro t.
  rewrite (htrans_eval (bhtpy H) (bhtpy H')).
  unfold htrans_fun.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - exact (bhtpy_base H (I_dbl t)).
  - exact (bhtpy_base H' (I_dbl' t)).
Defined.

Definition based_comp {X Y Z : PointedTop}
           {p p' : Y ~{Top_pointed}~> Z} {q q' : X ~{Top_pointed}~> Y}
           (H : BasedHomotopy p p') (H' : BasedHomotopy q q') :
  BasedHomotopy (p ∘ q) (p' ∘ q').
Proof.
  (* the ascription is what makes the two readings of the composite meet:
     [ptop_map (p ∘ q)] reduces to [ptop_map p ∘ ptop_map q], but only by
     conversion, which unification against a metavariable will not do *)
  refine {| bhtpy := (homotopy_comp (bhtpy H) (bhtpy H')
                       : Homotopy (ptop_map (p ∘ q))
                                  (ptop_map (p' ∘ q'))) |}.
  intro t.
  rewrite (hcomp_eval (bhtpy H) (bhtpy H')).
  unfold hcomp_fun.
  transitivity (htpy_map (bhtpy H) (ptop_pt Y) t).
  - apply (htpy_proper (bhtpy H)); [ exact (bhtpy_base H' t) | reflexivity ].
  - exact (bhtpy_base H t).
Defined.

Definition based_homotopic : HomRelT Top_pointed :=
  fun (X Y : PointedTop) (p q : X ~{Top_pointed}~> Y) => BasedHomotopy p q.

#[export]
Instance based_homotopy_congruence : HomCongruence based_homotopic.
Proof.
  constructor.
  - intros W Z p q E; exact (based_const E).
  - intros W Z p q H; exact (based_sym H).
  - intros W Z p q r H H'; exact (based_trans H H').
  - intros W Z V p p' q q' H H'; exact (based_comp H H').
Defined.

Definition Toph_pointed : Category := Quotient Top_pointed based_homotopic.

Definition Toph_pointed_Proj : Top_pointed ⟶ Toph_pointed :=
  @QuotientProj Top_pointed based_homotopic based_homotopy_congruence.

Definition Toph_pointed_Proj_Full : Full Toph_pointed_Proj :=
  @QuotientProj_Full Top_pointed based_homotopic based_homotopy_congruence.

(** ** Over the interval, the cylinder IS the square *)

(* The constant arrow, exactly [top_point]'s construction with the domain
   left free: the preimage of any open is a CONSTANT predicate, and every
   constant predicate is open. *)
Definition top_const (X Y : TopSpace) (b : Y) : X ~{Top}~> Y :=
  Build_ContinuousMorphism X Y
    (const_morphism (top_carrier X) (top_carrier Y) b)
    (fun U _ => open_const X (U b)).

(* Balls are open in the topology they generate.  Stated here rather than in
   Instance/Top/Interval.v because it is this file that needs it: the base
   open of a rectangle over the interval is a ball. *)
Lemma ball_open_ball (A : BallSpace) (x : A) (d : R) :
  ball_open A (fun y => bdist x y < d).
Proof.
  intros z Hz.
  exists (d - bdist x z); split.
  - lra.
  - intros y Hy.
    pose proof (bdist_tri A x z y) as Htri.
    lra.
Qed.

(* The bridge to the tree's existing machinery.  For maps OUT OF THE
   INTERVAL the cylinder is the unit square, which Instance/Top/Interval.v
   already builds as a ball space; so an arrow of the square with the two
   edge conditions is a homotopy in the sense of this file, and the
   certificate is read off from the sup-metric ball the square's own
   continuity supplies -- its base leg is a ball of the interval, open by
   [ball_open_ball], and its time leg is the same radius. *)
Definition homotopy_of_square {X : TopSpace} (F : Sq_Top ~{Top}~> X)
           (f g : I_Top ~{Top}~> X)
           (Hbot : ∀ t : Ipt, F (sq_pt t I_zero) ≈ f t)
           (Htop : ∀ t : Ipt, F (sq_pt t I_one) ≈ g t) : Homotopy f g.
Proof.
  (* the constructor is applied explicitly: with a record literal the field
     is elaborated before the domain space is known, and the domain here is
     [I_Top], whose points are [Ipt] only up to unfolding *)
  unshelve refine (@Build_Homotopy I_Top X f g (fun x t => F (sq_pt x t))
                     _ _ _ _).
  - intros x x' t t' Hx Ht.
    apply Sqap; [ exact Hx | exact Ht ].
  - intros V HV x t Vx.
    destruct (continuity F V HV (sq_pt x t) Vx) as [d [Hd Hball]].
    exists d; split; [ exact Hd | ].
    exists (fun y => @bdist BS_I x y < d); split;
      [ exact (ball_open_ball BS_I x d) | split ].
    + rewrite (bdist_zero BS_I x x (reflexivity x)); exact Hd.
    + intros y s Uy Hs.
      apply Hball.
      simpl; unfold BSprod_dist; simpl.
      revert Uy Hs; simpl; Rlin.
  - exact Hbot.
  - exact Htop.
Defined.

(** ** The interval is contractible, and Toph sees it *)

(* The straight-line homotopy (x, t) ↦ (1 - t)·x, as the [Sq_hmap] of
   Instance/Top/Interval.v at the identity and the constant 0.  Every
   estimate it needs is already proved there. *)
Definition I_straight : Sq_Top ~{Top}~> I_Top :=
  Sq_hmap rf_id rf_zero 2 two_pos rf_id_lo rf_id_hi rf_zero_lo rf_zero_hi
          rf_id_lip rf_zero_lip.

Definition I_const_zero : I_Top ~{Top}~> I_Top := top_const I_Top I_Top I_zero.

Lemma I_straight_bottom (t : Ipt) :
  I_straight (sq_pt t I_zero) ≈ (@id Top I_Top) t.
Proof.
  (* the two sides are stated in their reduced form: [lra] compares ATOMS,
     and would not see through the identity arrow or the constant one *)
  assert (H : ival (I_straight (sq_pt t I_zero)) = ival t).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Lemma I_straight_top (t : Ipt) : I_straight (sq_pt t I_one) ≈ I_const_zero t.
Proof.
  assert (H : ival (I_straight (sq_pt t I_one)) = ival I_zero).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_one, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Definition interval_contraction : Homotopy (@id Top I_Top) I_const_zero :=
  homotopy_of_square I_straight (@id Top I_Top) I_const_zero
    I_straight_bottom I_straight_top.

(* The identity of the interval and the constant map at 0 are homotopic ... *)
Theorem interval_id_homotopic_const :
  homotopic I_Top I_Top (@id Top I_Top) I_const_zero.
Proof. exact interval_contraction. Qed.

(* ... and they are NOT equal in Top: evaluate at the far endpoint. *)
Theorem interval_id_not_const : ((@id Top I_Top) ≈ I_const_zero) → False.
Proof.
  intro E.
  assert (Hval : ival I_one = ival I_zero) by exact (E I_one).
  rewrite ival_I_one, ival_I_zero in Hval.
  lra.
Qed.

(* So the projection genuinely identifies: two arrows Top keeps apart are one
   arrow of Toph.  This is the "arrows are not functions" moral of the
   homotopy category, machine-checked rather than asserted. *)
Theorem Toph_identifies_id_and_const :
  @equiv _ (@homset Toph I_Top I_Top)
    (fmap[TophProj] (@id Top I_Top)) (fmap[TophProj] I_const_zero).
Proof. exact interval_contraction. Qed.

(** ** The same witness, based at 0 *)

Definition I_pointed : PointedTop := {|
  ptop_space := I_Top;
  ptop_pt    := I_zero
|}.

Definition I_pt_id : I_pointed ~{Top_pointed}~> I_pointed.
Proof.
  unshelve refine (@Build_PointedMap I_pointed I_pointed (@id Top I_Top) _).
  reflexivity.
Defined.

Definition I_pt_const : I_pointed ~{Top_pointed}~> I_pointed.
Proof.
  unshelve refine (@Build_PointedMap I_pointed I_pointed I_const_zero _).
  reflexivity.
Defined.

(* The track at the basepoint is (1 - t)·0 = 0 for EVERY t, not merely at the
   two ends -- which is what [BasedHomotopy] demands. *)
Lemma interval_contraction_based (t : Ipt) :
  htpy_map interval_contraction I_zero t ≈ I_zero.
Proof.
  assert (H : ival (I_straight (sq_pt I_zero t)) = ival I_zero).
  { unfold I_straight.
    rewrite Sq_hmap_eval, sq_pt_t, sq_pt_s, ival_I_zero.
    unfold rf_id, rf_zero; lra. }
  exact H.
Qed.

Definition interval_based_contraction : BasedHomotopy I_pt_id I_pt_const.
Proof.
  refine {| bhtpy := (interval_contraction
                       : Homotopy (ptop_map I_pt_id)
                                  (ptop_map I_pt_const)) |}.
  exact interval_contraction_based.
Defined.

Theorem I_pt_id_not_const : (I_pt_id ≈ I_pt_const) → False.
Proof. intro E; exact (interval_id_not_const E). Qed.

Theorem Toph_pointed_identifies_id_and_const :
  @equiv _ (@homset Toph_pointed I_pointed I_pointed)
    (fmap[Toph_pointed_Proj] I_pt_id) (fmap[Toph_pointed_Proj] I_pt_const).
Proof. exact interval_based_contraction. Qed.

(** ** Homotopy equivalences are the isomorphisms of Toph *)

(* This is what the quotient is FOR: a map with a homotopy inverse is not
   invertible in [Top], and becomes invertible in [Toph].  Both directions
   are repackagings -- the composites of an isomorphism of the quotient ARE
   homotopies, by the definition of the quotient's hom-setoid -- which is
   the point: nothing has to be proved because [Toph] was built as the
   quotient rather than by hand. *)
Definition HomotopyEquivalence {X Y : TopSpace} (f : X ~{Top}~> Y) : Type :=
  { g : Y ~{Top}~> X &
    (homotopic Y Y (f ∘ g) (@id Top Y) ∧
     homotopic X X (g ∘ f) (@id Top X))%type }.

Definition homotopy_equivalence_Toph_iso {X Y : TopSpace} (f : X ~{Top}~> Y)
           (E : HomotopyEquivalence f) : X ≅[Toph] Y :=
  @Build_Isomorphism Toph X Y f (projT1 E)
    (fst (projT2 E)) (snd (projT2 E)).

Definition Toph_iso_homotopy_equivalence {X Y : TopSpace} (i : X ≅[Toph] Y) :
  HomotopyEquivalence (to i) :=
  (from i; (iso_to_from i, iso_from_to i)).

(* The two passages are mutually inverse ON THE NOSE -- both round
   trips are Leibniz [eq_refl]-level, so "homotopy equivalences ARE the
   isomorphisms of Toph" is a genuine bijection, not merely a pair of
   maps.  ([eq] on these sigma/record values is the convertibility
   exception: both sides are the same term after destructuring.) *)
Example homotopy_equivalence_round {X Y : TopSpace}
        (f : X ~{Top}~> Y) (E : HomotopyEquivalence f) :
  Toph_iso_homotopy_equivalence (homotopy_equivalence_Toph_iso f E) = E.
Proof. destruct E as [g [a b]]; reflexivity. Qed.

Example Toph_iso_round {X Y : TopSpace} (i : X ≅[Toph] Y) :
  homotopy_equivalence_Toph_iso (to i) (Toph_iso_homotopy_equivalence i)
    = i.
Proof. reflexivity. Qed.

(* The capstone: the interval is contractible, so in the homotopy category
   it IS the point -- while in [Top] it is not, the two categories having
   the same objects and the same arrows. *)
Theorem interval_contractible : HomotopyEquivalence (top_one I_Top).
Proof.
  exists (top_point I_Top I_zero).
  split.
  - apply cong_incl, top_one_unique.
  - apply (cong_trans (g := I_const_zero)).
    + apply cong_incl; intro x; reflexivity.
    + exact (homotopy_sym interval_contraction).
Defined.

Definition interval_iso_point_in_Toph : I_Top ≅[Toph] Point_Top :=
  homotopy_equivalence_Toph_iso (top_one I_Top) interval_contractible.

Theorem interval_not_iso_point_in_Top : I_Top ≅[Top] Point_Top → False.
Proof.
  intro i.
  apply interval_id_not_const.
  intro x.
  transitivity (from i (to i x)).
  - symmetry; exact (iso_from_to i x).
  - (* every point of the interval goes to the same place through the
       one-point space, so the composite is constant *)
    assert (Hpt : from i (to i x) ≈ from i (to i I_zero))
      by (apply proper_morphism;
          destruct (continuous_map (to i) x), (continuous_map (to i) I_zero);
          reflexivity).
    transitivity (from i (to i I_zero)); [ exact Hpt | ].
    exact (iso_from_to i I_zero).
Qed.
