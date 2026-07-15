Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * The double category of cospans *)

(* nLab: https://ncatlab.org/nlab/show/double+category+of+cospans

   Over a category [C] with chosen pushouts ([HasPushouts C]) the cospans of
   [C] organise into a pseudo double category [Cospan_Double]:

     - objects and (strict) vertical 1-cells: [C] itself;
     - horizontal 1-cells [X ⇸ Y]: cospans [X → N ← Y]
       ([CospanArrow X Y] of Construction/Cospan/Category.v);
     - squares
             X --h--> Y
             |        |
             u        v
             v        v
             Z --k--> W
       filling a boundary [(h, u, v, k)]: morphisms of cospans, i.e. maps of
       apexes [φ : apex h ~> apex k] intertwining the legs with the vertical
       edges ([φ ∘ in1 h ≈ in1 k ∘ u] and [φ ∘ in2 h ≈ in2 k ∘ v]);
     - horizontal composition: gluing along the shared boundary object by the
       CHOSEN pushout, exactly as in [cospan_compose];
     - the associator and both unitors: invertible globular squares whose
       apex maps are pushout mediators, with the triangle and pentagon
       coherence discharged by the joint epimorphy of pushout injections.

   Unlike [CospanCat] (which quotients by apex isomorphism to obtain a
   1-category), no quotient is taken here: the square setoid compares the
   apex maps themselves, so [dsq] is genuinely proof-relevant and all the
   weak structure carries real pushout content.

   Every equation in this file is an equality of morphisms OUT OF a (possibly
   iterated) pushout apex, so the whole development rides on a single
   principle: the pushout injections are jointly epic
   ([pushout_jointly_epic]), the op-dual of the "pullback projections are
   jointly monic" reasoning of Theory/Morphisms/Stability.v.  Each side of
   the triangle/pentagon is evaluated on the generator legs of the iterated
   pushout by the mediator computation rules [pushout_med_in1]/[_in2], and
   the results are compared leg by leg.

   Monoidal double categories (tensoring cospans alongside the double
   structure, towards decorated/structured cospans) are NOT attempted here;
   that development is deferred (ledger entry 9). *)

Section CospanDouble.

Context {C : Category}.
Context (HP : HasPushouts C).

(** The chosen gluing pushout for a composable pair of cospans: [f] then
    [g], glued over the shared boundary object [Y]. *)
Definition gpo {X Y Z : C} (f : CospanArrow X Y) (g : CospanArrow Y Z) :
  IsPushout (cospan_in2 f) (cospan_in1 g) :=
  pushout (cospan_in2 f) (cospan_in1 g).

(** ** Joint epimorphy of the pushout injections *)

Lemma pushout_jointly_epic {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) {Q : C} (m n : pushout_apex P ~> Q) :
  m ∘ pushout_in1 P ≈ n ∘ pushout_in1 P →
  m ∘ pushout_in2 P ≈ n ∘ pushout_in2 P →
  m ≈ n.
Proof.
  intros H1 H2.
  assert (Hc : (m ∘ pushout_in1 P) ∘ f ≈ (m ∘ pushout_in2 P) ∘ g).
  { rewrite <- !comp_assoc.
    now rewrite (pushout_commutes P). }
  apply (pushout_med_eq P Hc); try reflexivity.
  - now symmetry.
  - now symmetry.
Qed.

(** ** Squares: morphisms of cospans over a vertical boundary *)

Record CospanSq {a b c d : C}
       (h : CospanArrow a b) (u : a ~> c) (v : b ~> d)
       (k : CospanArrow c d) : Type := {
  sq_map : cospan_apex h ~> cospan_apex k;
  sq_in1 : sq_map ∘ cospan_in1 h ≈ cospan_in1 k ∘ u;
  sq_in2 : sq_map ∘ cospan_in2 h ≈ cospan_in2 k ∘ v
}.

Arguments sq_map {a b c d h u v k} _.
Arguments sq_in1 {a b c d h u v k} _.
Arguments sq_in2 {a b c d h u v k} _.

(** The square setoid compares the apex maps (real data, not a mere
    proposition). *)
Program Instance CospanSq_Setoid {a b c d : C}
        {h : CospanArrow a b} {u : a ~> c} {v : b ~> d}
        {k : CospanArrow c d} : Setoid (CospanSq h u v k) := {|
  equiv := fun s t => sq_map s ≈ sq_map t
|}.

(** Boundary coercion: the apex map is unchanged, only its recorded
    boundary proofs are rebuilt along [≈]-equal vertical edges. *)
Program Definition CospanSq_coerce {a b c d : C} {h : CospanArrow a b}
        {u u' : a ~> c} {v v' : b ~> d} {k : CospanArrow c d}
        (eu : u ≈ u') (ev : v ≈ v') (s : CospanSq h u v k) :
  CospanSq h u' v' k := {|
  sq_map := sq_map s
|}.
Next Obligation. rewrite <- eu; apply sq_in1. Qed.
Next Obligation. rewrite <- ev; apply sq_in2. Qed.

Lemma CospanSq_coerce_respects {a b c d : C} {h : CospanArrow a b}
      {u u' : a ~> c} {v v' : b ~> d} {k : CospanArrow c d}
      (eu : u ≈ u') (ev : v ≈ v') :
  Proper (equiv ==> equiv) (@CospanSq_coerce a b c d h u u' v v' k eu ev).
Proof. proper. Qed.

(** Vertical identity square. *)
Program Definition CospanSq_vid {a b : C} (h : CospanArrow a b) :
  CospanSq h id id h := {| sq_map := id |}.

(** Vertical pasting of squares. *)
Program Definition CospanSq_vcomp {a0 b0 a1 b1 a2 b2 : C}
        {h : CospanArrow a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
        {k : CospanArrow a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
        {l : CospanArrow a2 b2}
        (s : CospanSq h u v k) (t : CospanSq k u' v' l) :
  CospanSq h (u' ∘ u) (v' ∘ v) l := {|
  sq_map := sq_map t ∘ sq_map s
|}.
Next Obligation.
  rewrite <- comp_assoc, (sq_in1 s), comp_assoc, (sq_in1 t).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite <- comp_assoc, (sq_in2 s), comp_assoc, (sq_in2 t).
  now rewrite comp_assoc.
Qed.

Lemma CospanSq_vcomp_respects {a0 b0 a1 b1 a2 b2 : C}
      {h : CospanArrow a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
      {k : CospanArrow a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
      {l : CospanArrow a2 b2} :
  Proper (equiv ==> equiv ==> equiv)
    (@CospanSq_vcomp a0 b0 a1 b1 a2 b2 h u v k u' v' l).
Proof.
  proper.
Qed.

(** ** Horizontal pasting of squares

    Two squares sharing their middle vertical edge [v] induce, by the
    universal property of the gluing pushout of their top cospans, a square
    between the glued cospans.  The mediator's legs land in the gluing
    pushout of the bottom cospans. *)

Lemma glue_comm {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'}
      (s : CospanSq h u v k) (t : CospanSq h' v w k') :
  (pushout_in1 (gpo k k') ∘ sq_map s) ∘ cospan_in2 h
  ≈ (pushout_in2 (gpo k k') ∘ sq_map t) ∘ cospan_in1 h'.
Proof.
  rewrite <- comp_assoc, (sq_in2 s), comp_assoc.
  rewrite <- (comp_assoc _ (sq_map t)), (sq_in1 t), comp_assoc.
  now rewrite (pushout_commutes (gpo k k')).
Qed.

Definition CospanSq_hmap {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'}
      (s : CospanSq h u v k) (t : CospanSq h' v w k') :
  pushout_apex (gpo h h') ~> pushout_apex (gpo k k') :=
  pushout_med (gpo h h') (glue_comm s t).

Lemma CospanSq_hmap_in1 {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'}
      (s : CospanSq h u v k) (t : CospanSq h' v w k') :
  CospanSq_hmap s t ∘ pushout_in1 (gpo h h')
  ≈ pushout_in1 (gpo k k') ∘ sq_map s.
Proof. apply pushout_med_in1. Qed.

Lemma CospanSq_hmap_in2 {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'}
      (s : CospanSq h u v k) (t : CospanSq h' v w k') :
  CospanSq_hmap s t ∘ pushout_in2 (gpo h h')
  ≈ pushout_in2 (gpo k k') ∘ sq_map t.
Proof. apply pushout_med_in2. Qed.

Program Definition CospanSq_hcomp {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'}
      (s : CospanSq h u v k) (t : CospanSq h' v w k') :
  CospanSq (cospan_compose HP h' h) u w (cospan_compose HP k' k) := {|
  sq_map := CospanSq_hmap s t
|}.
Next Obligation.
  rewrite comp_assoc, CospanSq_hmap_in1.
  rewrite <- (comp_assoc (pushout_in1 (gpo k k'))), (sq_in1 s).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite comp_assoc, CospanSq_hmap_in2.
  rewrite <- (comp_assoc (pushout_in2 (gpo k k'))), (sq_in2 t).
  now rewrite comp_assoc.
Qed.

Lemma CospanSq_hcomp_respects {a b c a' b' c' : C}
      {h : CospanArrow a b} {h' : CospanArrow b c}
      {u : a ~> a'} {v : b ~> b'} {w : c ~> c'}
      {k : CospanArrow a' b'} {k' : CospanArrow b' c'} :
  Proper (equiv ==> equiv ==> equiv)
    (@CospanSq_hcomp a b c a' b' c' h h' u v w k k').
Proof.
  proper; simpl.
  apply (pushout_jointly_epic (gpo h h')).
  - etransitivity; [ apply (CospanSq_hmap_in1 x x0) |].
    etransitivity; [| symmetry; apply (CospanSq_hmap_in1 y y0) ].
    now apply compose_respects.
  - etransitivity; [ apply (CospanSq_hmap_in2 x x0) |].
    etransitivity; [| symmetry; apply (CospanSq_hmap_in2 y y0) ].
    now apply compose_respects.
Qed.

(** Interchange: both pastings of a 2x2 grid are mediators out of the same
    gluing pushout with the same legs. *)
Lemma CospanSq_interchange {a b c a' b' c' a'' b'' c'' : C}
      {h1 : CospanArrow a b} {h2 : CospanArrow b c}
      {u1 : a ~> a'} {u2 : b ~> b'} {u3 : c ~> c'}
      {j1 : CospanArrow a' b'} {j2 : CospanArrow b' c'}
      {w1 : a' ~> a''} {w2 : b' ~> b''} {w3 : c' ~> c''}
      {k1 : CospanArrow a'' b''} {k2 : CospanArrow b'' c''}
      (s11 : CospanSq h1 u1 u2 j1) (s12 : CospanSq h2 u2 u3 j2)
      (s21 : CospanSq j1 w1 w2 k1) (s22 : CospanSq j2 w2 w3 k2) :
  CospanSq_vcomp (CospanSq_hcomp s11 s12) (CospanSq_hcomp s21 s22)
  ≈ CospanSq_hcomp (CospanSq_vcomp s11 s21) (CospanSq_vcomp s12 s22).
Proof.
  simpl.
  apply (pushout_jointly_epic (gpo h1 h2)).
  - rewrite <- comp_assoc, (CospanSq_hmap_in1 s11 s12).
    rewrite comp_assoc, (CospanSq_hmap_in1 s21 s22).
    rewrite (CospanSq_hmap_in1 (CospanSq_vcomp s11 s21)
                               (CospanSq_vcomp s12 s22)); simpl.
    now rewrite comp_assoc.
  - rewrite <- comp_assoc, (CospanSq_hmap_in2 s11 s12).
    rewrite comp_assoc, (CospanSq_hmap_in2 s21 s22).
    rewrite (CospanSq_hmap_in2 (CospanSq_vcomp s11 s21)
                               (CospanSq_vcomp s12 s22)); simpl.
    now rewrite comp_assoc.
Qed.

(** ** The unit globular squares

    Gluing with the identity cospan is the identity cospan up to the
    canonical pushout isomorphism; both directions are packaged as squares
    with identity vertical edges. *)

Section Unitors.

Context {a b : C}.
Context (h : CospanArrow a b).

(** *** Left unitor: [dhid b ∘h h ≅ h] *)

Let PL : IsPushout (cospan_in2 h) (cospan_in1 (cospan_id b)) :=
  gpo h (cospan_id b).

Lemma luni_comm :
  id[cospan_apex h] ∘ cospan_in2 h ≈ cospan_in2 h ∘ cospan_in1 (cospan_id b).
Proof. simpl; cat. Qed.

Definition luni_map : pushout_apex PL ~> cospan_apex h :=
  pushout_med PL luni_comm.

Lemma luni_map_in1 : luni_map ∘ pushout_in1 PL ≈ id.
Proof. apply pushout_med_in1. Qed.

Lemma luni_map_in2 : luni_map ∘ pushout_in2 PL ≈ cospan_in2 h.
Proof. apply pushout_med_in2. Qed.

Lemma Cospan_dunit_left_fwd_in1 :
  luni_map ∘ (pushout_in1 PL ∘ cospan_in1 h) ≈ cospan_in1 h ∘ id[a].
Proof. rewrite comp_assoc, luni_map_in1; cat. Qed.

Lemma Cospan_dunit_left_fwd_in2 :
  luni_map ∘ (pushout_in2 PL ∘ cospan_in2 (cospan_id b))
  ≈ cospan_in2 h ∘ id[b].
Proof. simpl; rewrite comp_assoc, luni_map_in2; cat. Qed.

Definition Cospan_dunit_left_fwd :
  CospanSq (cospan_compose HP (cospan_id b) h) id id h := {|
  sq_map := (luni_map
             : cospan_apex (cospan_compose HP (cospan_id b) h)
               ~{C}~> cospan_apex h);
  sq_in1 := Cospan_dunit_left_fwd_in1;
  sq_in2 := Cospan_dunit_left_fwd_in2
|}.

Lemma Cospan_dunit_left_bwd_in1 :
  pushout_in1 PL ∘ cospan_in1 h ≈ (pushout_in1 PL ∘ cospan_in1 h) ∘ id[a].
Proof. cat. Qed.

Lemma Cospan_dunit_left_bwd_in2 :
  pushout_in1 PL ∘ cospan_in2 h
  ≈ (pushout_in2 PL ∘ cospan_in2 (cospan_id b)) ∘ id[b].
Proof. rewrite (pushout_commutes PL); simpl; cat. Qed.

Definition Cospan_dunit_left_bwd :
  CospanSq h id id (cospan_compose HP (cospan_id b) h) := {|
  sq_map := (pushout_in1 PL
             : cospan_apex h
               ~{C}~> cospan_apex (cospan_compose HP (cospan_id b) h));
  sq_in1 := Cospan_dunit_left_bwd_in1;
  sq_in2 := Cospan_dunit_left_bwd_in2
|}.

Lemma Cospan_dunit_left_from_to : pushout_in1 PL ∘ luni_map ≈ id.
Proof.
  apply (pushout_jointly_epic PL).
  - rewrite <- (comp_assoc (pushout_in1 PL)), luni_map_in1; cat.
  - rewrite <- (comp_assoc (pushout_in1 PL)), luni_map_in2.
    rewrite (pushout_commutes PL); simpl; cat.
Qed.

(** *** Right unitor: [h ∘h dhid a ≅ h] *)

Let PR : IsPushout (cospan_in2 (cospan_id a)) (cospan_in1 h) :=
  gpo (cospan_id a) h.

Lemma runi_comm :
  cospan_in1 h ∘ cospan_in2 (cospan_id a) ≈ id[cospan_apex h] ∘ cospan_in1 h.
Proof. simpl; cat. Qed.

Definition runi_map : pushout_apex PR ~> cospan_apex h :=
  pushout_med PR runi_comm.

Lemma runi_map_in1 : runi_map ∘ pushout_in1 PR ≈ cospan_in1 h.
Proof. apply pushout_med_in1. Qed.

Lemma runi_map_in2 : runi_map ∘ pushout_in2 PR ≈ id.
Proof. apply pushout_med_in2. Qed.

Lemma Cospan_dunit_right_fwd_in1 :
  runi_map ∘ (pushout_in1 PR ∘ cospan_in1 (cospan_id a))
  ≈ cospan_in1 h ∘ id[a].
Proof. simpl; rewrite comp_assoc, runi_map_in1; cat. Qed.

Lemma Cospan_dunit_right_fwd_in2 :
  runi_map ∘ (pushout_in2 PR ∘ cospan_in2 h) ≈ cospan_in2 h ∘ id[b].
Proof. rewrite comp_assoc, runi_map_in2; cat. Qed.

Definition Cospan_dunit_right_fwd :
  CospanSq (cospan_compose HP h (cospan_id a)) id id h := {|
  sq_map := (runi_map
             : cospan_apex (cospan_compose HP h (cospan_id a))
               ~{C}~> cospan_apex h);
  sq_in1 := Cospan_dunit_right_fwd_in1;
  sq_in2 := Cospan_dunit_right_fwd_in2
|}.

Lemma Cospan_dunit_right_bwd_in1 :
  pushout_in2 PR ∘ cospan_in1 h
  ≈ (pushout_in1 PR ∘ cospan_in1 (cospan_id a)) ∘ id[a].
Proof. rewrite <- (pushout_commutes PR); simpl; cat. Qed.

Lemma Cospan_dunit_right_bwd_in2 :
  pushout_in2 PR ∘ cospan_in2 h ≈ (pushout_in2 PR ∘ cospan_in2 h) ∘ id[b].
Proof. cat. Qed.

Definition Cospan_dunit_right_bwd :
  CospanSq h id id (cospan_compose HP h (cospan_id a)) := {|
  sq_map := (pushout_in2 PR
             : cospan_apex h
               ~{C}~> cospan_apex (cospan_compose HP h (cospan_id a)));
  sq_in1 := Cospan_dunit_right_bwd_in1;
  sq_in2 := Cospan_dunit_right_bwd_in2
|}.

Lemma Cospan_dunit_right_from_to : pushout_in2 PR ∘ runi_map ≈ id.
Proof.
  apply (pushout_jointly_epic PR).
  - rewrite <- (comp_assoc (pushout_in2 PR)), runi_map_in1.
    rewrite <- (pushout_commutes PR); simpl; cat.
  - rewrite <- (comp_assoc (pushout_in2 PR)), runi_map_in2; cat.
Qed.

End Unitors.

(** ** The associator globular squares

    The two bracketings of a triple gluing are canonically isomorphic: both
    apexes receive the three cospan apexes through pushout injections, and
    the mediators in either direction are assembled from the pushout UMP in
    two steps.  All computation rules on the three "generator" legs are
    recorded, since the triangle and pentagon coherence proofs evaluate
    everything on generators. *)

Section Associator.

Context {X Y Z W : C}.
Context (p : CospanArrow X Y) (q : CospanArrow Y Z) (r : CospanArrow Z W).

Let Ppq : IsPushout (cospan_in2 p) (cospan_in1 q) := gpo p q.
Let Pqr : IsPushout (cospan_in2 q) (cospan_in1 r) := gpo q r.

(* Apex of [r ∘h (q ∘h p)]. *)
Let PL : IsPushout (pushout_in2 Ppq ∘ cospan_in2 q) (cospan_in1 r) :=
  gpo (cospan_compose HP q p) r.

(* Apex of [(r ∘h q) ∘h p]. *)
Let PR : IsPushout (cospan_in2 p) (pushout_in1 Pqr ∘ cospan_in1 q) :=
  gpo p (cospan_compose HP r q).

(** *** The forward mediator *)

Lemma assoc_m1_comm :
  pushout_in1 PR ∘ cospan_in2 p
  ≈ (pushout_in2 PR ∘ pushout_in1 Pqr) ∘ cospan_in1 q.
Proof.
  rewrite <- (comp_assoc (pushout_in2 PR)).
  apply (pushout_commutes PR).
Qed.

Definition assoc_m1 : pushout_apex Ppq ~> pushout_apex PR :=
  pushout_med Ppq assoc_m1_comm.

Lemma assoc_m1_in1 : assoc_m1 ∘ pushout_in1 Ppq ≈ pushout_in1 PR.
Proof. apply pushout_med_in1. Qed.

Lemma assoc_m1_in2 :
  assoc_m1 ∘ pushout_in2 Ppq ≈ pushout_in2 PR ∘ pushout_in1 Pqr.
Proof. apply pushout_med_in2. Qed.

Lemma assoc_fwd_comm :
  assoc_m1 ∘ (pushout_in2 Ppq ∘ cospan_in2 q)
  ≈ (pushout_in2 PR ∘ pushout_in2 Pqr) ∘ cospan_in1 r.
Proof.
  rewrite (comp_assoc assoc_m1), assoc_m1_in2.
  rewrite <- (comp_assoc (pushout_in2 PR)).
  rewrite (pushout_commutes Pqr).
  now rewrite (comp_assoc (pushout_in2 PR)).
Qed.

Definition assoc_fwd_map : pushout_apex PL ~> pushout_apex PR :=
  pushout_med PL assoc_fwd_comm.

Lemma assoc_fwd_in1 : assoc_fwd_map ∘ pushout_in1 PL ≈ assoc_m1.
Proof. apply pushout_med_in1. Qed.

(* Generator computation rules: the [p], [q] and [r] legs. *)

Lemma assoc_fwd_p :
  assoc_fwd_map ∘ (pushout_in1 PL ∘ pushout_in1 Ppq) ≈ pushout_in1 PR.
Proof.
  rewrite (comp_assoc assoc_fwd_map), assoc_fwd_in1.
  apply assoc_m1_in1.
Qed.

Lemma assoc_fwd_q :
  assoc_fwd_map ∘ (pushout_in1 PL ∘ pushout_in2 Ppq)
  ≈ pushout_in2 PR ∘ pushout_in1 Pqr.
Proof.
  rewrite (comp_assoc assoc_fwd_map), assoc_fwd_in1.
  apply assoc_m1_in2.
Qed.

Lemma assoc_fwd_r :
  assoc_fwd_map ∘ pushout_in2 PL ≈ pushout_in2 PR ∘ pushout_in2 Pqr.
Proof. apply pushout_med_in2. Qed.

(** *** The backward mediator *)

Lemma assoc_m2_comm :
  (pushout_in1 PL ∘ pushout_in2 Ppq) ∘ cospan_in2 q
  ≈ pushout_in2 PL ∘ cospan_in1 r.
Proof.
  rewrite <- (comp_assoc (pushout_in1 PL)).
  apply (pushout_commutes PL).
Qed.

Definition assoc_m2 : pushout_apex Pqr ~> pushout_apex PL :=
  pushout_med Pqr assoc_m2_comm.

Lemma assoc_m2_in1 :
  assoc_m2 ∘ pushout_in1 Pqr ≈ pushout_in1 PL ∘ pushout_in2 Ppq.
Proof. apply pushout_med_in1. Qed.

Lemma assoc_m2_in2 : assoc_m2 ∘ pushout_in2 Pqr ≈ pushout_in2 PL.
Proof. apply pushout_med_in2. Qed.

Lemma assoc_bwd_comm :
  (pushout_in1 PL ∘ pushout_in1 Ppq) ∘ cospan_in2 p
  ≈ assoc_m2 ∘ (pushout_in1 Pqr ∘ cospan_in1 q).
Proof.
  rewrite <- (comp_assoc (pushout_in1 PL)).
  rewrite (pushout_commutes Ppq).
  rewrite (comp_assoc (pushout_in1 PL)).
  rewrite <- assoc_m2_in1.
  now rewrite <- (comp_assoc assoc_m2).
Qed.

Definition assoc_bwd_map : pushout_apex PR ~> pushout_apex PL :=
  pushout_med PR assoc_bwd_comm.

Lemma assoc_bwd_p :
  assoc_bwd_map ∘ pushout_in1 PR ≈ pushout_in1 PL ∘ pushout_in1 Ppq.
Proof. apply pushout_med_in1. Qed.

Lemma assoc_bwd_in2 : assoc_bwd_map ∘ pushout_in2 PR ≈ assoc_m2.
Proof. apply pushout_med_in2. Qed.

Lemma assoc_bwd_q :
  assoc_bwd_map ∘ (pushout_in2 PR ∘ pushout_in1 Pqr)
  ≈ pushout_in1 PL ∘ pushout_in2 Ppq.
Proof.
  rewrite (comp_assoc assoc_bwd_map), assoc_bwd_in2.
  apply assoc_m2_in1.
Qed.

Lemma assoc_bwd_r :
  assoc_bwd_map ∘ (pushout_in2 PR ∘ pushout_in2 Pqr) ≈ pushout_in2 PL.
Proof.
  rewrite (comp_assoc assoc_bwd_map), assoc_bwd_in2.
  apply assoc_m2_in2.
Qed.

(** *** The two mediators are mutually inverse *)

Lemma assoc_bwd_fwd : assoc_bwd_map ∘ assoc_fwd_map ≈ id.
Proof.
  apply (pushout_jointly_epic PL).
  - apply (pushout_jointly_epic Ppq).
    + rewrite <- (comp_assoc (assoc_bwd_map ∘ assoc_fwd_map)).
      rewrite <- (comp_assoc assoc_bwd_map).
      rewrite assoc_fwd_p, assoc_bwd_p.
      cat.
    + rewrite <- (comp_assoc (assoc_bwd_map ∘ assoc_fwd_map)).
      rewrite <- (comp_assoc assoc_bwd_map).
      rewrite assoc_fwd_q, assoc_bwd_q.
      cat.
  - rewrite <- (comp_assoc assoc_bwd_map).
    rewrite assoc_fwd_r, assoc_bwd_r.
    cat.
Qed.

Lemma assoc_fwd_bwd : assoc_fwd_map ∘ assoc_bwd_map ≈ id.
Proof.
  apply (pushout_jointly_epic PR).
  - rewrite <- (comp_assoc assoc_fwd_map).
    rewrite assoc_bwd_p, assoc_fwd_p.
    cat.
  - apply (pushout_jointly_epic Pqr).
    + rewrite <- (comp_assoc (assoc_fwd_map ∘ assoc_bwd_map)).
      rewrite <- (comp_assoc assoc_fwd_map).
      rewrite assoc_bwd_q, assoc_fwd_q.
      cat.
    + rewrite <- (comp_assoc (assoc_fwd_map ∘ assoc_bwd_map)).
      rewrite <- (comp_assoc assoc_fwd_map).
      rewrite assoc_bwd_r, assoc_fwd_r.
      cat.
Qed.

(** *** The associator squares *)

Lemma Cospan_dassoc_fwd_in1 :
  assoc_fwd_map ∘ (pushout_in1 PL ∘ (pushout_in1 Ppq ∘ cospan_in1 p))
  ≈ (pushout_in1 PR ∘ cospan_in1 p) ∘ id[X].
Proof.
  rewrite (comp_assoc (pushout_in1 PL)).
  rewrite (comp_assoc assoc_fwd_map), assoc_fwd_p.
  cat.
Qed.

Lemma Cospan_dassoc_fwd_in2 :
  assoc_fwd_map ∘ (pushout_in2 PL ∘ cospan_in2 r)
  ≈ (pushout_in2 PR ∘ (pushout_in2 Pqr ∘ cospan_in2 r)) ∘ id[W].
Proof.
  rewrite (comp_assoc assoc_fwd_map), assoc_fwd_r.
  rewrite id_right.
  now rewrite (comp_assoc (pushout_in2 PR)).
Qed.

Definition Cospan_dassoc_fwd :
  CospanSq (cospan_compose HP r (cospan_compose HP q p)) id id
           (cospan_compose HP (cospan_compose HP r q) p) := {|
  sq_map := (assoc_fwd_map
             : cospan_apex (cospan_compose HP r (cospan_compose HP q p))
               ~{C}~> cospan_apex
                        (cospan_compose HP (cospan_compose HP r q) p));
  sq_in1 := Cospan_dassoc_fwd_in1;
  sq_in2 := Cospan_dassoc_fwd_in2
|}.

Lemma Cospan_dassoc_bwd_in1 :
  assoc_bwd_map ∘ (pushout_in1 PR ∘ cospan_in1 p)
  ≈ (pushout_in1 PL ∘ (pushout_in1 Ppq ∘ cospan_in1 p)) ∘ id[X].
Proof.
  rewrite (comp_assoc assoc_bwd_map), assoc_bwd_p.
  rewrite id_right.
  now rewrite (comp_assoc (pushout_in1 PL)).
Qed.

Lemma Cospan_dassoc_bwd_in2 :
  assoc_bwd_map ∘ (pushout_in2 PR ∘ (pushout_in2 Pqr ∘ cospan_in2 r))
  ≈ (pushout_in2 PL ∘ cospan_in2 r) ∘ id[W].
Proof.
  rewrite (comp_assoc (pushout_in2 PR)).
  rewrite (comp_assoc assoc_bwd_map), assoc_bwd_r.
  cat.
Qed.

Definition Cospan_dassoc_bwd :
  CospanSq (cospan_compose HP (cospan_compose HP r q) p) id id
           (cospan_compose HP r (cospan_compose HP q p)) := {|
  sq_map := (assoc_bwd_map
             : cospan_apex (cospan_compose HP (cospan_compose HP r q) p)
               ~{C}~> cospan_apex
                        (cospan_compose HP r (cospan_compose HP q p)));
  sq_in1 := Cospan_dassoc_bwd_in1;
  sq_in2 := Cospan_dassoc_bwd_in2
|}.

End Associator.

(** ** The strict vertical laws and coercion groupoid laws

    All of them are φ-level identities: [CospanSq_coerce] preserves the apex
    map on the nose, and vertical pasting is composition of apex maps. *)

Lemma CospanSq_coerce_id {a b c d : C} {h : CospanArrow a b}
      {u : a ~> c} {v : b ~> d} {k : CospanArrow c d}
      (eu : u ≈ u) (ev : v ≈ v) (s : CospanSq h u v k) :
  CospanSq_coerce eu ev s ≈ s.
Proof. simpl; reflexivity. Qed.

Lemma CospanSq_coerce_trans {a b c d : C} {h : CospanArrow a b}
      {u u' u'' : a ~> c} {v v' v'' : b ~> d} {k : CospanArrow c d}
      (eu : u ≈ u') (eu' : u' ≈ u'') (ev : v ≈ v') (ev' : v' ≈ v'')
      (s : CospanSq h u v k) :
  CospanSq_coerce eu' ev' (CospanSq_coerce eu ev s)
    ≈ CospanSq_coerce (Equivalence_Transitive _ _ _ eu eu')
                      (Equivalence_Transitive _ _ _ ev ev') s.
Proof. simpl; reflexivity. Qed.

Lemma CospanSq_vid_left {a b c d : C} {h : CospanArrow a b}
      {u : a ~> c} {v : b ~> d} {k : CospanArrow c d}
      (s : CospanSq h u v k) :
  CospanSq_coerce (id_left u) (id_left v)
                  (CospanSq_vcomp s (CospanSq_vid k)) ≈ s.
Proof. simpl; cat. Qed.

Lemma CospanSq_vid_right {a b c d : C} {h : CospanArrow a b}
      {u : a ~> c} {v : b ~> d} {k : CospanArrow c d}
      (s : CospanSq h u v k) :
  CospanSq_coerce (id_right u) (id_right v)
                  (CospanSq_vcomp (CospanSq_vid h) s) ≈ s.
Proof. simpl; cat. Qed.

Lemma CospanSq_vassoc {a0 b0 a1 b1 a2 b2 a3 b3 : C}
      {h : CospanArrow a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
      {k : CospanArrow a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
      {l : CospanArrow a2 b2} {u'' : a2 ~> a3} {v'' : b2 ~> b3}
      {m : CospanArrow a3 b3}
      (s : CospanSq h u v k) (t : CospanSq k u' v' l)
      (r : CospanSq l u'' v'' m) :
  CospanSq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
                  (CospanSq_vcomp (CospanSq_vcomp s t) r)
    ≈ CospanSq_vcomp s (CospanSq_vcomp t r).
Proof. simpl; apply comp_assoc. Qed.

(** ** Reduction bridges for the apex maps of the named squares

    These let the coherence proofs replace [sq_map (...)] subterms by their
    underlying pushout mediators without relying on [simpl]'s traversal. *)

Lemma CospanSq_vid_map {a b : C} (h : CospanArrow a b) :
  sq_map (CospanSq_vid h) ≈ id[cospan_apex h].
Proof. reflexivity. Qed.

Lemma Cospan_dunit_left_fwd_map {a b : C} (h : CospanArrow a b) :
  sq_map (Cospan_dunit_left_fwd h) ≈ luni_map h.
Proof. reflexivity. Qed.

Lemma Cospan_dunit_right_fwd_map {a b : C} (h : CospanArrow a b) :
  sq_map (Cospan_dunit_right_fwd h) ≈ runi_map h.
Proof. reflexivity. Qed.

Lemma Cospan_dassoc_fwd_map {X Y Z W : C}
      (p : CospanArrow X Y) (q : CospanArrow Y Z) (r : CospanArrow Z W) :
  sq_map (Cospan_dassoc_fwd p q r) ≈ assoc_fwd_map p q r.
Proof. reflexivity. Qed.

(** ** Triangle coherence

    Whiskering the left unitor equals the associator followed by whiskering
    the right unitor, evaluated on the three generator legs of the iterated
    gluing pushout of [k ∘h (dhid b ∘h f)].  The middle generator is exactly
    the pushout square of the bottom gluing [gpo f k]. *)

Lemma Cospan_triangle {a b c : C} (f : CospanArrow a b) (k : CospanArrow b c) :
  CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k)
    ∘ assoc_fwd_map f (cospan_id b) k
  ≈ CospanSq_hmap (Cospan_dunit_left_fwd f) (CospanSq_vid k).
Proof.
  apply (pushout_jointly_epic (gpo (cospan_compose HP (cospan_id b) f) k)).
  - apply (pushout_jointly_epic (gpo f (cospan_id b))).
    + (* generator: apex f *)
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
      rewrite <- (comp_assoc (assoc_fwd_map f (cospan_id b) k)).
      rewrite (assoc_fwd_p f (cospan_id b) k).
      rewrite (CospanSq_hmap_in1 (CospanSq_vid f) (Cospan_dunit_right_fwd k)).
      rewrite (CospanSq_vid_map f), id_right.
      rewrite (CospanSq_hmap_in1 (Cospan_dunit_left_fwd f) (CospanSq_vid k)).
      rewrite (Cospan_dunit_left_fwd_map f).
      rewrite <- (comp_assoc (pushout_in1 (gpo f k))).
      rewrite (luni_map_in1 f).
      cat.
    + (* generator: the shared boundary object b *)
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
      rewrite <- (comp_assoc (assoc_fwd_map f (cospan_id b) k)).
      rewrite (assoc_fwd_q f (cospan_id b) k).
      rewrite (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
      rewrite (CospanSq_hmap_in2 (CospanSq_vid f) (Cospan_dunit_right_fwd k)).
      rewrite (Cospan_dunit_right_fwd_map k).
      rewrite <- (comp_assoc (pushout_in2 (gpo f k))).
      rewrite (runi_map_in1 k).
      rewrite (CospanSq_hmap_in1 (Cospan_dunit_left_fwd f) (CospanSq_vid k)).
      rewrite (Cospan_dunit_left_fwd_map f).
      rewrite <- (comp_assoc (pushout_in1 (gpo f k))).
      rewrite (luni_map_in2 f).
      symmetry.
      apply (pushout_commutes (gpo f k)).
  - (* generator: apex k *)
    rewrite <- (comp_assoc
      (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
    rewrite (assoc_fwd_r f (cospan_id b) k).
    rewrite (comp_assoc
      (CospanSq_hmap (CospanSq_vid f) (Cospan_dunit_right_fwd k))).
    rewrite (CospanSq_hmap_in2 (CospanSq_vid f) (Cospan_dunit_right_fwd k)).
    rewrite (Cospan_dunit_right_fwd_map k).
    rewrite <- (comp_assoc (pushout_in2 (gpo f k))).
    rewrite (runi_map_in2 k), id_right.
    rewrite (CospanSq_hmap_in2 (Cospan_dunit_left_fwd f) (CospanSq_vid k)).
    rewrite (CospanSq_vid_map k).
    cat.
Qed.

(** ** Pentagon coherence

    The two globular paths from [k ∘h (h ∘h (g ∘h f))] to
    [((k ∘h h) ∘h g) ∘h f] agree.  Both sides are morphisms out of a
    three-fold iterated pushout, so the proof evaluates them on the four
    generator legs (the apexes of [f], [g], [h] and [k]) via three nested
    applications of joint epimorphy; on each generator both sides compute,
    by the mediator rules, to the same composite of injections into the
    target apex. *)

Lemma Cospan_pentagon {a b c d e : C}
      (f : CospanArrow a b) (g : CospanArrow b c)
      (h : CospanArrow c d) (k : CospanArrow d e) :
  CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
    ∘ (assoc_fwd_map f (cospan_compose HP h g) k
       ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k))
  ≈ assoc_fwd_map f g (cospan_compose HP k h)
    ∘ assoc_fwd_map (cospan_compose HP g f) h k.
Proof.
  apply (pushout_jointly_epic
           (gpo (cospan_compose HP h (cospan_compose HP g f)) k)).
  - apply (pushout_jointly_epic (gpo (cospan_compose HP g f) h)).
    + apply (pushout_jointly_epic (gpo f g)).
      * (* generator: apex f *)
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
           ∘ (assoc_fwd_map f (cospan_compose HP h g) k
              ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k)))).
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
           ∘ (assoc_fwd_map f (cospan_compose HP h g) k
              ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k)))).
        rewrite <- (comp_assoc (pushout_in1
          (gpo (cospan_compose HP h (cospan_compose HP g f)) k))).
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
        rewrite <- (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
        rewrite (comp_assoc
          (CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k))).
        rewrite (CospanSq_hmap_in1 (Cospan_dassoc_fwd f g h)
                                   (CospanSq_vid k)).
        rewrite (Cospan_dassoc_fwd_map f g h).
        rewrite <- (comp_assoc (pushout_in1
          (gpo (cospan_compose HP (cospan_compose HP h g) f) k))).
        rewrite (assoc_fwd_p f g h).
        rewrite (assoc_fwd_p f (cospan_compose HP h g) k).
        rewrite (CospanSq_hmap_in1 (CospanSq_vid f)
                                   (Cospan_dassoc_fwd g h k)).
        rewrite (CospanSq_vid_map f), id_right.
        rewrite <- (comp_assoc
          (assoc_fwd_map f g (cospan_compose HP k h)
           ∘ assoc_fwd_map (cospan_compose HP g f) h k)).
        rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
        rewrite (assoc_fwd_p (cospan_compose HP g f) h k).
        rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
        rewrite (assoc_fwd_p f g (cospan_compose HP k h)).
        reflexivity.
      * (* generator: apex g *)
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
           ∘ (assoc_fwd_map f (cospan_compose HP h g) k
              ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k)))).
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
           ∘ (assoc_fwd_map f (cospan_compose HP h g) k
              ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k)))).
        rewrite <- (comp_assoc (pushout_in1
          (gpo (cospan_compose HP h (cospan_compose HP g f)) k))).
        rewrite <- (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
        rewrite <- (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
        rewrite (comp_assoc
          (CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k))).
        rewrite (CospanSq_hmap_in1 (Cospan_dassoc_fwd f g h)
                                   (CospanSq_vid k)).
        rewrite (Cospan_dassoc_fwd_map f g h).
        rewrite <- (comp_assoc (pushout_in1
          (gpo (cospan_compose HP (cospan_compose HP h g) f) k))).
        rewrite (assoc_fwd_q f g h).
        rewrite (comp_assoc (pushout_in1
          (gpo (cospan_compose HP (cospan_compose HP h g) f) k))).
        rewrite (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
        rewrite (assoc_fwd_q f (cospan_compose HP h g) k).
        rewrite <- (comp_assoc (pushout_in2
          (gpo f (cospan_compose HP k (cospan_compose HP h g))))).
        rewrite (comp_assoc
          (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
        rewrite (CospanSq_hmap_in2 (CospanSq_vid f)
                                   (Cospan_dassoc_fwd g h k)).
        rewrite (Cospan_dassoc_fwd_map g h k).
        rewrite <- (comp_assoc (pushout_in2
          (gpo f (cospan_compose HP (cospan_compose HP k h) g)))).
        rewrite (assoc_fwd_p g h k).
        rewrite <- (comp_assoc
          (assoc_fwd_map f g (cospan_compose HP k h)
           ∘ assoc_fwd_map (cospan_compose HP g f) h k)).
        rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
        rewrite (assoc_fwd_p (cospan_compose HP g f) h k).
        rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
        rewrite (assoc_fwd_q f g (cospan_compose HP k h)).
        reflexivity.
    + (* generator: apex h *)
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k)
         ∘ (assoc_fwd_map f (cospan_compose HP h g) k
            ∘ CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k)))).
      rewrite <- (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
      rewrite <- (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
      rewrite (comp_assoc
        (CospanSq_hmap (Cospan_dassoc_fwd f g h) (CospanSq_vid k))).
      rewrite (CospanSq_hmap_in1 (Cospan_dassoc_fwd f g h) (CospanSq_vid k)).
      rewrite (Cospan_dassoc_fwd_map f g h).
      rewrite <- (comp_assoc (pushout_in1
        (gpo (cospan_compose HP (cospan_compose HP h g) f) k))).
      rewrite (assoc_fwd_r f g h).
      rewrite (comp_assoc (pushout_in1
        (gpo (cospan_compose HP (cospan_compose HP h g) f) k))).
      rewrite (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
      rewrite (assoc_fwd_q f (cospan_compose HP h g) k).
      rewrite <- (comp_assoc (pushout_in2
        (gpo f (cospan_compose HP k (cospan_compose HP h g))))).
      rewrite (comp_assoc
        (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
      rewrite (CospanSq_hmap_in2 (CospanSq_vid f) (Cospan_dassoc_fwd g h k)).
      rewrite (Cospan_dassoc_fwd_map g h k).
      rewrite <- (comp_assoc (pushout_in2
        (gpo f (cospan_compose HP (cospan_compose HP k h) g)))).
      rewrite (assoc_fwd_q g h k).
      rewrite <- (comp_assoc
        (assoc_fwd_map f g (cospan_compose HP k h)
         ∘ assoc_fwd_map (cospan_compose HP g f) h k)).
      rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
      rewrite (assoc_fwd_q (cospan_compose HP g f) h k).
      rewrite (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
      rewrite (assoc_fwd_r f g (cospan_compose HP k h)).
      rewrite <- (comp_assoc (pushout_in2
        (gpo f (cospan_compose HP (cospan_compose HP k h) g)))).
      reflexivity.
  - (* generator: apex k *)
    rewrite <- (comp_assoc
      (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
    rewrite <- (comp_assoc (assoc_fwd_map f (cospan_compose HP h g) k)).
    rewrite (CospanSq_hmap_in2 (Cospan_dassoc_fwd f g h) (CospanSq_vid k)).
    rewrite (CospanSq_vid_map k), id_right.
    rewrite (assoc_fwd_r f (cospan_compose HP h g) k).
    rewrite (comp_assoc
      (CospanSq_hmap (CospanSq_vid f) (Cospan_dassoc_fwd g h k))).
    rewrite (CospanSq_hmap_in2 (CospanSq_vid f) (Cospan_dassoc_fwd g h k)).
    rewrite (Cospan_dassoc_fwd_map g h k).
    rewrite <- (comp_assoc (pushout_in2
      (gpo f (cospan_compose HP (cospan_compose HP k h) g)))).
    rewrite (assoc_fwd_r g h k).
    rewrite <- (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
    rewrite (assoc_fwd_r (cospan_compose HP g f) h k).
    rewrite (comp_assoc (assoc_fwd_map f g (cospan_compose HP k h))).
    rewrite (assoc_fwd_r f g (cospan_compose HP k h)).
    rewrite <- (comp_assoc (pushout_in2
      (gpo f (cospan_compose HP (cospan_compose HP k h) g)))).
    reflexivity.
Qed.

(** ** The double category of cospans *)

Definition Cospan_Double : DoubleCategory := {|
  dcat := C;
  dhor := @CospanArrow C;
  dsq := @CospanSq;
  dsq_setoid := @CospanSq_Setoid;
  dsq_coerce := @CospanSq_coerce;
  dsq_coerce_respects := @CospanSq_coerce_respects;
  dsq_coerce_id := @CospanSq_coerce_id;
  dsq_coerce_trans := @CospanSq_coerce_trans;
  dsq_vid := @CospanSq_vid;
  dsq_vcomp := @CospanSq_vcomp;
  dsq_vcomp_respects := @CospanSq_vcomp_respects;
  dsq_vid_left := @CospanSq_vid_left;
  dsq_vid_right := @CospanSq_vid_right;
  dsq_vassoc := @CospanSq_vassoc;
  dhid := cospan_id;
  dhcomp := fun x y z g f => cospan_compose HP g f;
  dsq_hcomp := @CospanSq_hcomp;
  dsq_hcomp_respects := @CospanSq_hcomp_respects;
  dinterchange := @CospanSq_interchange;
  dassoc := fun x y z w f g h =>
    existT _ (Cospan_dassoc_fwd f g h)
      (existT _ (Cospan_dassoc_bwd f g h)
         (assoc_bwd_fwd f g h, assoc_fwd_bwd f g h));
  dunit_left := fun x y h =>
    existT _ (Cospan_dunit_left_fwd h)
      (existT _ (Cospan_dunit_left_bwd h)
         (Cospan_dunit_left_from_to h, luni_map_in1 h));
  dunit_right := fun x y h =>
    existT _ (Cospan_dunit_right_fwd h)
      (existT _ (Cospan_dunit_right_bwd h)
         (Cospan_dunit_right_from_to h, runi_map_in2 h));
  dcoherence_triangle := fun x y z f k => Cospan_triangle f k;
  dcoherence_pentagon := fun x y z w v f g h k => Cospan_pentagon f g h k
|}.

End CospanDouble.

Arguments Cospan_Double : clear implicits.
