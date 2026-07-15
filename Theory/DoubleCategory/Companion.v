Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.

Generalizable All Variables.

(** * Companions and conjoints in a double category *)

(* nLab: https://ncatlab.org/nlab/show/companion+pair

   In a double category, a COMPANION of a vertical morphism [u : a ~> b] is a
   horizontal 1-cell [comp_hor : dhor a b] together with two binding squares

        a ==1a=> a                a --û--> b
        |        |                |        |
        id   η   u    and         u    ε   id
        v        v                v        v
        a --û--> b                b ==1b=> b

   (the unit [η] and counit [ε]) subject to two zigzag identities: pasting
   [η] beside [ε] horizontally is the composite of the unitors of [û]
   ([comp_zig] below), and pasting [η] above [ε] vertically is the horizontal
   identity square on [u].  The class [DoubleCategory] deliberately has no
   primitive producing a horizontal identity square on a general vertical
   morphism (only [dsq_vid], whose vertical edges are identities), so the
   vertical zigzag is not expressible in its textbook form here.  We state it
   instead in its standard equivalent REPRESENTABILITY form: the pair
   [(η, ε)] induces a transposition bijection between squares

        a --h'-> b                 a --h'-> b
        |        |                 |        |
        u        id      and       id       id
        v        v                 v        v
        b ==1b=> b                 a --û--> b

   ([companion_eval] one way, [companion_name] the other), and the two
   binding identities [comp_zag_eval]/[comp_zag_name] say the round trips
   are the identity.  In any double category with horizontal identity
   squares and natural unitors this is equivalent to the vertical zigzag;
   here it is exactly the strength needed to make companions unique up to a
   canonical invertible globular square ([companion_unique] below).

   Strength note: the record captures the POINTWISE-bijection form of the
   zigzag — the two round trips only, with no naturality of the
   transposition in [h'] — which is precisely what the uniqueness theorems
   below consume.  The equivalence with the textbook vertical zigzag quoted
   above holds against the richer signature (horizontal identity squares on
   verticals, natural unitors) that [DoubleCategory] deliberately does not
   require (see the SCOPE note in Theory/DoubleCategory.v), so it is stated
   for orientation, not re-proven here.

   A CONJOINT of [u] is the horizontal-opposite notion: a 1-cell
   [conj_hor : dhor b a] with binding squares mirrored left-to-right, and
   the transposition stated for squares whose RIGHT edge is [u]. *)

(* A composite-of-identities collapse used in the transposes' boundaries. *)
Lemma triple_id {C : Category} {x : C} : id[x] ∘ (id ∘ id) ≈ id.
Proof. cat. Qed.

(** ** Boundary coercion versus vertical pasting

    The uniqueness argument must slide a boundary coercion out of one factor
    of a vertical composite.  [DoubleCategory] states its laws with
    [dsq_coerce] outermost only, and — exactly as documented for
    [dtransport_comp_l]/[dtransport_comp_r] in Theory/Displayed.v, whose
    pattern [dsq_coerce] re-applies — the interchange of coercion with
    composition is not derivable from those laws (a 2-cocycle twist model
    separates them).  We therefore package the two missing interchange laws
    as a mixin, quantified over ANY proof of the composite boundary
    relation so no proof-term surgery is ever needed at use sites.  Both
    in-tree models satisfy them: in Sq squares are propositions, and in
    Cospan/Double [dsq_coerce] leaves the apex map untouched.  Only the
    coercion-vs-VERTICAL-composition laws are packaged, because they are
    all the uniqueness proofs below need; the horizontal analogues
    (sliding [dsq_coerce] through [dsq_hcomp]) would join this mixin when
    a consumer arrives, and hold in both models for the same reasons. *)

Class DoubleCoerceComp (D : DoubleCategory) : Type := {
  dsq_coerce_vcomp_l {a0 b0 a1 b1 a2 b2 : dcat}
    {h : dhor a0 b0} {u u' : a0 ~> a1} {v v' : b0 ~> b1} {k : dhor a1 b1}
    {w : a1 ~> a2} {x : b1 ~> b2} {l : dhor a2 b2}
    (eu : u ≈ u') (ev : v ≈ v')
    (E1 : w ∘ u ≈ w ∘ u') (E2 : x ∘ v ≈ x ∘ v')
    (s : dsq h u v k) (t : dsq k w x l) :
    dsq_vcomp (dsq_coerce eu ev s) t ≈ dsq_coerce E1 E2 (dsq_vcomp s t);

  dsq_coerce_vcomp_r {a0 b0 a1 b1 a2 b2 : dcat}
    {h : dhor a0 b0} {u : a0 ~> a1} {v : b0 ~> b1} {k : dhor a1 b1}
    {w w' : a1 ~> a2} {x x' : b1 ~> b2} {l : dhor a2 b2}
    (ew : w ≈ w') (ex : x ≈ x')
    (E1 : w ∘ u ≈ w' ∘ u) (E2 : x ∘ v ≈ x' ∘ v)
    (s : dsq h u v k) (t : dsq k w x l) :
    dsq_vcomp s (dsq_coerce ew ex t) ≈ dsq_coerce E1 E2 (dsq_vcomp s t)
}.

Section Companion.

Context {D : DoubleCategory}.

(** ** The companion transposes *)

Section CompanionTranspose.

Context {a b : dcat} (u : a ~> b) (h : dhor a b).

(* Transpose a square with left edge [u] into a globular square into [h]:
   paste the unit on its left and normalise by the unitors. *)
Definition companion_name (eta : dsq (dhid a) id u h)
  {h' : dhor a b} (e : dsq h' u id (dhid b)) : dsq h' id id h :=
  dsq_coerce triple_id triple_id
    (dsq_vcomp
       (dsq_vcomp (dunit_right_from h') (dsq_hcomp eta e))
       (dunit_left_to h)).

(* Transpose a globular square into [h] back into a square with left edge
   [u]: paste the counit underneath. *)
Definition companion_eval (eps : dsq h u id (dhid b))
  {h' : dhor a b} (g : dsq h' id id h) : dsq h' u id (dhid b) :=
  dsq_coerce (id_right u) (id_left id) (dsq_vcomp g eps).

Lemma companion_name_proper (eta : dsq (dhid a) id u h)
  {h' : dhor a b} (e e' : dsq h' u id (dhid b)) :
  e ≈ e' → companion_name eta e ≈ companion_name eta e'.
Proof.
  intros He; unfold companion_name.
  now rewrite He.
Qed.

Lemma companion_eval_proper (eps : dsq h u id (dhid b))
  {h' : dhor a b} (g g' : dsq h' id id h) :
  g ≈ g' → companion_eval eps g ≈ companion_eval eps g'.
Proof.
  intros Hg; unfold companion_eval.
  now rewrite Hg.
Qed.

End CompanionTranspose.

(** ** Companions *)

Record Companion {a b : dcat} (u : a ~> b) : Type := {
  comp_hor : dhor a b;

  (* The binding squares. *)
  comp_unit : dsq (dhid a) id u comp_hor;
  comp_counit : dsq comp_hor u id (dhid b);

  (* Horizontal zigzag: [η] beside [ε] is the composite of the unitors of
     the companion 1-cell (pasted side coerced onto plain side). *)
  comp_zig :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (dunit_right_to comp_hor) (dunit_left_from comp_hor))
    ≈ dsq_hcomp comp_unit comp_counit;

  (* Vertical zigzag, in representability form: the two transposes are
     mutually inverse. *)
  comp_zag_eval : ∀ (h' : dhor a b) (e : dsq h' u id (dhid b)),
    companion_eval u comp_hor comp_counit
      (companion_name u comp_hor comp_unit e) ≈ e;

  comp_zag_name : ∀ (h' : dhor a b) (g : dsq h' id id comp_hor),
    companion_name u comp_hor comp_unit
      (companion_eval u comp_hor comp_counit g) ≈ g
}.

End Companion.

Arguments comp_hor {D a b u} _.
Arguments comp_unit {D a b u} _.
Arguments comp_counit {D a b u} _.
Arguments comp_zig {D a b u} _.
Arguments comp_zag_eval {D a b u} _ _ _.
Arguments comp_zag_name {D a b u} _ _ _.

(** ** Uniqueness of companions *)

Section CompanionUnique.

Context {D : DoubleCategory}.
Context {CC : DoubleCoerceComp D}.
Context {a b : dcat} {u : a ~> b}.

(* The canonical comparison: transpose [P]'s counit through [Q]. *)
Definition companion_compare (P Q : Companion u) :
  dsq (comp_hor P) id id (comp_hor Q) :=
  companion_name u (comp_hor Q) (comp_unit Q) (comp_counit P).

(* The round trip [P → Q → P] is the vertical identity square.  Proof:
   both sides are fixed by the transposition bijection of [P], and under
   [companion_eval P] the composite evaluates — one binding identity per
   companion — back to [P]'s counit, which is also the evaluation of the
   identity square. *)
Lemma companion_compare_zigzag (P Q : Companion u) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (companion_compare P Q) (companion_compare Q P))
  ≈ dsq_vid (comp_hor P).
Proof using CC D a b u.
  assert (A1 : u ∘ (id ∘ id) ≈ (u ∘ id) ∘ id) by cat.
  assert (A2 : id[b] ∘ (id ∘ id) ≈ (id ∘ id) ∘ id) by cat.
  assert (H1 : (u ∘ id) ∘ id ≈ u) by cat.
  assert (H2 : (id[b] ∘ id) ∘ id ≈ id) by cat.
  assert (E1 : u ∘ (id ∘ id) ≈ u ∘ id) by cat.
  assert (E2 : id[b] ∘ (id ∘ id) ≈ id ∘ id) by cat.
  assert (F1 : u ∘ (id ∘ id) ≈ u) by cat.
  assert (F2 : id[b] ∘ (id ∘ id) ≈ id) by cat.
  assert (B1 : u ∘ id ≈ (u ∘ id) ∘ id) by cat.
  assert (B2 : id[b] ∘ id ≈ (id ∘ id) ∘ id) by cat.
  (* Transfer along the transposition bijection of [P]. *)
  transitivity
    (companion_name u (comp_hor P) (comp_unit P)
       (companion_eval u (comp_hor P) (comp_counit P)
          (dsq_coerce (id_left id) (id_left id)
             (dsq_vcomp (companion_compare P Q) (companion_compare Q P))))).
  { symmetry; apply comp_zag_name. }
  transitivity
    (companion_name u (comp_hor P) (comp_unit P)
       (companion_eval u (comp_hor P) (comp_counit P)
          (dsq_vid (comp_hor P)))).
  2: { apply comp_zag_name. }
  apply companion_name_proper.
  (* The identity square evaluates to the counit. *)
  transitivity (comp_counit P).
  2: {
    symmetry; unfold companion_eval.
    apply dsq_vid_right_any.
  }
  unfold companion_eval.
  (* Slide the boundary coercion of the composite out to the left. *)
  rewrite (dsq_coerce_vcomp_l (id_left id) (id_left id) E1 E2 _
             (comp_counit P)).
  rewrite (dsq_coerce_trans_any E1 (id_right u) F1 E2 (id_left id) F2).
  (* Reassociate the triple underneath a fresh coercion. *)
  rewrite <- (dsq_coerce_trans_any A1 H1 F1 A2 H2 F2).
  rewrite (dsq_vassoc_any A1 A2 (companion_compare P Q)
             (companion_compare Q P) (comp_counit P)).
  (* The lower pair is [companion_eval P] of the comparison [Q → P]. *)
  rewrite (fst (dsq_coerce_flip (id_right u) (id_left id) _ _)
             (comp_zag_eval P _ (comp_counit Q))).
  (* Slide the residual coercion out to the right and collapse. *)
  rewrite (dsq_coerce_vcomp_r (symmetry (id_right u))
             (symmetry (id_left id)) B1 B2 (companion_compare P Q)
             (comp_counit Q)).
  rewrite (dsq_coerce_trans_any B1 H1 (id_right u) B2 H2 (id_left id)).
  (* What remains is [companion_eval Q] of the comparison [P → Q]. *)
  apply (comp_zag_eval Q _ (comp_counit P)).
Qed.

(* Any two companions of [u] are connected by a canonical INVERTIBLE
   globular square, packaged exactly like the coherence isomorphisms of
   [DoubleCategory] (forward square, backward square, two round trips). *)
Definition companion_unique (P Q : Companion u) :
  { fwd : dsq (comp_hor P) id id (comp_hor Q) &
  { bwd : dsq (comp_hor Q) id id (comp_hor P) &
    prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
            ≈ dsq_vid (comp_hor P))
         (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
            ≈ dsq_vid (comp_hor Q)) } } :=
  existT _ (companion_compare P Q)
    (existT _ (companion_compare Q P)
       (companion_compare_zigzag P Q, companion_compare_zigzag Q P)).

End CompanionUnique.

(** ** Conjoints *)

Section Conjoint.

Context {D : DoubleCategory}.

Section ConjointTranspose.

Context {a b : dcat} (u : a ~> b) (h : dhor b a).

(* Transpose a square with right edge [u] into a globular square into [h]:
   paste the unit on its right and normalise by the unitors. *)
Definition conjoint_name (eta : dsq (dhid a) u id h)
  {h' : dhor b a} (e : dsq h' id u (dhid b)) : dsq h' id id h :=
  dsq_coerce triple_id triple_id
    (dsq_vcomp
       (dsq_vcomp (dunit_left_from h') (dsq_hcomp e eta))
       (dunit_right_to h)).

(* Transpose a globular square into [h] back into a square with right edge
   [u]: paste the counit underneath. *)
Definition conjoint_eval (eps : dsq h id u (dhid b))
  {h' : dhor b a} (g : dsq h' id id h) : dsq h' id u (dhid b) :=
  dsq_coerce (id_left id) (id_right u) (dsq_vcomp g eps).

Lemma conjoint_name_proper (eta : dsq (dhid a) u id h)
  {h' : dhor b a} (e e' : dsq h' id u (dhid b)) :
  e ≈ e' → conjoint_name eta e ≈ conjoint_name eta e'.
Proof.
  intros He; unfold conjoint_name.
  now rewrite He.
Qed.

Lemma conjoint_eval_proper (eps : dsq h id u (dhid b))
  {h' : dhor b a} (g g' : dsq h' id id h) :
  g ≈ g' → conjoint_eval eps g ≈ conjoint_eval eps g'.
Proof.
  intros Hg; unfold conjoint_eval.
  now rewrite Hg.
Qed.

End ConjointTranspose.

Record Conjoint {a b : dcat} (u : a ~> b) : Type := {
  conj_hor : dhor b a;

  (* The binding squares (companion squares mirrored left-to-right). *)
  conj_unit : dsq (dhid a) u id conj_hor;
  conj_counit : dsq conj_hor id u (dhid b);

  (* Horizontal zigzag: [ε] beside [η] is the composite of the unitors of
     the conjoint 1-cell. *)
  conj_zig :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (dunit_left_to conj_hor) (dunit_right_from conj_hor))
    ≈ dsq_hcomp conj_counit conj_unit;

  (* Vertical zigzag, in representability form. *)
  conj_zag_eval : ∀ (h' : dhor b a) (e : dsq h' id u (dhid b)),
    conjoint_eval u conj_hor conj_counit
      (conjoint_name u conj_hor conj_unit e) ≈ e;

  conj_zag_name : ∀ (h' : dhor b a) (g : dsq h' id id conj_hor),
    conjoint_name u conj_hor conj_unit
      (conjoint_eval u conj_hor conj_counit g) ≈ g
}.

End Conjoint.

Arguments conj_hor {D a b u} _.
Arguments conj_unit {D a b u} _.
Arguments conj_counit {D a b u} _.
Arguments conj_zig {D a b u} _.
Arguments conj_zag_eval {D a b u} _ _ _.
Arguments conj_zag_name {D a b u} _ _ _.

(** ** Uniqueness of conjoints *)

Section ConjointUnique.

Context {D : DoubleCategory}.
Context {CC : DoubleCoerceComp D}.
Context {a b : dcat} {u : a ~> b}.

Definition conjoint_compare (P Q : Conjoint u) :
  dsq (conj_hor P) id id (conj_hor Q) :=
  conjoint_name u (conj_hor Q) (conj_unit Q) (conj_counit P).

Lemma conjoint_compare_zigzag (P Q : Conjoint u) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (conjoint_compare P Q) (conjoint_compare Q P))
  ≈ dsq_vid (conj_hor P).
Proof using CC D a b u.
  assert (A1 : id[b] ∘ (id ∘ id) ≈ (id ∘ id) ∘ id) by cat.
  assert (A2 : u ∘ (id ∘ id) ≈ (u ∘ id) ∘ id) by cat.
  assert (H1 : (id[b] ∘ id) ∘ id ≈ id) by cat.
  assert (H2 : (u ∘ id) ∘ id ≈ u) by cat.
  assert (E1 : id[b] ∘ (id ∘ id) ≈ id ∘ id) by cat.
  assert (E2 : u ∘ (id ∘ id) ≈ u ∘ id) by cat.
  assert (F1 : id[b] ∘ (id ∘ id) ≈ id) by cat.
  assert (F2 : u ∘ (id ∘ id) ≈ u) by cat.
  assert (B1 : id[b] ∘ id ≈ (id ∘ id) ∘ id) by cat.
  assert (B2 : u ∘ id ≈ (u ∘ id) ∘ id) by cat.
  (* Transfer along the transposition bijection of [P]. *)
  transitivity
    (conjoint_name u (conj_hor P) (conj_unit P)
       (conjoint_eval u (conj_hor P) (conj_counit P)
          (dsq_coerce (id_left id) (id_left id)
             (dsq_vcomp (conjoint_compare P Q) (conjoint_compare Q P))))).
  { symmetry; apply conj_zag_name. }
  transitivity
    (conjoint_name u (conj_hor P) (conj_unit P)
       (conjoint_eval u (conj_hor P) (conj_counit P)
          (dsq_vid (conj_hor P)))).
  2: { apply conj_zag_name. }
  apply conjoint_name_proper.
  (* The identity square evaluates to the counit. *)
  transitivity (conj_counit P).
  2: {
    symmetry; unfold conjoint_eval.
    apply dsq_vid_right_any.
  }
  unfold conjoint_eval.
  (* Slide the boundary coercion of the composite out to the left. *)
  rewrite (dsq_coerce_vcomp_l (id_left id) (id_left id) E1 E2 _
             (conj_counit P)).
  rewrite (dsq_coerce_trans_any E1 (id_left id) F1 E2 (id_right u) F2).
  (* Reassociate the triple underneath a fresh coercion. *)
  rewrite <- (dsq_coerce_trans_any A1 H1 F1 A2 H2 F2).
  rewrite (dsq_vassoc_any A1 A2 (conjoint_compare P Q)
             (conjoint_compare Q P) (conj_counit P)).
  (* The lower pair is [conjoint_eval P] of the comparison [Q → P]. *)
  rewrite (fst (dsq_coerce_flip (id_left id) (id_right u) _ _)
             (conj_zag_eval P _ (conj_counit Q))).
  (* Slide the residual coercion out to the right and collapse. *)
  rewrite (dsq_coerce_vcomp_r (symmetry (id_left id))
             (symmetry (id_right u)) B1 B2 (conjoint_compare P Q)
             (conj_counit Q)).
  rewrite (dsq_coerce_trans_any B1 H1 (id_left id) B2 H2 (id_right u)).
  (* What remains is [conjoint_eval Q] of the comparison [P → Q]. *)
  apply (conj_zag_eval Q _ (conj_counit P)).
Qed.

(* Any two conjoints of [u] are connected by a canonical INVERTIBLE
   globular square. *)
Definition conjoint_unique (P Q : Conjoint u) :
  { fwd : dsq (conj_hor P) id id (conj_hor Q) &
  { bwd : dsq (conj_hor Q) id id (conj_hor P) &
    prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
            ≈ dsq_vid (conj_hor P))
         (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
            ≈ dsq_vid (conj_hor Q)) } } :=
  existT _ (conjoint_compare P Q)
    (existT _ (conjoint_compare Q P)
       (conjoint_compare_zigzag P Q, conjoint_compare_zigzag Q P)).

End ConjointUnique.
