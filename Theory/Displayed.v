Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Displayed categories *)

(* nLab:      https://ncatlab.org/nlab/show/displayed+category
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
              Categories", Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   A displayed category [D] over a base category [C] assigns to each object
   [x : C] a type [dobj x] of objects lying over [x], and to each base
   morphism [f : x ~> y] and displayed objects [dx : dobj x], [dy : dobj y] a
   setoid [dhom dx dy f] of morphisms lying over [f], together with displayed
   identities lying over [id] and displayed composition lying over [∘]. This
   is the Coq-friendly primitive presentation of fibred/indexed category
   theory: the total category [∫ D] (Construction/Displayed/Total.v) has
   pairs [(x; dx)] as objects and pairs [(f; ff)] as morphisms, and a
   displayed category is exactly the data making that total assembly a
   category, packaged without ever comparing objects of [C] for equality.

   Because homs in this library are setoids, the family [dhom dx dy] is
   indexed by base morphisms that are only ever compared up to [≈], so the
   family must itself cohere across [≈]. That coherence is [dtransport]:
   along every proof [e : f ≈ g] a map
   [dtransport e : dhom dx dy f → dhom dx dy g] which respects [≈]
   ([dtransport_respects]), is functorial ([dtransport_trans]), and is
   proof-irrelevant ([dtransport_id]: transport along any proof of [f ≈ f]
   is the identity up to [≈]; combined with functoriality this yields
   irrelevance along arbitrary parallel proofs, [dtransport_proof_irrel]
   below). The displayed unit and associativity laws are then stated over
   the corresponding base laws by transporting one side along them.

   Interface note (a disclosed strengthening of the Phase 10 skeleton). The
   interchange of transport with displayed composition,

     dcomp (dtransport e ff) gg ≈ dtransport e' (dcomp ff gg)
     dcomp ff (dtransport e gg) ≈ dtransport e' (dcomp ff gg),

   is not derivable from the other fields, so it is part of the interface as
   [dtransport_comp_l]/[dtransport_comp_r]. Underivability: take the base to
   be the one-object category with hom-monoid (ℤ, +, 0) and with [f ≈ g]
   meaning congruence modulo 2; display over it the constant family
   [dhom _ _ f := ℤ] under [eq], with [dtransport e] the identity map,
   [did := 0], and with displayed composition over outer base [f] and inner
   base [g] given by [(k, l) ↦ k + l + f·g]. Since [f·g] is bilinear (a
   2-cocycle on ℤ vanishing when either argument is 0), every other field
   below holds in this model; yet with outer bases [e : 0 ≈ 2] and inner
   base [1], the left-hand side of the interchange computes over (2, 1) to
   [0 + 0 + 2·1 = 2] while the right-hand side computes over (0, 1) to
   [0 + 0 + 0·1 = 0], and [2 ≠ 0] in the strict fibre (ℤ, eq). The
   composite-side proof [e'] is universally quantified rather than pinned to
   the canonical [compose_respects] witness: by proof-irrelevance of
   [dtransport] the two phrasings are interderivable, and the quantified
   form spares consumers from massaging proof terms. *)

Class Displayed (C : Category) := {
  dobj : C → Type;

  dhom {x y} : dobj x → dobj y → (x ~> y) → Type;

  dhomset {x y} (dx : dobj x) (dy : dobj y) (f : x ~> y) :
    Setoid (dhom dx dy f);

  dtransport {x y} {dx dy} {f g : x ~> y} (e : f ≈ g) :
    dhom dx dy f → dhom dx dy g;

  dtransport_respects {x y dx dy} {f g : x ~> y} (e : f ≈ g) :
    Proper (equiv ==> equiv) (@dtransport x y dx dy f g e);

  (* Proof irrelevance: transport along a loop is the identity. *)
  dtransport_id {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (e : f ≈ f) (ff : dhom dx dy f) :
    dtransport e ff ≈ ff;

  dtransport_trans {x y} {dx : dobj x} {dy : dobj y} {f g h : x ~> y}
    (e1 : f ≈ g) (e2 : g ≈ h) (ff : dhom dx dy f) :
    dtransport e2 (dtransport e1 ff)
      ≈ dtransport (Equivalence_Transitive _ _ _ e1 e2) ff;

  did {x} (dx : dobj x) : dhom dx dx id;

  dcomp {x y z} {dx dy dz} {f : y ~> z} {g : x ~> y} :
    dhom dy dz f → dhom dx dy g → dhom dx dz (f ∘ g);

  dcomp_respects {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g : x ~> y} :
    Proper (equiv ==> equiv ==> equiv) (@dcomp x y z dx dy dz f g);

  (* Interchange of transport with displayed composition, on either side
     (see the interface note above for why these are structure, not
     consequences). *)
  dtransport_comp_l {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f f' : y ~> z} {g : x ~> y} (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g)
    (ff : dhom dy dz f) (gg : dhom dx dy g) :
    dcomp (dtransport e ff) gg ≈ dtransport e' (dcomp ff gg);

  dtransport_comp_r {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g g' : x ~> y} (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g')
    (ff : dhom dy dz f) (gg : dhom dx dy g) :
    dcomp ff (dtransport e gg) ≈ dtransport e' (dcomp ff gg);

  did_left {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (ff : dhom dx dy f) :
    dcomp (did dy) ff ≈ dtransport (symmetry (id_left f)) ff;

  did_right {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (ff : dhom dx dy f) :
    dcomp ff (did dx) ≈ dtransport (symmetry (id_right f)) ff;

  dcomp_assoc {w x y z}
    {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g : x ~> y} {h : w ~> x}
    (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
    dcomp ff (dcomp gg hh)
      ≈ dtransport (symmetry (comp_assoc f g h)) (dcomp (dcomp ff gg) hh)
}.
#[export] Existing Instance dhomset.   (* mirrors homset's registration *)
#[export] Existing Instance dtransport_respects.  (* mirrors compose_respects *)
#[export] Existing Instance dcomp_respects.

(** ** The derived transport lemma pack

    Everything below is a consequence of the class fields. These lemmas are
    budgeted here deliberately: the associativity and unit proofs for the
    total category (Construction/Displayed/Total.v) spend all of their time
    reorienting and cancelling transports, and each step is one of the
    lemmas in this pack. *)

Section DisplayedTransport.

Context {C : Category}.
Context {D : Displayed C}.

(* Transporting there and back again cancels (left orientation). *)
Lemma dtransport_symm_l {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (ff : dhom dx dy f) :
  dtransport (symmetry e) (dtransport e ff) ≈ ff.
Proof.
  rewrite dtransport_trans; apply dtransport_id.
Qed.

(* Transporting back and there again cancels (right orientation). *)
Lemma dtransport_symm_r {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (gg : dhom dx dy g) :
  dtransport e (dtransport (symmetry e) gg) ≈ gg.
Proof.
  rewrite dtransport_trans; apply dtransport_id.
Qed.

(* Reorienting a transport equation: a transport may be moved to the other
   side of [≈] by inverting the proof it rides on. *)
Lemma dtransport_flip {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (ff : dhom dx dy f) (gg : dhom dx dy g) :
  dtransport e ff ≈ gg ↔ ff ≈ dtransport (symmetry e) gg.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply dtransport_symm_l.
  - rewrite H.
    apply dtransport_symm_r.
Qed.

(* Transport does not depend on the proof transported along: the groupoid
   laws [dtransport_id]/[dtransport_trans] force any two parallel proofs to
   transport identically. *)
Lemma dtransport_proof_irrel {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e e' : f ≈ g) (ff : dhom dx dy f) :
  dtransport e ff ≈ dtransport e' ff.
Proof.
  apply (snd (dtransport_flip e ff (dtransport e' ff))).
  symmetry; rewrite dtransport_trans; apply dtransport_id.
Qed.

(* [dtransport_trans] with the composite proof replaced by any proof of the
   endpoints' relation. *)
Lemma dtransport_trans_any {x y : C} {dx : dobj x} {dy : dobj y}
  {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h) (e3 : f ≈ h)
  (ff : dhom dx dy f) :
  dtransport e2 (dtransport e1 ff) ≈ dtransport e3 ff.
Proof.
  rewrite dtransport_trans; apply dtransport_proof_irrel.
Qed.

(* Congruence of displayed composition under transport in both arguments at
   once; the two interchange fields, fused. *)
Lemma dtransport_dcomp {x y z : C} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f f' : y ~> z} {g g' : x ~> y} (e1 : f ≈ f') (e2 : g ≈ g')
  (e' : f ∘ g ≈ f' ∘ g') (ff : dhom dy dz f) (gg : dhom dx dy g) :
  dcomp (dtransport e1 ff) (dtransport e2 gg) ≈ dtransport e' (dcomp ff gg).
Proof.
  rewrite (dtransport_comp_l e1
             (compose_respects f f' e1 g' g' (Equivalence_Reflexive g'))).
  rewrite (dtransport_comp_r e2
             (compose_respects f f (Equivalence_Reflexive f) g g' e2)).
  apply dtransport_trans_any.
Qed.

(* The unit laws in transported orientation, along any proof of the base
   law: exactly the shape of the total category's unit obligations. *)
Lemma dtransport_did_left {x y : C} {dx : dobj x} {dy : dobj y}
  {f : x ~> y} (e : id ∘ f ≈ f) (ff : dhom dx dy f) :
  dtransport e (dcomp (did dy) ff) ≈ ff.
Proof.
  rewrite did_left, dtransport_trans; apply dtransport_id.
Qed.

Lemma dtransport_did_right {x y : C} {dx : dobj x} {dy : dobj y}
  {f : x ~> y} (e : f ∘ id ≈ f) (ff : dhom dx dy f) :
  dtransport e (dcomp ff (did dx)) ≈ ff.
Proof.
  rewrite did_right, dtransport_trans; apply dtransport_id.
Qed.

(* Associativity in transported orientation, along any proof of the base
   law, in both directions (matching [comp_assoc]/[comp_assoc_sym]). *)
Lemma dtransport_dcomp_assoc {w x y z : C}
  {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h)
  (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
  dtransport e (dcomp ff (dcomp gg hh)) ≈ dcomp (dcomp ff gg) hh.
Proof.
  rewrite dcomp_assoc, dtransport_trans; apply dtransport_id.
Qed.

Lemma dtransport_dcomp_assoc_sym {w x y z : C}
  {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h))
  (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
  dtransport e (dcomp (dcomp ff gg) hh) ≈ dcomp ff (dcomp gg hh).
Proof.
  rewrite dcomp_assoc; apply dtransport_proof_irrel.
Qed.

End DisplayedTransport.
