Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.

Generalizable All Variables.

(** * The Grothendieck construction *)

(* nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

   The Grothendieck construction assembles an indexed category
   [A : IndexedCat B] (Construction/Indexed.v, the coherent
   "pseudofunctor-lite") into a category over [B], presented as a displayed
   category (Theory/Displayed.v) whose total category
   (Construction/Displayed/Total.v) is the classical ∫ A:

   - an object over [x : B] is an object of the fibre [idx_fib A x];
   - a morphism over [f : x ~> y] from [dx] to [dy] is a fibre morphism
     [idx_map A f dx ~> dy] — reindex forward along [f], then compare in
     the target fibre;
   - the identity over [id] is the unit iso [idx_id]; composition over
     [f ∘ g] reindexes the inner leg forward along [f] and mediates with
     the chosen composition iso [idx_comp];
   - transport along [e : f ≈ g] precomposes with the inverse of the
     mediator iso [idx_resp e], recentring the source from [idx_map g dx]
     to [idx_map f dx].

   Every displayed law is discharged from a corresponding coherence field
   of [IndexedCat]: proof irrelevance and functoriality of transport come
   from [idx_resp_id] and [idx_resp_trans]; the unit laws from
   [idx_unit_left]/[idx_unit_right] plus naturality of [idx_id];
   associativity from the cocycle [idx_cocycle] plus naturality of
   [idx_comp] in the fibre argument; and the transport/composition
   interchange from compatibility of [idx_comp] with [idx_resp]
   ([idx_comp_resp_l]/[idx_comp_resp_r]).  This file is the payoff of the
   coherent-data design: a bare [Functor B Cat] could not supply the
   cross-application equations these proofs consume (see the honesty note
   in Construction/Indexed.v).

   Following the sanctioned staging for this construction, each displayed
   law is first proven as a standalone lemma about [IndexedCat] — stated
   over an arbitrary proof of the base-law instance it transports along,
   which is harmless by proof irrelevance of [idx_resp] — and the
   [Displayed] record is then assembled from the named lemmas.

   [Grothendieck A] is the total category ∫ A, and [Grothendieck_Proj] is
   the evident projection ∫ A ⟶ B, taking an object over [x] to [x]. *)

#[local] Obligation Tactic := idtac.

Section Grothendieck.

Context {B : Category}.
Context (A : IndexedCat B).

(** ** Reindexing preserves isomorphisms

    [idx_map A f] carries fibre isos to fibre isos.  This is the generic
    fact that functors preserve isomorphisms, packaged with a stable head
    so the iso-level inversions below can name its components. *)

Program Definition idx_map_iso {x y : B} (f : x ~> y) {a b : idx_fib A x}
  (i : a ≅ b) : idx_map A f a ≅ idx_map A f b := {|
  to   := fmap[idx_map A f] (to i);
  from := fmap[idx_map A f] (from i)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.

(** ** The from-side coherence pack

    The displayed structure below writes its transports and mediators with
    [from]-components, so each coherence field of [IndexedCat] is consumed
    here in inverted orientation.  Inverting an equation between composites
    of isos is [to_equiv_implies_iso_equiv] applied at an [iso_compose]
    packaging of each side, projected to the [from] components — note the
    inverses compose in reverse order. *)

(* Transport inverses are proof-irrelevant, so [from] at [e] agrees with
   [to] at any proof [e'] of the reversed relation. *)
Lemma idx_resp_from_flip {x y : B} {f g : x ~> y} (e : f ≈ g) (e' : g ≈ f)
  (a : idx_fib A x) :
  from (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym A e a).
  apply idx_resp_irrel.
Qed.

(* [idx_comp_resp_l], inverted. *)
Lemma idx_comp_resp_l_from {x y z : B} {f f' : y ~> z} (g : x ~> y)
  (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib A x) :
  from (idx_resp A e (idx_map A g a)) ∘ from (idx_comp A f' g a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f' g a) (idx_resp A e (idx_map A g a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_l A g e e' a))).
Qed.

(* [idx_comp_resp_r], inverted. *)
Lemma idx_comp_resp_r_from {x y z : B} (f : y ~> z) {g g' : x ~> y}
  (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g') (a : idx_fib A x) :
  fmap[idx_map A f] (from (idx_resp A e a)) ∘ from (idx_comp A f g' a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f g' a) (idx_map_iso f (idx_resp A e a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_r A f e e' a))).
Qed.

(* [idx_unit_left] rearranged: cancelling the composition iso against its
   inverse isolates the mediator of the left unit law. *)
Lemma idx_unit_left_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  to (idx_id A (idx_map A f a)) ∘ from (idx_comp A (@id B y) f a)
    ≈ to (idx_resp A (id_left f) a).
Proof.
  rewrite <- (idx_unit_left A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_unit_right] rearranged likewise. *)
Lemma idx_unit_right_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  fmap[idx_map A f] (to (idx_id A a)) ∘ from (idx_comp A f (@id B x) a)
    ≈ to (idx_resp A (id_right f) a).
Proof.
  rewrite <- (idx_unit_right A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_cocycle], inverted: the from-composites reverse. *)
Lemma idx_cocycle_from {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : idx_fib A w) :
  from (idx_comp A f g (idx_map A h a)) ∘ from (idx_comp A (f ∘ g) h a)
    ≈ fmap[idx_map A f] (from (idx_comp A g h a))
        ∘ (from (idx_comp A f (g ∘ h) a)
             ∘ from (idx_resp A (comp_assoc f g h) a)).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A (f ∘ g) h a) (idx_comp A f g (idx_map A h a)))
    (iso_compose (iso_compose (idx_resp A (comp_assoc f g h) a)
                              (idx_comp A f (g ∘ h) a))
                 (idx_map_iso f (idx_comp A g h a)))
    (idx_cocycle A f g h a))).
Qed.

(** ** The displayed laws, one standalone lemma each

    Each lemma below is the exact shape of one law of the displayed
    category, with the data of the construction inlined and the transport
    proof held abstract: any proof of the relevant base relation works, by
    proof irrelevance of [idx_resp], and quantifying over it lets the
    record assembly below unify against whatever proof term the [Displayed]
    interface pins. *)

Lemma Grothendieck_transport_trans {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f g h : x ~> y}
  (e1 : f ≈ g) (e2 : g ≈ h) (e3 : f ≈ h) (ff : idx_map A f dx ~> dy) :
  (ff ∘ from (idx_resp A e1 dx)) ∘ from (idx_resp A e2 dx)
    ≈ ff ∘ from (idx_resp A e3 dx).
Proof.
  rewrite <- comp_assoc.
  rewrite (idx_resp_from_trans A e1 e2 dx).
  apply compose_respects.
  - reflexivity.
  - apply idx_resp_from_irrel.
Qed.

Lemma Grothendieck_transport_comp_l {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f f' : y ~> z} {g : x ~> y} (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g)
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  (ff ∘ from (idx_resp A e dy)) ∘ fmap[idx_map A f'] gg
      ∘ from (idx_comp A f' g dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_resp A e dy)) (fmap[idx_map A f'] gg)).
  rewrite <- (idx_resp_natural_from A e gg).
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_l_from g e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_transport_comp_r {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g g' : x ~> y} (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g')
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  ff ∘ fmap[idx_map A f] (gg ∘ from (idx_resp A e dx))
     ∘ from (idx_comp A f g' dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_r_from f e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_left {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ @id B y ∘ f) (ff : idx_map A f dx ~> dy) :
  to (idx_id A dy) ∘ fmap[idx_map A (@id B y)] ff
     ∘ from (idx_comp A (@id B y) f dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_left f) dx).
  rewrite <- (idx_id_natural A ff).
  rewrite <- comp_assoc.
  rewrite (idx_unit_left_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_right {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ f ∘ @id B x) (ff : idx_map A f dx ~> dy) :
  ff ∘ fmap[idx_map A f] (to (idx_id A dx))
     ∘ from (idx_comp A f (@id B x) dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_right f) dx).
  rewrite <- comp_assoc.
  rewrite (idx_unit_right_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_assoc {w x y z : B}
  {dw : idx_fib A w} {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h))
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy)
  (hh : idx_map A h dw ~> dx) :
  ff ∘ fmap[idx_map A f]
         (gg ∘ fmap[idx_map A g] hh ∘ from (idx_comp A g h dw))
     ∘ from (idx_comp A f (g ∘ h) dw)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
          ∘ fmap[idx_map A (f ∘ g)] hh ∘ from (idx_comp A (f ∘ g) h dw))
        ∘ from (idx_resp A e dw).
Proof.
  rewrite (idx_resp_from_flip e (comp_assoc f g h) dw).
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g dx))
                      (fmap[idx_map A (f ∘ g)] hh)).
  rewrite <- (idx_comp_natural_from A f g hh).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g (idx_map A h dw)))
                      (from (idx_comp A (f ∘ g) h dw))).
  rewrite (idx_cocycle_from f g h dw).
  rewrite <- !comp_assoc.
  rewrite (iso_from_to (idx_resp A (comp_assoc f g h) dw)).
  rewrite id_right.
  reflexivity.
Qed.

(** ** The displayed category over B, its total category, the projection *)

Program Definition Grothendieck_Displayed : Displayed B := {|
  dobj := fun x => idx_fib A x;
  dhom := fun x y dx dy f => idx_map A f dx ~{ idx_fib A y }~> dy;
  dhomset := fun x y dx dy f => @homset (idx_fib A y) (idx_map A f dx) dy;
  dtransport := fun x y dx dy f g e ff => ff ∘ from (idx_resp A e dx);
  did := fun x dx => to (idx_id A dx);
  dcomp := fun x y z dx dy dz f g ff gg =>
             ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
|}.
Next Obligation.
  (* dtransport_respects *)
  intros x y dx dy f g e ff gg Hfg; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  (* dtransport_id, from proof irrelevance of [idx_resp] *)
  intros x y dx dy f e ff; simpl.
  rewrite (idx_resp_from_id A e dx).
  apply id_right.
Qed.
Next Obligation.
  (* dtransport_trans *)
  intros x y dx dy f g h e1 e2 ff; simpl.
  apply Grothendieck_transport_trans.
Qed.
Next Obligation.
  (* dcomp_respects *)
  intros x y z dx dy dz f g ff ff' Hf gg gg' Hg; simpl.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  (* dtransport_comp_l *)
  intros x y z dx dy dz f f' g e e' ff gg; simpl.
  apply Grothendieck_transport_comp_l.
Qed.
Next Obligation.
  (* dtransport_comp_r *)
  intros x y z dx dy dz f g g' e e' ff gg; simpl.
  apply Grothendieck_transport_comp_r.
Qed.
Next Obligation.
  (* did_left *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_left.
Qed.
Next Obligation.
  (* did_right *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_right.
Qed.
Next Obligation.
  (* dcomp_assoc *)
  intros w x y z dw dx dy dz f g h ff gg hh; simpl.
  apply Grothendieck_assoc.
Qed.

(** The Grothendieck construction ∫ A: the total category of the displayed
    presentation. *)
Definition Grothendieck : Category := Total Grothendieck_Displayed.

(** The projection ∫ A ⟶ B, taking first components. *)
Definition Grothendieck_Proj : Grothendieck ⟶ B :=
  Total_Proj Grothendieck_Displayed.

End Grothendieck.
