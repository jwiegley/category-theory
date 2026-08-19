Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Coequalizer.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * An evaluated coequalizer: interconnecting a set of ports *)

(* Fong and Spivak, "Seven Sketches in Compositionality", §6.2.4
   example 6.42 (printed p. 194).  Take X the set of "connect these two"
   markers and Y the set of ports of a circuit; the two families of
   arrows give functions f, g : X → Y, and the coequalizer of f and g is
   the set of TERMINALS resulting from the interconnection -- the
   connected groups of ports.

   This file works one such circuit end to end over
   Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers]: six ports, three
   wires, and three resulting terminals, one of which is a lone
   unconnected port.  Nothing here is a new construction; it is the
   delivered one, exercised.

   WHY [Sets] AND NOT [FinSet], AND WHAT "EVALUATED" MEANS HERE

   [FinSet] is where this library's finite combinatorics computes:
   Instance/FinSet/Pushout.v labels connected components with
   [components], counts them at [po_apex] (:406), maps into them at
   [po_cls] (:420) and selects representatives at [po_cls_rep] (:445).
   A witness built there would compute the terminal COUNT by [eq_refl] on
   a numeral.  It would also compute it in a category for which no
   [HasCoequalizers] instance exists -- building one is a separate piece
   of work and is NOT part of this file or of the issue it serves --
   so it would exercise a parallel construction rather than the delivered
   one.  The witness is therefore over [Sets].

   Over [Sets] the delivered coequalizer is the codomain under a coarser
   `≈`, and the coarser `≈` is an INDUCTIVE relation, so it does not
   reduce: exhibiting two ports as connected is a derivation, and no
   amount of computation will produce one.  What does reduce is
   everything on the other side of the universal property, and that is
   where this file puts its [eq_refl]s:

     - the coequalizer's CARRIER is the ic_port type on the nose
       ([interconnect_carrier]);
     - the terminal-labelling map computes on every closed port
       ([label_P0] and its five siblings);
     - the mediator produced by [coeq_desc] out of the delivered
       [IsCoequalizer] IS that labelling, evaluated
       ([interconnect_med_at_P2] and siblings) -- so it is the universal
       property being run, not a hand-built map;
     - one leg of the isomorphism with the three-element terminal set
       closes by [eq_refl] ([ic_label_of_rep]), the other being the
       six derivations that [ic_rep_of_label] collects.

   And the count is PROVED, not read off: [interconnect_iso] exhibits
   the coequalizer as isomorphic in [Sets] to a three-element discrete
   setoid whose three elements are pairwise distinct
   ([ic_terminal_distinct]) and which has no others
   ([ic_terminal_cases]).  Without those two the isomorphism would pin
   nothing.

   NEGATIVE RESULTS GO OUT THROUGH THE MEDIATOR.  That two ports are NOT
   connected cannot be shown by induction on the generated relation --
   an induction over a congruence yields no negation -- so
   [port_P0_P3_apart] and its siblings map out into the terminal setoid,
   where the question is an equation between constructors and
   [discriminate] settles it.  This is the discipline
   Instance/Mod/Tensor.v uses for the same reason. *)

(* WHAT IS DELIVERED

   * The circuit: [ic_port] (six), [ic_wire] (three), [ic_terminal] (three), each
     as a discrete setoid, with [ic_wire_src] and [ic_wire_dst] the two ends.

   * [Interconnect], the coequalizer of that pair, taken from
     [Sets_HasCoequalizers] rather than rebuilt
     ([interconnect_is_chosen], by [eq_refl]).

   * The three groups, each proved to be a group
     ([port_P0_P1_merged], [port_P0_P2_merged], [port_P4_P5_merged]) and
     proved to be separate from the others ([port_P0_P3_apart],
     [port_P0_P4_apart], [port_P3_P4_apart]).

   * [interconnect_iso], the coequalizer identified with the
     three-element terminal setoid, with [ic_terminal_distinct] and
     [ic_terminal_cases] pinning that set at exactly three elements.

   * Evaluated readings throughout, all [eq_refl] -- including the
     defining triangle [interconnect_triangle], which holds pointwise by
     [reflexivity] because the coequalizing map is the identity
     function.

   WHAT IS NOT DELIVERED

   * NO [HasCoequalizers FinSet], and no claim about FinSet at all.

   * NO GENERAL CIRCUIT VOCABULARY.  There is no type of circuits, no
     composition of interconnections, and no connection to
     Construction/Cospan/ or to the hypergraph-category development,
     which is where Seven Sketches takes the example next.

   * NO DECISION PROCEDURE for connectedness of the generated relation.
     Each negative below is a separate mapping-out argument; nothing
     produces them uniformly.

   A NOTE ON NAMES.  The circuit vocabulary carries an [Ic]/[ic_] prefix
   ([ic_port], [IcP0], [ic_wire], [IcW0], [ic_terminal], [IcT0], [ic_label],
   [ic_rep]) because the Makefile's [print-assumptions] target requires
   every audited module into ONE scope, where the later [Require] wins a
   duplicated short name and the audit then silently reports on the wrong
   constant.  Unprefixed, [wire] would have collided with
   Construction/ColouredPROP.v:175 and Construction/PROP/Term.v:86, and
   [P1] with Structure/Monoidal/Drinfeld.v:307.

   STATUS: axiom-free.  61 named constants (the three inductives and
   their twelve constructors included), no [Program] obligations, all reporting
   "Closed under the global context"; the Makefile's
   [print-assumptions] target audits eight of them. *)

(** ** The circuit *)

Inductive ic_port : Set := IcP0 | IcP1 | IcP2 | IcP3 | IcP4 | IcP5.
Inductive ic_wire : Set := IcW0 | IcW1 | IcW2.
Inductive ic_terminal : Set := IcT0 | IcT1 | IcT2.

Definition IcPortSet : SetoidObject :=
  {| carrier := ic_port ; is_setoid := eq_Setoid ic_port |}.
Definition IcWireSet : SetoidObject :=
  {| carrier := ic_wire ; is_setoid := eq_Setoid ic_wire |}.
Definition IcTerminalSet : SetoidObject :=
  {| carrier := ic_terminal ; is_setoid := eq_Setoid ic_terminal |}.

(* Three wires: IcP0-IcP1, IcP1-IcP2, IcP4-IcP5.  IcP3 is left unconnected, which is
   what makes the third terminal a singleton and keeps the example from
   degenerating into "everything is joined". *)
Definition ic_wire_src_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP0 | IcW1 => IcP1 | IcW2 => IcP4 end.

Definition ic_wire_dst_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP1 | IcW1 => IcP2 | IcW2 => IcP5 end.

Definition ic_wire_src : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_src_fun |}. Defined.

Definition ic_wire_dst : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_dst_fun |}. Defined.

(** ** The coequalizer, taken from the delivered instance *)

Definition Interconnect : SetoidObject := SetsCoeq ic_wire_src ic_wire_dst.

Definition interconnect_proj : IcPortSet ~{Sets}~> Interconnect :=
  sets_coeq_proj ic_wire_src ic_wire_dst.

(* It IS the object [Sets_HasCoequalizers] chooses, by conversion. *)
Example interconnect_is_chosen :
  `1 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst)
    = Interconnect.
Proof. reflexivity. Qed.

(* ... and so is the coequalizing map. *)
Example interconnect_proj_is_chosen :
  `1 (`2 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst))
    = interconnect_proj.
Proof. reflexivity. Qed.

(* The carrier is the ic_port type on the nose, and the coequalizing map is
   the identity function on it: only `≈` moved. *)
Example interconnect_carrier : carrier Interconnect = ic_port.
Proof. reflexivity. Qed.

Example interconnect_proj_at (p : ic_port) : interconnect_proj p = p.
Proof. reflexivity. Qed.

(** ** The three terminals, and that they are three *)

Definition ic_label_fun (p : ic_port) : ic_terminal :=
  match p with
  | IcP0 => IcT0 | IcP1 => IcT0 | IcP2 => IcT0
  | IcP3 => IcT1
  | IcP4 => IcT2 | IcP5 => IcT2
  end.

Definition ic_label : IcPortSet ~{Sets}~> IcTerminalSet.
Proof. unshelve refine {| morphism := ic_label_fun |}. Defined.

Example label_P0 : ic_label IcP0 = IcT0. Proof. reflexivity. Qed.
Example label_P1 : ic_label IcP1 = IcT0. Proof. reflexivity. Qed.
Example label_P2 : ic_label IcP2 = IcT0. Proof. reflexivity. Qed.
Example label_P3 : ic_label IcP3 = IcT1. Proof. reflexivity. Qed.
Example label_P4 : ic_label IcP4 = IcT2. Proof. reflexivity. Qed.
Example label_P5 : ic_label IcP5 = IcT2. Proof. reflexivity. Qed.

(* The labelling coforks the wire pair: one computation per wire. *)
Lemma ic_label_coforks : ic_label ∘ ic_wire_src ≈ ic_label ∘ ic_wire_dst.
Proof. intros [ | | ]; reflexivity. Qed.

(* The terminal set has exactly three elements: three cases and no
   others, and the three are pairwise distinct.  Without both halves the
   isomorphism below would pin no count. *)
Lemma ic_terminal_cases (t : ic_terminal) : ((t = IcT0) ∨ (t = IcT1)) ∨ (t = IcT2).
Proof. destruct t; [ left; left | left; right | right ]; reflexivity. Qed.

Lemma ic_terminal_distinct :
  ((IcT0 = IcT1 → False) ∧ (IcT0 = IcT2 → False)) ∧ (IcT1 = IcT2 → False).
Proof. repeat split; intro E; discriminate E. Qed.

(** ** The universal property, run *)

(* The mediator [coeq_desc] produces out of the DELIVERED
   [IsCoequalizer], evaluated at closed ports.  This is the point of the
   file: the arrow whose existence the universal property asserts is a
   function that computes. *)
Definition interconnect_med : Interconnect ~{Sets}~> IcTerminalSet :=
  unique_obj
    (coeq_desc (sets_coeq_IsCoequalizer ic_wire_src ic_wire_dst) ic_label ic_label_coforks).

Example interconnect_med_at_P0 : interconnect_med IcP0 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P2 : interconnect_med IcP2 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P3 : interconnect_med IcP3 = IcT1.
Proof. reflexivity. Qed.
Example interconnect_med_at_P5 : interconnect_med IcP5 = IcT2.
Proof. reflexivity. Qed.

(* ... and it IS the labelling, by conversion -- the universal property
   rebuilt nothing.  The defining triangle then holds pointwise by
   [reflexivity], the coequalizing map being the identity function. *)
Example interconnect_med_is_label (p : ic_port) : interconnect_med p = ic_label p.
Proof. reflexivity. Qed.

Example interconnect_triangle : interconnect_med ∘ interconnect_proj ≈ ic_label.
Proof. intro p; reflexivity. Qed.

(** ** What the interconnection joins *)

(* Directly joined by a wire. *)
Lemma port_P0_P1_merged : @equiv _ Interconnect IcP0 IcP1.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW0). Qed.

Lemma port_P4_P5_merged : @equiv _ Interconnect IcP4 IcP5.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW2). Qed.

(* Joined only through a third port: this is where transitivity of the
   generated relation does the work, and it is a DERIVATION, not a
   computation. *)
Lemma port_P0_P2_merged : @equiv _ Interconnect IcP0 IcP2.
Proof.
  exact (cq_trans ic_wire_src ic_wire_dst IcP0 IcP1 IcP2
           (cq_glue ic_wire_src ic_wire_dst IcW0) (cq_glue ic_wire_src ic_wire_dst IcW1)).
Qed.

(** ** What it does not join *)

(* Every negative goes out through [interconnect_med]: from a supposed
   identification in the coequalizer, respectfulness of the mediator
   gives an equation of terminals, and terminals are constructors. *)
Lemma interconnect_apart (p q : ic_port) (H : ic_label_fun p = ic_label_fun q → False) :
  @equiv _ Interconnect p q → False.
Proof.
  intro Hpq.
  exact (H (@proper_morphism _ _ _ _ interconnect_med p q Hpq)).
Qed.

Lemma port_P0_P3_apart : @equiv _ Interconnect IcP0 IcP3 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P0_P4_apart : @equiv _ Interconnect IcP0 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P3_P4_apart : @equiv _ Interconnect IcP3 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

(** ** The count, as an isomorphism *)

(* A chosen port in each group. *)
Definition ic_rep_fun (t : ic_terminal) : ic_port :=
  match t with IcT0 => IcP0 | IcT1 => IcP3 | IcT2 => IcP4 end.

(* The source is discrete, so respectfulness is [Proper (eq ==> _)] and
   instance resolution discharges it against reflexivity of the
   coequalizer's relation; both carriers are concrete, so nothing
   polymorphic is at stake in leaving it to resolution. *)
Definition ic_rep : IcTerminalSet ~{Sets}~> Interconnect.
Proof.
  unshelve refine
    (@Build_SetoidMorphism ic_terminal (is_setoid IcTerminalSet)
       ic_port (is_setoid Interconnect) ic_rep_fun _).
Defined.

(* One leg computes: labelling a chosen representative returns its own
   terminal, for all three, by [eq_refl]. *)
Lemma ic_label_of_rep (t : ic_terminal) : ic_label_fun (ic_rep_fun t) = t.
Proof. destruct t; reflexivity. Qed.

(* The other leg is the six derivations -- one per port -- that each port
   is joined to its group's representative. *)
Lemma ic_rep_of_label (p : ic_port) : @equiv _ Interconnect (ic_rep_fun (ic_label_fun p)) p.
Proof.
  destruct p.
  - apply coeq_rel_refl.
  - exact port_P0_P1_merged.
  - exact port_P0_P2_merged.
  - apply coeq_rel_refl.
  - apply coeq_rel_refl.
  - exact port_P4_P5_merged.
Qed.

(* Seven Sketches' conclusion, at this circuit: the coequalizer IS the
   set of terminals.  With [ic_terminal_cases] and [ic_terminal_distinct] this
   says the interconnection has exactly three terminals. *)
Definition interconnect_iso : @Isomorphism Sets Interconnect IcTerminalSet.
Proof.
  unshelve refine {| to := interconnect_med ; from := ic_rep |}.
  - intro t; exact (ic_label_of_rep t).
  - intro p; exact (ic_rep_of_label p).
Defined.

(* Both legs read off, by conversion. *)
Example interconnect_iso_to (p : ic_port) : to interconnect_iso p = ic_label_fun p.
Proof. reflexivity. Qed.

Example interconnect_iso_from (t : ic_terminal) : from interconnect_iso t = ic_rep_fun t.
Proof. reflexivity. Qed.

(* The isomorphism is not vacuous in either direction: it identifies
   three ports with the same terminal and separates ports in different
   groups. *)
Example interconnect_iso_groups :
  ((to interconnect_iso IcP0 = IcT0) ∧ (to interconnect_iso IcP2 = IcT0))
    ∧ (to interconnect_iso IcP3 = IcT1).
Proof. repeat split; reflexivity. Qed.
