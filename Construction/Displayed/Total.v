Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.

Generalizable All Variables.

(** * The total category of a displayed category *)

(* nLab:      https://ncatlab.org/nlab/show/displayed+category
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
              Categories", Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   The total category ∫ D of a displayed category D over C: objects are
   dependent pairs (x; dx) of a base object x : C and an object dx displayed
   over it; morphisms (x; dx) ~> (y; dy) are dependent pairs (f; ff) of a
   base morphism f : x ~> y and a displayed morphism ff : dhom dx dy f lying
   over it. Since base morphisms are compared by ≈ rather than by equality,
   two total morphisms are equivalent when some proof e relates their base
   components and transporting the first displayed component along e yields
   the second; by proof irrelevance of transport ([dtransport_id], and its
   consequence [dtransport_proof_irrel]) the choice of e is immaterial, so
   this is a bona fide equivalence relation.

   Identity and composition are the displayed ones paired over the base
   ones. Each category law is proven by supplying the base law as the first
   component and closing the displayed side with the derived transport
   lemma pack of Theory/Displayed.v ([dtransport_did_left],
   [dtransport_did_right], [dtransport_dcomp_assoc], and friends), which was
   budgeted there for exactly this purpose.

   [Total_Proj] is the evident projection functor ∫ D ⟶ C taking first
   components; its functor laws hold by reflexivity because identity and
   composition in ∫ D are componentwise. Cleavings on D make this projection
   a cloven fibration — see Theory/Fibration.v. *)

#[local] Obligation Tactic := program_simpl.

Program Definition Total {C : Category} (D : Displayed C) : Category := {|
  obj := ∃ x : C, dobj x;
  hom := fun x y => ∃ f : `1 x ~> `1 y, dhom (`2 x) (`2 y) f;
  homset := fun x y => {| equiv := fun f g =>
    { e : `1 f ≈ `1 g & dtransport e (`2 f) ≈ `2 g } |};
  id := fun x => (id; did (`2 x));
  compose := fun x y z f g => (`1 f ∘ `1 g; dcomp (`2 f) (`2 g))
|}.
Next Obligation.
  (* The total hom equivalence is an equivalence relation. *)
  split.
  - (* reflexivity: the identity proof, cancelled by [dtransport_id] *)
    intros [f ff].
    exists (Equivalence_Reflexive f).
    now apply dtransport_id.
  - (* symmetry: invert the base proof; flip the transport across ≈ *)
    intros [f ff] [g gg] [e He]; simpl in *.
    exists (symmetry e).
    symmetry.
    now apply (fst (dtransport_flip e ff gg)).
  - (* transitivity: compose the base proofs; fuse the transports *)
    intros [f ff] [g gg] [h hh] [e1 He1] [e2 He2]; simpl in *.
    exists (Equivalence_Transitive _ _ _ e1 e2).
    rewrite <- dtransport_trans.
    now rewrite He1.
Qed.
Next Obligation.
  (* Composition respects the total equivalence in both arguments. *)
  intros [f1 ff1] [g1 gg1] [e1 He1] [f2 ff2] [g2 gg2] [e2 He2]; simpl in *.
  exists (compose_respects _ _ e1 _ _ e2).
  rewrite <- He1, <- He2.
  symmetry.
  apply dtransport_dcomp.
Qed.
Next Obligation.
  (* Left identity over the base law. *)
  exists (id_left _).
  apply dtransport_did_left.
Qed.
Next Obligation.
  (* Right identity over the base law. *)
  exists (id_right _).
  apply dtransport_did_right.
Qed.
Next Obligation.
  (* Associativity over the base law. *)
  exists (comp_assoc _ _ _).
  apply dtransport_dcomp_assoc.
Qed.
Next Obligation.
  (* Associativity, dual orientation, over the base law. *)
  exists (comp_assoc_sym _ _ _).
  apply dtransport_dcomp_assoc_sym.
Qed.

(** The projection functor ∫ D ⟶ C: first components. Identity and
    composition in the total category are componentwise, so both functor
    laws are the base category's, holding by reflexivity. *)

Program Definition Total_Proj {C : Category} (D : Displayed C) :
  Total D ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
|}.
Next Obligation.
  (* fmap respects ≈: the base component of a total ≈ is exactly a base ≈ *)
  intros f g [e _]; exact e.
Qed.
Next Obligation.
  (* identities project to identities, on the nose *)
  reflexivity.
Qed.
Next Obligation.
  (* composites project to composites, on the nose *)
  reflexivity.
Qed.
