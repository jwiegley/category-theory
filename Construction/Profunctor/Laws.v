Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Profunctor.
Require Import Category.Construction.Profunctor.Compose.

Generalizable All Variables.

(** * Coherence laws of profunctor composition *)

(* nLab: https://ncatlab.org/nlab/show/profunctor
        https://ncatlab.org/nlab/show/bicategory+of+profunctors

   Profunctor composition [prof_compose] (Construction/Profunctor/Compose.v),
   with [prof_id := Hom C] as identity, satisfies the unit and associativity
   laws of a bicategory up to natural isomorphism of profunctors, i.e. up to
   iso in the functor category [C^op ∏ D ⟶ Sets].  This file supplies the three
   structural isomorphisms:

     - the left unitor    [prof_unit_left_iso  : prof_id ∘ P ≅ P],
     - the right unitor    [prof_unit_right_iso : P ∘ prof_id ≅ P],
     - the associator     [prof_assoc_iso      : (P ∘ Q) ∘ R ≅ P ∘ (Q ∘ R)].

   The unitors are the co-Yoneda reduction: gluing along the identity leg of a
   representable collapses the mediating coend onto a single functor value.  The
   associator is a Fubini-style rebracketing of the triple coend
   [∫^d ∫^e P(c,d) × Q(d,e) × R(e,f)]; its forward and backward mediators send
   generators to generators, so both round trips close by reflexivity, giving an
   axiom-free isomorphism.

   Assembling these into a [Bicategory] instance for the bicategory of
   profunctors is deferred; here we deliver the laws themselves. *)

(* Discharge every [Program] obligation by hand, as in Compose.v: the default
   tactic would destructure the product-category objects and rename the
   variables the proofs below refer to. *)

(** ** Pointwise [fmap] lemmas on [Sets]-valued functors *)

(* Respectfulness of [fmap] read pointwise at an element. *)
Lemma fmap_pt {A : Category} (G : A ⟶ Sets) {x y : A}
  (m m' : x ~{A}~> y) (Hm : m ≈ m') (a : G x) :
  fmap[G] m a ≈ fmap[G] m' a.
Proof. exact (@fmap_respects _ _ G x y m m' Hm a). Qed.

(* The interchange law [fmap_comp] read pointwise at an element. *)
Lemma fmap_comp_pt {A : Category} (G : A ⟶ Sets) {x y z : A}
  (m2 : y ~{A}~> z) (m1 : x ~{A}~> y) (a : G x) :
  fmap[G] (m2 ∘ m1) a ≈ fmap[G] m2 (fmap[G] m1 a).
Proof. exact (@fmap_comp _ _ G x y z m2 m1 a). Qed.

(* Collapse two successive [fmap]s whose morphisms compose to a known [m3]. *)
Lemma fmap_two {A : Category} (G : A ⟶ Sets) {x y z : A}
  (m1 : y ~{A}~> z) (m2 : x ~{A}~> y) (m3 : x ~{A}~> z)
  (Hm : m1 ∘ m2 ≈ m3) (w : G x) :
  fmap[G] m1 (fmap[G] m2 w) ≈ fmap[G] m3 w.
Proof.
  transitivity (fmap[G] (m1 ∘ m2) w).
  - symmetry; apply fmap_comp_pt.
  - exact (@fmap_respects _ _ G _ _ (m1 ∘ m2) m3 Hm w).
Qed.

(* Post-composing a coend's injections with a fixed morphism keeps the cowedge
   condition, by the coend's own cowedge law. *)
Lemma postcomp_cowedge {K : Category} (G : K^op ∏ K ⟶ Sets)
  (Ecw : Coend G) (Q : SetoidObject) (mm : coend_obj Ecw ~{Sets}~> Q) :
  Cowedge_cond G Q (fun x => mm ∘ @coend_inj K Sets G Ecw x).
Proof.
  intros x y f.
  rewrite <- !comp_assoc, (coend_cowedge Ecw f).
  reflexivity.
Qed.

#[local] Obligation Tactic := idtac.

(** ** The left unitor: [prof_id ∘ P ≅ P] *)

Section LeftUnit.
Context {C D : Category}.
Context (P : C ⇸ D).

Notation II c d := (prof_integrand prof_id P c d).

(* The leg at [m]: an element [(g, a) ∈ Hom C (m, c) × P(m, d)] maps to
   [P(g, id) a ∈ P(c, d)], reindexing [P] along [g]. *)
Program Definition lu_leg (c : C) (d : D) (m : C) :
  SetoidMorphism (II c d (m, m)) (P (c, d)) :=
  {| morphism := fun ga =>
       @fmap (C^op ∏ D) Sets P (m, d) (c, d)
         ((fst ga : m ~{C^op}~> c), id[d]) (snd ga) |}.
Next Obligation.
  intros c d m [g a] [g' a'] [Hg Ha]; simpl in *.
  rewrite Ha.
  apply (fmap_pt P (x:=(m,d)) (y:=(c,d)) (g, id) (g', id)).
  split; [ exact Hg | reflexivity ].
Qed.

Lemma lu_cowedge (c : C) (d : D) :
  Cowedge_cond (II c d) (P (c, d)) (lu_leg c d).
Proof.
  intros m1 m2 f [g a]; simpl.
  transitivity (@fmap (C^op ∏ D) Sets P (m2, d) (c, d)
                  ((f ∘ g : m2 ~{C^op}~> c), id[d]) a).
  - apply (fmap_two P
             (((id ∘ g ∘ id : m1 ~{C^op}~> c), id[d]) : (m1,d) ~{C^op ∏ D}~> (c,d))
             (((op f : m2 ~{C^op}~> m1), id[d]) : (m2,d) ~{C^op ∏ D}~> (m1,d))
             (((f ∘ g : m2 ~{C^op}~> c), id[d]) : (m2,d) ~{C^op ∏ D}~> (c,d))).
    split; simpl; cat.
  - symmetry.
    apply (fmap_two P
             (((f ∘ g ∘ id : m2 ~{C^op}~> c), id[d]) : (m2,d) ~{C^op ∏ D}~> (c,d))
             (@id (C^op ∏ D) (m2, d))
             (((f ∘ g : m2 ~{C^op}~> c), id[d]) : (m2,d) ~{C^op ∏ D}~> (c,d))).
    split; simpl; cat.
Qed.

Definition lu_to (c : C) (d : D) :
  coend_apex_setoid (II c d) ~{Sets}~> P (c, d) :=
  coend_mediator (II c d) (lu_leg c d) (lu_cowedge c d).

Lemma lu_to_inj (c : C) (d : D) (m : C) :
  lu_to c d ∘ @coend_inj C Sets (II c d) (SetsCoend (II c d)) m ≈ lu_leg c d m.
Proof. intro w; reflexivity. Qed.

(* The reverse map: embed [b ∈ P(c, d)] at the identity leg [ci c (id, b)]. *)
Program Definition lu_from (c : C) (d : D) :
  SetoidMorphism (P (c, d)) (coend_apex_setoid (II c d)) :=
  {| morphism := fun b => ci (II c d) c (id[c], b) |}.
Next Obligation.
  intros c d b b' Hb; simpl.
  apply ce_point; split; simpl; [ reflexivity | exact Hb ].
Qed.

Program Definition lu_iso (c : C) (d : D) :
  @Isomorphism Sets (coend_apex_setoid (II c d)) (P (c, d)) := {|
  to   := lu_to c d;
  from := lu_from c d
|}.
Next Obligation.
  intros c d b; simpl.
  exact (@fmap_id _ _ P (c, d) b).
Qed.
Next Obligation.
  intros c d x; destruct x as [x0 [g a]]; simpl.
  apply (ce_trans (II c d) _
           (ci (II c d) c (bimap[II c d] (op g : x0 ~{C^op}~> c) (id[c]) (id[c], a)))
           _).
  - apply ce_point; split; simpl; [ cat | reflexivity ].
  - apply (ce_trans (II c d) _
             (ci (II c d) x0 (bimap[II c d] (id[x0] : x0 ~{C^op}~> x0) g (id[c], a)))
             _).
    + exact (ce_glue (II c d) c x0 g (id[c], a)).
    + apply ce_point; split; simpl; [ cat | exact (@fmap_id _ _ P (x0, d) a) ].
Qed.

(* Naturality of [lu_to]: pure [fmap] algebra, no coend gluing. *)
Lemma lu_to_square (c1 c2 : C) (d1 d2 : D)
  (φc : c1 ~{C^op}~> c2) (φd : d1 ~{D}~> d2) :
  lu_to c2 d2 ∘ fmap[prof_compose prof_id P]
                  ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
  ≈ fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)) ∘ lu_to c1 d1.
Proof.
  apply (coend_med_eq (SetsCoend (II c1 d1)) (P (c2, d2))
           (fun m => (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
                       ∘ lu_to c1 d1)
                     ∘ @coend_inj C Sets (II c1 d1) (SetsCoend (II c1 d1)) m)
           (postcomp_cowedge (II c1 d1) (SetsCoend (II c1 d1)) _
              (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)) ∘ lu_to c1 d1))).
  - intro m.
    transitivity (lu_leg c2 d2 m
                  ∘[Sets] transform[prof_theta prof_id P c1 c2 d1 d2 φc φd] (m, m)).
    { rewrite <- comp_assoc.
      change (fmap[prof_compose prof_id P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)))
        with (prof_compose_map prof_id P c1 c2 d1 d2 φc φd).
      rewrite (prof_compose_map_inj prof_id P c1 c2 d1 d2 φc φd m).
      rewrite comp_assoc.
      rewrite lu_to_inj.
      reflexivity. }
    transitivity (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
                  ∘[Sets] lu_leg c1 d1 m).
    2:{ rewrite <- comp_assoc.
        rewrite lu_to_inj.
        reflexivity. }
    intro w; destruct w as [g a]; simpl.
    transitivity (@fmap (C^op ∏ D) Sets P (m, d1) (c2, d2)
                    ((φc ∘ g : m ~{C^op}~> c2), (φd : d1 ~{D}~> d2)) a).
    + apply (fmap_two P
               (((id ∘ g ∘ φc : m ~{C^op}~> c2), id[d2]) : (m,d2) ~{C^op ∏ D}~> (c2,d2))
               (((id[m] : m ~{C^op}~> m), φd) : (m,d1) ~{C^op ∏ D}~> (m,d2))
               (((φc ∘ g : m ~{C^op}~> c2), (φd : d1 ~{D}~> d2)) : (m,d1) ~{C^op ∏ D}~> (c2,d2))).
      split; simpl; cat.
    + symmetry.
      apply (fmap_two P
               (((φc : c1 ~{C^op}~> c2), φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
               (((g : m ~{C^op}~> c1), id[d1]) : (m,d1) ~{C^op ∏ D}~> (c1,d1))
               (((φc ∘ g : m ~{C^op}~> c2), (φd : d1 ~{D}~> d2)) : (m,d1) ~{C^op ∏ D}~> (c2,d2))).
      split; simpl; cat.
  - intro m; reflexivity.
Qed.

Lemma lu_from_to_id (c : C) (d : D) :
  lu_from c d ∘[Sets] lu_to c d ≈ id.
Proof. exact (iso_from_to (lu_iso c d)). Qed.

Lemma lu_natural_form (c1 c2 : C) (d1 d2 : D)
  (φc : c1 ~{C^op}~> c2) (φd : d1 ~{D}~> d2) :
  fmap[prof_compose prof_id P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
  ≈ lu_from c2 d2
      ∘[Sets] fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
      ∘[Sets] lu_to c1 d1.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (lu_to_square c1 c2 d1 d2 φc φd).
  rewrite comp_assoc.
  rewrite lu_from_to_id.
  rewrite id_left.
  reflexivity.
Qed.

Definition lu_iso_family (x : C^op ∏ D) :
  (prof_compose prof_id P) x ≅ P x :=
  match x with (c, d) => lu_iso c d end.

Definition prof_unit_left_iso : prof_compose prof_id P ≅[Fun] P.
Proof.
  apply equiv_iso.
  exists lu_iso_family.
  intros [c1 d1] [c2 d2] [φc φd].
  apply (lu_natural_form c1 c2 d1 d2 φc φd).
Defined.

End LeftUnit.

(** ** The right unitor: [P ∘ prof_id ≅ P] *)

Section RightUnit.
Context {C D : Category}.
Context (P : C ⇸ D).

Notation JJ c d := (prof_integrand P prof_id c d).

(* The leg at [m]: an element [(a, h) ∈ P(c, m) × Hom D (m, d)] maps to
   [P(id, h) a ∈ P(c, d)], reindexing [P] along [h]. *)
Program Definition ru_leg (c : C) (d : D) (m : D) :
  SetoidMorphism (JJ c d (m, m)) (P (c, d)) :=
  {| morphism := fun ah =>
       @fmap (C^op ∏ D) Sets P (c, m) (c, d)
         (id[c], (snd ah : m ~{D}~> d)) (fst ah) |}.
Next Obligation.
  intros c d m [a h] [a' h'] [Ha Hh]; simpl in *.
  rewrite Ha.
  apply (fmap_pt P (x:=(c,m)) (y:=(c,d)) (id, h) (id, h')).
  split; [ reflexivity | exact Hh ].
Qed.

Lemma ru_cowedge (c : C) (d : D) :
  Cowedge_cond (JJ c d) (P (c, d)) (ru_leg c d).
Proof.
  intros m1 m2 f [a h]; simpl.
  transitivity (@fmap (C^op ∏ D) Sets P (c, m1) (c, d)
                  ((id[c] : c ~{C^op}~> c), (h ∘ f : m1 ~{D}~> d)) a).
  - apply (fmap_two P
             (((id[c] : c ~{C^op}~> c), (id ∘ h ∘ op f : m1 ~{D}~> d)) : (c,m1) ~{C^op ∏ D}~> (c,d))
             (((id[c] : c ~{C^op}~> c), (id[m1] : m1 ~{D}~> m1)) : (c,m1) ~{C^op ∏ D}~> (c,m1))
             (((id[c] : c ~{C^op}~> c), (h ∘ f : m1 ~{D}~> d)) : (c,m1) ~{C^op ∏ D}~> (c,d))).
    split; simpl; cat.
  - symmetry.
    apply (fmap_two P
             (((id[c] : c ~{C^op}~> c), (id ∘ h ∘ id : m2 ~{D}~> d)) : (c,m2) ~{C^op ∏ D}~> (c,d))
             (((id[c] : c ~{C^op}~> c), (f : m1 ~{D}~> m2)) : (c,m1) ~{C^op ∏ D}~> (c,m2))
             (((id[c] : c ~{C^op}~> c), (h ∘ f : m1 ~{D}~> d)) : (c,m1) ~{C^op ∏ D}~> (c,d))).
    split; simpl; cat.
Qed.

Definition ru_to (c : C) (d : D) :
  coend_apex_setoid (JJ c d) ~{Sets}~> P (c, d) :=
  coend_mediator (JJ c d) (ru_leg c d) (ru_cowedge c d).

Lemma ru_to_inj (c : C) (d : D) (m : D) :
  ru_to c d ∘ @coend_inj D Sets (JJ c d) (SetsCoend (JJ c d)) m ≈ ru_leg c d m.
Proof. intro w; reflexivity. Qed.

(* The reverse map: embed [b ∈ P(c, d)] at the identity leg [ci d (b, id)]. *)
Program Definition ru_from (c : C) (d : D) :
  SetoidMorphism (P (c, d)) (coend_apex_setoid (JJ c d)) :=
  {| morphism := fun b => ci (JJ c d) d (b, id[d]) |}.
Next Obligation.
  intros c d b b' Hb; simpl.
  apply ce_point; split; simpl; [ exact Hb | reflexivity ].
Qed.

Program Definition ru_iso (c : C) (d : D) :
  @Isomorphism Sets (coend_apex_setoid (JJ c d)) (P (c, d)) := {|
  to   := ru_to c d;
  from := ru_from c d
|}.
Next Obligation.
  intros c d b; simpl.
  exact (@fmap_id _ _ P (c, d) b).
Qed.
Next Obligation.
  intros c d x; destruct x as [x0 [a h]]; simpl.
  apply ce_sym.
  apply (ce_trans (JJ c d) _
           (ci (JJ c d) x0 (bimap[JJ c d] (op h : d ~{D^op}~> x0) (id[x0] : x0 ~{D}~> x0) (a, id[d])))
           _).
  - apply ce_point; split; simpl; [ symmetry; exact (@fmap_id _ _ P (c, x0) a) | cat ].
  - apply (ce_trans (JJ c d) _
             (ci (JJ c d) d (bimap[JJ c d] (id[d] : d ~{D^op}~> d) h (a, id[d])))
             _).
    + exact (ce_glue (JJ c d) x0 d h (a, id[d])).
    + apply ce_point; split; simpl; [ reflexivity | cat ].
Qed.

(* Naturality of [ru_to]: pure [fmap] algebra, no coend gluing. *)
Lemma ru_to_square (c1 c2 : C) (d1 d2 : D)
  (φc : c1 ~{C^op}~> c2) (φd : d1 ~{D}~> d2) :
  ru_to c2 d2 ∘ fmap[prof_compose P prof_id]
                  ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
  ≈ fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)) ∘ ru_to c1 d1.
Proof.
  apply (coend_med_eq (SetsCoend (JJ c1 d1)) (P (c2, d2))
           (fun m => (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
                       ∘ ru_to c1 d1)
                     ∘ @coend_inj D Sets (JJ c1 d1) (SetsCoend (JJ c1 d1)) m)
           (postcomp_cowedge (JJ c1 d1) (SetsCoend (JJ c1 d1)) _
              (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)) ∘ ru_to c1 d1))).
  - intro m.
    transitivity (ru_leg c2 d2 m
                  ∘[Sets] transform[prof_theta P prof_id c1 c2 d1 d2 φc φd] (m, m)).
    { rewrite <- comp_assoc.
      change (fmap[prof_compose P prof_id] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2)))
        with (prof_compose_map P prof_id c1 c2 d1 d2 φc φd).
      rewrite (prof_compose_map_inj P prof_id c1 c2 d1 d2 φc φd m).
      rewrite comp_assoc.
      rewrite ru_to_inj.
      reflexivity. }
    transitivity (fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
                  ∘[Sets] ru_leg c1 d1 m).
    2:{ rewrite <- comp_assoc.
        rewrite ru_to_inj.
        reflexivity. }
    intro w; destruct w as [a h]; simpl.
    transitivity (@fmap (C^op ∏ D) Sets P (c1, m) (c2, d2)
                    ((φc : c1 ~{C^op}~> c2), (φd ∘ h : m ~{D}~> d2)) a).
    + apply (fmap_two P
               (((id[c2] : c2 ~{C^op}~> c2), (φd ∘ h ∘ id : m ~{D}~> d2)) : (c2,m) ~{C^op ∏ D}~> (c2,d2))
               (((φc : c1 ~{C^op}~> c2), (id[m] : m ~{D}~> m)) : (c1,m) ~{C^op ∏ D}~> (c2,m))
               (((φc : c1 ~{C^op}~> c2), (φd ∘ h : m ~{D}~> d2)) : (c1,m) ~{C^op ∏ D}~> (c2,d2))).
      split; simpl; cat.
    + symmetry.
      apply (fmap_two P
               (((φc : c1 ~{C^op}~> c2), φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
               (((id[c1] : c1 ~{C^op}~> c1), (h : m ~{D}~> d1)) : (c1,m) ~{C^op ∏ D}~> (c1,d1))
               (((φc : c1 ~{C^op}~> c2), (φd ∘ h : m ~{D}~> d2)) : (c1,m) ~{C^op ∏ D}~> (c2,d2))).
      split; simpl; cat.
  - intro m; reflexivity.
Qed.

Lemma ru_from_to_id (c : C) (d : D) :
  ru_from c d ∘[Sets] ru_to c d ≈ id.
Proof. exact (iso_from_to (ru_iso c d)). Qed.

Lemma ru_natural_form (c1 c2 : C) (d1 d2 : D)
  (φc : c1 ~{C^op}~> c2) (φd : d1 ~{D}~> d2) :
  fmap[prof_compose P prof_id] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
  ≈ ru_from c2 d2
      ∘[Sets] fmap[P] ((φc, φd) : (c1,d1) ~{C^op ∏ D}~> (c2,d2))
      ∘[Sets] ru_to c1 d1.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (ru_to_square c1 c2 d1 d2 φc φd).
  rewrite comp_assoc.
  rewrite ru_from_to_id.
  rewrite id_left.
  reflexivity.
Qed.

Definition ru_iso_family (x : C^op ∏ D) :
  (prof_compose P prof_id) x ≅ P x :=
  match x with (c, d) => ru_iso c d end.

Definition prof_unit_right_iso : prof_compose P prof_id ≅[Fun] P.
Proof.
  apply equiv_iso.
  exists ru_iso_family.
  intros [c1 d1] [c2 d2] [φc φd].
  apply (ru_natural_form c1 c2 d1 d2 φc φd).
Defined.

End RightUnit.

(** ** The associator: [(P ∘ Q) ∘ R ≅ P ∘ (Q ∘ R)] *)

Section Associator.
Context {C D E FF : Category}.
Context (P : C ⇸ D) (Q : D ⇸ E) (R : E ⇸ FF).

Notation PQi c e := (prof_integrand P Q c e).
Notation QRi d f := (prof_integrand Q R d f).
Notation LOI c f := (prof_integrand (prof_compose P Q) R c f).
Notation ROI c f := (prof_integrand P (prof_compose Q R) c f).

(* Forward inner leg at a fixed [(e, r)]: send [(p, q) ∈ P(c,d) × Q(d,e)] to
   [ci d (p, ci e (q, r))] in the right-bracketed coend
   [∫^d P(c,d) × (∫^e Q(d,e) × R(e,f))]. *)
Program Definition Ato_inner_leg (c : C) (f : FF) (e : E) (r : R (e, f)) (d : D) :
  SetoidMorphism (PQi c e (d, d)) (coend_apex_setoid (ROI c f)) :=
  {| morphism := fun pq =>
       ci (ROI c f) d (fst pq, ci (QRi d f) e (snd pq, r)) |}.
Next Obligation.
  intros c f e r d [p q] [p' q'] [Hp Hq]; simpl in *.
  apply ce_point; split; simpl.
  - exact Hp.
  - apply ce_point; split; simpl; [ exact Hq | reflexivity ].
Qed.

Lemma Ato_inner_cond (c : C) (f : FF) (e : E) (r : R (e, f)) :
  Cowedge_cond (PQi c e) (coend_apex_setoid (ROI c f)) (Ato_inner_leg c f e r).
Proof.
  intros d1 d2 g [p q]; simpl.
  apply (ce_trans (ROI c f) _
    (ci (ROI c f) d1
       (fmap[P] ((id[c], id[d1]) : (c,d1) ~{C^op ∏ D}~> (c,d1)) p,
        fmap[prof_compose Q R] ((op g, id[f]) : (d2,f) ~{D^op ∏ FF}~> (d1,f))
          (ci (QRi d2 f) e (q, r)))) _).
  { apply ce_point; split; simpl.
    - reflexivity.
    - apply ce_sym.
      apply (ce_trans (QRi d1 f) _
        (ci (QRi d1 f) e
           (fmap[Q] ((op g, id[e]) : (d2,e) ~{D^op ∏ E}~> (d1,e)) q,
            fmap[R] ((id[e], id[f]) : (e,f) ~{E^op ∏ FF}~> (e,f)) r)) _).
      + apply (prof_compose_map_inj Q R d2 d1 f f (op g) id e (q, r)).
      + apply ce_point; split; simpl; [ reflexivity | apply (@fmap_id _ _ R (e,f) r) ]. }
  apply (ce_trans (ROI c f) _
    (ci (ROI c f) d2
       (fmap[P] ((id[c], g) : (c,d1) ~{C^op ∏ D}~> (c,d2)) p,
        fmap[prof_compose Q R] ((id[d2], id[f]) : (d2,f) ~{D^op ∏ FF}~> (d2,f))
          (ci (QRi d2 f) e (q, r)))) _).
  { exact (ce_glue (ROI c f) d1 d2 g (p, ci (QRi d2 f) e (q, r))). }
  apply ce_point; split; simpl.
  - reflexivity.
  - apply (ce_trans (QRi d2 f) _
      (ci (QRi d2 f) e
         (fmap[Q] ((id[d2], id[e]) : (d2,e) ~{D^op ∏ E}~> (d2,e)) q,
          fmap[R] ((id[e], id[f]) : (e,f) ~{E^op ∏ FF}~> (e,f)) r)) _).
    + apply (prof_compose_map_inj Q R d2 d2 f f id id e (q, r)).
    + apply ce_point; split; simpl; [ reflexivity | apply (@fmap_id _ _ R (e,f) r) ].
Qed.

Definition Ato_inner (c : C) (f : FF) (e : E) (r : R (e, f)) :
  coend_apex_setoid (PQi c e) ~{Sets}~> coend_apex_setoid (ROI c f) :=
  coend_mediator (PQi c e) (Ato_inner_leg c f e r) (Ato_inner_cond c f e r).

Lemma Ato_inner_proper_r (c : C) (f : FF) (e : E) (r r' : R (e, f))
  (Hr : r ≈ r') (X : coend_apex_setoid (PQi c e)) :
  Ato_inner c f e r X ≈ Ato_inner c f e r' X.
Proof.
  destruct X as [xd [p q]]; simpl.
  apply ce_point; split; simpl.
  - reflexivity.
  - apply ce_point; split; simpl; [ reflexivity | exact Hr ].
Qed.

Program Definition Ato_outer_leg (c : C) (f : FF) (e : E) :
  SetoidMorphism (LOI c f (e, e)) (coend_apex_setoid (ROI c f)) :=
  {| morphism := fun Xr => Ato_inner c f e (snd Xr) (fst Xr) |}.
Next Obligation.
  intros c f e [X r] [X' r'] [HX Hr].
  transitivity (Ato_inner c f e r X').
  - exact (proper_morphism (Ato_inner c f e r) X X' HX).
  - apply Ato_inner_proper_r; exact Hr.
Qed.

Lemma Ato_outer_cond (c : C) (f : FF) :
  Cowedge_cond (LOI c f) (coend_apex_setoid (ROI c f)) (Ato_outer_leg c f).
Proof.
  intros e1 e2 k [X r]; destruct X as [xd [p q]]; simpl.
  apply (ce_trans (ROI c f) _
    (ci (ROI c f) xd
       (fmap[P] ((id[c], id[xd]) : (c,xd) ~{C^op ∏ D}~> (c,xd)) p,
        ci (QRi xd f) e1
          (fmap[Q] ((id[xd], id[e1]) : (xd,e1) ~{D^op ∏ E}~> (xd,e1)) q,
           fmap[R] ((op k, id[f]) : (e2,f) ~{E^op ∏ FF}~> (e1,f)) r))) _).
  { exact (proper_morphism
             (Ato_inner c f e1 (fmap[R] ((op k, id[f]) : (e2,f) ~{E^op ∏ FF}~> (e1,f)) r))
             _ _ (prof_compose_map_inj P Q c c e1 e1 id id xd (p, q))). }
  apply (ce_trans (ROI c f) _
    (ci (ROI c f) xd
       (fmap[P] ((id[c], id[xd]) : (c,xd) ~{C^op ∏ D}~> (c,xd)) p,
        ci (QRi xd f) e2
          (fmap[Q] ((id[xd], k) : (xd,e1) ~{D^op ∏ E}~> (xd,e2)) q,
           fmap[R] ((id[e2], id[f]) : (e2,f) ~{E^op ∏ FF}~> (e2,f)) r))) _).
  2:{ apply ce_sym.
      exact (proper_morphism
               (Ato_inner c f e2 (fmap[R] ((id[e2], id[f]) : (e2,f) ~{E^op ∏ FF}~> (e2,f)) r))
               _ _ (prof_compose_map_inj P Q c c e1 e2 id k xd (p, q))). }
  apply ce_point; split; simpl.
  - reflexivity.
  - exact (ce_glue (QRi xd f) e1 e2 k (q, r)).
Qed.

Definition A_to (c : C) (f : FF) :
  coend_apex_setoid (LOI c f) ~{Sets}~> coend_apex_setoid (ROI c f) :=
  coend_mediator (LOI c f) (Ato_outer_leg c f) (Ato_outer_cond c f).

(* Backward inner leg at a fixed [(d, p)]: send [(q, r) ∈ Q(d,e) × R(e,f)] to
   [ci e (ci d (p, q), r)] in the left-bracketed coend
   [∫^e (∫^d P(c,d) × Q(d,e)) × R(e,f)]. *)
Program Definition Afrom_inner_leg (c : C) (f : FF) (d : D) (p : P (c, d)) (e : E) :
  SetoidMorphism (QRi d f (e, e)) (coend_apex_setoid (LOI c f)) :=
  {| morphism := fun qr =>
       ci (LOI c f) e (ci (PQi c e) d (p, fst qr), snd qr) |}.
Next Obligation.
  intros c f d p e [q r] [q' r'] [Hq Hr]; simpl in *.
  apply ce_point; split; simpl.
  - apply ce_point; split; simpl; [ reflexivity | exact Hq ].
  - exact Hr.
Qed.

Lemma Afrom_inner_cond (c : C) (f : FF) (d : D) (p : P (c, d)) :
  Cowedge_cond (QRi d f) (coend_apex_setoid (LOI c f)) (Afrom_inner_leg c f d p).
Proof.
  intros e1 e2 k [q r]; simpl.
  apply (ce_trans (LOI c f) _
    (ci (LOI c f) e1
       (fmap[prof_compose P Q] ((id[c], id[e1]) : (c,e1) ~{C^op ∏ E}~> (c,e1))
          (ci (PQi c e1) d (p, q)),
        fmap[R] ((op k, id[f]) : (e2,f) ~{E^op ∏ FF}~> (e1,f)) r)) _).
  { apply ce_point; split; simpl.
    - apply ce_sym.
      apply (ce_trans (PQi c e1) _
        (ci (PQi c e1) d
           (fmap[P] ((id[c], id[d]) : (c,d) ~{C^op ∏ D}~> (c,d)) p,
            fmap[Q] ((id[d], id[e1]) : (d,e1) ~{D^op ∏ E}~> (d,e1)) q)) _).
      + apply (prof_compose_map_inj P Q c c e1 e1 id id d (p, q)).
      + apply ce_point; split; simpl; [ apply (@fmap_id _ _ P (c,d) p) | reflexivity ].
    - reflexivity. }
  apply (ce_trans (LOI c f) _
    (ci (LOI c f) e2
       (fmap[prof_compose P Q] ((id[c], k) : (c,e1) ~{C^op ∏ E}~> (c,e2))
          (ci (PQi c e1) d (p, q)),
        fmap[R] ((id[e2], id[f]) : (e2,f) ~{E^op ∏ FF}~> (e2,f)) r)) _).
  { exact (ce_glue (LOI c f) e1 e2 k (ci (PQi c e1) d (p, q), r)). }
  apply ce_point; split; simpl.
  - apply (ce_trans (PQi c e2) _
      (ci (PQi c e2) d
         (fmap[P] ((id[c], id[d]) : (c,d) ~{C^op ∏ D}~> (c,d)) p,
          fmap[Q] ((id[d], k) : (d,e1) ~{D^op ∏ E}~> (d,e2)) q)) _).
    + apply (prof_compose_map_inj P Q c c e1 e2 id k d (p, q)).
    + apply ce_point; split; simpl; [ apply (@fmap_id _ _ P (c,d) p) | reflexivity ].
  - reflexivity.
Qed.

Definition Afrom_inner (c : C) (f : FF) (d : D) (p : P (c, d)) :
  coend_apex_setoid (QRi d f) ~{Sets}~> coend_apex_setoid (LOI c f) :=
  coend_mediator (QRi d f) (Afrom_inner_leg c f d p) (Afrom_inner_cond c f d p).

Lemma Afrom_inner_proper_p (c : C) (f : FF) (d : D) (p p' : P (c, d))
  (Hp : p ≈ p') (Y : coend_apex_setoid (QRi d f)) :
  Afrom_inner c f d p Y ≈ Afrom_inner c f d p' Y.
Proof.
  destruct Y as [ye [q r]]; simpl.
  apply ce_point; split; simpl.
  - apply ce_point; split; simpl; [ exact Hp | reflexivity ].
  - reflexivity.
Qed.

Program Definition Afrom_outer_leg (c : C) (f : FF) (d : D) :
  SetoidMorphism (ROI c f (d, d)) (coend_apex_setoid (LOI c f)) :=
  {| morphism := fun pY => Afrom_inner c f d (fst pY) (snd pY) |}.
Next Obligation.
  intros c f d [p Y] [p' Y'] [Hp HY].
  transitivity (Afrom_inner c f d p Y').
  - exact (proper_morphism (Afrom_inner c f d p) Y Y' HY).
  - apply Afrom_inner_proper_p; exact Hp.
Qed.

Lemma Afrom_outer_cond (c : C) (f : FF) :
  Cowedge_cond (ROI c f) (coend_apex_setoid (LOI c f)) (Afrom_outer_leg c f).
Proof.
  intros d1 d2 g [p Y]; destruct Y as [ye [q r]]; simpl.
  apply (ce_trans (LOI c f) _
    (ci (LOI c f) ye
       (ci (PQi c ye) d1
          (fmap[P] ((id[c], id[d1]) : (c,d1) ~{C^op ∏ D}~> (c,d1)) p,
           fmap[Q] ((op g, id[ye]) : (d2,ye) ~{D^op ∏ E}~> (d1,ye)) q),
        fmap[R] ((id[ye], id[f]) : (ye,f) ~{E^op ∏ FF}~> (ye,f)) r)) _).
  { exact (proper_morphism
             (Afrom_inner c f d1 (fmap[P] ((id[c], id[d1]) : (c,d1) ~{C^op ∏ D}~> (c,d1)) p))
             _ _ (prof_compose_map_inj Q R d2 d1 f f (op g) id ye (q, r))). }
  apply (ce_trans (LOI c f) _
    (ci (LOI c f) ye
       (ci (PQi c ye) d2
          (fmap[P] ((id[c], g) : (c,d1) ~{C^op ∏ D}~> (c,d2)) p,
           fmap[Q] ((id[d2], id[ye]) : (d2,ye) ~{D^op ∏ E}~> (d2,ye)) q),
        fmap[R] ((id[ye], id[f]) : (ye,f) ~{E^op ∏ FF}~> (ye,f)) r)) _).
  2:{ apply ce_sym.
      exact (proper_morphism
               (Afrom_inner c f d2 (fmap[P] ((id[c], g) : (c,d1) ~{C^op ∏ D}~> (c,d2)) p))
               _ _ (prof_compose_map_inj Q R d2 d2 f f id id ye (q, r))). }
  apply ce_point; split; simpl.
  - exact (ce_glue (PQi c ye) d1 d2 g (p, q)).
  - reflexivity.
Qed.

Definition A_from (c : C) (f : FF) :
  coend_apex_setoid (ROI c f) ~{Sets}~> coend_apex_setoid (LOI c f) :=
  coend_mediator (ROI c f) (Afrom_outer_leg c f) (Afrom_outer_cond c f).

(* Both composites send a nested generator to itself, so the round trips close
   by reflexivity. *)
Lemma A_to_from_id (c : C) (f : FF) :
  A_to c f ∘[Sets] A_from c f ≈ id.
Proof.
  intro Y; destruct Y as [yd [p YY]]; destruct YY as [ye [q r]]; reflexivity.
Qed.

Lemma A_from_to_id (c : C) (f : FF) :
  A_from c f ∘[Sets] A_to c f ≈ id.
Proof.
  intro Z; destruct Z as [ze [X r]]; destruct X as [zd [p q]]; reflexivity.
Qed.

Program Definition assoc_iso (c : C) (f : FF) :
  @Isomorphism Sets (coend_apex_setoid (LOI c f)) (coend_apex_setoid (ROI c f)) := {|
  to   := A_to c f;
  from := A_from c f
|}.
Next Obligation. apply A_to_from_id. Qed.
Next Obligation. apply A_from_to_id. Qed.

(* Naturality of [A_to]: on a nested generator both sides rebracket to the same
   triple [ci zd (P φc p, ci m (Q q, R φf r))]. *)
Lemma A_to_square (c1 c2 : C) (f1 f2 : FF)
  (φc : c1 ~{C^op}~> c2) (φf : f1 ~{FF}~> f2) :
  A_to c2 f2 ∘ fmap[prof_compose (prof_compose P Q) R]
                  ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2))
  ≈ fmap[prof_compose P (prof_compose Q R)]
        ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2)) ∘ A_to c1 f1.
Proof.
  apply (coend_med_eq (SetsCoend (LOI c1 f1)) (coend_apex_setoid (ROI c2 f2))
    (fun m => (fmap[prof_compose P (prof_compose Q R)]
                 ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2)) ∘ A_to c1 f1)
              ∘ @coend_inj E Sets (LOI c1 f1) (SetsCoend (LOI c1 f1)) m)
    (postcomp_cowedge (LOI c1 f1) (SetsCoend (LOI c1 f1)) _
       (fmap[prof_compose P (prof_compose Q R)]
          ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2)) ∘ A_to c1 f1))).
  2:{ intro m; reflexivity. }
  intro m.
  intro w; destruct w as [X r]; destruct X as [zd [p q]].
  transitivity (ci (ROI c2 f2) zd
    (fmap[P] ((φc, id[zd]) : (c1,zd) ~{C^op ∏ D}~> (c2,zd)) p,
     ci (QRi zd f2) m
       (fmap[Q] ((id[zd], id[m]) : (zd,m) ~{D^op ∏ E}~> (zd,m)) q,
        fmap[R] ((id[m], φf) : (m,f1) ~{E^op ∏ FF}~> (m,f2)) r))).
  { transitivity (A_to c2 f2
      (ci (LOI c2 f2) m
         (ci (PQi c2 m) zd
            (fmap[P] ((φc, id[zd]) : (c1,zd) ~{C^op ∏ D}~> (c2,zd)) p,
             fmap[Q] ((id[zd], id[m]) : (zd,m) ~{D^op ∏ E}~> (zd,m)) q),
          fmap[R] ((id[m], φf) : (m,f1) ~{E^op ∏ FF}~> (m,f2)) r))).
    - apply (proper_morphism (A_to c2 f2)).
      apply (ce_trans (LOI c2 f2) _
        (ci (LOI c2 f2) m
           (fmap[prof_compose P Q] ((φc, id[m]) : (c1,m) ~{C^op ∏ E}~> (c2,m))
              (ci (PQi c1 m) zd (p, q)),
            fmap[R] ((id[m], φf) : (m,f1) ~{E^op ∏ FF}~> (m,f2)) r)) _).
      + exact (prof_compose_map_inj (prof_compose P Q) R c1 c2 f1 f2 φc φf m
                 (ci (PQi c1 m) zd (p, q), r)).
      + apply ce_point; split; simpl.
        * exact (prof_compose_map_inj P Q c1 c2 m m φc id zd (p, q)).
        * reflexivity.
    - reflexivity. }
  symmetry.
  apply (ce_trans (ROI c2 f2) _
    (ci (ROI c2 f2) zd
       (fmap[P] ((φc, id[zd]) : (c1,zd) ~{C^op ∏ D}~> (c2,zd)) p,
        fmap[prof_compose Q R] ((id[zd], φf) : (zd,f1) ~{D^op ∏ FF}~> (zd,f2))
          (ci (QRi zd f1) m (q, r)))) _).
  - exact (prof_compose_map_inj P (prof_compose Q R) c1 c2 f1 f2 φc φf zd
             (p, ci (QRi zd f1) m (q, r))).
  - apply ce_point; split; simpl.
    + reflexivity.
    + exact (prof_compose_map_inj Q R zd zd f1 f2 id φf m (q, r)).
Qed.

Lemma assoc_natural_form (c1 c2 : C) (f1 f2 : FF)
  (φc : c1 ~{C^op}~> c2) (φf : f1 ~{FF}~> f2) :
  fmap[prof_compose (prof_compose P Q) R]
      ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2))
  ≈ A_from c2 f2
      ∘[Sets] fmap[prof_compose P (prof_compose Q R)]
                ((φc, φf) : (c1,f1) ~{C^op ∏ FF}~> (c2,f2))
      ∘[Sets] A_to c1 f1.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (A_to_square c1 c2 f1 f2 φc φf).
  rewrite comp_assoc.
  rewrite A_from_to_id.
  rewrite id_left.
  reflexivity.
Qed.

Definition assoc_iso_family (x : C^op ∏ FF) :
  (prof_compose (prof_compose P Q) R) x ≅ (prof_compose P (prof_compose Q R)) x :=
  match x with (c, f) => assoc_iso c f end.

Definition prof_assoc_iso :
  prof_compose (prof_compose P Q) R ≅[Fun] prof_compose P (prof_compose Q R).
Proof.
  apply equiv_iso.
  exists assoc_iso_family.
  intros [c1 f1] [c2 f2] [φc φf].
  apply (assoc_natural_form c1 c2 f1 f2 φc φf).
Defined.

End Associator.
