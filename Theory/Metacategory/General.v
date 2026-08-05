Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.

Generalizable All Variables.

(** Arrows-only metacategories over an arbitrary type of arrows *)

(* nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer 1998, I.1 (the "arrows-only" description) and I.8
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.1

   Mac Lane's single-sorted axiomatization of a category, stated here over an
   ARBITRARY type of arrows, where Theory/Metacategory.v works over [nat] and
   Theory/Metacategory/ArrowsOnly.v over [N], each with the composable pairs
   held in one finite map. The data are arrows, the composable pairs, and the
   composite assigned to each such pair; there is no separate sort of objects.
   Objects are recovered as the identity arrows.
   [Category_from_Metacategory] rebuilds a [Category] from that data and
   [ToArrows] runs the passage the other way, the two being mutually inverse
   in the precise senses recorded below — the content of Mac Lane's I.1 and of
   his remark in I.8.

   THE DATA. Composition is kept as its GRAPH: [mcomp g f h] reads "g∙f is
   defined, and equals h", so that the composable pairs and the composite
   operation are a single datum. This follows Mac Lane's own phrasing
   ("certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows, and
   an operation assigning to each composable pair ⟨g, f⟩ an arrow g∙f"), and
   both sibling files already encode composition this way, as an entry of a
   finite map ([M.MapsTo (f, g) h pairs], resp. [M.find (f, g) pairs = Some
   h]). A partial FUNCTION [arrow → arrow → option arrow] was rejected: it
   makes definedness decidable by construction, since one may always ask
   whether the value is [None], and decidable definedness is not part of the
   first-order theory. What the option form would give for free —
   single-valuedness — is here the explicit field [mcomp_unique], which is
   what makes the graph the graph of a partial operation.

   Arrows carry a setoid, and this is forced by the converse passage. The
   arrows of a category are its bundled morphisms, and morphisms in this
   library are identified only up to the hom-setoid's ≈, never up to Coq's
   [=]; a metacategory over a bare type could therefore not receive them
   without collapsing that identification. Every law below is accordingly
   stated up to ≈.

   THE THREE AXIOMS. Mac Lane requires:

     (i)   the composite (k∙g)∙f is defined if and only if k∙(g∙f) is defined,
           and when either is defined they are equal;
     (ii)  the triple composite k∙g∙f is defined whenever both k∙g and g∙f are;
     (iii) for each arrow g there exist identity arrows u and u' such that g∙u
           and u'∙g are defined.

   Axiom (i) is stated here as the two fields [mcomp_assoc_l] and
   [mcomp_assoc_r], at full strength: "(k∙g)∙f is defined" is read as "k∙g is
   defined AND (k∙g)∙f is defined", so that each half also ASSERTS the
   definedness of the other association. Both sibling files instead state the
   biconditional under the hypothesis that k∙g and g∙f are BOTH already
   defined (Theory/Metacategory.v:167-170,
   Theory/Metacategory/ArrowsOnly.v:60-63), which is strictly weaker. The
   difference is not cosmetic: under the weaker reading Mac Lane's remark that
   the identities flanking an arrow are unique is refutable, and
   [weak_identity_not_unique] at the end of this file exhibits a four-arrow
   countermodel in which one arrow has two distinct source identities. The
   weak form is recovered from the strong one as [mcomp_law], so nothing is
   lost; [Weaken] records the implication at the level of records.

   Axiom (iii) is a CONJUNCTION, as Mac Lane states it. Both sibling files
   encode it with implications where the conjunction belongs, and both say so
   in place (Theory/Metacategory.v:184-190,
   Theory/Metacategory/ArrowsOnly.v:77-83): as written there the axiom is
   satisfied by any non-identity witness and so constrains nothing. It is a
   real axiom here, and it is load-bearing — [mident_idem] derives u∙u = u for
   every identity from it, which is why the objects below need only carry
   their identity proof, where ArrowsOnly.v's [object] must carry a separate
   [obj_def] field to exclude arrows that are identities only vacuously.

   THE TWO PASSAGES. [Category_from_Metacategory] takes objects to be the
   identity arrows and morphisms to be the arrows flanked by the two given
   identities, with composition read off the graph; single-valuedness makes
   the choice of composite [Proper], and [mcompose_char] characterizes it.
   [ToArrows] takes the arrows of a category to be its bundled morphisms
   [Arr], with composability [atgt b = asrc a] an identity of objects. That
   identity type is where the two settings genuinely differ: Mac Lane's
   objects form a SET, so an identification of two objects carries no
   information, and the faithful translation of that assumption into
   intensional type theory is the hypothesis [obj_uip] that the objects of [C]
   are an h-set. The library already threads this assumption where the same
   issue arises (Construction/Grothendieck/Strict.v, whose constructors take
   fibrewise UIP and discharge it by an inline axiom-free Hedberg;
   Theory/Multicategory/Representable.v, which threads UIP on object lists).
   It is used at exactly ONE place here, [Arr_comp_unique]: without it the
   composite of a composable pair is only well defined relative to a chosen
   identification of the endpoints. Every other field of [ToArrows] is proved
   without it.

   THE ROUND TRIP, AND ITS EXACT STRENGTH. On the category side,
   [ToArrows_Equivalence] proves that [ToArrows_Functor], which sends x to the
   identity arrow at x and f to the bundle of f, is an
   [EquivalenceOfCategories] between [C] and
   [Category_from_Metacategory (ToArrows obj_uip)]. It is an EQUIVALENCE and
   not an isomorphism of categories, and this is not slack in the proof: the
   objects of the reconstruction are pairs of an arrow and a proof that it is
   an identity, so an object of [C] is recovered together with a proof
   component that no functor can strip. The three ingredients are proved
   separately and are available on their own — [ToArrows_Full],
   [ToArrows_Faithful], [ToArrows_EssentiallySurjective].

   On the metacategory side the composite passage cannot be formed at all:
   [ToArrows] would have to be applied to [Category_from_Metacategory M],
   whose objects carry those same proof components, and an h-set hypothesis
   for THAT object type is not available (it would require proof irrelevance
   for [mident]). What is proved instead is exactly the content such a round
   trip would have, and it needs no hypothesis: [arrow_realized] shows every
   arrow of [M] underlies a morphism of the reconstruction, and
   [arrow_endpoints] shows that ≈-equal arrows have ≈-equal endpoints, so the
   correspondence is bijective up to ≈ with the endpoints determined. That
   second half is precisely Mac Lane's uniqueness remark
   ([mident_unique_src], [mident_unique_tgt]) in use, and
   [arrow_endpoints_iso] upgrades it to canonical isomorphisms of objects via
   [mobject_iso]. No claim is made that the two passages are mutually inverse
   on the nose in either direction. *)

Record Metacategory : Type := {
  (* "The data for an arrows-only metacategory C consist of arrows," *)
  marr : Type;

  (* Arrows carry a chosen equivalence. *)
  marr_setoid : Setoid marr;

  (* "certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows, and
     an operation assigning to each composable pair ⟨g, f⟩ an arrow g∙f".
     [mcomp g f h] reads "g∙f is defined, and equals h". *)
  mcomp : marr → marr → marr → Type;

  mdefined (g f : marr) := ∃ h, mcomp g f h;

  mcomp_respects {g g' f f' h h'} :
    @equiv _ marr_setoid g g' →
    @equiv _ marr_setoid f f' →
    @equiv _ marr_setoid h h' →
    mcomp g f h → mcomp g' f' h';

  (* The graph is single-valued: it is the graph of a partial operation. *)
  mcomp_unique {g f h h'} :
    mcomp g f h → mcomp g f h' → @equiv _ marr_setoid h h';

  (* Axiom (i), left-to-right *)
  mcomp_assoc_l {k g f kg kgf} :
    mcomp k g kg → mcomp kg f kgf → ∃ gf, mcomp g f gf ∧ mcomp k gf kgf;

  (* Axiom (i), right-to-left *)
  mcomp_assoc_r {k g f gf kgf} :
    mcomp g f gf → mcomp k gf kgf → ∃ kg, mcomp k g kg ∧ mcomp kg f kgf;

  (* Axiom (ii) *)
  mcomp_match {k g f kg gf} :
    mcomp k g kg → mcomp g f gf → ∃ kgf, mcomp kg f kgf;

  mident (u : marr) :=
    (∀ f, mdefined f u → mcomp f u f) ∧ (∀ g, mdefined u g → mcomp u g g);

  (* Axiom (iii), as a conjunction *)
  mident_law (g : marr) :
    ∃ u u', (mident u ∧ mident u') ∧ (mdefined g u ∧ mdefined u' g)
}.

#[export] Existing Instance marr_setoid.

Arguments mdefined _ _ _ /.
Arguments mident _ _ /.

Section Metacategory.

Context (M : Metacategory).

(* The weak biconditional form of axiom (i). *)
Lemma mcomp_law {k g f kg gf} :
  mcomp M k g kg → mcomp M g f gf →
  ∀ kgf, mcomp M kg f kgf ↔ mcomp M k gf kgf.
Proof.
  intros Hkg Hgf kgf; split; intro H.
  - destruct (mcomp_assoc_l M Hkg H) as [gf' [Hgf' Hk]].
    exact (mcomp_respects M (reflexivity _) (mcomp_unique M Hgf' Hgf)
                            (reflexivity _) Hk).
  - destruct (mcomp_assoc_r M Hgf H) as [kg' [Hkg' Hcomp]].
    exact (mcomp_respects M (mcomp_unique M Hkg' Hkg) (reflexivity _)
                            (reflexivity _) Hcomp).
Qed.

(* Every identity composes with itself. *)
Lemma mident_idem {u} : mident M u → mcomp M u u u.
Proof.
  intro Hu.
  destruct (mident_law M u) as [s [t [[Hs _] [[su Hsu] _]]]].
  pose proof (snd Hu s (su; Hsu)) as Hus.   (* u∙s ≈ s *)
  pose proof (fst Hs u (su; Hsu)) as Hsu'.  (* u∙s ≈ u *)
  pose proof (mcomp_unique M Hus Hsu') as Heq.
  exact (mcomp_respects M (reflexivity _) Heq Heq Hus).
Qed.

Lemma mident_agree {u u'} :
  mident M u → mident M u' → mdefined M u u' → u ≈ u'.
Proof.
  intros Hu Hu' Hd.
  exact (mcomp_unique M (fst Hu' u Hd) (snd Hu u' Hd)).
Qed.

Theorem mident_unique_src {g u u'} :
  mident M u → mident M u' → mdefined M g u → mdefined M g u' → u ≈ u'.
Proof.
  intros Hu Hu' Hgu Hgu'.
  destruct (mcomp_assoc_l M (fst Hu g Hgu) (fst Hu' g Hgu')) as [w [Hw _]].
  exact (mident_agree Hu Hu' (w; Hw)).
Qed.

Theorem mident_unique_tgt {g u u'} :
  mident M u → mident M u' → mdefined M u g → mdefined M u' g → u ≈ u'.
Proof.
  intros Hu Hu' Hug Hu'g.
  destruct (mcomp_assoc_r M (snd Hu' g Hu'g) (snd Hu g Hug)) as [w [Hw _]].
  exact (mident_agree Hu Hu' (w; Hw)).
Qed.

Record mobject : Type := {
  obj_arr : marr M;
  obj_id  : mident M obj_arr
}.

Record mmorphism (x y : mobject) : Type := {
  mor_arr : marr M;
  mor_dom : mcomp M mor_arr (obj_arr x) mor_arr;
  mor_cod : mcomp M (obj_arr y) mor_arr mor_arr
}.

Arguments mor_arr {_ _} _.
Arguments mor_dom {_ _} _.
Arguments mor_cod {_ _} _.

Definition mid (x : mobject) : mmorphism x x :=
  {| mor_arr := obj_arr x
   ; mor_dom := mident_idem (obj_id x)
   ; mor_cod := mident_idem (obj_id x) |}.

Lemma mcomp_dom {f g fg x} :
  mcomp M f g fg → mcomp M g x g → mcomp M fg x fg.
Proof.
  intros Hfg Hgx.
  destruct (mcomp_assoc_r M Hgx Hfg) as [w [Hw Hwx]].
  exact (mcomp_respects M (mcomp_unique M Hw Hfg)
                          (reflexivity _) (reflexivity _) Hwx).
Qed.

Lemma mcomp_cod {f g fg z} :
  mcomp M f g fg → mcomp M z f f → mcomp M z fg fg.
Proof.
  intros Hfg Hzf.
  destruct (mcomp_assoc_l M Hzf Hfg) as [w [Hw Hzw]].
  exact (mcomp_respects M (reflexivity _) (mcomp_unique M Hw Hfg)
                          (reflexivity _) Hzw).
Qed.

Definition mcompose {x y z} (f : mmorphism y z) (g : mmorphism x y) :
  mmorphism x z :=
  let fg := mcomp_match M (mor_dom f) (mor_cod g) in
  {| mor_arr := `1 fg
   ; mor_dom := mcomp_dom (`2 fg) (mor_dom g)
   ; mor_cod := mcomp_cod (`2 fg) (mor_cod f) |}.

Lemma mmorphism_equiv (x y : mobject) :
  Equivalence (fun f g : mmorphism x y => mor_arr f ≈ mor_arr g).
Proof.
  constructor; repeat intro.
  - reflexivity.
  - symmetry; assumption.
  - etransitivity; eassumption.
Qed.

Definition mmorphism_setoid (x y : mobject) : Setoid (mmorphism x y) :=
  {| equiv        := fun f g => mor_arr f ≈ mor_arr g
   ; setoid_equiv := mmorphism_equiv x y |}.

Lemma mcompose_respects {x y z} (f f' : mmorphism y z) (g g' : mmorphism x y) :
  mor_arr f ≈ mor_arr f' → mor_arr g ≈ mor_arr g' →
  mor_arr (mcompose f g) ≈ mor_arr (mcompose f' g').
Proof.
  intros Hf Hg; unfold mcompose; simpl.
  destruct (mcomp_match M (mor_dom f) (mor_cod g)) as [h Hh]; simpl.
  destruct (mcomp_match M (mor_dom f') (mor_cod g')) as [h' Hh']; simpl.
  exact (mcomp_unique M Hh
           (mcomp_respects M (symmetry Hf) (symmetry Hg) (reflexivity _) Hh')).
Qed.

Lemma mcompose_id_left {x y} (f : mmorphism x y) :
  mor_arr (mcompose (mid y) f) ≈ mor_arr f.
Proof.
  unfold mcompose; simpl.
  destruct (mcomp_match M _ _) as [h Hh]; simpl.
  exact (mcomp_unique M Hh (mor_cod f)).
Qed.

Lemma mcompose_id_right {x y} (f : mmorphism x y) :
  mor_arr (mcompose f (mid x)) ≈ mor_arr f.
Proof.
  unfold mcompose; simpl.
  destruct (mcomp_match M _ _) as [h Hh]; simpl.
  exact (mcomp_unique M Hh (mor_dom f)).
Qed.

Lemma mcompose_assoc {x y z w}
      (f : mmorphism z w) (g : mmorphism y z) (h : mmorphism x y) :
  mor_arr (mcompose f (mcompose g h)) ≈ mor_arr (mcompose (mcompose f g) h).
Proof.
  unfold mcompose; simpl.
  destruct (mcomp_match M (mor_dom g) (mor_cod h)) as [gh Hgh]; simpl.
  destruct (mcomp_match M (mor_dom f) (mor_cod g)) as [fg Hfg]; simpl.
  destruct (mcomp_match M _ _) as [a Ha]; simpl.
  destruct (mcomp_match M _ _) as [b Hb]; simpl.
  exact (mcomp_unique M Ha (fst (mcomp_law Hfg Hgh b) Hb)).
Qed.

#[local] Instance mcompose_Proper {x y z} :
  Proper (@equiv _ (mmorphism_setoid y z) ==>
          @equiv _ (mmorphism_setoid x y) ==>
          @equiv _ (mmorphism_setoid x z)) (@mcompose x y z).
Proof. repeat intro; now apply mcompose_respects. Qed.

Definition Category_from_Metacategory : Category := {|
  obj     := mobject;
  hom     := mmorphism;
  homset  := mmorphism_setoid;
  id      := mid;
  compose := @mcompose;

  compose_respects := @mcompose_Proper;

  id_left        := @mcompose_id_left;
  id_right       := @mcompose_id_right;
  comp_assoc     := @mcompose_assoc;
  comp_assoc_sym := fun x y z w f g h => symmetry (@mcompose_assoc x y z w f g h)
|}.

(* The composite chosen by [mcompose] is characterised by the composition
   graph: any [h] with [mcomp (mor_arr f) (mor_arr g) h] IS that composite. *)
Lemma mcompose_char {x y z} (f : mmorphism y z) (g : mmorphism x y) h :
  mcomp M (mor_arr f) (mor_arr g) h → mor_arr (mcompose f g) ≈ h.
Proof.
  intro H; unfold mcompose; simpl.
  destruct (mcomp_match M _ _) as [h' Hh']; simpl.
  exact (mcomp_unique M Hh' H).
Qed.

(* Objects whose underlying identity arrows agree are isomorphic. *)
Definition mobject_iso_to {x y : mobject} (H : obj_arr x ≈ obj_arr y) :
  mmorphism x y :=
  {| mor_arr := obj_arr y
   ; mor_dom := mcomp_respects M (reflexivity _) (symmetry H) (reflexivity _)
                  (mident_idem (obj_id y))
   ; mor_cod := mident_idem (obj_id y) |}.

Definition mobject_iso_from {x y : mobject} (H : obj_arr x ≈ obj_arr y) :
  mmorphism y x :=
  {| mor_arr := obj_arr x
   ; mor_dom := mcomp_respects M (reflexivity _) H (reflexivity _)
                  (mident_idem (obj_id x))
   ; mor_cod := mident_idem (obj_id x) |}.

Definition mobject_iso {x y : mobject} (H : obj_arr x ≈ obj_arr y) :
  @Isomorphism Category_from_Metacategory x y :=
  @Build_Isomorphism Category_from_Metacategory x y
    (mobject_iso_to H) (mobject_iso_from H)
    (mcompose_char (mobject_iso_to H) (mobject_iso_from H)
       (obj_arr y) (mor_dom (mobject_iso_to H)))
    (mcompose_char (mobject_iso_from H) (mobject_iso_to H)
       (obj_arr x) (mor_dom (mobject_iso_from H))).

End Metacategory.

Arguments mor_arr _ {_ _} _.
Arguments mor_dom _ {_ _} _.
Arguments mor_cod _ {_ _} _.


(** * The converse passage: every category is an arrows-only metacategory *)

Section ToArrows.

Context {C : Category}.

(* The objects of [C] must form a SET: an arrows-only presentation identifies
   arrows whose endpoints agree, and in intensional type theory that comparison
   is an identity type. *)
Context (obj_uip : ∀ (x y : C) (p q : x = y), p = q).

Record Arr : Type := {
  asrc : C;
  atgt : C;
  aarr : asrc ~> atgt
}.

Definition tsrc {x y : C} (f : x ~> y) {x'} (p : x = x') : x' ~> y :=
  eq_rect x (fun s => s ~> y) f x' p.

Definition ttgt {x y : C} (f : x ~> y) {y'} (q : y = y') : x ~> y' :=
  eq_rect y (fun t => x ~> t) f y' q.

Definition Arr_bundle {x y : C} (f : x ~> y) : Arr :=
  {| asrc := x; atgt := y; aarr := f |}.

Definition Arr_eq (a b : Arr) : Type :=
  ∃ (p : asrc a = asrc b) (q : atgt a = atgt b),
    ttgt (tsrc (aarr a) p) q ≈ aarr b.

Definition Arr_comp (a b c : Arr) : Type :=
  ∃ p : atgt b = asrc a, Arr_eq (Arr_bundle (aarr a ∘ ttgt (aarr b) p)) c.

Definition Arr_defined (a b : Arr) := ∃ c, Arr_comp a b c.

Definition Arr_ident (u : Arr) :=
  (∀ f, Arr_defined f u → Arr_comp f u f) ∧
  (∀ g, Arr_defined u g → Arr_comp u g g).

Ltac arr_crush :=
  repeat (match goal with
  | [ a : Arr |- _ ] => destruct a
  | [ H : Arr_comp _ _ _ |- _ ] => destruct H as [? ?]
  | [ H : Arr_eq _ _ |- _ ] => destruct H as [? [? ?]]
  | [ H : Arr_defined _ _ |- _ ] => destruct H as [? ?]
  | [ p : @eq (@obj C) ?x ?x |- _ ] =>
    let H := fresh "Huip" in
    assert (H : p = eq_refl) by apply obj_uip; subst p
  | [ p : @eq (@obj C) _ _ |- _ ] => destruct p
  end; simpl in * ).

Lemma Arr_eq_equivalence : Equivalence Arr_eq.
Proof.
  constructor.
  - intros a; exists eq_refl, eq_refl; reflexivity.
  - intros a b H; arr_crush.
    exists eq_refl, eq_refl; simpl; symmetry; assumption.
  - intros a b c H1 H2; arr_crush.
    exists eq_refl, eq_refl; simpl.
    etransitivity; eassumption.
Qed.

Definition Arr_Setoid : Setoid Arr :=
  {| equiv := Arr_eq; setoid_equiv := Arr_eq_equivalence |}.

Ltac arr_finish :=
  repeat match goal with
  | [ H : ?x ≈ ?y |- _ ] => is_var x; rewrite H in *; clear H
  end;
  solve [ assumption
        | reflexivity
        | match goal with
          | [ H : _ ∘ _ ≈ _ |- _ ] => rewrite H; assumption
          end ].

Lemma Arr_comp_respects {a a' b b' c c'} :
  Arr_eq a a' → Arr_eq b b' → Arr_eq c c' → Arr_comp a b c → Arr_comp a' b' c'.
Proof.
  intros Ha Hb Hc H; arr_crush.
  exists eq_refl; exists eq_refl, eq_refl; simpl.
  arr_finish.
Qed.

Lemma Arr_comp_unique {a b c c'} :
  Arr_comp a b c → Arr_comp a b c' → Arr_eq c c'.
Proof using C obj_uip.
  intros H1 H2; arr_crush.
  exists eq_refl, eq_refl; simpl.
  etransitivity; [ symmetry; eassumption | eassumption ].
Qed.

Lemma Arr_comp_match {k g f kg gf} :
  Arr_comp k g kg → Arr_comp g f gf → ∃ kgf, Arr_comp kg f kgf.
Proof.
  intros H1 H2; arr_crush.
  eexists (Arr_bundle (_ ∘ _)).
  exists eq_refl; exists eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma Arr_comp_assoc_l {k g f kg kgf} :
  Arr_comp k g kg → Arr_comp kg f kgf →
  ∃ gf, Arr_comp g f gf ∧ Arr_comp k gf kgf.
Proof.
  intros H1 H2; arr_crush.
  eexists (Arr_bundle (_ ∘ _)); split.
  - exists eq_refl; exists eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; exists eq_refl, eq_refl; simpl.
    rewrite comp_assoc; arr_finish.
Qed.

Lemma Arr_comp_assoc_r {k g f gf kgf} :
  Arr_comp g f gf → Arr_comp k gf kgf →
  ∃ kg, Arr_comp k g kg ∧ Arr_comp kg f kgf.
Proof.
  intros H1 H2; arr_crush.
  eexists (Arr_bundle (_ ∘ _)); split.
  - exists eq_refl; exists eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; exists eq_refl, eq_refl; simpl.
    rewrite <- comp_assoc; arr_finish.
Qed.

Lemma Arr_ident_id (x : C) : Arr_ident (Arr_bundle (@id C x)).
Proof.
  split; intros f Hf.
  - destruct Hf as [c Hc]; destruct f as [f1 f2 f]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl; simpl; apply id_right.
  - destruct Hf as [c Hc]; destruct f as [f1 f2 f]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl; simpl; apply id_left.
Qed.

Lemma Arr_defined_src (a : Arr) : Arr_defined a (Arr_bundle (@id C (asrc a))).
Proof.
  exists a; destruct a; simpl.
  exists eq_refl; exists eq_refl, eq_refl; simpl; apply id_right.
Qed.

Lemma Arr_defined_tgt (a : Arr) : Arr_defined (Arr_bundle (@id C (atgt a))) a.
Proof.
  exists a; destruct a; simpl.
  exists eq_refl; exists eq_refl, eq_refl; simpl; apply id_left.
Qed.

Lemma Arr_ident_law (a : Arr) :
  ∃ u u', (Arr_ident u ∧ Arr_ident u') ∧ (Arr_defined a u ∧ Arr_defined u' a).
Proof.
  exists (Arr_bundle (@id C (asrc a))), (Arr_bundle (@id C (atgt a))).
  split; split.
  - apply Arr_ident_id.
  - apply Arr_ident_id.
  - apply Arr_defined_src.
  - apply Arr_defined_tgt.
Qed.

Definition ToArrows : Metacategory := {|
  marr           := Arr;
  marr_setoid    := Arr_Setoid;
  mcomp          := Arr_comp;
  mcomp_respects := @Arr_comp_respects;
  mcomp_unique   := @Arr_comp_unique;
  mcomp_assoc_l  := @Arr_comp_assoc_l;
  mcomp_assoc_r  := @Arr_comp_assoc_r;
  mcomp_match    := @Arr_comp_match;
  mident_law     := Arr_ident_law
|}.

End ToArrows.


(** * Round trip, category side *)

Section RoundTripCategory.

Context {C : Category}.
Context (obj_uip : ∀ (x y : C) (p q : x = y), p = q).

Notation M0 := (ToArrows obj_uip).

Definition FA_obj (x : C) : mobject M0 :=
  Build_mobject M0 (Arr_bundle (@id C x)) (Arr_ident_id x).

Lemma FA_dom {x y : C} (f : x ~> y) :
  Arr_comp (Arr_bundle f) (Arr_bundle (@id C x)) (Arr_bundle f).
Proof. exists eq_refl; exists eq_refl, eq_refl; simpl; apply id_right. Qed.

Lemma FA_cod {x y : C} (f : x ~> y) :
  Arr_comp (Arr_bundle (@id C y)) (Arr_bundle f) (Arr_bundle f).
Proof. exists eq_refl; exists eq_refl, eq_refl; simpl; apply id_left. Qed.

Definition FA_map {x y : C} (f : x ~> y) :
  mmorphism M0 (FA_obj x) (FA_obj y) :=
  Build_mmorphism M0 (FA_obj x) (FA_obj y) (Arr_bundle f) (FA_dom f) (FA_cod f).

Lemma FA_map_respects {x y : C} (f g : x ~> y) :
  f ≈ g → mor_arr M0 (FA_map f) ≈ mor_arr M0 (FA_map g).
Proof. intro H; exists eq_refl, eq_refl; exact H. Qed.

Lemma FA_fmap_id {x : C} :
  mor_arr M0 (FA_map (@id C x)) ≈ mor_arr M0 (mid M0 (FA_obj x)).
Proof. reflexivity. Qed.

Lemma FA_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  mor_arr M0 (FA_map (f ∘ g)) ≈ mor_arr M0 (mcompose M0 (FA_map f) (FA_map g)).
Proof.
  symmetry.
  apply (mcompose_char M0 (FA_map f) (FA_map g) (Arr_bundle (f ∘ g))).
  exists eq_refl; exists eq_refl, eq_refl; simpl; reflexivity.
Qed.

Definition ToArrows_Functor : C ⟶ Category_from_Metacategory M0 :=
  @Build_Functor C (Category_from_Metacategory M0)
    FA_obj (@FA_map)
    (fun x y f g H => @FA_map_respects x y f g H)
    (@FA_fmap_id) (@FA_fmap_comp).

Lemma ToArrows_fmap_inj {x y : C} (f g : x ~> y) :
  mor_arr M0 (FA_map f) ≈ mor_arr M0 (FA_map g) → f ≈ g.
Proof using C obj_uip.
  intros [p [q Hq]]; simpl in *.
  assert (Hp : p = eq_refl) by apply obj_uip; subst p.
  assert (Hq' : q = eq_refl) by apply obj_uip; subst q.
  exact Hq.
Qed.

Definition ToArrows_Faithful : Faithful ToArrows_Functor :=
  @Build_Faithful C (Category_from_Metacategory M0) ToArrows_Functor
    (@ToArrows_fmap_inj).

Definition ToArrows_prefmap {x y : C}
           (m : mmorphism M0 (FA_obj x) (FA_obj y)) : x ~> y.
Proof.
  destruct (mor_dom M0 m) as [p _].
  destruct (mor_cod M0 m) as [q _].
  simpl in p, q.
  exact (ttgt (tsrc (aarr (mor_arr M0 m)) (eq_sym p)) q).
Defined.

Lemma ToArrows_fmap_sur {x y : C} (m : mmorphism M0 (FA_obj x) (FA_obj y)) :
  mor_arr M0 (FA_map (ToArrows_prefmap m)) ≈ mor_arr M0 m.
Proof.
  unfold ToArrows_prefmap.
  destruct m as [a Hdom Hcod]; simpl in *.
  destruct Hdom as [p Hp]; destruct Hcod as [q Hq]; simpl in *.
  destruct a as [a1 a2 a]; simpl in *.
  destruct p, q; simpl.
  exists eq_refl, eq_refl; simpl; reflexivity.
Qed.

Definition ToArrows_Full : Full ToArrows_Functor :=
  @Build_Full C (Category_from_Metacategory M0) ToArrows_Functor
    (@ToArrows_prefmap) (@ToArrows_fmap_sur).

Lemma Arr_ident_is_id {a : marr M0} (H : mident M0 a) :
  a ≈ Arr_bundle (@id C (asrc a)).
Proof.
  exact (mident_unique_src M0 H (Arr_ident_id (asrc a))
           (a; mident_idem M0 H) (Arr_defined_src a)).
Qed.

Definition ToArrows_eso_obj (X : mobject M0) : C := asrc (obj_arr M0 X).

Lemma ToArrows_eso_eq (X : mobject M0) :
  obj_arr M0 (FA_obj (ToArrows_eso_obj X)) ≈ obj_arr M0 X.
Proof.
  symmetry; exact (Arr_ident_is_id (obj_id M0 X)).
Qed.

Definition ToArrows_EssentiallySurjective :
  EssentiallySurjective ToArrows_Functor :=
  @Build_EssentiallySurjective C (Category_from_Metacategory M0) ToArrows_Functor
    ToArrows_eso_obj (fun X => mobject_iso M0 (ToArrows_eso_eq X)).

Theorem ToArrows_Equivalence : EquivalenceOfCategories ToArrows_Functor.
Proof.
  exact (@FF_ESO_Equivalence C (Category_from_Metacategory M0) ToArrows_Functor
           ToArrows_Full ToArrows_Faithful ToArrows_EssentiallySurjective).
Defined.

End RoundTripCategory.


(** * Round trip, metacategory side *)

Section RoundTripMetacategory.

Context (M : Metacategory).

Definition arrow_of (a : @Arr (Category_from_Metacategory M)) : marr M :=
  mor_arr M (aarr a).

Theorem arrow_realized (f : marr M) :
  ∃ a : @Arr (Category_from_Metacategory M), arrow_of a ≈ f.
Proof.
  destruct (mident_law M f) as [u [u' [[Hu Hu'] [Hfu Hu'f]]]].
  unshelve eexists.
  - refine (@Build_Arr (Category_from_Metacategory M)
              (Build_mobject M u Hu) (Build_mobject M u' Hu') _).
    exact (Build_mmorphism M (Build_mobject M u Hu) (Build_mobject M u' Hu')
             f (fst Hu f Hfu) (snd Hu' f Hu'f)).
  - reflexivity.
Qed.

Theorem arrow_endpoints (a b : @Arr (Category_from_Metacategory M)) :
  arrow_of a ≈ arrow_of b →
  (obj_arr M (asrc a) ≈ obj_arr M (asrc b)) ∧
  (obj_arr M (atgt a) ≈ obj_arr M (atgt b)).
Proof.
  intro Heq; destruct a as [x y m], b as [x' y' m'].
  unfold arrow_of in Heq; simpl in *.
  split.
  - exact (mident_unique_src M (obj_id M x) (obj_id M x')
             (_; mor_dom M m)
             (_; mcomp_respects M (symmetry Heq) (reflexivity _)
                   (symmetry Heq) (mor_dom M m'))).
  - exact (mident_unique_tgt M (obj_id M y) (obj_id M y')
             (_; mor_cod M m)
             (_; mcomp_respects M (reflexivity _) (symmetry Heq)
                   (symmetry Heq) (mor_cod M m'))).
Qed.

Corollary arrow_endpoints_iso (a b : @Arr (Category_from_Metacategory M)) :
  arrow_of a ≈ arrow_of b →
  (@Isomorphism (Category_from_Metacategory M) (asrc a) (asrc b)) ∧
  (@Isomorphism (Category_from_Metacategory M) (atgt a) (atgt b)).
Proof.
  intro Heq; destruct (arrow_endpoints a b Heq) as [Hs Ht].
  exact (mobject_iso M Hs, mobject_iso M Ht).
Qed.

End RoundTripMetacategory.


(** * Why axiom (i) is stated in two halves *)

Record WeakMetacategory : Type := {
  wmarr : Type;
  wmarr_setoid : Setoid wmarr;
  wmcomp : wmarr → wmarr → wmarr → Type;
  wmdefined (g f : wmarr) := ∃ h, wmcomp g f h;

  wmcomp_respects {g g' f f' h h'} :
    @equiv _ wmarr_setoid g g' →
    @equiv _ wmarr_setoid f f' →
    @equiv _ wmarr_setoid h h' →
    wmcomp g f h → wmcomp g' f' h';

  wmcomp_unique {g f h h'} :
    wmcomp g f h → wmcomp g f h' → @equiv _ wmarr_setoid h h';

  (* Axiom (i) exactly as encoded in Theory/Metacategory.v and
     Theory/Metacategory/ArrowsOnly.v. *)
  wmcomp_law {k g f kg gf} :
    wmcomp k g kg → wmcomp g f gf →
    ∀ kgf, wmcomp kg f kgf ↔ wmcomp k gf kgf;

  wmcomp_match {k g f kg gf} :
    wmcomp k g kg → wmcomp g f gf → ∃ kgf, wmcomp kg f kgf;

  wmident (u : wmarr) :=
    (∀ f, wmdefined f u → wmcomp f u f) ∧ (∀ g, wmdefined u g → wmcomp u g g);

  wmident_law (g : wmarr) :
    ∃ u u', (wmident u ∧ wmident u') ∧ (wmdefined g u ∧ wmdefined u' g)
}.

#[export] Existing Instance wmarr_setoid.

(* Every metacategory is one, by [mcomp_law]. *)
Definition Weaken (M : Metacategory) : WeakMetacategory := {|
  wmarr           := marr M;
  wmarr_setoid    := marr_setoid M;
  wmcomp          := mcomp M;
  wmcomp_respects := @mcomp_respects M;
  wmcomp_unique   := @mcomp_unique M;
  wmcomp_law      := @mcomp_law M;
  wmcomp_match    := @mcomp_match M;
  wmident_law     := mident_law M
|}.

(* The countermodel: four arrows, with [Ag] flanked by TWO distinct source
   identities [Au] and [Aw]. *)
Inductive four := Ag | Au | Aw | Av.

Definition fcomp (a b c : four) : Prop :=
  match a, b, c with
  | Ag, Au, Ag => True
  | Ag, Aw, Ag => True
  | Av, Ag, Ag => True
  | Au, Au, Au => True
  | Aw, Aw, Aw => True
  | Av, Av, Av => True
  | _,  _,  _  => False
  end.

Ltac four_crush :=
  repeat match goal with
  | [ H : ∃ _ : four, _ |- _ ] => destruct H
  | [ a : four |- _ ] => destruct a
  end; simpl in *;
  try contradiction; try exact I; auto.

Ltac four_exists :=
  solve [ exists Ag; four_crush | exists Au; four_crush
        | exists Aw; four_crush | exists Av; four_crush ].

Definition fident (u : four) : Type :=
  (∀ f, (∃ h, fcomp f u h) → fcomp f u f) ∧
  (∀ g, (∃ h, fcomp u g h) → fcomp u g g).

Lemma fident_Au : fident Au.
Proof. split; intros f Hf; four_crush. Qed.

Lemma fident_Aw : fident Aw.
Proof. split; intros f Hf; four_crush. Qed.

Lemma fident_Av : fident Av.
Proof. split; intros f Hf; four_crush. Qed.

Definition FourWeak : WeakMetacategory.
Proof.
  unshelve refine {| wmarr := four
                   ; wmarr_setoid := eq_Setoid four
                   ; wmcomp := fcomp |}.
  - (* respects *) intros g g' f f' h h' Hg Hf Hh H; simpl in *; subst; exact H.
  - (* unique *) intros g f h h' H1 H2; simpl; four_crush.
  - (* weak axiom (i) *) intros k g f kg gf H1 H2 kgf; split; intro H; four_crush.
  - (* axiom (ii) *) intros k g f kg gf H1 H2; four_crush; four_exists.
  - (* axiom (iii) *)
    intro g; destruct g.
    + exists Au, Av; repeat split;
      solve [ apply fident_Au | apply fident_Av | four_exists ].
    + exists Au, Au; repeat split;
      solve [ apply fident_Au | four_exists ].
    + exists Aw, Aw; repeat split;
      solve [ apply fident_Aw | four_exists ].
    + exists Av, Av; repeat split;
      solve [ apply fident_Av | four_exists ].
Defined.

(* Under the weak encoding of axiom (i), Mac Lane's uniqueness remark is
   refuted: [Ag] has two distinct source identities. *)
Theorem weak_identity_not_unique :
  ∃ (W : WeakMetacategory) (g u u' : wmarr W),
    ((wmident W u ∧ wmident W u') ∧ (wmdefined W g u ∧ wmdefined W g u'))
      ∧ (u ≈ u' → False).
Proof.
  exists FourWeak, Ag, Au, Aw.
  split.
  - split.
    + exact (fident_Au, fident_Aw).
    + exact ((Ag; I), (Ag; I)).
  - intro Habs; simpl in Habs; discriminate.
Qed.
