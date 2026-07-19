Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(** Pseudofunctors between bicategories. *)

(* nLab: https://ncatlab.org/nlab/show/pseudofunctor

   A pseudofunctor (a.k.a. weak 2-functor) F : B ⟶ B' between bicategories
   sends 0-cells to 0-cells, and provides for each pair of 0-cells a functor
   of hom-categories

       pf1 : bicat B x y ⟶ bicat B' (pf0 x) (pf0 y),

   so that on 2-cells it acts functorially (vertical composition and identities
   are preserved on the nose).  Horizontal composition and identities are
   preserved only up to coherent invertible 2-cells: the unitor

       pf_id   : pf1 (bi1id) ≅ bi1id,

   and the compositor (natural in both arguments)

       pf_comp : pf1 (g ∘∘∘ f) ≅ pf1 g ∘∘∘ pf1 f.

   These are subject to three coherence laws relating them to the associator
   and unitors of the two bicategories: one associativity hexagon
   (`pf_assoc_coherence`) and two unit squares (`pf_unit_left`,
   `pf_unit_right`).  This mirrors the strong-monoidal-functor coherence of
   `Functor/Structure/Monoidal.v` under the dictionary tensor ↔ hcompose,
   I ↔ bi1id, μ ↔ pf_comp, η ↔ pf_id, α ↔ hassoc, λ/ρ ↔ hunit_left/right.

   Notation: `∘∘` is vertical 2-cell composition (`vcompose`), `∘∘∘` is
   horizontal 1-cell composition (`hcompose`), `hcomp2` the Godement
   horizontal composite of 2-cells; these follow `Theory/Bicategory.v`.  The
   `where`-notations of that file are local to its class body, so the two
   composition infixes are reinstated here (at their reserved levels).

   A hom-category `bicat B x y` is definitionally a `Category`, so the generic
   category laws hold for its 2-cells; but its composition prints as `vcompose`
   (`∘∘`) rather than the generic `∘`, and its identity as `bi2id`.  Rewriting
   therefore uses the bicategory's own `bi2id_left/right`, `vcompose_assoc`
   and the vcompose-form bridge lemmas below (isomorphism cancellation and
   functor action), all convertible to their generic counterparts. *)

Notation "f ∘∘ g" := (vcompose f g).
Notation "f ∘∘∘ g" := (hcompose (f, g)).

(* The image of an isomorphism under a functor, as a transparent definition so
   its `to`/`from` compute to `fmap` of the components — used to transport the
   compositor/unitor isos of one pseudofunctor through the hom-functor of
   another when composing pseudofunctors. *)
Program Definition map_iso `(F : C ⟶ D) {x y : C} (i : x ≅ y) : F x ≅ F y := {|
  to   := fmap[F] (to i);
  from := fmap[F] (from i)
|}.
Next Obligation. rewrite <- fmap_comp, iso_to_from; apply fmap_id. Qed.
Next Obligation. rewrite <- fmap_comp, iso_from_to; apply fmap_id. Qed.

(* Isomorphism cancellation, stated in `vcompose`/`bi2id` form for the 2-cells
   of a hom-category (each is the generic isomorphism law up to conversion). *)
Lemma bi_iso_to_from {B : Bicategory} {x y : @bi0cell B} {a b : @bicat B x y}
  (i : a ≅ b) : to i ∘∘ from i ≈ bi2id.
Proof. exact (iso_to_from i). Qed.

Lemma bi_iso_from_to {B : Bicategory} {x y : @bi0cell B} {a b : @bicat B x y}
  (i : a ≅ b) : from i ∘∘ to i ≈ bi2id.
Proof. exact (iso_from_to i). Qed.

(* Functor action on 2-cells, in `vcompose`/`bi2id` form.  `K` ranges over
   functors between hom-categories (the hom-functors `pf1` of a pseudofunctor);
   these are the generic `fmap_comp`/`fmap_id` up to conversion. *)
Lemma pfmap_comp {B B' : Bicategory} {x y : @bi0cell B} {c d : @bi0cell B'}
  (K : @bicat B x y ⟶ @bicat B' c d) {p q r : @bicat B x y}
  (u : q ~> r) (v : p ~> q) :
  fmap[K] (u ∘∘ v) ≈ fmap[K] u ∘∘ fmap[K] v.
Proof. exact (fmap_comp u v). Qed.

Lemma pfmap_id {B B' : Bicategory} {x y : @bi0cell B} {c d : @bi0cell B'}
  (K : @bicat B x y ⟶ @bicat B' c d) {p : @bicat B x y} :
  fmap[K] (bi2id (a:=p)) ≈ bi2id.
Proof. exact fmap_id. Qed.

Section Hcomp2.
Context {B : Bicategory}.

(* The Godement composite of two identity 2-cells is the identity, because
   `hcomp2` is the functorial action of `hcompose` and `(bi2id, bi2id)` is the
   identity of the product hom-category. *)
Lemma hcomp2_id {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
  hcomp2 (bi2id (a:=g)) (bi2id (a:=f)) ≈ bi2id.
Proof. exact (@fmap_id _ _ (@hcompose B x y z) (g, f)). Qed.

(* Middle-four interchange: `hcomp2` distributes over vertical composition,
   again as `fmap_comp` of `hcompose` on the componentwise-composed pair. *)
Lemma hcomp2_comp {x y z : @bi0cell B}
  {g g' g'' : @bicat B y z} {f f' f'' : @bicat B x y}
  (θ' : g' ~> g'') (θ : g ~> g') (η' : f' ~> f'') (η : f ~> f') :
  hcomp2 (θ' ∘∘ θ) (η' ∘∘ η) ≈ hcomp2 θ' η' ∘∘ hcomp2 θ η.
Proof.
  exact (@fmap_comp _ _ (@hcompose B x y z)
           (g,f) (g',f') (g'',f'') (θ',η') (θ,η)).
Qed.

(* `hcomp2` respects 2-cell equivalence in both arguments. *)
#[export] Instance hcomp2_respects {x y z : @bi0cell B}
  {g g' : @bicat B y z} {f f' : @bicat B x y} :
  Proper (equiv ==> equiv ==> equiv) (@hcomp2 B x y z g g' f f').
Proof.
  intros θ1 θ2 Hθ η1 η2 Hη.
  exact (@fmap_respects _ _ (@hcompose B x y z) (g,f) (g',f')
           (θ1,η1) (θ2,η2) (Hθ, Hη)).
Qed.

(* The two whiskered specialisations of interchange, closing the residual
   `bi2id ∘∘ bi2id` by unitality. *)
Lemma hcomp2_comp_left {x y z : @bi0cell B}
  {g g' g'' : @bicat B y z} {f : @bicat B x y}
  (θ' : g' ~> g'') (θ : g ~> g') :
  hcomp2 (θ' ∘∘ θ) (bi2id (a:=f)) ≈ hcomp2 θ' bi2id ∘∘ hcomp2 θ bi2id.
Proof.
  rewrite <- hcomp2_comp.
  rewrite bi2id_left.
  reflexivity.
Qed.

Lemma hcomp2_comp_right {x y z : @bi0cell B}
  {g : @bicat B y z} {f f' f'' : @bicat B x y}
  (η' : f' ~> f'') (η : f ~> f') :
  hcomp2 (bi2id (a:=g)) (η' ∘∘ η) ≈ hcomp2 bi2id η' ∘∘ hcomp2 bi2id η.
Proof.
  rewrite <- hcomp2_comp.
  rewrite bi2id_left.
  reflexivity.
Qed.

End Hcomp2.

(* The pseudofunctor class, at full strength.  Following the nLab definition,
   with the compositor oriented `pf1 (g ∘∘∘ f) ≅ pf1 g ∘∘∘ pf1 f` and the
   unitor `pf1 bi1id ≅ bi1id` (both invertible), and the coherence laws phrased
   through `hcomp2`, `hassoc` and the unitors of the target bicategory. *)
Class Pseudofunctor (B B' : Bicategory) := {
  pf0 : @bi0cell B → @bi0cell B';        (* action on 0-cells *)

  (* the hom-functors: functorial action on 1-cells and 2-cells *)
  pf1 {x y : @bi0cell B} : @bicat B x y ⟶ @bicat B' (pf0 x) (pf0 y);

  (* unitor: identities preserved up to invertible 2-cell *)
  pf_id {x : @bi0cell B} :
    pf1 (@bi1id B x) ≅[@bicat B' (pf0 x) (pf0 x)] @bi1id B' (pf0 x);

  (* compositor: horizontal composition preserved up to invertible 2-cell *)
  pf_comp {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
    pf1 (g ∘∘∘ f) ≅[@bicat B' (pf0 x) (pf0 z)] (pf1 g ∘∘∘ pf1 f);

  (* naturality of the compositor in both 1-cell arguments *)
  pf_comp_natural {x y z : @bi0cell B}
      {g g' : @bicat B y z} {f f' : @bicat B x y}
      (θ : g ~{@bicat B y z}~> g') (η : f ~{@bicat B x y}~> f') :
    to (pf_comp g' f') ∘∘ fmap[pf1] (hcomp2 θ η)
      ≈ hcomp2 (fmap[pf1] θ) (fmap[pf1] η) ∘∘ to (pf_comp g f);

  (* associativity hexagon: the two ways of comparing pf1 ((h∘g)∘f) with
     pf1 h ∘∘∘ (pf1 g ∘∘∘ pf1 f) — reassociating the images first, versus
     reassociating in the source and applying pf1 — agree. *)
  pf_assoc_coherence {w x y z : @bi0cell B}
      (h : @bicat B y z) (g : @bicat B x y) (f : @bicat B w x) :
    to (hassoc (pf1 h) (pf1 g) (pf1 f))
      ∘∘ hcomp2 (to (pf_comp h g)) (bi2id (a:=pf1 f))
      ∘∘ to (pf_comp (h ∘∘∘ g) f)
    ≈ hcomp2 (bi2id (a:=pf1 h)) (to (pf_comp g f))
      ∘∘ to (pf_comp h (g ∘∘∘ f))
      ∘∘ fmap[pf1] (to (hassoc h g f));

  (* left-unit coherence: the target left unitor factors through the
     compositor, the unitor, and pf1 of the source left unitor. *)
  pf_unit_left {x y : @bi0cell B} (f : @bicat B x y) :
    to (hunit_left (pf1 f))
      ≈ fmap[pf1] (to (hunit_left f))
         ∘∘ from (pf_comp (@bi1id B y) f)
         ∘∘ hcomp2 (from pf_id) (bi2id (a:=pf1 f));

  (* right-unit coherence, the mirror image on the other whiskering side *)
  pf_unit_right {x y : @bi0cell B} (f : @bicat B x y) :
    to (hunit_right (pf1 f))
      ≈ fmap[pf1] (to (hunit_right f))
         ∘∘ from (pf_comp f (@bi1id B x))
         ∘∘ hcomp2 (bi2id (a:=pf1 f)) (from pf_id)
}.

Arguments pf0 {B B'} _ _.
Arguments pf1 {B B' _ x y}.
Arguments pf_id {B B' _ x}.
Arguments pf_comp {B B' _ x y z} g f.

Notation "pf1[ F ]" := (@pf1 _ _ F%functor _ _)
  (at level 9, format "pf1[ F ]").

(* The compositor's naturality in its `from` (lax) orientation, obtained from
   `pf_comp_natural` by cancelling the invertible compositor on both sides.
   This is the form the composite-pseudofunctor coherence proofs consume. *)
Lemma pf_comp_natural_from {B B' : Bicategory} (P : Pseudofunctor B B')
  {x y z : @bi0cell B} {g g' : @bicat B y z} {f f' : @bicat B x y}
  (θ : g ~{@bicat B y z}~> g') (η : f ~{@bicat B x y}~> f') :
  fmap[pf1] (hcomp2 θ η) ∘∘ from (pf_comp g f)
    ≈ from (pf_comp g' f') ∘∘ hcomp2 (fmap[pf1] θ) (fmap[pf1] η).
Proof.
  rewrite <- (bi2id_left (fmap[pf1] (hcomp2 θ η) ∘∘ from (pf_comp g f))).
  rewrite <- (bi_iso_from_to (pf_comp g' f')).
  rewrite <- !vcompose_assoc.
  apply vcompose_respects; [ reflexivity | ].
  rewrite vcompose_assoc.
  rewrite (pf_comp_natural θ η).
  rewrite <- vcompose_assoc.
  rewrite bi_iso_to_from, bi2id_right.
  reflexivity.
Qed.

(* The identity pseudofunctor: the hom-functors are identity functors, and the
   unitor and compositor are identity isomorphisms (both hold definitionally,
   since `Id` preserves horizontal composition and identities on the nose). *)
Program Definition Identity_Pseudofunctor (B : Bicategory) :
  Pseudofunctor B B := {|
  pf0 := fun x => x;
  pf1 := fun x y => Id[@bicat B x y];
  pf_id := fun x => iso_id;
  pf_comp := fun x y z g f => iso_id
|}.
Next Obligation.
  (* pf_comp_natural *)
  simpl; rewrite ?hcomp2_id, ?bi2id_left, ?bi2id_right; reflexivity.
Qed.
Next Obligation.
  (* pf_assoc_coherence *)
  simpl; rewrite ?hcomp2_id, ?bi2id_left, ?bi2id_right; reflexivity.
Qed.
Next Obligation.
  (* pf_unit_left *)
  simpl; rewrite ?hcomp2_id, ?bi2id_left, ?bi2id_right; reflexivity.
Qed.
Next Obligation.
  (* pf_unit_right *)
  simpl; rewrite ?hcomp2_id, ?bi2id_left, ?bi2id_right; reflexivity.
Qed.

(* Pure-associativity assembly of the pseudofunctor associativity hexagon.  In
   an arbitrary category, given the four categorical facts that arise (two
   compositor-naturality squares GN1/GN2, the outer factor's hexagon GHEX, and
   the inner factor's hexagon transported through the outer hom-functor HGMF),
   the two sides of the composite hexagon agree.  Isolating the bookkeeping here
   keeps the composite proof free of associativity churn. *)
Lemma hex_assemble {C : Category}
  {s t v1 v2 v3 v4 u1 u2 u3 w1 w2 x1 : C}
  {P4 : s ~> v1} {P3 : v1 ~> v2} {P2 : v2 ~> v3} {P1 : v3 ~> v4} {A0 : v4 ~> t}
  {R3 : v1 ~> u1} {R2 : u1 ~> v3}
  {T : u1 ~> u2} {S : u2 ~> u3} {Q1 : u3 ~> t}
  {Q5 : s ~> w1} {Q4 : w1 ~> w2} {U : w2 ~> u2}
  {Q3 : w2 ~> x1} {Q2 : x1 ~> u3}
  (GN1 : R2 ∘ R3 ≈ P2 ∘ P3)
  (GHEX : A0 ∘ P1 ∘ R2 ≈ Q1 ∘ S ∘ T)
  (HGMF : T ∘ R3 ∘ P4 ≈ U ∘ Q4 ∘ Q5)
  (GN2 : S ∘ U ≈ Q2 ∘ Q3) :
  A0 ∘ P1 ∘ P2 ∘ P3 ∘ P4 ≈ Q1 ∘ Q2 ∘ Q3 ∘ Q4 ∘ Q5.
Proof.
  rewrite <- (comp_assoc (A0 ∘ P1) P2 P3).
  rewrite <- GN1.
  rewrite (comp_assoc (A0 ∘ P1) R2 R3).
  rewrite GHEX.
  rewrite <- (comp_assoc (Q1 ∘ S) T R3).
  rewrite <- (comp_assoc (Q1 ∘ S) (T ∘ R3) P4).
  rewrite HGMF.
  rewrite <- (comp_assoc Q1 S ((U ∘ Q4) ∘ Q5)).
  rewrite <- (comp_assoc U Q4 Q5).
  rewrite (comp_assoc S U (Q4 ∘ Q5)).
  rewrite GN2.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(* The composite of two pseudofunctors.  On 0-cells and hom-functors it is the
   pointwise composite; its unitor and compositor are built from those of the
   two factors, transporting the inner factor's iso through the outer factor's
   hom-functor with `map_iso`.  The coherence proofs combine the two factors'
   coherences with the naturality (`pf_comp_natural_from`) and functoriality of
   the outer hom-functor. *)
Section Compose.
Context {B B' B'' : Bicategory}.
Context (G : Pseudofunctor B' B'') (F : Pseudofunctor B B').

Definition comp_pf0 (x : @bi0cell B) : @bi0cell B'' := pf0 G (pf0 F x).

Definition comp_pf1 {x y : @bi0cell B} :
  @bicat B x y ⟶ @bicat B'' (comp_pf0 x) (comp_pf0 y) :=
  @pf1 _ _ G (pf0 F x) (pf0 F y) ◯ @pf1 _ _ F x y.

Definition comp_pf_id {x : @bi0cell B} :
  comp_pf1 (@bi1id B x) ≅[@bicat B'' (comp_pf0 x) (comp_pf0 x)]
    @bi1id B'' (comp_pf0 x) :=
  iso_compose (@pf_id _ _ G (pf0 F x))
              (map_iso (@pf1 _ _ G (pf0 F x) (pf0 F x)) (@pf_id _ _ F x)).

Definition comp_pf_comp {x y z : @bi0cell B}
    (g : @bicat B y z) (f : @bicat B x y) :
  comp_pf1 (g ∘∘∘ f) ≅[@bicat B'' (comp_pf0 x) (comp_pf0 z)]
    (comp_pf1 g ∘∘∘ comp_pf1 f) :=
  iso_compose
    (@pf_comp _ _ G (pf0 F x) (pf0 F y) (pf0 F z)
       (@pf1 _ _ F y z g) (@pf1 _ _ F x y f))
    (map_iso (@pf1 _ _ G (pf0 F x) (pf0 F z)) (@pf_comp _ _ F x y z g f)).

(* Reduction lemmas exposing the composite unitor/compositor and hom-functor
   action in `vcompose` normal form (each holds by conversion). *)
Lemma comp_pf1_fmap {x y : @bi0cell B} {a b : @bicat B x y} (u : a ~> b) :
  fmap[@comp_pf1 x y] u
    ≈ fmap[@pf1 _ _ G (pf0 F x) (pf0 F y)] (fmap[@pf1 _ _ F x y] u).
Proof. reflexivity. Qed.

Lemma to_comp_pf_comp {x y z : @bi0cell B}
    (g : @bicat B y z) (f : @bicat B x y) :
  to (comp_pf_comp g f)
    ≈ to (@pf_comp _ _ G _ _ _ (@pf1 _ _ F y z g) (@pf1 _ _ F x y f))
        ∘∘ fmap[@pf1 _ _ G (pf0 F x) (pf0 F z)] (to (@pf_comp _ _ F x y z g f)).
Proof. reflexivity. Qed.

Lemma from_comp_pf_comp {x y z : @bi0cell B}
    (g : @bicat B y z) (f : @bicat B x y) :
  from (comp_pf_comp g f)
    ≈ fmap[@pf1 _ _ G (pf0 F x) (pf0 F z)] (from (@pf_comp _ _ F x y z g f))
        ∘∘ from (@pf_comp _ _ G _ _ _ (@pf1 _ _ F y z g) (@pf1 _ _ F x y f)).
Proof. reflexivity. Qed.

Lemma from_comp_pf_id {x : @bi0cell B} :
  from (@comp_pf_id x)
    ≈ fmap[@pf1 _ _ G (pf0 F x) (pf0 F x)] (from (@pf_id _ _ F x))
        ∘∘ from (@pf_id _ _ G (pf0 F x)).
Proof. reflexivity. Qed.

Lemma comp_pf_comp_natural {x y z : @bi0cell B}
    {g g' : @bicat B y z} {f f' : @bicat B x y}
    (θ : g ~{@bicat B y z}~> g') (η : f ~{@bicat B x y}~> f') :
  to (comp_pf_comp g' f') ∘∘ fmap[comp_pf1] (hcomp2 θ η)
    ≈ hcomp2 (fmap[comp_pf1] θ) (fmap[comp_pf1] η) ∘∘ to (comp_pf_comp g f).
Proof.
  pose proof (@pf_comp_natural _ _ F _ _ _ _ _ _ _ θ η) as HF.
  pose proof (@pf_comp_natural _ _ G _ _ _ _ _ _ _
                (fmap[@pf1 _ _ F y z] θ) (fmap[@pf1 _ _ F x y] η)) as HG.
  rewrite !to_comp_pf_comp.
  rewrite !comp_pf1_fmap.
  rewrite <- vcompose_assoc.
  setoid_rewrite <- (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F z))) at 1.
  rewrite HF.
  setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F z))) at 1.
  rewrite vcompose_assoc.
  rewrite HG.
  rewrite <- vcompose_assoc.
  reflexivity.
Qed.

Lemma comp_pf_assoc_coherence {w x y z : @bi0cell B}
    (h : @bicat B y z) (g : @bicat B x y) (f : @bicat B w x) :
  to (hassoc (comp_pf1 h) (comp_pf1 g) (comp_pf1 f))
    ∘∘ hcomp2 (to (comp_pf_comp h g)) (bi2id (a:=comp_pf1 f))
    ∘∘ to (comp_pf_comp (h ∘∘∘ g) f)
  ≈ hcomp2 (bi2id (a:=comp_pf1 h)) (to (comp_pf_comp g f))
    ∘∘ to (comp_pf_comp h (g ∘∘∘ f))
    ∘∘ fmap[comp_pf1] (to (hassoc h g f)).
Proof.
  (* GN1: compositor-naturality of G, whiskered on the right by pf1[F] f. *)
  pose proof (@pf_comp_natural _ _ G _ _ _ _ _ _ _
                (to (@pf_comp _ _ F x y z h g)) (bi2id (a:=pf1[F] f))) as GN1.
  rewrite (pfmap_id (@pf1 _ _ G (pf0 F w) (pf0 F x))) in GN1.
  (* GN2: compositor-naturality of G, whiskered on the left by pf1[F] h. *)
  pose proof (@pf_comp_natural _ _ G _ _ _ _ _ _ _
                (bi2id (a:=pf1[F] h)) (to (@pf_comp _ _ F w x y g f))) as GN2.
  rewrite (pfmap_id (@pf1 _ _ G (pf0 F y) (pf0 F z))) in GN2.
  (* GHEX: the associativity hexagon of G at the images of h, g, f. *)
  pose proof (@pf_assoc_coherence _ _ G (pf0 F w) (pf0 F x) (pf0 F y) (pf0 F z)
                (pf1[F] h) (pf1[F] g) (pf1[F] f)) as GHEX.
  (* HGMF: the associativity hexagon of F, transported through G's hom-functor
     `pf1[G]` by merging the three factors, rewriting, and re-splitting. *)
  pose proof (@pf_assoc_coherence _ _ F w x y z h g f) as FHEX.
  assert (HGMF :
    fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
        (to (hassoc (pf1[F] h) (pf1[F] g) (pf1[F] f)))
      ∘∘ fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
          (hcomp2 (to (@pf_comp _ _ F x y z h g)) (bi2id (a:=pf1[F] f)))
      ∘∘ fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
          (to (@pf_comp _ _ F w x z (h ∘∘∘ g) f))
    ≈ fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
          (hcomp2 (bi2id (a:=pf1[F] h)) (to (@pf_comp _ _ F w x y g f)))
      ∘∘ fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
          (to (@pf_comp _ _ F w y z h (g ∘∘∘ f)))
      ∘∘ fmap[@pf1 _ _ G (pf0 F w) (pf0 F z)]
          (fmap[@pf1 _ _ F w z] (to (hassoc h g f)))).
  { setoid_rewrite <- (pfmap_comp (@pf1 _ _ G (pf0 F w) (pf0 F z))) at 1.
    setoid_rewrite <- (pfmap_comp (@pf1 _ _ G (pf0 F w) (pf0 F z))) at 1.
    rewrite FHEX.
    setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F w) (pf0 F z))) at 1.
    setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F w) (pf0 F z))) at 1.
    reflexivity. }
  (* Expose the composite compositors/hom-functor action, fully left-associate,
     and combine the four facts through the pure-associativity assembler. *)
  rewrite !to_comp_pf_comp.
  rewrite comp_pf1_fmap.
  rewrite hcomp2_comp_left.
  rewrite hcomp2_comp_right.
  rewrite !vcompose_assoc.
  exact (hex_assemble (C:=@bicat B'' (comp_pf0 w) (comp_pf0 z))
           GN1 GHEX HGMF GN2).
Qed.

Lemma comp_pf_unit_left {x y : @bi0cell B} (f : @bicat B x y) :
  to (hunit_left (comp_pf1 f))
    ≈ fmap[comp_pf1] (to (hunit_left f))
       ∘∘ from (comp_pf_comp (@bi1id B y) f)
       ∘∘ hcomp2 (from comp_pf_id) (bi2id (a:=comp_pf1 f)).
Proof.
  rewrite (@pf_unit_left _ _ G (pf0 F x) (pf0 F y) (pf1[F] f)).
  rewrite (@pf_unit_left _ _ F x y f).
  rewrite from_comp_pf_comp, from_comp_pf_id, comp_pf1_fmap.
  setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F y))) at 1.
  setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F y))) at 1.
  rewrite hcomp2_comp_left.
  pose proof (@pf_comp_natural_from _ _ G _ _ _ _ _ _ _
                (from (@pf_id _ _ F y)) (bi2id (a:=pf1[F] f))) as HGN.
  rewrite (pfmap_id (@pf1 _ _ G (pf0 F x) (pf0 F y))) in HGN.
  rewrite <- !vcompose_assoc.
  f_equiv.
  f_equiv.
  rewrite !vcompose_assoc.
  rewrite HGN.
  reflexivity.
Qed.

Lemma comp_pf_unit_right {x y : @bi0cell B} (f : @bicat B x y) :
  to (hunit_right (comp_pf1 f))
    ≈ fmap[comp_pf1] (to (hunit_right f))
       ∘∘ from (comp_pf_comp f (@bi1id B x))
       ∘∘ hcomp2 (bi2id (a:=comp_pf1 f)) (from comp_pf_id).
Proof.
  rewrite (@pf_unit_right _ _ G (pf0 F x) (pf0 F y) (pf1[F] f)).
  rewrite (@pf_unit_right _ _ F x y f).
  rewrite from_comp_pf_comp, from_comp_pf_id, comp_pf1_fmap.
  setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F y))) at 1.
  setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F y))) at 1.
  rewrite hcomp2_comp_right.
  pose proof (@pf_comp_natural_from _ _ G _ _ _ _ _ _ _
                (bi2id (a:=pf1[F] f)) (from (@pf_id _ _ F x))) as HGN.
  rewrite (pfmap_id (@pf1 _ _ G (pf0 F x) (pf0 F y))) in HGN.
  rewrite <- !vcompose_assoc.
  f_equiv.
  f_equiv.
  rewrite !vcompose_assoc.
  rewrite HGN.
  reflexivity.
Qed.

Program Definition Compose_Pseudofunctor : Pseudofunctor B B'' := {|
  pf0 := comp_pf0;
  pf1 := @comp_pf1;
  pf_id := @comp_pf_id;
  pf_comp := @comp_pf_comp
|}.
Next Obligation. apply comp_pf_comp_natural. Qed.
Next Obligation. apply comp_pf_assoc_coherence. Qed.
Next Obligation. apply comp_pf_unit_left. Qed.
Next Obligation. apply comp_pf_unit_right. Qed.

End Compose.
