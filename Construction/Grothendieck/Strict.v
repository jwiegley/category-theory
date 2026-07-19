Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * Constructors for indexed categories *)

(* nLab:      https://ncatlab.org/nlab/show/indexed+category
   nLab:      https://ncatlab.org/nlab/show/strict+category
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction
   Reference: Michael Hedberg, "A coherence theorem for Martin-Löf's type
              theory", Journal of Functional Programming 8(4), 1998
              (decidable equality implies uniqueness of identity proofs).

   This file provides two constructors for the coherent "pseudofunctor-lite"
   [IndexedCat] (Construction/Indexed.v).

   The first constructor turns a functor [F : B ⟶ StrictCat] into an indexed
   category.  [StrictCat] (Instance/StrictCat.v) compares functors by strict
   equality [Functor_StrictEq_Setoid]: equal object maps [F x = G x] together
   with a coherence forcing the morphism actions to agree after transport.
   Reading each such object equality through [iso_of_eq]
   (Instance/StrictCat/ToCat.v) supplies the chosen fibre isomorphisms that
   [IndexedCat] demands.  The naturality fields fall out of the strict-equality
   coherence read through the transport/iso dictionary
   ([transport_cod_to_iso], [transport_r_dom_to_iso]).  The remaining
   pseudofunctor coherence — proof irrelevance of [idx_resp], the unit laws,
   the associativity cocycle — asks that competing composites of [iso_of_eq]
   proofs agree; this needs the propositional object-equality proofs in each
   fibre to be unique, i.e. uniqueness of identity proofs (UIP) on the objects
   of every fibre.  UIP is taken as a hypothesis, discharged for fibres with
   decidable object equality by Hedberg's theorem (proved locally here so as
   not to depend on any one stdlib packaging of the result).

   The second constructor is the constant indexed category: every fibre is a
   fixed [D], every reindexing is the identity functor, and every mediating
   isomorphism is the identity, so all the coherence holds trivially.  Its
   Grothendieck construction is the product category, witnessed by the
   [≅[Cat]] isomorphism [Grothendieck_Constant_iso]. *)

(** ** Coherence of [iso_of_eq]

    The chosen fibre isomorphisms are all of the form [iso_of_eq p] for a
    propositional object equality [p].  These lemmas record how [iso_of_eq]
    interacts with transitivity, symmetry, functor action, and strict-equality
    coherence; none of them needs UIP. *)

(* Reading [iso_of_eq] through a concatenation of equalities composes the
   isomorphisms (in the opposite order, as always for [to]). *)
Lemma iso_of_eq_trans {C : Category} {x y z : C} (p : x = y) (q : y = z) :
  to (iso_of_eq (eq_trans p q)) ≈ to (iso_of_eq q) ∘ to (iso_of_eq p).
Proof. destruct p, q; cat. Qed.

(* [iso_of_eq] of a reversed equality is the inverse isomorphism. *)
Lemma iso_of_eq_sym {C : Category} {x y : C} (p : x = y) :
  to (iso_of_eq (eq_sym p)) ≈ from (iso_of_eq p).
Proof. destruct p; cat. Qed.

(* A functor carries [iso_of_eq p] to [iso_of_eq] of the image equality. *)
Lemma fmap_iso_of_eq {C D : Category} (G : C ⟶ D) {x y : C} (p : x = y) :
  fmap[G] (to (iso_of_eq p)) ≈ to (iso_of_eq (f_equal (fobj[G]) p)).
Proof. destruct p; simpl; apply fmap_id. Qed.

(* Strict equality of two functors makes the family [iso_of_eq (`1 S -)]
   natural: this is exactly the strict-equality coherence [`2 S] read through
   the transport/iso dictionary of Instance/StrictCat/ToCat.v. *)
Lemma strict_eq_iso_natural {C D : Category} {F' G' : C ⟶ D}
  (S : @equiv _ Functor_StrictEq_Setoid F' G') {a b : C} (k : a ~> b) :
  fmap[G'] k ∘ to (iso_of_eq (`1 S a)) ≈ to (iso_of_eq (`1 S b)) ∘ fmap[F'] k.
Proof.
  pose proof (`2 S a b k) as Hc.
  rewrite transport_cod_to_iso in Hc.
  rewrite transport_r_dom_to_iso in Hc.
  symmetry; exact Hc.
Qed.

(* The inverse-side companion, obtained by conjugating the naturality with the
   two inverse laws (the shape of [idx_resp_natural_from] in
   Construction/Indexed.v). *)
Lemma strict_eq_iso_natural_from {C D : Category} {F' G' : C ⟶ D}
  (S : @equiv _ Functor_StrictEq_Setoid F' G') {a b : C} (k : a ~> b) :
  fmap[F'] k ∘ from (iso_of_eq (`1 S a)) ≈ from (iso_of_eq (`1 S b)) ∘ fmap[G'] k.
Proof.
  rewrite <- (id_left (fmap[F'] k)).
  rewrite <- (iso_from_to (iso_of_eq (`1 S b))).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (strict_eq_iso_natural S k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (iso_of_eq (`1 S a))).
  apply id_right.
Qed.

(** ** Hedberg's theorem

    A type with decidable equality has uniqueness of identity proofs.  The
    proof is the classical one: a decision procedure yields a constant
    endofunction [hedberg_nu] on each identity type, and a constant
    endofunction with a retraction forces every two proofs to agree.  It is
    reproduced here rather than imported so this file does not depend on the
    particular module in which any given Rocq release ships the result. *)

(* Concatenating a reversed equality with itself is reflexivity. *)
Lemma eq_trans_sym_l {A : Type} {x z : A} (a : x = z) :
  eq_trans (eq_sym a) a = eq_refl.
Proof. destruct a; reflexivity. Qed.

(* The normalisation of an identity proof through a decision procedure. *)
Definition hedberg_nu {A : Type} (dec : ∀ x y : A, {x = y} + {x <> y})
  {x y : A} (p : x = y) : x = y :=
  match dec x y with
  | left e => e
  | right ne => match ne p with end
  end.

(* [hedberg_nu] does not depend on the proof it normalises. *)
Lemma hedberg_nu_const {A : Type} (dec : ∀ x y : A, {x = y} + {x <> y})
  {x y : A} (p q : x = y) : hedberg_nu dec p = hedberg_nu dec q.
Proof.
  unfold hedberg_nu; destruct (dec x y).
  - reflexivity.
  - destruct (n p).
Qed.

(* A retraction for [hedberg_nu]. *)
Definition hedberg_nu_inv {A : Type} (dec : ∀ x y : A, {x = y} + {x <> y})
  {x y : A} (e : x = y) : x = y :=
  eq_trans (eq_sym (hedberg_nu dec (@eq_refl A x))) e.

(* [hedberg_nu_inv] retracts [hedberg_nu]. *)
Lemma hedberg_nu_inv_nu {A : Type} (dec : ∀ x y : A, {x = y} + {x <> y})
  {x y : A} (p : x = y) : hedberg_nu_inv dec (hedberg_nu dec p) = p.
Proof.
  destruct p; unfold hedberg_nu_inv.
  apply eq_trans_sym_l.
Qed.

(* Hedberg: decidable equality implies uniqueness of identity proofs. *)
Theorem hedberg {A : Type} (dec : ∀ x y : A, {x = y} + {x <> y})
  {x y : A} (p q : x = y) : p = q.
Proof.
  rewrite <- (hedberg_nu_inv_nu dec p), <- (hedberg_nu_inv_nu dec q).
  now rewrite (hedberg_nu_const dec p q).
Qed.

(** ** The indexed category of a strict functor *)

Section StrictFunctorToIndexed.

Context {B : Category}.
Context (F : B ⟶ StrictCat).

(* Fibrewise uniqueness of identity proofs on objects: the coherence-collapsing
   hypothesis.  It is legitimate object-level [=] (sanctioned here by the strict
   fibre anchoring of the construction) and is discharged from decidable object
   equality by [hedberg] below. *)
Hypothesis Fuip : ∀ (b : B) (x y : F b) (p q : x = y), p = q.

(* Under UIP, [iso_of_eq] does not depend on its equality proof. *)
Lemma iso_of_eq_irrel {b : B} {X Y : F b} (p q : X = Y) :
  to (iso_of_eq p) ≈ to (iso_of_eq q).
Proof using B F Fuip. now rewrite (Fuip b X Y p q). Qed.

(* Under UIP, [iso_of_eq] of a self-equality is the identity. *)
Lemma iso_of_eq_refl_id {b : B} {X : F b} (p : X = X) : to (iso_of_eq p) ≈ id.
Proof using B F Fuip. now rewrite (Fuip b X X p (@eq_refl _ X)). Qed.

(* The strict-equality witnesses that [F] supplies for reindexing along
   equivalent, identity, and composite base morphisms. *)
Definition Sresp {x y : B} {f g : x ~> y} (e : f ≈ g) :
  @equiv _ Functor_StrictEq_Setoid (fmap[F] f) (fmap[F] g) :=
  @fmap_respects _ _ F x y f g e.

Definition Sid (x : B) :
  @equiv _ Functor_StrictEq_Setoid (fmap[F] (@id B x)) (@id StrictCat (F x)) :=
  @fmap_id _ _ F x.

Definition Scomp {x y z : B} (f : y ~> z) (g : x ~> y) :
  @equiv _ Functor_StrictEq_Setoid (fmap[F] (f ∘ g)) (fmap[F] f ∘ fmap[F] g) :=
  @fmap_comp _ _ F x y z f g.

(* The indexed-category data: fibres are [F]'s values, reindexing is [F]'s
   action, and the mediators are the [iso_of_eq]s of the strict-equality
   object components. *)
Definition SF_map {x y : B} (f : x ~> y) : F x ⟶ F y := fmap[F] f.

Definition SF_resp {x y : B} {f g : x ~> y} (e : f ≈ g) (a : F x) :
  SF_map f a ≅ SF_map g a := iso_of_eq (`1 (Sresp e) a).

Definition SF_id {x : B} (a : F x) : SF_map (@id B x) a ≅ a :=
  iso_of_eq (`1 (Sid x) a).

Definition SF_comp {x y z : B} (f : y ~> z) (g : x ~> y) (a : F x) :
  SF_map f (SF_map g a) ≅ SF_map (f ∘ g) a :=
  iso_of_eq (eq_sym (`1 (Scomp f g) a)).

(* Collapsing a to-side coherence equation: expose the mediators, absorb any
   functor action into an [iso_of_eq], fuse the composites, and appeal to
   proof irrelevance of [iso_of_eq]. *)
Ltac sf_collapse :=
  cbv beta delta [SF_comp SF_resp SF_id];
  rewrite ?fmap_iso_of_eq;
  rewrite <- ?iso_of_eq_trans;
  apply iso_of_eq_irrel.

Lemma SF_resp_natural {x y : B} {f g : x ~> y} (e : f ≈ g)
  {a b : F x} (k : a ~> b) :
  fmap[SF_map g] k ∘ to (SF_resp e a) ≈ to (SF_resp e b) ∘ fmap[SF_map f] k.
Proof. exact (strict_eq_iso_natural (Sresp e) k). Qed.

Lemma SF_resp_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : F x) :
  to (SF_resp e a) ≈ id.
Proof using B F Fuip. unfold SF_resp; apply iso_of_eq_refl_id. Qed.

Lemma SF_resp_trans {x y : B} {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h)
  (a : F x) :
  to (SF_resp e2 a) ∘ to (SF_resp e1 a)
    ≈ to (SF_resp (Equivalence_Transitive _ _ _ e1 e2) a).
Proof using B F Fuip. sf_collapse. Qed.

Lemma SF_id_natural {x : B} {a b : F x} (k : a ~> b) :
  k ∘ to (SF_id a) ≈ to (SF_id b) ∘ fmap[SF_map (@id B x)] k.
Proof. exact (strict_eq_iso_natural (Sid x) k). Qed.

Lemma SF_comp_natural {x y z : B} (f : y ~> z) (g : x ~> y)
  {a b : F x} (k : a ~> b) :
  fmap[SF_map (f ∘ g)] k ∘ to (SF_comp f g a)
    ≈ to (SF_comp f g b) ∘ fmap[SF_map f] (fmap[SF_map g] k).
Proof.
  unfold SF_comp; rewrite !iso_of_eq_sym.
  exact (strict_eq_iso_natural_from (Scomp f g) k).
Qed.

Lemma SF_comp_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
  (e' : f ∘ g ≈ f' ∘ g) (a : F x) :
  to (SF_comp f' g a) ∘ to (SF_resp e (SF_map g a))
    ≈ to (SF_resp e' a) ∘ to (SF_comp f g a).
Proof using B F Fuip. sf_collapse. Qed.

Lemma SF_comp_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
  (e' : f ∘ g ≈ f ∘ g') (a : F x) :
  to (SF_comp f g' a) ∘ fmap[SF_map f] (to (SF_resp e a))
    ≈ to (SF_resp e' a) ∘ to (SF_comp f g a).
Proof using B F Fuip. sf_collapse. Qed.

Lemma SF_unit_left {x y : B} (f : x ~> y) (a : F x) :
  to (SF_resp (id_left f) a) ∘ to (SF_comp id f a) ≈ to (SF_id (SF_map f a)).
Proof using B F Fuip. sf_collapse. Qed.

Lemma SF_unit_right {x y : B} (f : x ~> y) (a : F x) :
  to (SF_resp (id_right f) a) ∘ to (SF_comp f id a)
    ≈ fmap[SF_map f] (to (SF_id a)).
Proof using B F Fuip. sf_collapse. Qed.

Lemma SF_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : F w) :
  to (SF_comp (f ∘ g) h a) ∘ to (SF_comp f g (SF_map h a))
    ≈ to (SF_resp (comp_assoc f g h) a)
        ∘ to (SF_comp f (g ∘ h) a) ∘ fmap[SF_map f] (to (SF_comp g h a)).
Proof using B F Fuip. sf_collapse. Qed.

(* The indexed category built from [F] and the fibrewise UIP hypothesis. *)
Definition IndexedCat_of_StrictFunctor : IndexedCat B :=
  {| idx_fib          := fun x => F x
   ; idx_map          := @SF_map
   ; idx_resp         := @SF_resp
   ; idx_resp_natural := @SF_resp_natural
   ; idx_resp_id      := @SF_resp_id
   ; idx_resp_trans   := @SF_resp_trans
   ; idx_id           := @SF_id
   ; idx_id_natural   := @SF_id_natural
   ; idx_comp         := @SF_comp
   ; idx_comp_natural := @SF_comp_natural
   ; idx_comp_resp_l  := @SF_comp_resp_l
   ; idx_comp_resp_r  := @SF_comp_resp_r
   ; idx_unit_left    := @SF_unit_left
   ; idx_unit_right   := @SF_unit_right
   ; idx_cocycle      := @SF_cocycle |}.

End StrictFunctorToIndexed.

(** ** Hedberg corollary: decidable fibres discharge the hypothesis *)

(* When every fibre of [F] has decidable object equality, Hedberg's theorem
   supplies the fibrewise UIP hypothesis, so no side condition remains. *)
Definition IndexedCat_of_StrictFunctor_dec {B : Category}
  (F : B ⟶ StrictCat)
  (Fdec : ∀ (b : B) (x y : F b), {x = y} + {x <> y}) : IndexedCat B :=
  IndexedCat_of_StrictFunctor F (fun b => @hedberg (F b) (Fdec b)).

(** ** The constant indexed category *)

Section Constant.

Context (B D : Category).

(* Every fibre is [D], every reindexing is the identity functor, and every
   mediator is the identity isomorphism; all coherence is therefore trivial. *)
#[local] Obligation Tactic :=
  intros; simpl; rewrite ?id_left, ?id_right; reflexivity.

Program Definition Constant_IndexedCat : IndexedCat B :=
  {| idx_fib  := fun _ => D
   ; idx_map  := fun _ _ _ => Id
   ; idx_resp := fun _ _ _ _ _ _ => iso_id
   ; idx_id   := fun _ _ => iso_id
   ; idx_comp := fun _ _ _ _ _ _ => iso_id |}.

End Constant.

(** ** The Grothendieck construction of a constant family is a product *)

(* Conjugating by identity isomorphisms does nothing; the generic stripping
   step for equivalence cells whose isomorphism family is [iso_id]. *)
Lemma conj_id {C : Category} {a b : C} (f : a ~> b) :
  from (@iso_id C b) ∘ f ∘ to (@iso_id C a) ≈ f.
Proof. simpl; now rewrite id_left, id_right. Qed.

Section ConstantIso.

Context {B D : Category}.

#[local] Obligation Tactic := idtac.

(* The forward functor: ∫ (constant D) ⟶ B ∏ D, unpacking dependent pairs into
   plain pairs on both objects and morphisms. *)
Program Definition GC_to :
  Grothendieck (Constant_IndexedCat B D) ⟶ (B ∏ D) := {|
  fobj := fun s => (`1 s, `2 s);
  fmap := fun s t f => (`1 f, `2 f)
|}.
Next Obligation.
  intros x y f g [e He]; simpl in *.
  split; [ exact e |].
  now rewrite id_right in He.
Qed.
Next Obligation. intros x; split; simpl; reflexivity. Qed.
Next Obligation.
  intros x y z f g; simpl.
  split; simpl; [ reflexivity | now rewrite id_right ].
Qed.

(* The backward functor: B ∏ D ⟶ ∫ (constant D), packing plain pairs into
   dependent pairs. *)
Program Definition GC_from :
  (B ∏ D) ⟶ Grothendieck (Constant_IndexedCat B D) := {|
  fobj := fun p => (fst p; snd p);
  fmap := fun p q f => (fst f; snd f)
|}.
Next Obligation.
  intros x y f g [Hf Hg]; simpl in *.
  exists Hf.
  now rewrite id_right.
Qed.
Next Obligation. intros x; reflexivity. Qed.
Next Obligation.
  intros x y z f g.
  unshelve refine (_; _); [ reflexivity |].
  simpl; now rewrite id_right.
Qed.

(* Both composites are the identity up to the pair/dependent-pair repackaging;
   their natural-isomorphism cells carry identity components. *)
Definition GC_tofrom_iso (p : B ∏ D) : (GC_to ◯ GC_from) p ≅ Id p.
Proof. destruct p as [a b]; exact iso_id. Defined.

Definition GC_fromto_iso (s : Grothendieck (Constant_IndexedCat B D)) :
  (GC_from ◯ GC_to) s ≅ Id s.
Proof. destruct s as [a b]; exact iso_id. Defined.

Definition GC_iso_to_from : (GC_to ◯ GC_from) ≈ Id.
Proof.
  exists GC_tofrom_iso.
  intros p q f.
  destruct p as [px pd], q as [qx qd], f as [ff fd].
  cbn [GC_tofrom_iso].
  rewrite conj_id.
  reflexivity.
Defined.

Definition GC_iso_from_to : (GC_from ◯ GC_to) ≈ Id.
Proof.
  exists GC_fromto_iso.
  intros s t f.
  destruct s as [sx sd], t as [tx td], f as [fg fd].
  cbn [GC_fromto_iso].
  rewrite conj_id.
  reflexivity.
Defined.

(* The sanity isomorphism in Cat: the Grothendieck construction of the constant
   family over [D] is the product category [B ∏ D]. *)
Definition Grothendieck_Constant_iso :
  Grothendieck (Constant_IndexedCat B D) ≅[Cat] (B ∏ D) :=
  @Build_Isomorphism Cat _ _ GC_to GC_from GC_iso_to_from GC_iso_from_to.

End ConstantIso.
