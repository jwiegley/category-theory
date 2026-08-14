(** * The tensor product of abelian groups *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.8, printed pp. 28–29 (PDF pp. 38–39) — maclane:I.8:def5
   Book:      Mac Lane, ibid., §VII.1, printed pp. 163–164 (PDF pp.
              171–172) — maclane:VII.1:remark1 (the monoidal reading,
              delivered in Instance/Ab/Monoidal.v over this file)
   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product

   Because composition in an Ab-category is bilinear, it factors through
   the tensor product of abelian groups: G ⊗ H is the recipient of the
   universal bilinear map out of G × H, turning bilinear maps into plain
   group homomorphisms.  This file builds it for Instance/Ab.v's
   [AbObject]s, setoid-first and axiom-free:

     - [tsum]/[ts_eq]: formal sums over the two carriers, quotiented by
       exactly the commutative-group laws and the two bilinearity
       equations — an inductive setoid quotient in the style of
       Instance/Sets/Coend.v
     - [AbTensor G H : AbObject]: the tensor product itself
     - [Bilinear]: the bilinear-map interface, with [tensor_gen] the
       universal one
     - [tensor_ump]: the factorization of a bilinear map through a
       homomorphism out of the tensor, computing definitionally on
       formal sums
     - [tensor_hom_ext]: two homomorphisms out of the tensor agreeing on
       generators agree — the uniqueness half of the UMP, and the
       workhorse every later coherence proof reduces to
     - [AbTensor_Functor : Ab ∏ Ab ⟶ Ab]: bifunctoriality, its laws all
       instances of [tensor_hom_ext]

   Design:

   1. THE QUOTIENT IS AN INDUCTIVE RELATION, REFLEXIVITY DERIVED.  As in
      Instance/Sets/Coend.v (and Construction/Quotient.v's [CongClosure]),
      the carrier is a plain inductive of formal sums and the setoid
      equality [ts_eq] is an inductive relation closing under the group
      laws, the two bilinearity rules, congruence for the two term
      formers, saturation under the point setoids ([te_gen]), and
      symmetry/transitivity.  Reflexivity is a lemma ([ts_refl], by
      induction on the term), keeping the relation's induction principle
      one case shorter everywhere it is consumed.

   2. NO FREE-ALGEBRA DETOUR.  The tree has no free abelian group to
      quotient (verified across Construction/ and Instance/); building
      formal sums directly keeps the development self-contained and the
      mediator's respectfulness a single induction over [ts_eq], each
      rule discharged by the corresponding law of the target — which is
      precisely Mac Lane's "bilinear maps out of G × H are homomorphisms
      out of G ⊗ H".  This trades away the issue sketch's "free-abelian-
      group-on-a-setoid machinery, kept reusable": the carrier here is
      bespoke to the pair (G, H).  What IS reusable is the interface —
      [Bilinear], [tensor_ump] and [tensor_hom_ext] are stated over
      arbitrary [AbObject]s, and they are all any consumer downstream
      (Instance/Ab/Monoidal.v, Construction/Enriched/Ab.v) touches.

   3. THE MEDIATOR COMPUTES.  [tensor_med] is a fixpoint on formal sums,
      so [cmon_map_zero] and [cmon_map_plus] of the factorizing
      homomorphism hold by reflexivity, and every later equation between
      homomorphisms out of (iterated) tensors reduces along it to a
      statement about generators.  [tensor_hom_ext] is the induction that
      finishes such statements; preservation of negation, needed in its
      [ts_neg] case, is Instance/Ab.v's [ab_map_neg] theorem.

   4. UNIVERSES.  Nothing is annotated: like [CMonObject] and [AbObject]
      themselves (Instance/Grp.v's stated policy), the construction is
      universe-polymorphic, and [tsum] lives at the level of the two
      carriers. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Formal sums and the bilinearity quotient *)

Section Tensor.

Context (G H : AbObject).

(* Formal sums over the two carriers: generators, zero, sum, negation. *)
Inductive tsum : Type :=
  | ts_gen  : carrier G → carrier H → tsum
  | ts_zero : tsum
  | ts_plus : tsum → tsum → tsum
  | ts_neg  : tsum → tsum.

(* The quotienting relation: commutative-group laws, bilinearity in each
   variable, congruence, saturation under the point setoids, symmetry and
   transitivity.  Reflexivity is derived (design note 1). *)
Inductive ts_eq : tsum → tsum → Type :=
  | te_gen {g g' : carrier G} {h h' : carrier H} :
      g ≈ g' → h ≈ h' → ts_eq (ts_gen g h) (ts_gen g' h')
  | te_plus {s s' t t'} :
      ts_eq s s' → ts_eq t t' → ts_eq (ts_plus s t) (ts_plus s' t')
  | te_neg {s s'} : ts_eq s s' → ts_eq (ts_neg s) (ts_neg s')
  | te_assoc (s t u : tsum) :
      ts_eq (ts_plus (ts_plus s t) u) (ts_plus s (ts_plus t u))
  | te_comm (s t : tsum) : ts_eq (ts_plus s t) (ts_plus t s)
  | te_zero_l (s : tsum) : ts_eq (ts_plus ts_zero s) s
  | te_neg_l (s : tsum) : ts_eq (ts_plus (ts_neg s) s) ts_zero
  | te_bilin_l (g g' : carrier G) (h : carrier H) :
      ts_eq (ts_gen (cmon_plus G g g') h)
            (ts_plus (ts_gen g h) (ts_gen g' h))
  | te_bilin_r (g : carrier G) (h h' : carrier H) :
      ts_eq (ts_gen g (cmon_plus H h h'))
            (ts_plus (ts_gen g h) (ts_gen g h'))
  | te_sym {s t} : ts_eq s t → ts_eq t s
  | te_trans {s t u} : ts_eq s t → ts_eq t u → ts_eq s u.

Lemma ts_refl (s : tsum) : ts_eq s s.
Proof.
  induction s.
  - exact (te_gen (reflexivity _) (reflexivity _)).
  - exact (te_trans (te_sym (te_zero_l ts_zero)) (te_zero_l ts_zero)).
  - exact (te_plus IHs1 IHs2).
  - exact (te_neg IHs).
Qed.

Lemma ts_eq_Equivalence : Equivalence ts_eq.
Proof.
  constructor.
  - exact ts_refl.
  - exact (fun s t => te_sym).
  - exact (fun s t u => te_trans).
Qed.

Definition ts_Setoid : Setoid tsum := {|
  equiv        := ts_eq;
  setoid_equiv := ts_eq_Equivalence
|}.

(* The tensor product, as an abelian group: the laws are constructors of
   the relation. *)
Definition AbTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := tsum; is_setoid := ts_Setoid |};
    cmon_zero := ts_zero;
    cmon_plus := ts_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => te_plus Hs Ht;
    cmon_plus_assoc := te_assoc;
    cmon_plus_comm := te_comm;
    cmon_plus_zero_l := te_zero_l
  |};
  ab_neg := ts_neg;
  ab_neg_respects := fun _ _ Hs => te_neg Hs;
  ab_neg_left := te_neg_l
|}.

(** ** Bilinear maps and the universal property *)

(* A bilinear map into an abelian group K: respectful in each variable and
   additive in each variable.  (Preservation of zero and negation in each
   variable follows, as always for monoid maps between groups, and is not
   demanded.) *)
Record Bilinear (K : AbObject) := {
  bilin_map : carrier G → carrier H → carrier K;
  bilin_respects :
    Proper (equiv ==> equiv ==> equiv) bilin_map;
  bilin_add_l (g g' : carrier G) (h : carrier H) :
    bilin_map (cmon_plus G g g') h
      ≈ cmon_plus K (bilin_map g h) (bilin_map g' h);
  bilin_add_r (g : carrier G) (h h' : carrier H) :
    bilin_map g (cmon_plus H h h')
      ≈ cmon_plus K (bilin_map g h) (bilin_map g h')
}.

Arguments bilin_map {K} _ _ _.
Arguments bilin_respects {K} _.
Arguments bilin_add_l {K} _ _ _ _.
Arguments bilin_add_r {K} _ _ _ _.

(* The universal bilinear map: the generator former itself.  (Built with
   the explicit constructor: the record notation would have to inject
   [tsum] into [carrier] of an evar, which unification declines.) *)
Definition tensor_gen : Bilinear AbTensor :=
  @Build_Bilinear AbTensor ts_gen
    (fun _ _ Hg _ _ Hh => te_gen Hg Hh)
    te_bilin_l
    te_bilin_r.

(* The mediator: fold a formal sum through the target's operations.  It
   computes on constructors (design note 3). *)
Fixpoint tensor_med_fun {K : AbObject} (β : Bilinear K) (s : tsum) :
  carrier K :=
  match s with
  | ts_gen g h  => bilin_map β g h
  | ts_zero     => cmon_zero K
  | ts_plus s t => cmon_plus K (tensor_med_fun β s) (tensor_med_fun β t)
  | ts_neg s    => ab_neg K (tensor_med_fun β s)
  end.

(* Respectfulness is one induction over the relation, each rule met by
   the corresponding law of K (design note 2). *)
Lemma tensor_med_respects {K : AbObject} (β : Bilinear K) (s t : tsum) :
  ts_eq s t → tensor_med_fun β s ≈ tensor_med_fun β t.
Proof.
  intro He; induction He; simpl.
  - exact (bilin_respects β _ _ e _ _ e0).
  - exact (cmon_plus_respects K _ _ IHHe1 _ _ IHHe2).
  - exact (ab_neg_respects K _ _ IHHe).
  - exact (cmon_plus_assoc K _ _ _).
  - exact (cmon_plus_comm K _ _).
  - exact (cmon_plus_zero_l K _).
  - exact (ab_neg_left K _).
  - exact (bilin_add_l β _ _ _).
  - exact (bilin_add_r β _ _ _).
  - exact (symmetry IHHe).
  - exact (transitivity IHHe1 IHHe2).
Qed.

(* The factorization: a bilinear map becomes a homomorphism out of the
   tensor.  Zero- and sum-preservation hold by reflexivity. *)
Program Definition tensor_ump {K : AbObject} (β : Bilinear K) :
  AbHom AbTensor K := {|
  cmon_map := {| morphism := tensor_med_fun β |}
|}.
Next Obligation.
  intros K β s t He; exact (tensor_med_respects β s t He).
Qed.
Next Obligation.
  intros K β; simpl; reflexivity.
Qed.
Next Obligation.
  intros K β s t; simpl; reflexivity.
Qed.

Lemma tensor_ump_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (ts_gen g h) ≈ bilin_map β g h.
Proof.
  simpl; reflexivity.
Qed.

(* The same triangle stated through the universal bilinear map itself:
   factoring [β] and then evaluating on [tensor_gen] recovers [β]. *)
Lemma tensor_ump_tensor_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (bilin_map tensor_gen g h) ≈ bilin_map β g h.
Proof.
  exact (tensor_ump_gen β g h).
Qed.

(* Uniqueness, in its most consumable form: homomorphisms out of the
   tensor agreeing on generators agree everywhere.  The [ts_neg] case is
   Instance/Ab.v's [ab_map_neg]. *)
Lemma tensor_hom_ext {K : AbObject} (f g : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ cmon_map g (ts_gen a b)) →
  ∀ s : tsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects K _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects K _ _ IHs).
Qed.

(* The classical statement of the UMP, assembled from the two halves:
   factorization exists and is unique. *)
Lemma tensor_ump_unique {K : AbObject} (β : Bilinear K)
  (f : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ bilin_map β a b) →
  f ≈ tensor_ump β.
Proof.
  intros Hgen s.
  refine (tensor_hom_ext f (tensor_ump β) _ s).
  intros a b.
  exact (transitivity (Hgen a b) (symmetry (tensor_ump_gen β a b))).
Qed.

End Tensor.

Arguments ts_gen {G H} g h.
Arguments ts_zero {G H}.
Arguments ts_plus {G H} s t.
Arguments ts_neg {G H} s.
Arguments ts_eq {G H} s t.
Arguments ts_refl {G H} s.
Arguments te_gen {G H g g' h h'} _ _.
Arguments te_plus {G H s s' t t'} _ _.
Arguments te_neg {G H s s'} _.
Arguments te_assoc {G H} s t u.
Arguments te_comm {G H} s t.
Arguments te_zero_l {G H} s.
Arguments te_neg_l {G H} s.
Arguments te_bilin_l {G H} g g' h.
Arguments te_bilin_r {G H} g h h'.
Arguments te_sym {G H s t} _.
Arguments te_trans {G H s t u} _ _.

#[export] Existing Instance ts_eq_Equivalence.
Arguments AbTensor G H : clear implicits.
Arguments Bilinear G H K : clear implicits.
Arguments bilin_map {G H K} _ _ _.
Arguments bilin_respects {G H K} _.
Arguments bilin_add_l {G H K} _ _ _ _.
Arguments bilin_add_r {G H K} _ _ _ _.
Arguments tensor_gen {G H}.
Arguments tensor_med_fun {G H K} β s.
Arguments tensor_ump {G H K} β.
Arguments tensor_ump_gen {G H K} β g h.
Arguments tensor_hom_ext {G H K} f g _ s.
Arguments tensor_ump_unique {G H K} β f _.

(** ** Bifunctoriality *)

(* The arrow action: map the generators and extend.  Bilinearity of the
   composite generator map is the point saturation plus the bilinearity
   rules of the target tensor. *)
Program Definition tensor_map {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') :
  AbHom (AbTensor G H) (AbTensor G' H') :=
  tensor_ump (@Build_Bilinear G H (AbTensor G' H')
    (fun g h => ts_gen (cmon_map f g) (cmon_map k h)) _ _ _).
Next Obligation.
  intros G G' H H' f k g g' Hg h h' Hh.
  exact (te_gen (proper_morphism (cmon_map f) _ _ Hg)
                (proper_morphism (cmon_map k) _ _ Hh)).
Qed.
Next Obligation.
  intros G G' H H' f k g g' h.
  refine (te_trans (te_gen (cmon_map_plus f g g') (reflexivity _)) _).
  exact (te_bilin_l _ _ _).
Qed.
Next Obligation.
  intros G G' H H' f k g h h'.
  refine (te_trans (te_gen (reflexivity _) (cmon_map_plus k h h')) _).
  exact (te_bilin_r _ _ _).
Qed.

Lemma tensor_map_gen {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') (g : carrier G) (h : carrier H) :
  cmon_map (tensor_map f k) (ts_gen g h)
    ≈ ts_gen (cmon_map f g) (cmon_map k h).
Proof.
  simpl; reflexivity.
Qed.

(* The bifunctor Ab ∏ Ab ⟶ Ab.  Every law is [tensor_hom_ext] plus a
   computation on generators. *)
Program Definition AbTensor_Functor : Ab ∏ Ab ⟶ Ab := {|
  fobj := fun p => AbTensor (fst p) (snd p);
  fmap := fun p q f => tensor_map (fst f) (snd f)
|}.
Next Obligation.
  intros [G H] [G' H'] [f k] [f' k'] [Hf Hk]; simpl in *.
  apply (tensor_hom_ext (tensor_map f k) (tensor_map f' k')).
  intros a b.
  exact (te_gen (Hf a) (Hk b)).
Qed.
Next Obligation.
  intros [G H]; simpl.
  apply (tensor_hom_ext (tensor_map cmon_hom_id cmon_hom_id) cmon_hom_id).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  intros [G H] [G' H'] [G'' H''] [f k] [f' k']; simpl.
  apply (tensor_hom_ext
           (tensor_map (cmon_hom_compose f f') (cmon_hom_compose k k'))
           (cmon_hom_compose (tensor_map f k) (tensor_map f' k'))).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
