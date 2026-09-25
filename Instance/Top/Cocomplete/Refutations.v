Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Complete.Refutations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Cocompleteness of spaces refuted above the points *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
     that a small complete category is a preorder, consumed dually
     through Structure/Complete/Freyd.v; and §V.9, book p. 134 (PDF
     p. 143), whose "general colimits in Top" (maclane:V.9:remark2) this
     file bounds, as Instance/Top/StoneCech/Refutations.v bounds the
     completeness of [Top] and [CompHaus]
   nLab: https://ncatlab.org/nlab/show/complete+small+category
   nLab: https://ncatlab.org/nlab/show/Cantor%27s+theorem

   BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header)
   is that completeness in the book's sense is a property of LARGE
   categories: a category with products indexed by its own arrows and two
   distinct parallel arrows cannot exist.  Its dual bounds cocompleteness
   the same way.  For a category of spaces there is a second, more direct
   bound, Cantor's theorem at the points of ONE coproduct.  Let [K] be
   the type of pairs of a space [X] and a predicate on the points of [X];
   it quantifies over all spaces, so it sits strictly above the points'
   universe.  If the coproduct [Q] of [K]-many one-point spaces exists,
   every predicate [U] on the points of [Q] has a code in [Q], the point
   of the summand at the pair [(Q, U)].  A continuous map out of [Q] into
   a space of truth values, the copairing of "is this summand the one at
   [k0]?", tells the codes apart, and with decidable equality of spaces
   the dependent pair injectivity [inj_pair2_eq_dec] turns "the same
   summand" into "the same predicate".  So predicates on the points of
   [Q] inject into the points of [Q], which Cantor's diagonal forbids.
   Over [PTopCat] and over the Type-valued [Top] alike the two arguments
   reach the same shapes, because an arrow index moves between the object
   universes of [PTopCat] and between the hom universes of [Top]
   (Instance/Top/Complete/Refutations.v's [PTop_ArrowIndex_transport] and
   [Top_ArrowIndex_transport]).  Nothing here is an axiom: decidable
   equality of spaces
   (Construction/Quotient.v's [ObjDecEq]), informative excluded middle
   ([IEM], Instance/Sets/Classifier/OneLevel.v) and arrow indices
   ([ArrowIndex], Structure/Complete/Freyd.v) are hypotheses; [IEM] holds
   classically and yields the other two.

   NAMES.  The scheme of Instance/Top/Complete/Refutations.v's header,
   shared with this file, the colimit dual: [_Freyd] and [_Cantor_] name
   the argument, and the hypothesis suffix names the reach.  [_Freyd]:
   Freyd's argument from an arrow index at the shape universe [s],
   nothing tying [s] to the points' [o]; [_ObjDecEq] and [_IEM]:
   decidable equality of spaces and informative excluded middle, each at
   every [s] with [o < s], [o := Set] included; [_Cantor_ObjDecEq] and
   [_Cantor_IEM]: Cantor's argument under the same hypotheses and with
   the same reach, but that the [ObjDecEq] form needs [Set < o].  The
   limit side's [_below] does not occur here: no form of this file stops
   at the hom universe of [Top], and [Top_not_cocomplete_ObjDecEq] and
   [Top_not_cocomplete_IEM] reach below it under the plain suffixes.

   WHAT IS REFUTED.
     - Freyd's form over [PTopCat], dualized: [PTop_not_cocomplete_Freyd],
       an [ArrowIndex] of [PTopCat] at the shape universe refutes
       cocompleteness there.  The separated pair is Instance/Top/
       Subspace.v's [ppoint_true] and [ppoint_false], told apart by
       evaluation at the point.  [PTop_not_cocomplete_ObjDecEq] and
       [PTop_not_cocomplete_IEM]: under [ObjDecEq PTopCat], or under
       [IEM], no [Cocomplete@{r s o so} PTopCat@{o so}] at any shape
       universe [s] strictly above the points, [o < s], [o := Set]
       included: Structure/Complete/Freyd.v's [canonical_ArrowIndex] of
       [PTopCat@{o s}], transported, as the limit side does.
     - [Sets_not_cocomplete_IEM]: under [IEM], [Sets@{o so}] is not
       cocomplete at any shape universe above its carriers.  Were it,
       Instance/Top/Cocomplete.v's recipe [PTop_Colimit_lift] would make
       [PTopCat] cocomplete there, against [PTop_not_cocomplete_IEM].
     - Over the Type-valued [Top@{h o}]: [Top_not_cocomplete_Freyd] is
       the exact dual of Instance/Top/StoneCech/Refutations.v's
       [Top_not_complete] (an [ArrowIndex@{s h h}] refutes
       [Cocomplete@{r s h h}]).  The canonical index of [Top@{h o}] sits
       at [h]; the one of [Top@{s o}], moved to [Top@{h o}] by
       Instance/Top/Complete/Refutations.v's [Top_ArrowIndex_transport],
       indexes at [s].  Through it [Top_not_cocomplete_ObjDecEq] and
       [Top_not_cocomplete_IEM], under [ObjDecEq Top] or under [IEM],
       refute [Cocomplete@{r s h h} Top@{h o}] at every [s] with [o < s],
       the shapes strictly between the points and the homs included and
       [o := Set] as well.
     - Cantor's argument, a second and independent proof.  The engine:
       [cocomp_cantor_diagonal], no map from the predicates on a type into
       it is injective up to a reflexive relation; [pcc_contradiction]
       (over [PTopCat]) and [tcc_contradiction] (over [Top]) run the
       argument above against an abstract separator: a space [Om] and a
       family [c k0 k] of its points with [c k0 k ≈ c k0 k0] only at
       [k = k0]; [pcc_index] and [tcc_index] are [K].  Over [PTopCat],
       [PTop_not_cocomplete_Cantor_ObjDecEq] (the separator the discrete
       space on the truth values under [<->], [pcc_Prop], with
       [c k0 k := (k = k0)], whence [Set < o]) and
       [PTop_not_cocomplete_Cantor_IEM] (the separator Instance/Top/
       Prop.v's two-point [PBool], [c] deciding [k = k0] by [IEM], no
       [Set < o]); both reach no shape the Freyd forms above do not.  Over
       [Top], [Top_not_cocomplete_Cantor_ObjDecEq] and
       [Top_not_cocomplete_Cantor_IEM], the separators Instance/Top.v's
       [Discrete_Top] of [pcc_Prop] and [Bool_Discrete], at every
       [o < s], below [h] as well; they too reach no shape the transported
       Freyd forms do not, and the [ObjDecEq] one reaches fewer, needing
       [Set < o].

   THE BOUNDARY.  Cocompleteness of [PTopCat@{o so}] is provable at every
   shape universe [s <= o] (Instance/Top/Cocomplete.v's [PTop_Cocomplete],
   with no hypothesis) and refuted under [IEM], or under [ObjDecEq], at
   every [s] with [o < s] ([PTop_not_cocomplete_IEM],
   [PTop_not_cocomplete_ObjDecEq]); no shape universe lies between, and
   without one of the hypotheses or an index nothing above the points is
   refuted.  Measured in the scratch file of Instance/Top/Complete.v's
   boundary paragraph (the six files of #458 after the union of their
   import lists): [PTop_not_cocomplete_IEM] and
   [PTop_not_cocomplete_ObjDecEq] are accepted at an [s] with [o < s] and
   at [o := Set]; [PTop_not_cocomplete_IEM] and [Sets_not_cocomplete_IEM]
   read at [Cocomplete@{o o o so}] are refused ("Cannot enforce <1> = o
   because <1> < o", the generated universe written <1>), so the
   refutations do not reach the proved statement; at [o := Set]
   [PTop_not_cocomplete_Cantor_ObjDecEq] is refused ("Cannot enforce
   Set = <1> because Set < <1>"), its separator carrying [Set < o], and
   [PTop_not_cocomplete_Cantor_IEM] accepted.  Over the Type-valued [Top]
   [Top_not_cocomplete_IEM] and [Top_not_cocomplete_ObjDecEq] refute every
   [o < s], and at [s <= o] the question is open, walled as
   Instance/Top/Cocomplete/TypeValued.v records.  Measured in
   Test/ProbeTopComplete458.v: [Top_not_cocomplete_IEM] and
   [Top_not_cocomplete_Cantor_IEM] are accepted at an [s] with
   [o < s < h], and [Top_not_cocomplete_ObjDecEq] at [o := Set], where
   [Top_not_cocomplete_Cantor_ObjDecEq] is refused ("Cannot enforce
   Set = <2> because Set < <2>", the generated universes numbered in
   order of appearance in the message); [Top_not_cocomplete_IEM] read at
   [s := o], by its universe instance, is refused ("Cannot enforce o < o
   because o = o").

   STRENGTHS.  Every theorem concludes [False]; [cocomp_cantor_diagonal]
   concludes [False] from its hypotheses.  [ObjDecEq] is used only at
   [canonical_ArrowIndex] and [inj_pair2_eq_dec], and [IEM] only to decide
   equality of spaces and of indices.  No proof ends [Defined].

   UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
   left out; [o] the points, [so] the objects of [PTopCat], [h] the homs
   of [Top], [s] and [r] a shape and its colimit record, [e] the level of
   [IEM], which is free.
     PTop_not_cocomplete_Freyd@{r s o so} :
       ArrowIndex@{s so o} PTopCat@{o so} → ¬ Cocomplete@{r s o so}
       (* o < so; nothing ties s to o *)
     PTop_not_cocomplete_ObjDecEq@{r s o so} :
       ObjDecEq PTopCat@{o so} → ¬ Cocomplete@{r s o so}  (* o < s *)
     PTop_not_cocomplete_IEM@{e r s o so} :
       IEM@{e} → ¬ Cocomplete@{r s o so}         (* o < so, o < s *)
     Sets_not_cocomplete_IEM@{e r s o so} :
       IEM@{e} → ¬ Cocomplete@{r s o so} (at Sets@{o so})
       (* o < so, o < s *)
     Top_not_cocomplete_Freyd@{r s h o} :
       ArrowIndex@{s h h} Top@{h o} → ¬ Cocomplete@{r s h h}  (* o < h *)
     Top_not_cocomplete_ObjDecEq@{r s h o} :
       ObjDecEq Top@{h o} → ¬ Cocomplete@{r s h h}  (* o < h, o < s *)
     Top_not_cocomplete_IEM@{e r s h o} :
       IEM@{e} → ¬ Cocomplete@{r s h h}         (* o < h, o < s *)
     PTop_not_cocomplete_Cantor_ObjDecEq@{r s o so},
     PTop_not_cocomplete_Cantor_IEM@{e r s o so}: as the [PTopCat] forms
       above, the first with [Set < o].
     Top_not_cocomplete_Cantor_ObjDecEq@{r s h o},
     Top_not_cocomplete_Cantor_IEM@{e r s h o}: as the [Top] forms above,
       the first with [Set < o].
   [pcc_index@{o s}] and [tcc_index@{o s}] are declared outside the
   sections, so they carry only [o < s] and [Set < s]; the constants
   declared inside the sections carry the sections' universes and the
   bounds [s <= r] and [o <= r] (or [h <= r]) of the [Cocomplete]
   hypothesis in their [Context], whether or not their statements
   mention it.  Over the [About] output of all 32 of this file's
   constants (its [Print Module] listing, the one [Program] obligation
   included; it declares no record or inductive), [Set] occurs in no
   equation and pins no universe, and it occurs in no block of the three
   Freyd forms over [Top].  It occurs only as bounds, each implied by a
   declared one or recording a sort: [Set < s] in 25 blocks (the sort of
   [K], whose fibre [X → Prop] sits at [Set+1], and the [PTopCat@{o s}]
   the transported [PTopCat] forms build the index at; implied by
   [o < s]); [Set < so] in 14 ([PTopCat]'s); [Set < eq_ind_r.u0] in 7
   ([cocomp_cantor_diagonal]'s [subst] at the type of predicates
   [A → Prop], whose sort is at least [Set+1]);
   [Set < Logic_lemmas.equality.u0] and
   [Set < Eqdep_dec.inj_pair2_eq_dec.u1] in 8 each ([inj_pair2_eq_dec]
   at the same family of predicates, first in [pcc_enc_inj] and
   [tcc_enc_inj]); and [Set < o] in 4: [pcc_Prop], whose carrier [Prop]
   sits at [Set+1], its obligation, and the two [_Cantor_ObjDecEq] forms
   that use it, which are therefore stated for [o] above [Set]; no other
   form is.

   ROUTE AND COST.  Closure 176 [Category.*] modules excluding this file
   ([Print Libraries] on a file requiring it).  Instance/Top/Complete/
   Refutations.v (for [PTop_ArrowIndex_transport] and
   [Top_ArrowIndex_transport]) and Instance/Top/
   StoneCech/Refutations.v (for [ObjDecEq_of_IEM]) are required rather
   than restating either; dropped together from the import list they cost
   34 at the margin (142 without them); dropped singly, the first costs
   3 and the second nothing, the first loading the second.

   NOT DELIVERED.  No refutation, and no proof, of cocompleteness of the
   Type-valued [Top] at shapes at or below its points; nothing about
   completeness, which is the limit side's (Instance/Top/StoneCech/
   Refutations.v and Instance/Top/Complete/Refutations.v for [Top], the
   second for [PTopCat]); and no statement
   that an arrow index of [PTopCat] at the points' universe is refuted by
   pairing [PTop_not_cocomplete_Freyd] with [PTop_Cocomplete] (that
   reading is Instance/Top/Complete/Refutations.v's
   [PTop_no_ArrowIndex_at_points], from completeness).  The four
   [_Cantor_] forms are subsumed by the Freyd forms and kept as an
   independent second argument. *)

#[local] Obligation Tactic := idtac.

(** ** [PTopCat]: Freyd's form, dualized, and transported above the points *)

(* Freyd's form, dualized: an arrow index at the shape universe refutes
   cocompleteness there. *)
Theorem PTop_not_cocomplete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=PBool) (b:=PPoint) ppoint_true ppoint_false _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => PPoint))
           (fun h => pmap h ttt) (fun u v H => H ttt) eq_refl eq_refl).
Qed.

(* Every shape universe strictly above the points, under decidable
   equality of spaces: the canonical index is built at [PTopCat@{o s}]
   and transported by Instance/Top/Complete/Refutations.v's
   [PTop_ArrowIndex_transport], as the limit side does. *)
Theorem PTop_not_cocomplete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DE : ObjDecEq PTopCat@{o s})))
           cocomp).
Qed.

Theorem PTop_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so})
           cocomp).
Qed.

(* Through the recipe, the same boundary for the points: were [Sets]
   cocomplete at a shape universe above its carriers, Instance/Top/
   Cocomplete.v's [PTop_Colimit_lift] would make [PTopCat] cocomplete
   there. *)
Theorem Sets_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} Sets@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_IEM E
           (fun D F => PTop_Colimit_lift F (cocomp D (PForget ◯ F)))).
Qed.

(** ** The Type-valued [Top]: Freyd's form, and transported below the homs *)

(* Freyd's form, the exact dual of Instance/Top/StoneCech/Refutations.v's
   [Top_not_complete]. *)
Theorem Top_not_cocomplete_Freyd@{r s h o +}
  (AI : ArrowIndex@{s h h} Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=Bool_Discrete) (b:=Point_Top)
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => Point_Top))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* Every shape universe strictly above the points, the shapes below the
   homs included, under decidable equality of spaces: the canonical index
   is built at [Top@{s o}] and transported by Instance/Top/Complete/
   Refutations.v's [Top_ArrowIndex_transport], as the limit side does. *)
Theorem Top_not_cocomplete_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_Freyd
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           cocomp).
Qed.

Theorem Top_not_cocomplete_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) cocomp).
Qed.

(** ** A second argument: Cantor's diagonal at the points of one coproduct *)

(* No map from the predicates on a type into it is injective up to a
   reflexive relation: the predicate "encodes a predicate it does not
   hold of" holds of its own code exactly when it does not. *)
Lemma cocomp_cantor_diagonal@{u} {A : Type@{u}} (R : A → A → Type@{u})
  (R_refl : ∀ a, R a a) (enc : (A → Prop) → A)
  (enc_inj : ∀ U V, R (enc U) (enc V) → U = V) : False.
Proof.
  pose (Dg := fun p : A => ex (fun U => inhabited (R (enc U) p) /\ ~ U p)).
  assert (N : ~ Dg (enc Dg)).
  { intros [U [[HU] nU]]. pose proof (enc_inj U Dg HU) as E.
    subst U. apply nU. exists Dg. split; [constructor; exact HU|exact nU]. }
  apply N. exists Dg. split; [constructor; exact (R_refl _)|exact N].
Qed.

(** ** [PTopCat]: Cantor at the points of one coproduct *)

(* The index of the coproduct: a space with a predicate on its points.  It
   quantifies over the spaces, so it sits strictly above the points. *)
Definition pcc_index@{o s | o < s +} : Type@{s} :=
  { X : PTop@{o} & pt_carrier X → Prop }.

Section PCantor.

Universes o so s r.
Constraint o < so.
Constraint o < s.

Context (DE : ObjDecEq PTopCat@{o so}).
Context (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}).

#[local] Notation K := (pcc_index@{o s}).

(* A space [Om] and a family of its points [c k0 k] that recognizes [k0]:
   [c k0 k] is equivalent to [c k0 k0] only at [k = k0]. *)
Context (Om : PTop@{o}) (c : K → K → pt_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

(* The coproduct of [pcc_index]-many points, which cocompleteness at [s]
   supplies. *)
Definition pcc_sum : PTop@{o} :=
  complete_iprod_obj CC (fun _ : K => PPoint@{o}).

Definition pcc_inj (k : K) : PPoint@{o} ~{PTopCat@{o so}}~> pcc_sum :=
  complete_iprod_proj CC (fun _ : K => PPoint@{o}) k.

Definition pcc_leg (k0 k : K) : PPoint@{o} ~{PTopCat@{o so}}~> Om :=
  pdisc_mor unit_setoid_object Om (pconst unit_setoid_object Om (c k0 k)).

(* The copairing of the legs at [k0]. *)
Definition pcc_sep (k0 : K) : pcc_sum ~{PTopCat@{o so}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
                (c:=Om) (pcc_leg k0)).

Lemma pcc_sep_at (k0 k : K) :
  pmap (pcc_sep k0) (pmap (pcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
              (c:=Om) (pcc_leg k0)) k ttt).
Qed.

(* A predicate on the points of the coproduct encodes to the point of its
   own summand. *)
Definition pcc_enc (U : pt_carrier pcc_sum → Prop) : pt_carrier pcc_sum :=
  pmap (pcc_inj (existT _ pcc_sum U)) ttt.

Lemma pcc_enc_inj (U V : pt_carrier pcc_sum → Prop) :
  pcc_enc U ≈ pcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (pmap (pcc_sep (existT _ pcc_sum U))) _ _ H)
    as H1.
  assert (E : existT (fun X : PTop@{o} => pt_carrier X → Prop) pcc_sum V
              = existT _ pcc_sum U).
  { apply c_spec.
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc V));
      [symmetry; exact (pcc_sep_at _ _)|].
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc U));
      [symmetry; exact H1|exact (pcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma pcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (pt_carrier pcc_sum))
           (fun p => reflexivity p) pcc_enc pcc_enc_inj).
Qed.

End PCantor.

(* The truth values, under [<->], as a setoid at the points' universe. *)
Program Definition pcc_Prop@{o | Set < o} : SetoidObject@{o o} := {|
  carrier := Prop;
  is_setoid := {| equiv := fun P Q => P <-> Q |}
|}.
Next Obligation.
  constructor.
  - intro P; exact (iff_refl P).
  - intros P Q H; exact (iff_sym H).
  - intros P Q R H1 H2; exact (iff_trans H1 H2).
Qed.

(* Cocompleteness of [PTopCat] is refuted at every shape universe strictly
   above the points, under decidable equality of spaces: the separator is
   the discrete space of truth values. *)
Theorem PTop_not_cocomplete_Cantor_ObjDecEq@{r s o so +| o < so, o < s,
                                               Set < o +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction DE cocomp (PDiscrete pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

(* The same under informative excluded middle, with [PBool] as the
   separator, so that no [Set < o] is needed. *)
Theorem PTop_not_cocomplete_Cantor_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp PBool@{o}
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.

(** ** The Type-valued [Top]: Cantor's argument *)

Definition tcc_index@{o s | o < s +} : Type@{s} :=
  { X : TopSpace@{o} & top_carrier X → Prop }.

Section TCantor.

Universes o h s r.
Constraint o < h.
Constraint o < s.

Context (DE : ObjDecEq Top@{h o}).
Context (cocomp : @Cocomplete@{r s h h} Top@{h o}).

#[local] Notation K := (tcc_index@{o s}).

Context (Om : TopSpace@{o}) (c : K → K → top_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

Definition tcc_sum : TopSpace@{o} :=
  complete_iprod_obj CC (fun _ : K => Point_Top).

Definition tcc_inj (k : K) : Point_Top ~{Top@{h o}}~> tcc_sum :=
  complete_iprod_proj CC (fun _ : K => Point_Top) k.

Definition tcc_leg (k0 k : K) : Point_Top ~{Top@{h o}}~> Om :=
  top_point Om (c k0 k).

Definition tcc_sep (k0 : K) : tcc_sum ~{Top@{h o}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
                (c:=Om) (tcc_leg k0)).

Lemma tcc_sep_at (k0 k : K) :
  continuous_map (tcc_sep k0) (continuous_map (tcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
              (c:=Om) (tcc_leg k0)) k ttt).
Qed.

Definition tcc_enc (U : top_carrier tcc_sum → Prop) : top_carrier tcc_sum :=
  continuous_map (tcc_inj (existT _ tcc_sum U)) ttt.

Lemma tcc_enc_inj (U V : top_carrier tcc_sum → Prop) :
  tcc_enc U ≈ tcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (continuous_map (tcc_sep (existT _ tcc_sum U)))
                _ _ H) as H1.
  assert (E : existT (fun X : TopSpace@{o} => top_carrier X → Prop) tcc_sum V
              = existT _ tcc_sum U).
  { apply c_spec.
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc V));
      [symmetry; exact (tcc_sep_at _ _)|].
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc U));
      [symmetry; exact H1|exact (tcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma tcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (top_carrier tcc_sum))
           (fun p => reflexivity p) tcc_enc tcc_enc_inj).
Qed.

End TCantor.

Theorem Top_not_cocomplete_Cantor_ObjDecEq@{r s h o +| o < h, o < s,
                                              Set < o +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction DE cocomp (Discrete_Top pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

Theorem Top_not_cocomplete_Cantor_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp Bool_Discrete
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.
