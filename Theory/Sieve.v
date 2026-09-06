Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Sieves, and the presheaf of sieves *)

(* Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September
   2005), §8.8 (Topoi), printed pp. 210-211, inside the proof of
   Proposition 8.17 ([awodey:8.8:def-sieve],
   [awodey:8.8:construction-omega-sieves]).  Verbatim:

     "To that end, for any category C we define a sieve on an object C to
      be any set S of arrows f : · → C (with arbitrary domain) that is
      closed under precomposition, i.e. if f : D → C is in S then so is
      f ∘ g : E → D → C for every g : E → D (think of a sieve as a
      generalization of a "lower set" in a poset).  Then let:

          Ω(C) = {S ⊆ C_1 | S is a sieve on C}

      and given h : D → C let:

          h* : Ω(C) → Ω(D)

      be defined by:

          h*(S) = {g : · → D | h ∘ g ∈ S}.

      This clearly defines a presheaf Ω : C^op → Sets, with a
      distinguished point,

          t : 1 → Ω,

      namely, at each C, the "total sieve":

          t_C = {f : · → C}."

   This file delivers every display of that passage except the
   distinguished point t : 1 → Ω itself: the sieve, the object of sieves,
   the restriction h*, the total sieve t_C ([total_sieve], with
   [sieve_restrict_total] recording that h* fixes it), and the presheaf
   [Sieve_Presheaf].  The point t — the MORPHISM 1 ⟹ Ω in the presheaf
   category — is NOT here (see WHY THIS FILE IS LEAN below) and lives in
   Instance/Fun/Classifier.v as [sieve_truth], together with the classifier
   of Mac Lane §IV.9 construction 2 and remark 1 (book pp. 105-106,
   [maclane:IV.9:construction2], [maclane:IV.9:remark1]) that consumes it.

   WHAT A SIEVE IS HERE.  Awodey's "set S of arrows" becomes a
   [Prop]-valued membership predicate on each hom-set, carrying two
   fields beside it: respectfulness for the hom-setoid's [≈] (a set of
   arrows in a setoid-enriched category must not distinguish equivalent
   arrows) and Awodey's closure under precomposition.  Membership is
   [Prop]-valued and not [Type]-valued, and that is FORCED rather than
   chosen: a [Type@{o}]-valued sieve type sits at [o+1], so it is not the
   carrier of an object of [Sets@{o so}] — the refusal is "Cannot enforce
   o < o", a universe inconsistency, pinned in Test/ProbeFunClassifier403.v
   with the [Prop]-valued [Sieve] as the accepted control.  The price
   of [Prop] is paid in Instance/Fun/Classifier.v, where the
   characteristic sieve must truncate a [Type]-valued existential with
   Instance/Sets/Powerset.v's [Powerset_squash] and pay for the
   truncation with #402's [Untruncate] hypothesis, spent exactly once.

   THE TRUTH-VALUE CONVENTION, stated here because the record fixes it.  The
   distinguished point of [Sieve_Presheaf] is the TOTAL sieve, so "truth"
   is [total_sieve], and Ω(c) is a set of sieves carrying no numeral —
   there is nothing here to agree or disagree with Mac Lane's "0 on the
   subset" (§IV.9 construction 1, book p. 105) or Seven Sketches' "true on
   the subset", which name one and the same thing, the value every
   classifier puts on its subobjects.  The numeral enters only at the arrow
   shape, in Instance/Fun/Classifier.v's codes, which send the total sieve
   to [Fin.F1] — the page's 0, and also Instance/FinSet/Classifier.v's
   [fin_true]; Instance/Fun/Classifier.v's truth-value paragraph says
   exactly how much of a "convention" that is.

   WHY THIS FILE IS LEAN.  Its transitive in-project closure is 16
   modules, a SUBSET of both Theory/Sheaf.v's (18) and
   Construction/Localization.v's (23) — measured as a set, and the
   set difference is empty in both cases — the two files whose prose
   already mentions sieves (SGA 4's Grothendieck topologies, and covering
   sieves for orthogonal localization), so either could Require it later at
   ZERO extra module cost.  NEITHER IS REWIRED HERE; that is a future
   reuse, and the measurement is what makes it cheap rather than a
   promise.  Putting the truth point here instead would drag in
   Structure/Terminal, Instance/Fun and Instance/Fun/Terminal, whose own
   closure is 60, which is why [sieve_truth] lives downstream.
   For the same reason the reading of a sieve as a SUBOBJECT OF THE
   REPRESENTABLE PRESHEAF — Awodey's "lower set" made categorical — is NOT here
   either: it needs Functor/Hom.v's [Curried_CoHom] and
   Instance/Fun/Morphisms.v's pointwise mono characterisation, neither of which
   is in this closure.  It is Instance/Fun/Classifier.v's [sieve_subpresheaf] /
   [sieve_incl] / [sieve_subobject], where the classifier's uniqueness clause
   consumes the [sieve_subpresheaf] half together with its cone, while
   [sieve_incl] and [sieve_subobject] are the checkbox itself and have no
   consumer (measured there by deleting them).

   UNIVERSES, measured off BOTH binder and block.  NOT ONE of this file's
   constraint blocks contains a universe EQUATION; every entry is [<] or
   [<=].  The identification of hom with proof sits in the BINDER and is
   the record's own — [Sieve@{u u0}] is over [C : Category@{u u0 u0}]
   with a LITERALLY EMPTY block — because [sieve_respects] mentions [≈]
   on homs.  [SieveObj@{u u0 u1 u2}] carries [Set < u] (from [Prop :
   Type@{Set+1}], a strict lower bound and never a pin), [u1 <= u] and
   [u2 <= u]: the first of those two is Awodey's "for any SMALL category
   C" — C's objects at or below the carrier universe — and it is a BOUND,
   not an equation.  [Sieve_Presheaf] adds [Sets]' own [o < so] and one
   strict bound of the [Functor] record's, and no equation; ELEVEN of
   this file's 22 constants carry a word-bounded [Set], always as that
   same lower bound.
   The identifications the presheaf CATEGORY forces (C's hom with C's
   proof, and C's hom with [Sets]' carrier universe) are [Opposite]'s and
   [Fun]'s and appear only downstream; nothing here forces them, which is
   why this file can be Required by a consumer that never forms
   [[C^op, Sets]].

   COUNTS, WITH THEIR CRITERIA.  Constants closed under the global
   context: 22/22, zero [Axioms:] lines, counted as the 21 entries
   [Print Module] emits at five-space indent (the record's three
   projections and NINE [Program] obligations among them) plus
   [Build_Sieve], which it lists only after a [:=]; every one queried
   FULLY QUALIFIED, and all 22 are in the [print-assumptions] gate.
   [Defined] tokens: 0.  Statements closed by [:= eq_refl]: 0 (the
   readbacks are downstream, where the classifier is).  There is no
   refutation command in this file and it contributes ZERO [make todo]
   hits.

   NOT DELIVERED HERE.  No truth point, no classifier, no representable
   reading (all downstream, as above).  No Grothendieck topology, no
   coverage, no sheaf condition, and no relation to Theory/Sheaf.v's
   [Class Site], whose covering families are vector-indexed and carry no
   closure-under-precomposition condition at all.  No lattice of sieves:
   the pointwise order, meets, joins and pullback-stability are not
   built.  No comparison at a poset with a lower-set construction.  No
   cosieve (the covariant dual).  Nothing here is registered as an
   [Instance] except [Sieve_Setoid], which [SieveObj] needs. *)

#[local] Obligation Tactic := idtac.

(* ------------------------------------------------------------------ *)
(** ** Sieves *)

(* A sieve on c: a Prop-valued membership on the arrows into c, closed
   under [≈] and under precomposition. *)

Record Sieve {C : Category} (c : C) := {
  sieve_mem : ∀ (d : C), (d ~> c) → Prop;

  (* membership does not distinguish ≈-equal arrows *)
  sieve_respects : ∀ (d : C) (f g : d ~> c),
      f ≈ g → sieve_mem d f → sieve_mem d g;

  (* Awodey's closure: f ∈ S implies f ∘ g ∈ S *)
  sieve_closed : ∀ (d e : C) (f : d ~> c) (g : e ~> d),
      sieve_mem d f → sieve_mem e (f ∘ g)
}.

Arguments sieve_mem {C c} _ {d} _.
Arguments sieve_respects {C c} _ {d} _ _ _ _.
Arguments sieve_closed {C c} _ {d e} _ _ _.

(* Two sieves are equivalent when they have the same members. *)
Definition sieve_equiv {C : Category} {c : C} : crelation (Sieve c) :=
  fun S T => ∀ (d : C) (f : d ~> c), sieve_mem S f <-> sieve_mem T f.

#[export]
Program Instance Sieve_Setoid {C : Category} (c : C) : Setoid (Sieve c) := {|
  equiv := sieve_equiv
|}.
Next Obligation.
  intros C c.
  constructor; repeat intro.
  - split; auto.
  - split; apply X.
  - split; intro H.
    + apply X0, X, H.
    + apply X, X0, H.
Qed.

(* Awodey's Ω(C), as an object of [Sets]. *)
Definition SieveObj {C : Category} (c : C) : SetoidObject := {|
  carrier := Sieve c ; is_setoid := Sieve_Setoid c
|}.

(* ------------------------------------------------------------------ *)
(** ** The total sieve, and restriction *)

(* Awodey's t_C = {f : · → C}: every arrow into c. *)
Program Definition total_sieve {C : Category} (c : C) : Sieve c := {|
  sieve_mem := fun _ _ => True
|}.
Next Obligation. intros; exact I. Qed.
Next Obligation. intros; exact I. Qed.

(* Awodey's h*(S) = {g | h ∘ g ∈ S}, for h : d ~> c in C. *)
Program Definition sieve_restrict {C : Category} {c d : C} (h : d ~> c)
        (S : Sieve c) : Sieve d := {|
  sieve_mem := fun e (g : e ~> d) => sieve_mem S (h ∘ g)
|}.
Next Obligation.
  intros C c d h S e f g Hfg Hmem.
  eapply sieve_respects; [ | exact Hmem ].
  now rewrite Hfg.
Qed.
Next Obligation.
  intros C c d h S e e' f g Hmem.
  eapply sieve_respects.
  - symmetry; apply comp_assoc.
  - now apply sieve_closed.
Qed.

(* Restriction carries the total sieve to the total sieve; this is the
   naturality content of the truth point built downstream. *)
Lemma sieve_restrict_total {C : Category} {c d : C} (h : d ~> c) :
  sieve_restrict h (total_sieve c) ≈ total_sieve d.
Proof. intros e g; split; intro; exact I. Qed.

Program Definition sieve_restrict_mor {C : Category} {c d : C} (h : d ~> c) :
  SieveObj c ~{Sets}~> SieveObj d := {|
  morphism := sieve_restrict h
|}.
Next Obligation.
  intros C c d h.
  unfold Proper, respectful; intros S T HST e g; simpl.
  split; intro H; now apply HST.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The presheaf of sieves *)

(* Awodey's Ω : C^op → Sets.  The three functor laws are the three
   category laws of C read through membership: respectfulness of [fmap]
   is [sieve_respects] at [h ≈ h'], the identity law is [id_left] and
   the composition law is [comp_assoc]. *)

Program Definition Sieve_Presheaf (C : Category) : C^op ⟶ Sets := {|
  fobj := fun c => @SieveObj C c;
  fmap := fun x y (h : x ~{C^op}~> y) => @sieve_restrict_mor C x y h
|}.
Next Obligation.
  intros C x y.
  unfold Proper, respectful; intros h h2 Hh S d g; simpl.
  split; intro H; eapply sieve_respects; try exact H;
    [ now rewrite Hh | now rewrite Hh ].
Qed.
Next Obligation.
  intros C x S d f.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. apply id_left.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply id_left.
Qed.
Next Obligation.
  intros C x y z f g S d k.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply comp_assoc.
  - eapply sieve_respects; [ | exact H ]. apply comp_assoc.
Qed.
