Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Regular arrows in FinSet, by finite search *)

(* nLab:      https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

   Mac Lane, CWM 2nd ed., §I.5 Exercise 7, printed p. 21.  CITED BY LOCATION;
   the printed text was not consulted and no sentence of it is reproduced.
   The in-tree catalog (doc/plan/books/maclane/inventory/I.json, id
   maclane:I.5:ex7) summarizes the exercise as: "Call an arrow f : a -> b in
   a category C regular when there exists g : b -> a with f g f = f.  Show f
   is regular whenever it has either a left or a right inverse, and prove
   that in Set every arrow f : a -> b with a nonempty is regular."

   The first half is category theory and lives in Theory/Morphisms.v
   ([regular_of_section], [regular_of_retraction]).  This file is the second
   half, and the second half is where a choice principle would ordinarily be
   spent.  It is spent here on FINITENESS instead. *)

(* ------------------------------------------------------------------------ *)
(** ** What the classical statement costs, and what is proved instead *)

(* WHAT THE CLASSICAL ARGUMENT SPENDS.

   Fix f : A → B in Set with A inhabited by a₀.  A pseudoinverse must send
   each b ∈ B to SOME element of the fibre f⁻¹(b) when that fibre is
   nonempty, and anywhere at all (say a₀) when it is empty.  Nothing in the
   data of f selects a fibre element: the classical construction picks one
   simultaneously for every b in the image, which is an instance of the axiom
   of choice over the family of fibres.  Reading a regularity witness back
   off is choice-free, and is [regular_epic_retraction] /
   [regular_monic_section] in Theory/Morphisms.v.

   HOW MUCH THE BLANKET PRINCIPLE COSTS HERE.  Choice is what that argument
   spends under an ambient excluded middle.  It is not what the blanket
   principle costs in this library's ambient logic, where the principle is
   strictly STRONGER than any choice axiom: it decides every proposition.
   Instance/Sets/Regular.v proves that, axiom-free.
   [blanket_regularity_entails_LEM] there derives ∀ P : Prop, P + (P → False)
   from "every arrow of [Sets] with inhabited domain is regular", and
   [blanket_splitting_entails_LEM] derives the same conclusion from the
   weaker internal choice principle "every epimorphism with inhabited domain
   splits" -- the phrasing the nLab page on split epimorphisms records for
   the axiom of choice internal to a category, noting that "In Set this is
   equivalent to the usual axiom of choice" (retrieved 2026-08).  The
   implication BETWEEN those two quantified principles is
   [blanket_regularity_entails_splitting], itself a statement of Coq rather
   than a remark about the pointwise [regular_epic_retraction] it is one line
   from.  The countermodel driving all three is a two-element setoid
   coarsened by a proposition, in the shape of Diaconescu's argument; the
   header of that file carries the citations, and the reason a SETOID library
   pays this price where the standard library's intensional choice axioms do
   not.  No [Axiom] is declared in this file or in that one, and [Print
   Assumptions] on every constant of either reports "Closed under the global
   context".

   WHAT IS PROVED INSTEAD.  Over FinSet the fibre selection needs no choice
   at all, because a fibre of a map Fin.t m → Fin.t n can be SEARCHED: the
   domain is a finite type, so a scan over it terminates, and equality in the
   codomain is decidable, so each candidate can be tested ([Fin.eq_dec] of the
   standard library, which is transparent and reduces on closed terms).
   [fin_preimage] performs that search by structural recursion on m and
   [finset_regular] assembles the pseudoinverse from it, so the witness is a
   program rather than an appeal.  Because the library's `∃` is Type-valued
   (`sigT`, Lib/Foundation.v:61,66) the witness survives as data, and the
   [Example]s at the end of this file evaluate it by [eq_refl].  The
   inhabited-domain hypothesis is then disposed of in the only case it
   excludes: an epimorphism out of the empty object forces an empty codomain
   ([finset_epi_from_empty_absurd]), so [finset_every_epi_splits] holds for
   EVERY arrow of FinSet, with no restriction on the domain and no choice
   principle in sight.  The hypothesis is nevertheless SHARP for regularity
   itself -- [finset_empty_to_one_not_regular] refutes it for the unique
   arrow 0 → 1 -- so FinSet supplies its own witness that regularity is a
   real condition, and this file no longer has to reach to Instance/Two.v
   for one.

   The exchange is a genuine restriction and not a re-description: FinSet is
   the SKELETON of finite sets, so "every arrow with inhabited domain is
   regular" is proved here only for finite sets, and nothing below says
   anything about an arrow of [Sets] with an infinite domain.  What
   Instance/Sets/Regular.v adds about [Sets] is a bound in the other
   direction: the blanket statement is not available there, so the exercise's
   second half stops at the finite case for a reason, and not for want of an
   argument.  Instance/Sets.v is short of the ingredients in any case: its
   [surjectivity_is_epic] is abandoned in the epi → surjective direction for
   an unrelated size reason documented at Instance/Sets.v:412-427, so the
   tree has no route from [Epic] to a fibre witness in [Sets] to begin
   with. *)

(* ------------------------------------------------------------------------ *)
(** ** The finite search *)

(* [fin_preimage f b] scans the domain in index order and returns the first
   a with f a = b, or [None] if there is none.  The recursion is structural
   in m: at [S m'] it tests the head index [Fin.F1] and otherwise recurses on
   the tail map [fun q => f (Fin.FS q)], re-tagging the answer along
   [Fin.FS].  This mirrors the recursion pattern already used for [fin_split]
   in Instance/FinSet.v:157, and like it, reduces on closed input. *)

Fixpoint fin_preimage (m n : nat) (f : Fin.t m → Fin.t n) (b : Fin.t n)
         {struct m} : option (Fin.t m) :=
  match m return (Fin.t m → Fin.t n) → option (Fin.t m) with
  | O    => fun _ => None
  | S m' => fun f =>
      match Fin.eq_dec (f Fin.F1) b with
      | left _  => Some Fin.F1
      | right _ =>
          match fin_preimage m' n (fun q => f (Fin.FS q)) b with
          | Some q => Some (Fin.FS q)
          | None   => None
          end
      end
  end f.

Arguments fin_preimage {m n} f b.

(* Correctness of the search, in the only form needed: at a value that IS
   attained the search succeeds, and what it returns is a genuine preimage.
   Both halves are packaged in one [match] so that a single induction on the
   witness a proves them together -- the [None] branch is the statement that
   the search cannot miss, and the [Some] branch that it cannot lie.

   Note the use of `=` rather than `≈` here and in [fin3_cases] below: these
   are equations between ELEMENTS of [Fin.t n], not between morphisms, so the
   library's `≈`-only rule for morphism equality does not apply (this is not
   the same-term exception documented at Functor/Bifunctor.v:42-45).  Every
   MORPHISM equation in this file -- [finset_split_pair], [finset_point_bang],
   [finset_collapse_not_id] and the [RegularMorphism] statements -- is stated
   with `≈`, which over FinSet unfolds to pointwise `=` on [Fin.t] via
   [Fin_Setoid] (Lib/Setoid.v:89) and [fun_setoid] (Lib/Datatypes.v:360). *)

Lemma fin_preimage_correct {m n : nat} (f : Fin.t m → Fin.t n) (a : Fin.t m) :
  match fin_preimage f (f a) with
  | Some a' => f a' = f a
  | None    => False
  end.
Proof.
  revert f.
  induction a as [m | m a IH]; intros f; simpl.
  - (* head index: the test at [Fin.F1] succeeds outright *)
    destruct (Fin.eq_dec (f Fin.F1) (f Fin.F1)) as [_ | ne].
    + reflexivity.
    + now contradiction ne.
  - (* tail index: either the head already hits the value, or recurse *)
    destruct (Fin.eq_dec (f Fin.F1) (f (Fin.FS a))) as [e | _].
    + exact e.
    + specialize (IH (fun q => f (Fin.FS q))); simpl in IH.
      destruct (fin_preimage (fun q => f (Fin.FS q)) (f (Fin.FS a)));
        exact IH.
Qed.

(* The pseudoinverse of f relative to a chosen fallback point a0 of the
   domain: search the fibre, and land on a0 where the fibre is empty.  The
   fallback is the only use made of the inhabitation hypothesis. *)

Definition finset_pseudoinverse {m n : nat} (a0 : Fin.t m)
           (f : Fin.t m → Fin.t n) : Fin.t n → Fin.t m :=
  fun b => match fin_preimage f b with
           | Some a => a
           | None   => a0
           end.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane §I.5 Exercise 7, second half, over FinSet *)

(* Every arrow of FinSet whose domain is inhabited is regular.  Inhabitation
   is taken as DATA (an actual element a0), which is what "nonempty" means
   constructively and what the finite search needs; the special case of a
   successor domain, where [Fin.F1] serves, is [finset_regular_pos] below.

   This is [Definition] ... [Defined] rather than [Qed] so the pseudoinverse
   really can be projected out and run; the [Example]s below do exactly
   that. *)

Definition finset_regular {m n : nat} (a0 : Fin.t m) (f : m ~{FinSet}~> n) :
  RegularMorphism f.
Proof.
  exists (finset_pseudoinverse a0 f).
  intro a; simpl; unfold finset_pseudoinverse.
  pose proof (fin_preimage_correct f a) as H.
  destruct (fin_preimage f (f a)) as [a' |].
  - exact H.
  - contradiction.
Defined.

(* The same statement with inhabitation read off the object: an arrow out of
   a successor object is regular, with [Fin.F1] as the fallback. *)
Definition finset_regular_pos {m n : nat} (f : S m ~{FinSet}~> n) :
  RegularMorphism f := finset_regular Fin.F1 f.

(* ------------------------------------------------------------------------ *)
(** ** The hypothesis is sharp, and every epimorphism splits regardless *)

(* The inhabitation hypothesis of [finset_regular] is not an artefact of the
   search.  An arrow out of the empty object into a nonempty one has no
   pseudoinverse at all, since a pseudoinverse would be an arrow BACK, and
   there is no map into the empty set from a nonempty one. *)

Lemma finset_empty_domain_not_regular {n : nat} (f : 0%nat ~{FinSet}~> S n) :
  RegularMorphism f → False.
Proof. intros [g _]; exact (Fin.case0 (fun _ => False) (g Fin.F1)). Qed.

(* The smallest instance is the unique arrow from the empty set to the
   singleton -- the [zero] of [FinSet_Initial] (Instance/FinSet.v:223),
   written out -- and it is FinSet's own non-regular arrow.  Regularity is
   therefore a real condition on an arrow of THIS category, without appeal to
   the interval category of Instance/Two.v. *)

Definition finset_empty_to_one : 0%nat ~{FinSet}~> 1%nat :=
  fun a => Fin.case0 (fun _ => Fin.t 1) a.

Definition finset_empty_to_one_not_regular :
  RegularMorphism finset_empty_to_one → False :=
  finset_empty_domain_not_regular finset_empty_to_one.

(* Splitting, unlike regularity, survives the empty domain: an epimorphism
   out of the empty object forces its codomain to be empty as well.  Probe it
   with the two constant maps into the two-element object, which agree after
   it vacuously -- there is nothing to evaluate them at -- hence agree
   outright, which they do not.  No choice principle and no case distinction
   on a proposition enters, only the emptiness of [Fin.t 0]. *)

Lemma finset_epi_from_empty_absurd {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Fin.t n → False.
Proof.
  intros E b.
  destruct n as [| n'].
  - exact (Fin.case0 (fun _ => False) b).
  - pose proof (@epic _ _ _ f E 2%nat (fun _ => Fin.F1)
                  (fun _ => Fin.FS Fin.F1)
                  (fun a => Fin.case0 (fun _ => _) a)) as H.
    discriminate (H Fin.F1).
Qed.

(* So such an epimorphism splits vacuously: its codomain has no element to
   choose a preimage for. *)
Lemma finset_epi_from_empty_splits {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Retraction f.
Proof.
  intro E.
  exists (fun b => False_rect (Fin.t 0) (finset_epi_from_empty_absurd f E b)).
  intro b.
  exact (False_rect _ (finset_epi_from_empty_absurd f E b)).
Qed.

(* EVERY epimorphism of FinSet splits, with no hypothesis on the domain: the
   successor case is [finset_regular_pos] read back through
   [regular_epic_retraction], the zero case is the vacuous splitting above.
   Stated as a [match] on the domain so the retraction still reduces on
   closed input, as [finset_epi_split_computes] at the end of this file
   checks. *)
Definition finset_every_epi_splits {m n : nat} (f : m ~{FinSet}~> n) :
  Epic f → Retraction f :=
  match m return ∀ f : m ~{FinSet}~> n, Epic f → Retraction f with
  | O    => fun f E => finset_epi_from_empty_splits f E
  | S m' => fun f E => regular_epic_retraction f (finset_regular_pos f) E
  end f.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity I: regular, but neither a section nor a retraction *)

(* Every isomorphism is trivially regular, so an invertible witness would
   establish nothing.  [finset_shift3] is the self-map of a three-element set

     0 ↦ 2,  1 ↦ 2,  2 ↦ 0.

   It identifies 0 with 1 and it misses the value 1 entirely.  The first
   refutes any left inverse ([finset_shift3_not_section], by evaluating the
   left-inverse law at the two indices sharing an image) and the second any
   right inverse ([finset_shift3_not_retraction], by evaluating the
   right-inverse law at the missed value), so the arrow is neither a section
   nor a retraction, and a fortiori not an isomorphism
   ([finset_shift3_not_iso]).  Regularity nevertheless holds, by the finite
   search.

   Both refutations are DIRECT.  The tree does have the bridge that would let
   them go the long way round -- [finset_monic_iff_injective]
   (Instance/FinSet/Classifier.v:335) proves monic in FinSet is exactly
   injective, and [sections_are_monic] would finish the first half -- but
   taking it would place this file downstream of the subobject-classifier
   development for no gain, and there is no companion epi/surjective
   characterization for FinSet to run the second half through.

   The same two features are what put the search through its paces: the
   missed value forces the fallback, and the shared image forces a choice,
   resolved by taking the first index. *)

Definition finset_shift3 : 3%nat ~{FinSet}~> 3%nat :=
  fun a =>
    Fin.caseS' a (fun _ => Fin.t 3)
      (Fin.FS (Fin.FS Fin.F1))
      (fun a1 =>
         Fin.caseS' a1 (fun _ => Fin.t 3)
           (Fin.FS (Fin.FS Fin.F1))
           (fun _ => Fin.F1)).

(* Exhaustive case analysis on a three-element index, needed to show that a
   value is missed by every argument. *)
Lemma fin3_cases (a : Fin.t 3) :
  (a = Fin.F1) ∨ (a = Fin.FS Fin.F1) ∨ (a = Fin.FS (Fin.FS Fin.F1)).
Proof.
  apply (Fin.caseS' a
           (fun a => (a = Fin.F1) ∨ (a = Fin.FS Fin.F1)
                       ∨ (a = Fin.FS (Fin.FS Fin.F1)))).
  - now left.
  - intro b.
    apply (Fin.caseS' b
             (fun b => (Fin.FS b = Fin.F1) ∨ (Fin.FS b = Fin.FS Fin.F1)
                         ∨ (Fin.FS b = Fin.FS (Fin.FS Fin.F1)))).
    + right; now left.
    + (* the remaining index lives in [Fin.t 1], a singleton by
         [fin1_unique] (Instance/FinSet.v:229) *)
      intro c.
      right; right.
      now rewrite (fin1_unique c).
Qed.

(* It is regular: the finite search supplies the pseudoinverse. *)
Definition finset_shift3_regular : RegularMorphism finset_shift3 :=
  finset_regular_pos finset_shift3.

(* It is not injective -- indices 0 and 1 share an image -- so it has no left
   inverse. *)
Lemma finset_shift3_not_section : Section finset_shift3 → False.
Proof.
  intros [s Hs].
  (* s ∘ f ≈ id, evaluated at the two indices sharing an image *)
  pose proof (Hs Fin.F1) as H0.
  pose proof (Hs (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  (* both reduce to a statement about s applied to the SAME value *)
  rewrite H0 in H1.
  discriminate.
Qed.

(* It misses the value 1 entirely, so it has no right inverse. *)
Lemma finset_shift3_not_retraction : Retraction finset_shift3 → False.
Proof.
  intros [r Hr].
  pose proof (Hr (Fin.FS Fin.F1)) as H.
  simpl in H.
  destruct (fin3_cases (r (Fin.FS Fin.F1))) as [E | [E | E]];
    rewrite E in H; discriminate.
Qed.

(* Hence not an isomorphism either: an inverse would in particular be a left
   inverse. *)
Lemma finset_shift3_not_iso : IsIsomorphism finset_shift3 → False.
Proof.
  intros [g _ Hl].
  exact (finset_shift3_not_section (Build_Section _ _ finset_shift3 g Hl)).
Qed.

(* The exercise's point, packaged: regularity is strictly weaker than
   one-sided invertibility, and strictly weaker than invertibility. *)
Definition finset_regular_not_split :
  RegularMorphism finset_shift3
  * (Section finset_shift3 → False)
  * (Retraction finset_shift3 → False)
  * (IsIsomorphism finset_shift3 → False) :=
  (finset_shift3_regular, finset_shift3_not_section,
   finset_shift3_not_retraction, finset_shift3_not_iso).

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity II: a split pair whose idempotent is not the identity *)

(* [split_pair_idempotent] (Theory/Morphisms.v) would say nothing if every
   available split pair made h ∘ g the identity.  A 1-element object beside a
   2-element one settles that: the point inclusion and the terminal map
   compose to the identity ONE WAY ONLY. *)

Definition finset_point : 1%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.
Definition finset_bang  : 2%nat ~{FinSet}~> 1%nat := fun _ => Fin.F1.
Definition finset_collapse : 2%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.

(* One composite is the identity of the 1-element object. *)
Lemma finset_split_pair : finset_bang ∘ finset_point ≈ id.
Proof. intro i; exact (eq_sym (fin1_unique i)). Qed.

(* The other composite is [finset_collapse], on the nose. *)
Lemma finset_point_bang : finset_point ∘ finset_bang ≈ finset_collapse.
Proof. intro i; reflexivity. Qed.

(* So the collapse is idempotent -- by the general lemma, not by hand. *)
Lemma finset_collapse_idempotent : Idempotent finset_collapse.
Proof.
  apply (idempotent_respects (finset_point ∘ finset_bang)).
  - exact finset_point_bang.
  - exact (split_pair_idempotent finset_bang finset_point finset_split_pair).
Qed.

(* And it is NOT the identity: it sends index 1 to index 0.  Without this the
   idempotence above would be witnessed by identities alone. *)
Lemma finset_collapse_not_id : finset_collapse ≈ id → False.
Proof.
  intro H.
  pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H1.
  discriminate.
Qed.

(* Mac Lane's [maclane:I.5:def5] over FinSet, packaged: a split pair, the
   identification of its OTHER composite with [finset_collapse], the
   idempotence of that composite, and the refutation that it is an identity.
   The second component is what ties the package to its own headline:
   [finset_collapse] is an independently defined constant, so without
   [finset_point_bang] the remaining three would say only that a split pair
   exists and that some non-identity idempotent exists, separately. *)
Definition finset_split_pair_nontrivial :
  (finset_bang ∘ finset_point ≈ id)
  * (finset_point ∘ finset_bang ≈ finset_collapse)
  * Idempotent finset_collapse
  * (finset_collapse ≈ id → False) :=
  (finset_split_pair, finset_point_bang,
   finset_collapse_idempotent, finset_collapse_not_id).

(* ------------------------------------------------------------------------ *)
(** ** The search runs *)

(* The three behaviours of [fin_preimage] on [finset_shift3], each by
   [eq_refl], so the finite search is executable and not merely provable.  In
   order: a hit at a LATER index (the search scans past 0 and 1 before
   finding 2), a MISS (nothing maps to index 1, so the fallback in
   [finset_pseudoinverse] is what supplies the value), and a hit at index
   0 where two indices compete and the first wins. *)

Example finset_preimage_late :
  fin_preimage finset_shift3 Fin.F1 = Some (Fin.FS (Fin.FS Fin.F1)) := eq_refl.

Example finset_preimage_miss :
  fin_preimage finset_shift3 (Fin.FS Fin.F1) = None := eq_refl.

Example finset_preimage_first :
  fin_preimage finset_shift3 (Fin.FS (Fin.FS Fin.F1)) = Some Fin.F1 := eq_refl.

(* The assembled pseudoinverse, evaluated at all three indices.  The middle
   value is the fallback -- [Fin.F1], the same one [finset_regular_pos]
   supplies -- because index 1 has an empty fibre. *)
Example finset_pseudoinverse_computes :
  (finset_pseudoinverse Fin.F1 finset_shift3 Fin.F1,
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS Fin.F1),
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(* And the witness projected out of the regularity proof is that same
   program, at every index -- the [Defined] on [finset_regular] is what makes
   this hold by [eq_refl]. *)
Example finset_regular_witness_computes :
  (`1 finset_shift3_regular Fin.F1,
   `1 finset_shift3_regular (Fin.FS Fin.F1),
   `1 finset_shift3_regular (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(* [finset_every_epi_splits] computes too, so it is not vacuous on the side
   that matters.  [finset_bang] is epic -- everything out of the singleton is
   determined at [Fin.F1], which [finset_bang] hits -- and the retraction the
   theorem returns for it is the finite search's answer, by [eq_refl]. *)

Lemma finset_bang_epic : Epic finset_bang.
Proof.
  constructor; intros z g1 g2 H i.
  rewrite (fin1_unique i).
  exact (H Fin.F1).
Qed.

Example finset_epi_split_computes :
  @retract _ _ _ _ (finset_every_epi_splits finset_bang finset_bang_epic) Fin.F1
  = Fin.F1 := eq_refl.
