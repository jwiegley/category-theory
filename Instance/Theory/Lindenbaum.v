Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.

Generalizable All Variables.

(** * The Lindenbaum category of an elementary theory *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, 1998, §IV.6, printed p. 98, Exercise 2
   (catalog id maclane:IV.6:ex2).  Verbatim from the printed page:

     "In some elementary theory T, consider the set S = {p, q, ...} of
      sentences of T as a preorder, with p ≤ q meaning "p entails q"
      (i.e., q is a consequence of p on the basis of the axioms of T).
      Prove that S is a cartesian closed category, with product given by
      conjunction and exponential q^p given by "p implies q"."

   (The book prints the relation symbol as the double-bar ≦; it is
   rendered ≤ above.  The exercise sits on the same page as Exercises 1,
   3, 4 and 5, none of which is treated here.)

   nLab:      https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra
   nLab:      https://ncatlab.org/nlab/show/Heyting+algebra
   nLab:      https://ncatlab.org/nlab/show/deduction+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra
   Wikipedia: https://en.wikipedia.org/wiki/Deduction_theorem
   Book:      Lambek and Scott, "Introduction to Higher Order Categorical
              Logic", Cambridge Studies in Advanced Mathematics 7, 1986,
              Part I §§1-3 (the deductive system of a cartesian closed
              category).

   ** What this file builds

   [Sent V] is a deliberately MINIMAL propositional syntax over a type V
   of atoms: an atom former, truth, conjunction and implication, and
   nothing else.  That is the whole of what Mac Lane's exercise needs —
   product is conjunction, terminal is truth, exponential is implication
   — and a full first-order language (quantifiers, equality, function
   and relation symbols, a signature, substitution) is OUT OF SCOPE
   here.  Nothing below is claimed about first-order theories, and
   [Sent] is not proposed as a model of one.

   A theory is a bare set of sentences, [Theo V := Sent V -> Prop]; no
   deductive closure is imposed on it, and no consistency is required.
   Entailment RELATIVE to that theory, [Entails T p q], is Mac Lane's
   "q is a consequence of p on the basis of the axioms of T": it is an
   inductive family in Prop, so that [Instance/Proset.v]'s [Proset] —
   whose relation argument is a stdlib [relation A], hence Prop-valued —
   applies directly, and the resulting category is thin ([lind_thin])
   with no truncation or squashing anywhere.

   ** The design decision that makes the exercise cheap

   The rules of [Entails] are given in NATURAL DEDUCTION form, and this
   was a choice rather than the only option.  The consequence is that the
   deduction theorem is the CONSTRUCTOR [ent_curry] and evaluation is the
   CONSTRUCTOR [ent_eval], so the currying bijection of a cartesian
   closed category is available with no induction at all.  Presented
   instead as a Hilbert system — K and S plus modus ponens axiomatise
   the IMPLICATIONAL fragment, and [Entails] carries conjunction and
   truth as well, so a Hilbert presentation matching it needs analogues
   of [ent_top], [ent_pair], [ent_fst] and [ent_snd] besides — the
   deduction theorem is a metatheorem whose proof is an induction over
   derivations, and that induction would then have to be carried out
   before [Lind_Closed] could be stated.  That the two presentations
   define the same relation is the standard equivalence and is NOT
   established here.

   ** Which rule each structure consumes (measured, not asserted)

   Each of the nine constructors was deleted in turn from [Entails] and
   the file recompiled up to the end of section (D); the first site that
   then stopped resolving is recorded here.

     ent_refl   -> [entails_PreOrder], i.e. [id] of [Lind]
     ent_cut    -> [entails_PreOrder], i.e. [compose] of [Lind]
     ent_ax     -> NOTHING: sections (A)-(D) compile unchanged without it
     ent_top    -> [Lind_Terminal]  ([one])
     ent_pair   -> [Lind_Cartesian] ([fork])
     ent_fst    -> [Lind_Cartesian] ([exl])
     ent_snd    -> [Lind_Cartesian] ([exr])
     ent_curry  -> [Lind_Closed]    ([to exp_iso])
     ent_eval   -> [lind_uncurry],  i.e. [from exp_iso]

   So exactly eight of the nine are consumed by the four structures, and
   the ninth, the axiom rule [ent_ax], is what makes the theory parameter
   do any work at all: it is the only rule whose case in
   [entails_weaken] consumes the theory, and the only one used on the
   target side of section (G)'s [no_full_functor_empty_to_all].  The
   section is not built from it alone — [entails_weaken] is an induction
   applying all nine constructors by name — but it is the rule the
   section turns on, where two different axiom sets are shown to give
   two categories that are not equivalent.  No rule was dropped as
   redundant, and no rule is claimed
   here to be underivable from the others — that would take a countermodel
   per rule, and none is built.

   ** What is free because the category is thin

   Every hom-setoid of [Lind T] is trivially true ([Proset]'s [equiv] is
   [fun _ _ => True]), so [lind_thin] holds by [I].  Consequently every
   obligation of the four structures is discharged by [Program]'s
   default tactic with no proof written in this file.  Counted off
   [Print Module], they are fourteen: [one_unique] for [Lind_Terminal];
   [fork_respects] and [ump_products] for [Lind_Cartesian]; for
   [Lind_Closed] the two [proper_morphism] certificates of the transpose
   and its inverse (they are morphisms of [Sets]), both isomorphism laws
   of [exp_iso], and [ump_exponents']; and [fmap_respects], [fmap_id],
   [fmap_comp] three times over for each of [LindSound] and
   [LindWeaken].  So uniqueness of the transpose is free, and is not
   proved here because there is nothing to prove; the four structures
   carry exactly the data of the nine rules and no equational content.

   ** The comparison with Instance/Props.v

   [Instance/Props.v] is the semantic side: its objects are Props,
   its arrows implications, and its header already records that cartesian
   closure there is the deduction theorem.  The bridge is a valuation:
   given [val : V -> Prop] under which every axiom of T holds,
   [ent_soundness] carries derivations to implications, and [LindSound]
   packages that as a functor [Lind T ⟶ Props].  Its measured strength,
   with nothing claimed beyond what compiles below:

     - it is a functor (all three functor laws are free, Props is thin);
     - it preserves the terminal object, binary products and
       exponentials ON THE NOSE, at Leibniz equality of objects
       ([sound_terminal], [sound_product], [sound_exponent], all
       [eq_refl]);
     - it is Faithful, but VACUOUSLY: the source is thin, so [f ≈ g]
       there is [True] and EVERY functor out of [Lind T] is faithful —
       that general statement is [lind_any_Faithful], and
       [LindSound_Faithful] is literally it;
     - it is NOT full ([sound_not_Full]) and NOT essentially surjective
       ([sound_not_EssentiallySurjective]), hence not an equivalence,
       both refuted at the empty theory under the valuation that sends
       every atom to True.

   So the CCC structure of [Props] is reproduced on the nose by the
   comparison, while the two refutations show that THIS comparison is
   neither full nor essentially surjective.  They are statements about
   the single functor [LindSound T_empty val_true val_true_empty], and
   no constant here says that [Lind T_empty] and [Props] are
   inequivalent.  Fullness would be COMPLETENESS of the calculus with
   respect to a single valuation, which is a strictly stronger statement
   than the exercise asks for and is refuted here rather than attempted.

   ** Engineering findings

   [Lib.v:12] sets [Uniform Inductive Parameters] for the whole
   development, so inside the body of [Inductive Sent (V : Type)] the
   name [Sent] already stands for [Sent V]; writing the parameter
   explicitly there is rejected with "Illegal application
   (Non-functional construction)", an error that names the parameter but
   neither the flag nor the cause: it reports [Sent] as a non-functional
   term applied to [V], without saying that [Sent] has already absorbed
   the parameter.  The same applies inside [Entails].

   [PreOrder] in this file's scope is [CRelationClasses.PreOrder], the
   crelation-valued one, because [Category.Lib] exports it; the one
   [Proset] wants is the Prop-valued [RelationClasses.PreOrder], written
   qualified in [entails_PreOrder].  No extra [Require] is needed for the
   qualified name, since that module is already loaded transitively.

   [lind_thin] is proved here in one term rather than by requiring
   [Instance/Proset/Order.v:153]'s [proset_thin], which is the donor and
   applies to [Lind T] by conversion.  That is a measurement, not a
   preference: the transitive in-project closure of this file is 27
   modules, and adding [Instance/Proset/Order] takes it to 35. *)

(** ** (A) Syntax *)

(* Atoms, truth, conjunction, implication.  Nothing else; see the scope
   note in the header. *)
Inductive Sent (V : Type) : Type :=
  | s_var : V -> Sent
  | s_top : Sent
  | s_and : Sent -> Sent -> Sent
  | s_imp : Sent -> Sent -> Sent.

Arguments s_var {V} _.
Arguments s_top {V}.
Arguments s_and {V} _ _.
Arguments s_imp {V} _ _.

(* A theory is a bare set of sentences: its axioms.  It is not required
   to be deductively closed, consistent, or inhabited. *)
Definition Theo (V : Type) : Type := Sent V -> Prop.

(** ** (B) Entailment relative to a theory *)

(* Mac Lane's "q is a consequence of p on the basis of the axioms of T".
   Prop-valued, so [Proset] accepts it and the category below is thin
   without any truncation. *)
Inductive Entails {V : Type} (T : Theo V) : Sent V -> Sent V -> Prop :=
  (* assumption / reflexivity *)
  | ent_refl p : Entails p p
  (* cut / transitivity *)
  | ent_cut p q r : Entails p q -> Entails q r -> Entails p r
  (* the axiom rule: an axiom of T follows from anything *)
  | ent_ax p a : T a -> Entails p a
  (* ⊤-introduction *)
  | ent_top p : Entails p s_top
  (* ∧-introduction *)
  | ent_pair p q r : Entails p q -> Entails p r -> Entails p (s_and q r)
  (* the two ∧-eliminations *)
  | ent_fst p q : Entails (s_and p q) p
  | ent_snd p q : Entails (s_and p q) q
  (* →-introduction: the deduction theorem, here a CONSTRUCTOR *)
  | ent_curry p q r : Entails (s_and p q) r -> Entails p (s_imp q r)
  (* evaluation / modus ponens in sequent form *)
  | ent_eval q r : Entails (s_and (s_imp q r) q) r.

(* Reflexivity is [ent_refl] and transitivity is [ent_cut], so the
   preorder is the two structural rules and nothing more.  Given as a
   record literal rather than through [Program] so that [id] and
   [compose] of [Lind] reduce; see [lind_id] and [lind_compose]. *)
Definition entails_PreOrder {V} (T : Theo V) :
  RelationClasses.PreOrder (Entails T) :=
  {| RelationClasses.PreOrder_Reflexive := ent_refl T
   ; RelationClasses.PreOrder_Transitive :=
       fun p q r H K => ent_cut T p q r H K |}.

(** ** (C) The category of sentences ordered by entailment *)

Definition Lind {V} (T : Theo V) : Category :=
  Proset (entails_PreOrder T).

Example lind_obj {V} (T : Theo V) : obj[Lind T] = Sent V := eq_refl.

Example lind_hom {V} (T : Theo V) (p q : Sent V) :
  (p ~{Lind T}~> q) = Entails T p q := eq_refl.

Example lind_id {V} (T : Theo V) (p : Sent V) :
  @id (Lind T) p = ent_refl T p := eq_refl.

Example lind_compose {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T p q) (g : Entails T q r) :
  (g ∘[Lind T] f) = ent_cut T p q r f g := eq_refl.

(* Every hom-setoid is trivially true, so the category is thin.  This is
   [proset_thin] at [entails_PreOrder T] by conversion; see the closure
   measurement in the header for why it is restated in one term. *)
Definition lind_thin {V} (T : Theo V) : Thin (Lind T) :=
  fun _ _ _ _ => I.

(* Thinness of the SOURCE makes faithfulness vacuous: the conclusion
   [f ≈ g] of [fmap_inj] is True whatever the functor does, so every
   functor out of [Lind T] is faithful and no property of the functor is
   consulted.  [LindSound_Faithful] in section (F) is this term, so the
   vacuity is visible in the definition rather than argued in prose. *)
Definition lind_any_Faithful {V} (T : Theo V) {D : Category}
  (F : Lind T ⟶ D) : Faithful F :=
  @Build_Faithful (Lind T) D F (fun x y f g _ => I).

(** ** (D) Terminal, cartesian and closed *)

(* Terminal object: truth.  [one] is ⊤-introduction; [one_unique] is
   free by thinness. *)
#[export] Program Instance Lind_Terminal {V} (T : Theo V) :
  @Terminal (Lind T) := {
  terminal_obj := s_top;
  one := fun p => ent_top T p
}.

(* Product: conjunction, exactly as the exercise says.  [fork] is
   ∧-introduction, the projections are the two ∧-eliminations;
   [fork_respects] and [ump_products] are free by thinness. *)
#[export] Program Instance Lind_Cartesian {V} (T : Theo V) :
  @Cartesian (Lind T) := {
  product_obj := s_and;
  fork := fun p q r f g => ent_pair T p q r f g;
  exl  := fun p q => ent_fst T p q;
  exr  := fun p q => ent_snd T p q
}.

(* The inverse transpose.  This is the one derived rule in the file: it
   pairs the given entailment with the second projection and cuts
   against evaluation, so it consumes ent_cut, ent_pair, ent_fst,
   ent_snd and ent_eval, and nothing else. *)
Definition lind_uncurry {V} {T : Theo V} {p q r : Sent V}
  (f : Entails T p (s_imp q r)) : Entails T (s_and p q) r :=
  ent_cut T (s_and p q) (s_and (s_imp q r) q) r
    (ent_pair T (s_and p q) (s_imp q r) q
       (ent_cut T (s_and p q) p (s_imp q r) (ent_fst T p q) f)
       (ent_snd T p q))
    (ent_eval T q r).

(* Exponential: implication.  In this library [exponent_obj x y] is
   displayed [y ^ x], so [exponent_obj := s_imp] gives q ^ p = "p
   implies q", which is Mac Lane's q^p.  [to exp_iso] is the deduction
   theorem [ent_curry]; [from exp_iso] is [lind_uncurry]; both
   isomorphism laws and [ump_exponents'] are free by thinness. *)
#[export] Program Instance Lind_Closed {V} (T : Theo V) :
  @Closed (Lind T) _ := {
  exponent_obj := s_imp;
  exp_iso := fun p q r =>
    {| to   := {| morphism := fun f => ent_curry T p q r f |}
     ; from := {| morphism := fun f => lind_uncurry f |} |}
}.

(* The exercise's three identifications, pinned so that a later edit
   cannot drift away from them. *)
Example lind_terminal_is_top {V} (T : Theo V) :
  @terminal_obj (Lind T) (Lind_Terminal T) = s_top := eq_refl.

Example lind_product_is_and {V} (T : Theo V) (p q : Sent V) :
  @product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q := eq_refl.

Example lind_exponent_is_imp {V} (T : Theo V) (p q : Sent V) :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(* Currying IS the deduction rule, on the nose. *)
Example lind_curry_is_rule {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T (s_and p q) r) :
  @curry (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q r f
    = ent_curry T p q r f := eq_refl.

(* ...and the counit is [lind_uncurry] at the identity derivation. *)
Example lind_eval_unfold {V} (T : Theo V) (q r : Sent V) :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) q r
    = lind_uncurry (ent_refl T (s_imp q r)) := eq_refl.

(** ** (E) Soundness under a valuation *)

(* The interpretation of a sentence under a valuation of the atoms.
   Conjunction goes to /\ and implication to ->, which is what makes
   section (F)'s three preservation statements hold at eq_refl. *)
Fixpoint sdenote {V} (val : V -> Prop) (p : Sent V) : Prop :=
  match p with
  | s_var v   => val v
  | s_top     => True
  | s_and a b => sdenote val a /\ sdenote val b
  | s_imp a b => sdenote val a -> sdenote val b
  end.

(* Soundness: if every axiom of T holds under val, then every derivation
   carries the interpretation of its premise to that of its conclusion.
   By induction on the derivation; the only case that consumes the
   hypothesis on T is [ent_ax]. *)
Theorem ent_soundness {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) {p q : Sent V} :
  Entails T p q -> sdenote val p -> sdenote val q.
Proof.
  intros D; induction D; simpl in *; try tauto.
  - intros _; exact (HT a H).
Qed.

(** ** (F) The comparison functor into Instance/Props.v *)

(* The soundness map packaged as a functor.  All three functor laws are
   free: Props is thin, so every equation between its arrows is True. *)
Program Definition LindSound {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) : Lind T ⟶ Props := {|
  fobj := sdenote val;
  fmap := fun p q f => ent_soundness T val HT f
|}.

(* Preservation of the three pieces of cartesian closed structure, at
   Leibniz equality of objects rather than up to isomorphism. *)
Example sound_terminal {V} (T : Theo V) val HT :
  fobj[LindSound T val HT] (@terminal_obj (Lind T) (Lind_Terminal T))
    = @terminal_obj Props Props_Terminal := eq_refl.

Example sound_product {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@product_obj (Lind T) (Lind_Cartesian T) p q)
    = @product_obj Props Props_Cartesian
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

Example sound_exponent {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q)
    = @exponent_obj Props Props_Cartesian Props_Closed
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

(* Faithful, but VACUOUSLY so: this IS [lind_any_Faithful], so nothing
   about soundness is consulted and the vacuity is not a claim about the
   proof but the definition itself. *)
#[export] Instance LindSound_Faithful {V} (T : Theo V) val HT :
  Faithful (LindSound T val HT) :=
  lind_any_Faithful T (LindSound T val HT).

(** ** (G) Two axiom sets, two categories *)

(* Monotonicity of entailment in the theory: enlarging the axiom set
   only adds derivations.  By induction; every case but [ent_ax] is the
   corresponding constructor applied to the inductive hypotheses. *)
Lemma entails_weaken {V} {T T' : Theo V} (HTT : forall a, T a -> T' a)
  {p q : Sent V} : Entails T p q -> Entails T' p q.
Proof.
  intros D; induction D;
    [ apply ent_refl
    | eapply ent_cut; eassumption
    | apply ent_ax; apply HTT; assumption
    | apply ent_top
    | apply ent_pair; assumption
    | apply ent_fst
    | apply ent_snd
    | apply ent_curry; assumption
    | apply ent_eval ].
Defined.

(* ...as an identity-on-objects functor between the two categories. *)
Program Definition LindWeaken {V} {T T' : Theo V}
  (HTT : forall a, T a -> T' a) : Lind T ⟶ Lind T' := {|
  fobj := fun p => p;
  fmap := fun p q f => entails_weaken HTT f
|}.

(* Two atoms, and three theories over them: no axioms, the single
   implication between the atoms, and every sentence an axiom. *)
Definition sv (b : bool) : Sent bool := s_var b.

Definition T_empty : Theo bool := fun _ => False.
Definition T_mp : Theo bool := fun s => s = s_imp (sv true) (sv false).
Definition T_all : Theo bool := fun _ => True.

(* The separating valuation: the first atom true, the second not. *)
Definition val_sep (b : bool) : Prop := b = true.

Lemma val_sep_empty : forall a, T_empty a -> sdenote val_sep a.
Proof. intros a []. Qed.

(* Non-derivability at the empty theory, by soundness at [val_sep].
   This is the half that cannot be got by exhibiting a derivation. *)
Theorem not_entails_empty :
  Entails T_empty (sv true) (sv false) -> False.
Proof.
  intros D.
  pose proof (@ent_soundness bool T_empty val_sep val_sep_empty _ _ D
                eq_refl) as Hf.
  discriminate Hf.
Qed.

(* Derivability at the theory whose one axiom is that implication.  The
   derivation is categorical: pair the identity with itself to get the
   diagonal, then uncurry the axiom and cut — that is, modus ponens read
   off the cartesian closed structure rather than assumed as a rule. *)
Theorem entails_mp : Entails T_mp (sv true) (sv false).
Proof.
  apply (ent_cut _ _ (s_and (sv true) (sv true))).
  - apply ent_pair; apply ent_refl.
  - apply (@lind_uncurry bool T_mp).
    apply ent_ax; reflexivity.
Defined.

Definition empty_sub_mp : forall a, T_empty a -> T_mp a :=
  fun a H => match H return T_mp a with end.

(* The comparison functor between the two categories is identity on
   objects, and it is NOT full: [entails_mp] has no preimage. *)
Theorem weaken_not_Full : Full (LindWeaken empty_sub_mp) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) entails_mp)).
Qed.

(* [empty_sub_all] is declared for the reader rather than consumed: no
   constant below applies it, and this file names no functor
   [Lind T_empty ⟶ Lind T_all].  One exists — [LindWeaken empty_sub_all]
   typechecks at exactly that type — so the quantifier in the next
   theorem is not empty, but that is recorded here rather than pinned by
   a constant. *)
Definition empty_sub_all : forall a, T_empty a -> T_all a :=
  fun a H => match H return T_all a with end.

(* Stronger, and independent of any choice of comparison: NO full
   functor at all goes from the empty theory's category to the category
   of the theory that asserts everything.  Only [ent_ax] is used on the
   target side, and only [not_entails_empty] on the source side. *)
Theorem no_full_functor_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  Full F -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty
           (pre (sv true) (sv false)
              (ent_ax T_all (fobj[F] (sv true)) (fobj[F] (sv false)) I))).
Qed.

(* ...hence the two categories are not equivalent, since the functor of
   an equivalence is full ([Equivalence_Full]).  This is the strongest
   form of "two different axiom sets give two different categories"
   delivered here. *)
Theorem no_equivalence_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False.
Proof.
  intros E.
  exact (no_full_functor_empty_to_all F (Equivalence_Full E)).
Qed.

(** ** (H) The comparison with Props is not an equivalence *)

(* The valuation under which every atom, hence every sentence, holds. *)
Definition val_true (b : bool) : Prop := True.

Lemma val_true_empty : forall a, T_empty a -> sdenote val_true a.
Proof. intros a []. Qed.

Lemma sdenote_all {V} (val : V -> Prop)
  (Hv : forall v, val v) (p : Sent V) : sdenote val p.
Proof.
  induction p; simpl;
    [ apply Hv | exact I | split; assumption | intros _; assumption ].
Qed.

(* Not full: fullness at this valuation would be completeness, and it
   would hand back the underivable entailment of [not_entails_empty]. *)
Theorem sound_not_Full :
  Full (LindSound T_empty val_true val_true_empty) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) (fun x => x))).
Qed.

(* Every object in the image of this comparison is inhabited, so none of
   them is isomorphic to False in Props. *)
Theorem sound_misses_False (p : Sent bool) :
  @Isomorphism Props (sdenote val_true p) False -> False.
Proof.
  intros i.
  exact (to i (sdenote_all val_true (fun _ => I) p)).
Qed.

(* Not essentially surjective, by the previous result at False. *)
Theorem sound_not_EssentiallySurjective :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False.
Proof.
  intros [pick iso].
  exact (sound_misses_False (pick False) (iso False)).
Qed.
