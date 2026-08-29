Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Construction.Karoubi.Universal.

Generalizable All Variables.

(** * Paré's criterion: a left adjoint exists exactly when an idempotent
      splits

    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/idempotent
    nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+category
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §IV.1 Exercise 4, printed p. 86 --
          [maclane:IV.1:ex4].  Mac Lane credits the exercise to R. Paré.
          CITED BY LOCATION: the printed page was not consulted and no
          sentence of it is reproduced here.  The in-tree catalog entry
          (doc/plan/books/maclane/inventory/IV.json, id maclane:IV.1:ex4)
          summarizes it as: "(Pare) Given functors G : A -> X, K : X -> A
          and natural transformations epsilon : KG -> id_A, rho : id_X ->
          GK with G-epsilon after rho-G equal to 1_G, prove that
          epsilon-K composed with K-rho is an idempotent in the functor
          category A^X, and that G has a left adjoint if and only if this
          idempotent splits; explicitly, if it splits as alpha . beta with
          beta . alpha = 1 and beta : K -> F, then F is a left adjoint of
          G with unit G-beta . rho and counit epsilon . alpha-G."

    The names below follow that summary letter for letter.  [PareData]
    bundles G, K, ε, ρ and the single triangle; [pare_idem] is his
    εK ∘ Kρ, an endomorphism of K in the functor category [[X, A]] (his
    A^X); a splitting's retraction is his β and its section his α; and
    [pare_unit] and [pare_counit] are Gβ ∘ ρ and ε ∘ αG themselves, not a
    convenient variant of them -- see WHY THE UNIT AND COUNIT COST NOTHING
    below.  The headline is [pare_left_adjoint_iff_splits].

    WHAT IS DELIVERED.  The hypotheses as the record [PareData A X]; the
    idempotent [pare_idem] with [pare_idem_Idempotent] inhabiting
    [Theory/Morphisms.v]'s own [Idempotent] class at [[X, A]]; both
    directions ([pare_Adjunction] and its [SplitIdempotent]-fed wrapper
    [pare_adjunction_of_split] one way, [pare_SplitIdempotent] and
    [pare_splits_of_adjunction] the other); the biconditional
    [pare_left_adjoint_iff_splits]; and the Cauchy-complete corollary
    [pare_left_adjoint_of_CauchyComplete].  Both sides of the
    biconditional are [Type]-valued and every passage is [Defined], so a
    consumer gets the adjoint as DATA rather than as an opaque existence
    claim; [pare_adjunction_of_split_unit] and its counit twin check at
    [eq_refl] that the [SplitIdempotent]-fed wrapper hands
    [pare_Adjunction] the splitting's own retraction and section.

    THE TWO SIDES, AND WHY THEY ARE SHAPED THIS WAY.  [SplitIdempotent]
    carries the idempotent it splits as a FIELD, so the class alone cannot
    say WHICH idempotent splits, and its retract object is an INDEX, so it
    cannot be bound inside the class either.  [PareSplits] therefore binds
    both -- the retract F and the splitting S -- and then asserts
    [split_idem S ≈ pare_idem P].  That is deliberately the shape of the
    donor's own [split_of] field ([Construction/Karoubi/Universal.v:54]),
    which is why the Cauchy-complete corollary below is a [:=] with no
    tactic and no repackaging.  The other side, "G has a left adjoint", is
    [∃ F, F ∹ G] in [Adjunction_Transform]'s unit/counit form.

    THE ONE STRUCTURAL FRICTION, AND IT IS MAC LANE'S OWN NOTATION.
    Neither of his two vertical composites is formable in this library.
    For the triangle the elaborator says

      The term "rho ⊲ G" has type "Id[X] ◯ G ⟹ G ◯ K ◯ G"
      while it is expected to have type "Id[X] ◯ G ⟹ G ◯ (K ◯ G)"
      (cannot unify "G ◯ K ◯ G" and "G ◯ (K ◯ G)")

    and for the idempotent, at [pare_epsK] ∙ [pare_Krho], the same failure
    between "pare_K P ◯ (pare_G P ◯ pare_K P)" and
    "pare_K P ◯ pare_G P ◯ pare_K P".  THREE identifications are missing,
    not one: associativity of [Compose] and BOTH unitors -- [Id[X] ◯ G = G]
    and [G ◯ Id[A] = G] are each rejected too, so even repairing the middle
    would leave the endpoints wrong ([Gε ∘ ρG] would land at
    [Id[X] ◯ G ⟹ G ◯ Id[A]], not at [G ⟹ G], and [εK ∘ Kρ] at
    [K ◯ Id[X] ⟹ Id[A] ◯ K], not at [K ⟹ K]).  All of these were measured
    and rejected; they are not guarded here, probes being out of scope for
    this file.  The obstruction is LOCATED rather than asserted:
    [pare_assoc_fobj], [pare_assoc_fmap], [pare_unitor_fobj] and
    [pare_unitor_fmap] show at [eq_refl] that [fobj] and [fmap] agree,
    [Functor] has exactly five fields, and the whole records do not agree,
    so the difference is confined to the remaining three -- which
    Theory/Functor.v's printed body identifies as [Compose_obligation_1..3]
    at different arguments, opaque under [Unset Transparent Obligations].

    Consequently the record carries the triangle COMPONENTWISE and
    [pare_idem] is hand-built.  That is a change of spelling and not of
    content, and the file says so with computation rather than prose: the
    four whiskered pieces ARE named ([pare_Geps], [pare_rhoG], [pare_epsK],
    [pare_Krho]), their components read back at [eq_refl]
    ([pare_Geps_at] and its three siblings), and [pare_idem_at] shows the
    idempotent's component IS [pare_epsK P x ∘ pare_Krho P x].

    WHY THE UNIT AND COUNIT COST NOTHING, WHICH IS THE ASYMMETRY WORTH
    KNOWING.  The two composites Mac Lane forms for the ADJUNCTION happen
    to have endpoints that already agree on the nose: [ρ : Id[X] ⟹ G ◯ K]
    meets [G ⊳ β : G ◯ K ⟹ G ◯ F], and [α ⊲ G : F ◯ G ⟹ K ◯ G] meets
    [ε : K ◯ G ⟹ Id[A]], with [Id[X]] and [Id[A]] in exactly the positions
    [Adjunction_Transform] wants.  So [pare_unit] and [pare_counit] are
    plain [Definition]s -- [(G ⊳ r) ∙ ρ] and [ε ∙ (s ⊲ G)] -- with NO
    obligation of their own, naturality inherited from [nat_compose] and
    the two whiskerings.  The theory below discharges naturality by hand
    exactly three times ([pare_idem_natural], [pare_r_natural],
    [pare_s_natural]); the two transformations of the inhabitation section
    have theirs closed by [Program]'s default obligation tactic.  Only the
    two composites Mac Lane names were measured against the elaborator;
    [pare_r] and [pare_s] are hand-built because the whiskered spellings
    [(ε ⊲ F) ∙ (K ⊳ η)] and [(δ ⊲ K) ∙ (F ⊳ ρ)] have the same shape, which
    is an argument by inspection and not a second measurement.

    ITEM 2's ROUTE: [split_pair_idempotent] DOES NOT APPLY.  That lemma
    (Theory/Morphisms.v:294) reads [g ∘ h ≈ id → Idempotent (h ∘ g)].  The
    triangle is indeed a one-sided inverse pair, but it is a pair on G --
    [Gε] and [ρG], whose other composite is an endomorphism of GKG --
    whereas the idempotent to be produced is an endomorphism of K.
    There is no instantiation of that lemma whose conclusion is
    [Idempotent (εK ∘ Kρ)].  Idempotence is therefore a component
    computation, [pare_idem_idem], whose one reusable step is
    [pare_eps_absorb] (ε absorbs the idempotent read at G a); the triangle
    is spent there, once, and nowhere else in that argument.

    STRENGTHS, MEASURED STRICT-FIRST.  Seventeen [eq_refl] Examples HOLD and
    none was weakened to [≈]: the four [fobj]/[fmap] agreements above; the
    four whiskered components; [pare_idem_at]; [pare_unit_at] and
    [pare_counit_at]; and, on the produced adjunction,
    [pare_Adjunction_unit] and [pare_Adjunction_counit] (the record's
    projections return the named transformations) together with
    [pare_Adjunction_unit_at] and [pare_Adjunction_counit_at] (their
    components are [fmap[G] (r x) ∘ rho x] and [eps a ∘ s (G a)]).  That
    last pair is the reviewer bar for "literally the prescribed unit and
    counit", checked rather than claimed; the remaining two are the
    wrapper checks just mentioned.

    MEASURED AND REJECTED, NOT GUARDED HERE.  Besides the formability
    failures above: with [Adj := pare_Adjunction P F r s Hsr Hrs], the
    round trip [pare_r P F Adj = r] is rejected with [cannot unify].  No
    round trip is delivered in any form, [≈] included.

    THE CAUCHY-COMPLETE COROLLARY IS A CONDITIONAL WITH NO IN-TREE
    PREMISE WITNESS, AND THAT IS STATED RATHER THAN LEFT TO BE FOUND.
    [pare_splits_of_CauchyComplete] is [split_of] applied at [pare_idem],
    a [:=] with no tactic, and [pare_left_adjoint_of_CauchyComplete] is
    [snd] of the biconditional applied to it.  But the tree's only two
    [IdempotentsSplit] instances are [Karoubi_IdempotentsSplit]
    (Karoubi envelopes) and [Sets_IdempotentsSplit] (Sets), and neither is
    a functor category, so nothing in tree discharges [CauchyComplete
    ([X, A])] for any X and A.

    INHABITATION.  [pare_of_adjunction] turns any adjunction into Paré
    data by forgetting one of its two triangles -- a record literal with no
    tactic, [pare_triangle]'s type being literally [fmap_counit_unit]'s --
    and [pare_of_adjunction_idem] proves such data DEGENERATE: its
    idempotent is the identity, by the other triangle.  [pare_triv] is a
    uniform family -- not a closed term, and never instantiated here at
    a concrete category (everything the identity on a category), and
    [pare_triv_left_adjoint] runs the assembly end to end on it.  Read the
    scope: no [PareData] whose idempotent is provably NOT an identity is
    exhibited, so the biconditional is never exercised at a nontrivial
    splitting.

    ENGINEERING NOTES.  (a) [Lib.v:13] sets [Default Proof Using "Type"],
    so the three results whose statements do not mention [Hsr]/[Hrs] --
    [pare_split_law], [pare_tri_one], [pare_tri_two] -- carry an explicit
    [Proof using All].  (b) The whiskering notations [⊳] and [⊲] are at
    level 10 with arguments at level 9, so [G ⊳ pare_eps P] does not parse
    as intended; every whiskering below parenthesizes the application.
    (c) Writing a section abbreviation as [Let eps (a : A) : … := ε a]
    leaves a beta-redex [(λ a, …) a] in every exported statement; writing
    [Let eps : ∀ a : A, … := ε] instead, letting the [transform] coercion
    fire against the ascription, gives the same clean component type with
    no redex.  Both forms were tried; the second is what ships.

    AXIOMS.  All 83 constants declared here report "Closed under the
    global context": the 69 [def]/[prf]/[proj]/[rec] entries of the [.glob],
    the 13 [Program] obligations the [.glob] does not record, and
    [Build_PareData], which appears in neither.  That is a one-time
    measurement made with [Print Assumptions] over all 83; NINETEEN of
    them are additionally carried PERMANENTLY by the [print-assumptions]
    make target, on which [check] depends, so the file IS wired into the
    gate.  (An earlier revision of this sentence said it was not wired
    into any make target; that was false of its own commit.)

    NOT DELIVERED.  No round trip in either direction and at any strength;
    no uniqueness of the left adjoint (the tree's [left_adjoint_iso] is not
    instantiated -- it is Theory/Adjunction.v:407, in the hom-set
    presentation, which this file never enters); no hom-set [⊣] reading
    (Adjunction/Natural/Transformation/Universal.v converts, and that
    conversion is not performed here); no [PareData] with a nontrivial
    idempotent, hence no non-degenerate exercise of the biconditional; no
    [IdempotentsSplit] instance for any functor category; no dual (right
    adjoint from the mirrored hypotheses); nothing relating [pare_idem] to
    the Karoubi envelope beyond consuming
    [Construction/Karoubi/Universal.v]'s [IdempotentsSplit] class; and no
    universe measurement of any kind. *)

Record PareData (A X : Category) := {
  pare_G : A ⟶ X;
  pare_K : X ⟶ A;
  pare_eps : pare_K ◯ pare_G ⟹ Id[A];
  pare_rho : Id[X] ⟹ pare_G ◯ pare_K;
  pare_triangle (a : A) :
    fmap[pare_G] (pare_eps a) ∘ pare_rho (pare_G a) ≈ id
}.

Arguments pare_G {_ _} _.
Arguments pare_K {_ _} _.
Arguments pare_eps {_ _} _.
Arguments pare_rho {_ _} _.
Arguments pare_triangle {_ _} _ _.

Section Pare.

Context {A X : Category}.
Context (P : PareData A X).

Let G := pare_G P.
Let K := pare_K P.
Let eps : ∀ a : A, K (G a) ~> a := pare_eps P.
Let rho : ∀ x : X, x ~> G (K x) := pare_rho P.

(* WHERE THE FRICTION IS, LOCATED RATHER THAN ASSERTED.  Mac Lane's
   Gε ∘ ρG and εK ∘ Kρ are not formable here (the header PARAPHRASES the
   elaborator -- the real message displays [pare_G P]/[pare_K P] where
   the header writes [G]/[K]; both types and the [cannot unify] pair
   match exactly, only the display is normalised).  The obstruction is
   that [Compose] is not associative on
   the nose and [Id] is not a strict unit for it -- but only in the LAW
   fields: [Functor] has exactly five fields, [fobj] and [fmap] agree at
   [eq_refl] below, and the whole records do not agree, so the difference
   is confined to the remaining three.  That step is sharp for a reason
   worth stating: [Functor] has primitive projections WITH ETA CONVERSION
   (Rocq reports this on [Print Functor]), so record equality IS field
   equality.  Test/ProbePare350.v turns the confinement from an inference
   into a MEASUREMENT, failing each of the three law fields
   individually.  Reading Theory/Functor.v's printed body confirms what
   those three are: [Compose_obligation_1..3] applied to different
   arguments, and [Unset Transparent Obligations] makes them opaque. *)
Example pare_assoc_fobj :
  @fobj A X ((G ◯ K) ◯ G) = @fobj A X (G ◯ (K ◯ G)) := eq_refl.
Example pare_assoc_fmap :
  @fmap A X ((G ◯ K) ◯ G) = @fmap A X (G ◯ (K ◯ G)) := eq_refl.
Example pare_unitor_fobj :
  @fobj A X (Id[X] ◯ G) = @fobj A X G := eq_refl.
Example pare_unitor_fmap :
  @fmap A X (Id[X] ◯ G) = @fmap A X G := eq_refl.

(* The four whiskered composites Mac Lane writes.  Each is formable on its
   own; it is only their vertical composites that are not. *)
Definition pare_Geps : G ◯ (K ◯ G) ⟹ G ◯ Id[A] := G ⊳ (pare_eps P).
Definition pare_rhoG : Id[X] ◯ G ⟹ (G ◯ K) ◯ G := (pare_rho P) ⊲ G.
Definition pare_epsK : (K ◯ G) ◯ K ⟹ Id[A] ◯ K := (pare_eps P) ⊲ K.
Definition pare_Krho : K ◯ Id[X] ⟹ K ◯ (G ◯ K) := K ⊳ (pare_rho P).

Example pare_Geps_at (a : A) :
  transform[pare_Geps] a = fmap[G] (eps a) := eq_refl.
Example pare_rhoG_at (a : A) :
  transform[pare_rhoG] a = rho (G a) := eq_refl.
Example pare_epsK_at (x : X) :
  transform[pare_epsK] x = eps (K x) := eq_refl.
Example pare_Krho_at (x : X) :
  transform[pare_Krho] x = fmap[K] (rho x) := eq_refl.

Lemma pare_tri (a : A) : fmap[G] (eps a) ∘ rho (G a) ≈ id.
Proof. exact (pare_triangle P a). Qed.

Lemma pare_rho_nat {x y : X} (f : x ~> y) :
  fmap[G] (fmap[K] f) ∘ rho x ≈ rho y ∘ f.
Proof. exact (naturality (pare_rho P) _ _ f). Qed.

Lemma pare_eps_nat {a b : A} (g : a ~> b) :
  g ∘ eps a ≈ eps b ∘ fmap[K] (fmap[G] g).
Proof. exact (naturality (pare_eps P) _ _ g). Qed.

(* ---------------------------------------------------------------------- *)
(** ** The idempotent εK ∘ Kρ *)

Lemma pare_idem_natural {x y : X} (f : x ~> y) :
  fmap[K] f ∘ (eps (K x) ∘ fmap[K] (rho x))
    ≈ (eps (K y) ∘ fmap[K] (rho y)) ∘ fmap[K] f.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_idem : K ⟹ K := {|
  transform := λ x, eps (K x) ∘ fmap[K] (rho x)
|}.
Next Obligation. apply pare_idem_natural. Qed.
Next Obligation. symmetry; apply pare_idem_natural. Qed.

Example pare_idem_at (x : X) :
  transform[pare_idem] x
    = transform[pare_epsK] x ∘ transform[pare_Krho] x := eq_refl.

Lemma pare_eps_absorb (a : A) :
  eps a ∘ (eps (K (G a)) ∘ fmap[K] (rho (G a))) ≈ eps a.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_tri.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_idem_idem (x : X) :
  (eps (K x) ∘ fmap[K] (rho x)) ∘ (eps (K x) ∘ fmap[K] (rho x))
    ≈ eps (K x) ∘ fmap[K] (rho x).
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[K] (rho x)) (eps (K x)) (fmap[K] (rho x))).
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (eps (K (G (K x))))).
  rewrite comp_assoc.
  rewrite pare_eps_absorb.
  reflexivity.
Qed.

Definition pare_idem_Idempotent : @Idempotent ([X, A]) K pare_idem.
Proof. constructor; intro x; apply pare_idem_idem. Qed.

(* ---------------------------------------------------------------------- *)
(** ** From a splitting to a left adjoint *)

Section FromSplitting.

Context (F : X ⟶ A).
Context (r : K ⟹ F) (s : F ⟹ K).
Context (Hsr : ∀ x, s x ∘ r x ≈ pare_idem x).
Context (Hrs : ∀ x, r x ∘ s x ≈ id).

(* [Hsr] unfolded to the components of εK ∘ Kρ; the two statements are
   convertible, so this is [Hsr] itself with no proof step. *)
Lemma pare_split_law (x : X) :
  s x ∘ r x ≈ eps (K x) ∘ fmap[K] (rho x).
Proof using All. exact (Hsr x). Qed.

Definition pare_unit : Id[X] ⟹ G ◯ F := (G ⊳ r) ∙ (pare_rho P).
Definition pare_counit : F ◯ G ⟹ Id[A] := (pare_eps P) ∙ (s ⊲ G).

Example pare_unit_at (x : X) :
  transform[pare_unit] x = fmap[G] (r x) ∘ rho x := eq_refl.
Example pare_counit_at (a : A) :
  transform[pare_counit] a = eps a ∘ s (G a) := eq_refl.

Lemma pare_s_nat {x y : X} (h : x ~> y) :
  fmap[K] h ∘ s x ≈ s y ∘ fmap[F] h.
Proof. exact (naturality s _ _ h). Qed.

Lemma pare_tri_one (x : X) :
  (eps (F x) ∘ s (G (F x))) ∘ fmap[F] (fmap[G] (r x) ∘ rho x) ≈ id.
Proof using All.
  rewrite <- comp_assoc.
  rewrite <- pare_s_nat.
  rewrite fmap_comp.
  (* the next two are not a no-op: they change which subterm the following
     rewrite matches first. *)
  rewrite <- comp_assoc.
  rewrite comp_assoc.
  rewrite <- pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (eps (K x)) (fmap[K] (rho x)) (s x)).
  rewrite <- pare_split_law.
  rewrite <- comp_assoc.
  rewrite Hrs.
  rewrite id_right.
  rewrite Hrs.
  reflexivity.
Qed.

Lemma pare_tri_two (a : A) :
  fmap[G] (eps a ∘ s (G a)) ∘ (fmap[G] (r (G a)) ∘ rho (G a)) ≈ id.
Proof using All.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[G] (s (G a))) (fmap[G] (r (G a))) (rho (G a))).
  rewrite <- fmap_comp.
  rewrite pare_split_law.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite pare_rho_nat.
  rewrite (comp_assoc (fmap[G] (eps (K (G a))))).
  rewrite pare_tri.
  rewrite id_left.
  rewrite pare_tri.
  reflexivity.
Qed.

Definition pare_Adjunction : F ∹ G := {|
  unit             := pare_unit;
  counit           := pare_counit;
  counit_fmap_unit := λ x, pare_tri_one x;
  fmap_counit_unit := λ a, pare_tri_two a
|}.

Example pare_Adjunction_unit :
  unit[pare_Adjunction] = pare_unit := eq_refl.
Example pare_Adjunction_counit :
  counit[pare_Adjunction] = pare_counit := eq_refl.
Example pare_Adjunction_unit_at (x : X) :
  transform[unit[pare_Adjunction]] x = fmap[G] (r x) ∘ rho x := eq_refl.
Example pare_Adjunction_counit_at (a : A) :
  transform[counit[pare_Adjunction]] a = eps a ∘ s (G a) := eq_refl.

End FromSplitting.

(* ---------------------------------------------------------------------- *)
(** ** From a left adjoint to a splitting *)

Section FromAdjunction.

Context (F : X ⟶ A).
Context (Adj : F ∹ G).

Let eta : ∀ x : X, x ~> G (F x) := unit[Adj].
Let del : ∀ a : A, F (G a) ~> a := counit[Adj].

Lemma pare_eta_nat {x y : X} (h : x ~> y) :
  fmap[G] (fmap[F] h) ∘ eta x ≈ eta y ∘ h.
Proof. exact (naturality unit[Adj] _ _ h). Qed.

Lemma pare_del_nat {a b : A} (g : a ~> b) :
  g ∘ del a ≈ del b ∘ fmap[F] (fmap[G] g).
Proof. exact (naturality counit[Adj] _ _ g). Qed.

Lemma pare_adj_tri_one (x : X) : del (F x) ∘ fmap[F] (eta x) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Adj x). Qed.

Lemma pare_adj_tri_two (a : A) : fmap[G] (del a) ∘ eta (G a) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ Adj a). Qed.

Lemma pare_r_natural {x y : X} (h : x ~> y) :
  fmap[F] h ∘ (eps (F x) ∘ fmap[K] (eta x))
    ≈ (eps (F y) ∘ fmap[K] (eta y)) ∘ fmap[K] h.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_eta_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_r : K ⟹ F := {|
  transform := λ x, eps (F x) ∘ fmap[K] (eta x)
|}.
Next Obligation. apply pare_r_natural. Qed.
Next Obligation. symmetry; apply pare_r_natural. Qed.

Lemma pare_s_natural {x y : X} (h : x ~> y) :
  fmap[K] h ∘ (del (K x) ∘ fmap[F] (rho x))
    ≈ (del (K y) ∘ fmap[F] (rho y)) ∘ fmap[F] h.
Proof.
  rewrite comp_assoc.
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_s : F ⟹ K := {|
  transform := λ x, del (K x) ∘ fmap[F] (rho x)
|}.
Next Obligation. apply pare_s_natural. Qed.
Next Obligation. symmetry; apply pare_s_natural. Qed.

Lemma pare_eps_of_s (a : A) :
  eps a ∘ (del (K (G a)) ∘ fmap[F] (rho (G a))) ≈ del a.
Proof.
  rewrite comp_assoc.
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_tri.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_del_of_r (a : A) :
  del a ∘ (eps (F (G a)) ∘ fmap[K] (eta (G a))) ≈ eps a.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_adj_tri_two.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_split_rs (x : X) :
  (eps (F x) ∘ fmap[K] (eta x)) ∘ (del (K x) ∘ fmap[F] (rho x)) ≈ id.
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[K] (eta x)) (del (K x)) (fmap[F] (rho x))).
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (del (K (G (F x))))).
  rewrite comp_assoc.
  rewrite pare_eps_of_s.
  rewrite pare_adj_tri_one.
  reflexivity.
Qed.

Lemma pare_split_sr (x : X) :
  (del (K x) ∘ fmap[F] (rho x)) ∘ (eps (F x) ∘ fmap[K] (eta x))
    ≈ eps (K x) ∘ fmap[K] (rho x).
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[F] (rho x)) (eps (F x)) (fmap[K] (eta x))).
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_eta_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (eps (F (G (K x))))).
  rewrite comp_assoc.
  rewrite pare_del_of_r.
  reflexivity.
Qed.

Program Definition pare_SplitIdempotent : @SplitIdempotent ([X, A]) K F := {|
  split_idem   := pare_idem;
  split_idem_r := pare_r;
  split_idem_s := pare_s
|}.
Next Obligation. apply pare_split_sr. Qed.
Next Obligation.
  rewrite pare_split_rs.
  symmetry; apply fmap_id.
Qed.

End FromAdjunction.

(* ---------------------------------------------------------------------- *)
(** ** The biconditional, and the Cauchy-complete corollary *)

Definition PareSplits : Type :=
  ∃ (F : X ⟶ A) (S : @SplitIdempotent ([X, A]) K F),
    @split_idem ([X, A]) K F S ≈ pare_idem.

Definition PareLeftAdjoint : Type := ∃ F : X ⟶ A, F ∹ G.

Definition pare_adjunction_of_split (F : X ⟶ A)
           (S : @SplitIdempotent ([X, A]) K F)
           (HS : @split_idem ([X, A]) K F S ≈ pare_idem) : F ∹ G.
Proof.
  refine (pare_Adjunction F (@split_idem_r ([X, A]) K F S)
                            (@split_idem_s ([X, A]) K F S) _ _).
  - intro x.
    transitivity (@split_idem ([X, A]) K F S x).
    + exact (@split_idem_sr ([X, A]) K F S x).
    + exact (HS x).
  - intro x.
    transitivity (fmap[F] (@id X x)).
    + exact (@split_idem_rs ([X, A]) K F S x).
    + apply fmap_id.
Defined.

(* The wrapper does not lose the prescribed unit and counit: what it feeds
   [pare_Adjunction] is the splitting's own retraction and section, and the
   two proof arguments do not appear in either field. *)
Example pare_adjunction_of_split_unit (F : X ⟶ A)
        (S : @SplitIdempotent ([X, A]) K F)
        (HS : @split_idem ([X, A]) K F S ≈ pare_idem) :
  unit[pare_adjunction_of_split F S HS]
    = pare_unit F (@split_idem_r ([X, A]) K F S) := eq_refl.

Example pare_adjunction_of_split_counit (F : X ⟶ A)
        (S : @SplitIdempotent ([X, A]) K F)
        (HS : @split_idem ([X, A]) K F S ≈ pare_idem) :
  counit[pare_adjunction_of_split F S HS]
    = pare_counit F (@split_idem_s ([X, A]) K F S) := eq_refl.

Definition pare_splits_of_adjunction (F : X ⟶ A) (Adj : F ∹ G) : PareSplits.
Proof.
  refine (existT _ F (existT _ (pare_SplitIdempotent F Adj) _)).
  reflexivity.
Defined.

Theorem pare_left_adjoint_iff_splits : PareLeftAdjoint ↔ PareSplits.
Proof.
  split.
  - intros [F Adj].
    exact (pare_splits_of_adjunction F Adj).
  - intros [F [S HS]].
    exact (existT _ F (pare_adjunction_of_split F S HS)).
Defined.

Definition pare_splits_of_CauchyComplete
           (HS : CauchyComplete ([X, A])) : PareSplits :=
  @split_of ([X, A]) HS K pare_idem pare_idem_Idempotent.

Definition pare_left_adjoint_of_CauchyComplete
           (HS : CauchyComplete ([X, A])) : PareLeftAdjoint :=
  snd pare_left_adjoint_iff_splits (pare_splits_of_CauchyComplete HS).

End Pare.

(* ---------------------------------------------------------------------- *)
(** ** Inhabitation *)

(* Every adjunction is Paré data: forget one of its two triangles.  This is
   a record literal with no tactic -- [pare_triangle]'s type is literally
   [fmap_counit_unit]'s.  It also says exactly how degenerate such data is:
   [pare_of_adjunction_idem] shows the idempotent is then the identity, by
   the OTHER triangle, so a splitting is available for free and nothing is
   learned.  This exercises the hypotheses and not a nontrivial splitting;
   no [PareData] whose idempotent is provably not an identity is exhibited
   anywhere below. *)
Definition pare_of_adjunction {A X : Category} {F : X ⟶ A} {G : A ⟶ X}
           (Adj : F ∹ G) : PareData A X := {|
  pare_G        := G;
  pare_K        := F;
  pare_eps      := counit[Adj];
  pare_rho      := unit[Adj];
  pare_triangle := λ a, @fmap_counit_unit _ _ _ _ Adj a
|}.

Lemma pare_of_adjunction_idem {A X : Category} {F : X ⟶ A} {G : A ⟶ X}
      (Adj : F ∹ G) (x : X) : pare_idem (pare_of_adjunction Adj) x ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Adj x). Qed.

(* A uniform family -- not a closed term, and never instantiated here at
   a concrete category: everything the identity on a category. *)
Program Definition pare_triv_rho (C : Category) : Id[C] ⟹ Id[C] ◯ Id[C] :=
  {| transform := λ _, id |}.

Program Definition pare_triv_eps (C : Category) : Id[C] ◯ Id[C] ⟹ Id[C] :=
  {| transform := λ _, id |}.

Program Definition pare_triv (C : Category) : PareData C C := {|
  pare_G   := Id[C];
  pare_K   := Id[C];
  pare_eps := pare_triv_eps C;
  pare_rho := pare_triv_rho C
|}.

Lemma pare_triv_idem (C : Category) (x : C) :
  pare_idem (pare_triv C) x ≈ id.
Proof. simpl; cat. Qed.

(* The assembly run end to end on that inhabitant: the identity idempotent
   splits by identities, and what comes back out is Id ∹ Id. *)
Definition pare_triv_left_adjoint (C : Category) : Id[C] ∹ Id[C].
Proof.
  refine (pare_Adjunction (pare_triv C) Id[C] nat_id nat_id _ _).
  - intro x; simpl; cat.
  - intro x; simpl; cat.
Defined.
