Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.

Open Scope category_scope.

Generalizable All Variables.

(** * Exponentials of presheaves: [C^op, Sets] is cartesian closed *)

(* Book:      Awodey, Category Theory (1st ed., Carnegie Mellon
              pre-print, September 2005), §8.7 "Exponentials in
              categories of diagrams", display (8.5) and Proposition
              8.13, printed p. 208, and Theorem 8.14, printed p. 209
              ([awodey:8.7:def-presheaf-exponential], [awodey:8.7:prop13],
              [awodey:8.7:thm14]).  Verbatim, from the rendered pages:

                "If we had such an exponential Q^P, we could compute its
                 value at any object C ∈ C by Yoneda:

                     Q^P(C) ≅ Hom(yC, Q^P)

                 And if it's to be an exponential, then we must also
                 have:

                     Hom(yC, Q^P) ≅ Hom(yC × P, Q)

                 But this latter set does exist.  Thus, we can just
                 define:

                     Q^P(C) = Hom(yC × P, Q)                      (8.5)

                 with the action on h : C' → C being:

                     Q^P(h) = Hom(yh × 1_P, Q)

                 This is clearly a contravariant, set-valued functor on
                 C.  Let us now check that it indeed gives an exponential
                 of P and Q."

                "Proposition 8.13.  For any objects X, P, Q in Sets^{C^op},
                 there is an isomorphism, natural in X,

                     Hom(X, Q^P) ≅ Hom(X × P, Q)"

                "Theorem 8.14.  For any small category C, the category of
                 diagrams Sets^{C^op} is cartesian closed."

   Book:      Riehl, Category Theory in Context, 2nd ed., §4.4,
              printed pp. 152-153 ([riehl:4.4:lem11]).  Verbatim:

                "Lemma 4.4.11.  For any small category C, the functor
                 category Set^C is cartesian closed."

                "Proof.  Given functors F, G : C → Set our aim is to
                 define a functor G^F : C → Set so that there is a
                 natural bijection between sets of natural
                 transformations

                 (4.4.12)          {H × F ⇒ G} ≅ {H ⇒ G^F}

                 for all functors H : C → Set.  To define the value of
                 G^F on an object c, we define

                 (4.4.13)   G^F(c) := {C(c, −) × F ⇒ G} ≅ {C(c, −) ⇒ G^F}

                 so that the desired bijection can be given by the Yoneda
                 lemma."

                "There is a formal reason why the natural bijection
                 (4.4.12) follows from the special case (4.4.13) (see
                 Exercise 6.5.iii) but this bijection can also be
                 demonstrated directly by providing formulas for adjoint
                 transposition."

                "Given α : H × F ⇒ G, its transpose is the natural
                 transformation β : H ⇒ G^F defined for c ∈ C and x ∈
                 Hc by declaring β_c(x) : C(c, −) × F ⇒ G to be the
                 natural transformation whose component at d ∈ D is the
                 function that takes f : c → d and z ∈ Fd to the element
                 α_d((H f)x, z).  These operations can be seen to be
                 natural in all of the variables mentioned and inverses."

   Book:      Riehl, ibid., §6.5 Exercise 6.5.iii, printed p. 248
              ([riehl:6.5:exiii]).  Verbatim:

                "Exercise 6.5.iii.  Use Theorem 6.5.7 to give a second
                 proof of Lemma 4.4.11, showing that the desired natural
                 isomorphism follows from the definition of the internal
                 hom."

   nLab:      https://ncatlab.org/nlab/show/exponential+object
   nLab:      closed+monoidal+structure+on+presheaves (same site), which
              states exactly [X,Y](c) = Hom(y(c) × X, Y)
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   WHAT IS DELIVERED.  [Functor_Category_Closed C], an [#[export]
   Program Instance] of type

       @Closed ([C^op, Sets])
         (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)

   for an ARBITRARY category C -- at the universe levels measured below,
   which is where Awodey's word "small" lands -- together with
   [presheaf_exp_iso], Proposition 8.13 as an isomorphism of hom-setoids
   in [Sets], and [to_exp_natural_X] / [from_exp_natural_X], its
   naturality in X in both directions.  The exponential object is the
   display-(8.5) formula and nothing else: [PshExp_obj P Q c] IS the
   hom-setoid of the presheaf category at the representable-times-P, and
   [exp_obj_is_display85] reads that back at [eq_refl].

   The terminal half is #339's and is NOT rebuilt: [presheaf_terminal] is
   [Functor_Category_Terminal Sets_Terminal] specialised to [C^op] and
   [Sets], with [presheaf_terminal_is_donor] reading that back at
   [eq_refl].  With [Functor_Category_Cartesian] for binary products,
   that is Theorem 8.14's first clause in this library's own vocabulary.

   Riehl's Set^C is the COVARIANT functor category and Awodey's
   Sets^{C^op} is the contravariant one; here the passage between them
   costs no proof, since [(C^op)^op = C] holds by [eq_refl] in this tree,
   so [Functor_Category_Closed_cov] is [Functor_Category_Closed] at the
   opposite category supplied by [:=] with no tactic and no transport.
   It is annotated like the instance, and measured to sit at the same
   universes ([∀ C : Category@{o h h}, Closed@{so h u}] with the same
   block); left unannotated it minimizes to [Category@{u0 u0 u0}] and is
   refused at the very C where the instance is accepted, so the
   covariant reading would otherwise have been delivered at a strictly
   narrower class of categories than the contravariant one.

   WHICH ROUTE WAS TAKEN, AND WHY IT IS NOT MERELY A MATTER OF TASTE.
   The DIRECT route: Riehl's explicit formulas for adjoint transposition,
   quoted above.  Nothing below requires Category.Functor.Hom.Yoneda or
   Category.Functor.Hom.Yoneda.Natural, and the Yoneda step of Riehl's
   proof -- her "the desired bijection can be given by the Yoneda lemma"
   -- is discharged in [to_from_exp] by the OUTER transformation's own
   [naturality] field plus one identity law.

   That choice has a MEASURED consequence.  [Yoneda_Lemma] and
   [yoneda_natural_pre] are declared over [Category@{u0 u0 u0}], object
   universe identified with hom and with proof, and at a C whose objects
   sit strictly BELOW its homs they are refused, while the display-(8.5)
   object, [PshExp], [presheaf_exp_iso] and [Functor_Category_Closed] are
   all accepted at that very C.  So a route through the Yoneda LEMMA
   would have narrowed the theorem from Awodey's hypothesis to a strictly
   stronger one.  Both halves of that measurement are pinned in
   Test/ProbePresheafExp718.v -- the two refusals against seven positive
   controls at those very levels.

   THE BOOK'S OWN ROUTE GOES THROUGH DENSITY, and it is not taken.
   Awodey proves Proposition 8.13 by writing X as a colimit of
   representables (his Proposition 8.10) and then commuting that colimit
   past [− × P] (his Lemma 8.12).  Proposition 8.10 IS in tree, in the
   presheaf orientation, as Theory/Density.v's [presheaf_density]; it is
   cited by path here and deliberately not required.  Lemma 8.12 is NOT
   in tree, and the two constants in
   Instance/Sets/Cartesian/Closed/Adjunction.v that look like it do not
   serve: [Sets_prod_preserves_colimits] is at [Sets] and not at a
   functor category, and [CCC_prod_preserves_colimits] takes a [Closed]
   structure as a HYPOTHESIS and derives colimit-preservation from the
   currying adjunction, so applying it at a presheaf category before this
   file exists would be circular.  That reading is off those two
   constants' TYPES and is not a compiled experiment.  Riehl's Exercise
   6.5.iii asks for exactly that density proof; it is recorded here as
   the alternative and is not delivered.

   UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK with
   [Set Printing Universes].

     Functor_Category_Closed@{o h so u} : ∀ C : Category@{o h h},
                                            Closed@{so h u}
       block: h < so, h < u, o <= h, o <= so, plus stdlib bounds.

     presheaf_exp_iso@{u u0 u1 u2} :
       ∀ {C : Category@{u u0 u0}} (X P Q : C^op ⟶ Sets@{u0 u1}), ...
       block: u0 < u1, u0 < u2, u <= u0, u <= u1, plus stdlib bounds.

   Read three things off that.

   (1) The OBJECT universe is FREE of the hom universe -- bounded above
   by it, never identified.  That bound (C's objects at or below the
   carrier universe of [Sets]) IS Awodey's "for any small category C",
   and it is NEW relative to the presheaf category itself, which carries
   only the hom identification.  Its mechanism is
   Theory/Natural/Transformation.v's [Transform], whose result type is
   [Type@{max(o1,p2)}]: a set of natural transformations is a family
   indexed by the OBJECTS of the source, so those objects must fit where
   the target's hom-sets live.  Construction/Elements/Kan.v's [KanNat]
   and [KanCone] carry the same bound with the same attribution and its
   header works the point out; the precedent is followed here, including
   its refusal to claim the bound unavoidable.  It is NOT claimed
   unavoidable here either, and no attempt is made to restate the
   theorem at a coarser level.

   (2) THE UNIVERSE ANNOTATIONS ARE LOAD-BEARING, and that is measured
   rather than assumed.  Written with NO annotation at all -- no binder
   list, [C : Category] bare and [Sets] bare -- the same body elaborates
   at [∀ C : Category@{u0 u0 u0}], object, hom AND proof identified, a
   minimization artifact, and is then refused at a C whose objects sit
   strictly below its homs, where the shipped instance is accepted.  The
   probe carries that clone and pins the refusal against the shipped
   instance.  Read the attribution narrowly, because it was measured one
   annotation at a time: with the binder [Category@{o h h}] on C kept
   and [Sets@{h so}] dropped, the object universe stays free ([o <= h],
   with [so] then unused); and with [Sets@{h so}] kept and C bare it
   stays free as well (a fresh level bounded by [h]).  So EITHER
   annotation alone blocks the collapse and it is their joint absence
   that produces it; neither is decorative, and the pair is kept so that
   the levels the instance is stated at carry names.  The trailing [+]
   is required, and the reason is the STATEMENT, not [Program]: without
   it the elaborator reports an unbound universe, and the TYPE alone --
   with no [Program] and no obligation -- is refused the same way, taking
   four further levels once [+] is supplied (measured).

   (3) HOM = PROOF in the binder is the donors' doing, not this file's.
   [Opposite] and [Fun] each refuse a C whose hom universe is declared
   strictly below its proof universe, with no reference to the other,
   while [@Functor C Sets] is ACCEPTED at those very levels -- so
   [Functor] is not a donor.  Both refusals and that control are pinned.

   One further reading, because it is easy to get backwards: [PshExp]
   taken ALONE lands in a possibly LARGER [Sets] than the one its
   arguments take values in (its binder reads [C^op ⟶ Sets@{u0 u1} →
   C^op ⟶ Sets@{u0 u1} → C^op ⟶ Sets@{u3 u2}] with [u0 <= u3]).  It is
   [presheaf_exp_iso]'s STATEMENT -- which forces the exponential to be
   an object of the same presheaf category -- that collapses [u3] to
   [u0], and with it produces the smallness bound.  No [Set] occurs in
   the binder or the block of any constant in this file.  The twelve
   constants of section F -- [one_exp_to], [one_from_comp],
   [one_exp_from], [one_exp_iso] and their obligations -- carry block
   EQUATIONS identifying the two [1^op]-presheaves' universe triples
   with each other ([u = u2], [u0 = u3], [u1 = u4]; the two
   [one_from_comp] constants the first two only), reported and not
   attributed; the other thirty-four constants carry none.

   WHAT EACH CONSTANT CONSUMES.  Each entry names the SUBSTANTIVE input;
   the structural step every equation in [Sets] takes -- [proper_morphism]
   of a [SetoidMorphism], to descend to the pair's two components -- is
   used throughout and is not repeated per entry.

     PshExp            fmap_respects: respectfulness of composition in C
                       in its left argument, a rewrite with the
                       hypothesis after unfolding [op]; fmap_comp:
                       associativity in C.
                       fmap_id is discharged by the file's default
                       obligation tactic and is not written out.
     to_exp_inner      the component's respectfulness is fmap_respects of
                       X; the naturality square is naturality of alpha
                       followed by fmap_comp of X.
     to_exp            fmap_comp of X and nothing further -- in
                       particular NO naturality of alpha and no lemma
                       about [Curried_CoHom], the representable's action
                       having already reduced away (see the [first] note
                       below).
     from_exp          naturality of the INNER transformation, naturality
                       of beta, and the identity laws.
     from_to_exp       exactly fmap_id of X.
     to_from_exp       exactly naturality of beta and one identity law.
                       This is Riehl's Yoneda step.
     ump_exponents'    fmap_respects then fmap_id of the presheaf, to
                       normalise [op id ∘ id] to [id].

   A MEASURED SPELLING NOTE.  Awodey's [y h × 1_P] is written with
   [first] rather than with [split _ id].  Both elaborate at the same
   printed type and the two are NOT convertible, which the probe pins;
   [first] is chosen because in the pointwise-cartesian presheaf category
   its identity factor leaves NO [fmap[P] id] residue, so the second
   component of the pair passes through untouched.  The probe carries
   that reduction as two [eq_refl] controls.  WHY it reduces was not
   isolated, and no claim is made about it.

   STRICT VERSUS [≈], MEASURED STRICT FIRST.  FIVE identifications are
   shipped as [Example ... := eq_refl], and that is the whole count of
   [eq_refl] statements in the file: the display-(8.5) object action;
   the class's [exponent_obj] IS [PshExp]; [curry'] IS [to_exp];
   [uncurry'] IS [from_exp]; and [presheaf_terminal] IS the #339 donor.
   A sixth fact is definitional although its statement is written with
   [≈], as every morphism equation here is: the FROM direction of
   naturality in X closes by [reflexivity], where the TO direction costs
   exactly one appeal to the naturality field of the transformation
   being precomposed, in its [naturality_sym] orientation.

   Exactly one identification comes out at [≈] and not at [eq_refl], and
   its cause is exhibited rather than guessed.  Riehl's counit formula
   ev_c(γ, y) = γ_c(id_c, y) is [eval_is_at_identity]; the [eq_refl] form
   is REFUTED and pinned as a conversion negative.  The reason is that
   [eval'] is [uncurry' id] and the identity of a functor category has
   component [fmap[−] id] rather than [id], so the value reduces to
   γ_c(op id ∘ id, y) and the residue is exactly one identity law,
   [id ∘ id ≈ id], an instance of [id_left] and of [id_right] alike.
   Repairing it would mean changing [nat_id], which is not on the table.

   NON-VACUITY, IN TWO DIRECTIONS.

     At C := 1 the construction recovers [Sets_Closed]'s exponential:
     [one_exp_iso] is an isomorphism in [Sets] between the value of
     [PshExp P Q] at the unique object and [Sets]' own exponential of the
     two values.  The backward leg needs a [match] on the object rather
     than a plain function, because [obj[1]] is [poly_unit], which has no
     eta here: written pointwise, the second projection of the pair
     elaborates at the wrong object and the definition is rejected.

     At C := _2 the conditional theorem of Instance/Fun/Closed.v becomes
     unconditional.  That file's Section AwodeyPointwise is stated for an
     arbitrary [@Closed ([_2^op, Sets]) CC], and its own header records
     that nothing in tree witnessed that hypothesis; this instance does,
     so [awodey_pointwise_not_exponential_unconditional] and
     [pq_point_distinct_unconditional] land there with no hypothesis
     outstanding.  DISCLOSE THE PIN: [_2] is declared with its homs at the
     literal [Set] and [Fun] identifies source and target hom universes,
     so that corollary is about presheaves valued in setoids whose carrier
     lives in [Set].  The pin is [_2]'s, is inherited, and is not
     introduced here.

   PRIOR ART, MEASURED BY SHAPE AS WELL AS BY NAME.  There was no
   [@Closed] structure on any functor category anywhere in this tree
   before this file.  READ THE CRITERION, because the count moves with
   it: sweeping the lines that ASSIGN [exponent_obj] (the two new files
   excluded) returns fifteen, of which two are prose inside comments and
   one, Instance/Comp.v's [Algs_Closed], is a whole instance inside a
   block comment, leaving twelve live assignments; two of those belong
   to other classes ([SymMonClosed] in Instance/Mod/Closed.v,
   [ClosedMonoidal] in Structure/Monoidal/Internal/Product.v), leaving
   ten live for the [Closed] class, and not one of the ten -- nor the
   dead eleventh -- is over a functor category.
   Instance/Cat/Cartesian/Closed.v's [Cat_Closed] is the different claim
   that the exponential OBJECT in [Cat] is a functor category.  Every
   occurrence of [@Closed] at a functor category was a HYPOTHESIS, in
   Instance/Fun/Closed.v, whose [ccc_point] family CONSUMES a closed
   structure and so could not have proved this.

   Two Transform-valued functors into [Sets] already existed, neither
   an exponential: Construction/Elements/Kan.v's [KanNat], a presheaf,
   and Functor/Hom/Yoneda/Natural.v's [YoNat], a bifunctor out of a
   product category, BOTH pure assemblies of
   [Curried_Hom] composites with zero obligations and all three functor
   laws INHERITED, as each file's own comment says.  This file follows
   neither: [PshExp_obj] packages the hom-setoid by hand through
   Instance/Fun.v's notation, and [PshExp] is a hand-built [Program Definition]
   over separate plain definitions of the object and arrow actions, and
   its [fmap_respects] and [fmap_comp] are discharged explicitly, which is
   what the contravariance in the object argument -- the place where the
   objectwise formula gives the wrong object -- deserves.

   THE ISSUE'S "CURRENT STATE" IS STALE ON THREE COUNTS, all re-measured.
   [ls Instance/Fun/] was nine [.v] files before this one, not
   [Cartesian.v] alone; there IS a [@Terminal (@Fun _ _)] instance,
   #339's [Functor_Category_Terminal], which is consumed here; and its
   list of ten [Closed] instances omits Instance/Theory/Lindenbaum.v's
   [Lind_Closed], whose type wraps onto a second line and so escapes a
   one-line sweep, while counting Instance/Comp.v's [Algs_Closed], which
   sits inside a block comment; and its "[exponent_obj :=] occurs at 11
   sites" is fifteen lines, twelve of them live.  A sharper claim
   survives in each case, and each is stated above.  Four of its cited
   donor line numbers have also drifted (Instance/Fun.v's two,
   Functor/Hom/Yoneda.v's and Theory/Sheaf.v's).

   A NAMING HAZARD, RECORDED BECAUSE THE GATE IS WHERE IT WOULD BITE.
   The [print-assumptions] target loads many modules into ONE scope, and
   it already loads Instance/Cat/Exponential.v, so the SHORT module name
   [Exponential] is shared between that file and this one.  That is legal
   -- the kernel paths differ -- but nothing here may be referenced as
   [Exponential.<name>], and every gate entry for this file is written
   fully qualified.

   WHAT IS NOT DELIVERED -- read this as the scope of the file.

     * No naturality in P or in Q.  [PshExp] is not exhibited as a
       bifunctor [([C^op, Sets])^op ∏ [C^op, Sets] ⟶ [C^op, Sets]], so
       Awodey's "natural in X" is the only naturality proved.

     * No Lemma 8.12 and no density proof.  Riehl's Exercise 6.5.iii is
       cited above and no artifact answers it.

     * No [ElementaryTopos] for a presheaf category.  This supplies the
       cartesian-closure component of that assembly, the classifier
       component being Instance/Fun/Classifier.v's; nothing here joins
       them.

     * Nothing about the Yoneda embedding preserving products and
       exponentials -- Awodey's Theorem 8.14 second clause, which is his
       §8.9 Exercise 4 and a separate catalog item.

     * No general target D in place of [Sets].  The positive theorem for
       a complete cartesian closed D is not attempted, and
       Instance/Fun/Closed.v's counterexample shows the hypothesis on D
       is not decorative.

     * No comparison with [Cat_Closed], and no statement relating the
       exponential built here to the exponential of [Cat].

     * Nothing is registered as an [Instance] except
       [Functor_Category_Closed].  [presheaf_terminal] and
       [Functor_Category_Closed_cov] are plain definitions.

     * This file contributes NO lines to [make todo].  Its probe does,
       as every probe in this tree does, and that is disclosed rather
       than hidden. *)

(** ** A: the exponential presheaf -- Awodey display (8.5) *)

Section PshExpSec.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (P Q : C^op ⟶ Sets).

(* Display (8.5): Q^P(c) is the hom-setoid of the presheaf category at
   the representable on c times P.  Instance/Fun.v's [[[ , ]]]( , )
   notation packages exactly that as an object of [Sets]. *)
Definition PshExp_obj (c : C) : Sets :=
  [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q ).

(* Awodey's Q^P(h) = Hom(y h × 1_P, Q): precomposition with the
   representable's action on h, crossed with the identity of P.  The
   variance comes out on the nose with no transport, because
   [Curried_CoHom C] is [Curried_Hom C^op] and its source is [(C^op)^op],
   which is [C] definitionally: for [h : c ~{C^op}~> c'] the arrow
   [fmap[Curried_CoHom C] h] runs from the representable at [c'] to the
   representable at [c], which is the direction precomposition wants. *)
Definition PshExp_fmap (c c' : C) (h : c ~{C^op}~> c') :
  PshExp_obj c ~{Sets}~> PshExp_obj c'.
Proof.
  unshelve econstructor.
  - refine (fun alpha => nat_compose alpha _).
    exact (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
  - proper. exact (X x0 _).
Defined.

(* The two functor laws are PROVED, not inherited.  [fmap_id] is the one
   the default obligation tactic closes; a third [Next Obligation] is
   rejected for want of a goal. *)
Program Definition PshExp : C^op ⟶ Sets := {|
  fobj := PshExp_obj;
  fmap := PshExp_fmap
|}.
Next Obligation.
  proper.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; now rewrite X.
Qed.
Next Obligation.
  simpl; intros.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

End PshExpSec.

(** ** B: the transposition, both ways *)

Section Transpose.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X P Q : C^op ⟶ Sets).

(* Riehl's beta_c(x), component at d: the function taking f : c -> d and
   z in P d to alpha_d ((X f) x, z). *)
Program Definition to_exp_inner_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  (d : C^op) :
  fobj[@product_obj _ PshCart (Curried_CoHom C c) P] d ~{Sets}~> fobj[Q] d :=
  {| morphism := fun hp => alpha d (fmap[X] (fst hp) x, snd hp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl in *.
  apply proper_morphism; split; simpl;
    [ exact (@fmap_respects _ _ X _ _ _ _ Hu x) | exact Hv ].
Qed.

Definition to_exp_inner
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  : @product_obj _ PshCart (Curried_CoHom C c) P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_inner_comp alpha c x).
  - intros d e f hp; simpl.
    etransitivity;
      [ exact (@naturality _ _ _ _ alpha _ _ f
                 (fmap[X] (fst hp) x, snd hp)) | ].
    simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
    symmetry; exact (@fmap_comp _ _ X _ _ _ f (fst hp) x).
Defined.

Program Definition to_exp_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C^op) :
  fobj[X] c ~{Sets}~> fobj[PshExp P Q] c :=
  {| morphism := fun x => to_exp_inner alpha c x |}.
Next Obligation.
  intros u v Huv d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  now apply proper_morphism.
Qed.

(* Riehl's beta : H ==> G^F.  Awodey's transpose of Hom(X × P, Q) into
   Hom(X, Q^P). *)
Definition to_exp (alpha : @product_obj _ PshCart X P ⟹ Q)
  : X ⟹ PshExp P Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_comp alpha).
  - intros c c' f x d hp; simpl.
    apply proper_morphism; split; simpl; [ | reflexivity ].
    exact (@fmap_comp _ _ X _ _ _ (fst hp) f x).
Defined.

(* The counit route: alpha_c (x, p) = (beta_c x)_c (id_c, p), which is
   Riehl's ev composed with beta × F. *)
Program Definition from_exp_comp (beta : X ⟹ PshExp P Q) (c : C^op) :
  fobj[@product_obj _ PshCart X P] c ~{Sets}~> fobj[Q] c :=
  {| morphism := fun xp => (beta c (fst xp)) c (id[c], snd xp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl.
  etransitivity;
    [ exact (@proper_morphism _ _ _ _ (transform[beta] c) _ _ Hu c
               (id[c], snd u)) | ].
  apply proper_morphism; split; simpl; [ reflexivity | exact Hv ].
Qed.

Definition from_exp (beta : X ⟹ PshExp P Q)
  : @product_obj _ PshCart X P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (from_exp_comp beta).
  - intros c c' f xp; simpl.
    transitivity ((beta c (fst xp)) c' (f, fmap[P] f (snd xp))).
    + etransitivity;
        [ exact (@naturality _ _ _ _ (beta c (fst xp)) _ _ f
                   (id[c], snd xp)) | ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
    + etransitivity;
        [ | exact (@naturality _ _ _ _ beta _ _ f (fst xp) c'
                     (id[c'], fmap[P] f (snd xp))) ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
Defined.

(* One round trip is exactly [fmap_id] of X. *)
Lemma from_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  from_exp (to_exp alpha) ≈[[C^op, Sets]] alpha.
Proof.
  intros c xp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@fmap_id _ _ X c (fst xp)).
Qed.

(* The other is Riehl's Yoneda step, and it needs no Yoneda: the
   [naturality] field of beta at [fst hp], plus one identity law. *)
Lemma to_from_exp (beta : X ⟹ PshExp P Q) :
  to_exp (from_exp beta) ≈[[C^op, Sets]] beta.
Proof.
  intros c x d hp; simpl.
  symmetry.
  etransitivity;
    [ | exact (@naturality _ _ _ _ beta _ _ (fst hp) x d
                 (id[d], snd hp)) ].
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

(* Proposition 8.13 / Riehl (4.4.12), as an isomorphism of hom-setoids in
   [Sets].  Only the two isomorphism laws are written: the two
   respectfulness obligations are closed by the default tactic. *)
Program Definition presheaf_exp_iso :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp P Q )) := {|
  to   := {| morphism := to_exp |};
  from := {| morphism := from_exp |}
|}.
Next Obligation. exact (to_from_exp x x0 x1 x2 (h, c)). Qed.
Next Obligation. exact (from_to_exp x x0 (c, c0)). Qed.

End Transpose.

(** ** C: naturality in X -- Awodey's "And these isos are clearly
       natural in X" *)

Section NaturalX.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X X' P Q : C^op ⟶ Sets).

(* One appeal to the naturality field of g -- its [naturality_sym]
   orientation -- and nothing else. *)
Lemma to_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (alpha : @product_obj _ PshCart X P ~{[C^op, Sets]}~> Q) :
  to_exp X' P Q (alpha ∘[[C^op, Sets]] @first _ PshCart _ _ P g)
    ≈[[C^op, Sets]] to_exp X P Q alpha ∘[[C^op, Sets]] g.
Proof.
  intros c x d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@naturality_sym _ _ _ _ g _ _ (fst hp) x).
Qed.

(* The other direction is DEFINITIONAL: [reflexivity] closes it. *)
Lemma from_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (beta : X ~{[C^op, Sets]}~> PshExp P Q) :
  from_exp X' P Q (beta ∘[[C^op, Sets]] g)
    ≈[[C^op, Sets]] from_exp X P Q beta
                      ∘[[C^op, Sets]] @first _ PshCart _ _ P g.
Proof.
  intros c xp; simpl.
  reflexivity.
Qed.

End NaturalX.

(** ** D: Theorem 8.14, first clause *)

(* The universe binders are load-bearing and the trailing [+] is
   required; see the header.  [ump_exponents'] is the one written
   obligation: its goal normalises [op id ∘ id] to [id] by
   [fmap_respects] and then applies [fmap_id]. *)
#[export] Program Instance Functor_Category_Closed@{o h so +}
  (C : Category@{o h h}) :
  @Closed ([C^op, Sets@{h so}])
    (@Functor_Category_Cartesian (C^op) Sets@{h so} Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(* Riehl's Set^C, the covariant reading of the same theorem: a [:=] with
   no tactic and no transport, since [(C^op)^op] is [C].  Annotated like
   the instance so that it is delivered at the same universes; written
   unannotated it minimizes to [Category@{u0 u0 u0}] and is refused where
   the instance is accepted (measured; the probe pins the annotated form
   as a control at that very C). *)
Definition Functor_Category_Closed_cov@{o h so +} (C : Category@{o h h}) :
  @Closed ([C, Sets@{h so}])
    (@Functor_Category_Cartesian C Sets@{h so} Sets_Cartesian) :=
  Functor_Category_Closed (C^op).

(* The terminal presheaf is #339's, specialised.  With
   [Functor_Category_Cartesian] this completes the finite-product half of
   Theorem 8.14. *)
Definition presheaf_terminal (C : Category) : @Terminal ([C^op, Sets]) :=
  @Functor_Category_Terminal (C^op) Sets Sets_Terminal.

(** ** E: readbacks *)

Section Readbacks.
Context {C : Category}.
Context (X P Q : C^op ⟶ Sets).

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* Awodey display (8.5) on the nose. *)
Example exp_obj_is_display85 (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's exponential IS the presheaf built above. *)
Example exponent_obj_is_PshExp :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

(* The class's transposes ARE the two maps built above. *)
Example curry_is_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  @curry' _ _ (Functor_Category_Closed C) X P Q alpha = to_exp X P Q alpha
  := eq_refl.

Example uncurry_is_from_exp (beta : X ⟹ PshExp P Q) :
  @uncurry' _ _ (Functor_Category_Closed C) X P Q beta = from_exp X P Q beta
  := eq_refl.

(* Riehl's counit formula, at [≈] and not at [eq_refl]; see the header
   for the residue and the probe for the refutation. *)
Lemma eval_is_at_identity (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy).
Proof.
  simpl; apply proper_morphism; split; simpl;
    [ unfold op; cat | reflexivity ].
Qed.
End Readbacks.

Example presheaf_terminal_is_donor (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(** ** F: at C := 1 the construction recovers [Sets_Closed] *)

Section AtOne.
Context (P Q : _1^op ⟶ Sets).

#[local] Notation OneCart :=
  (@Functor_Category_Cartesian (_1^op) Sets Sets_Cartesian).

Program Definition one_exp_to :
  fobj[PshExp P Q] ttt
    ~{Sets}~> @exponent_obj Sets Sets_Cartesian Sets_Closed
                 (fobj[P] ttt) (fobj[Q] ttt) :=
  {| morphism := fun alpha => {| morphism := fun p => alpha ttt (ttt, p) |} |}.
Next Obligation.
  proper.
  apply proper_morphism; split; simpl; [ reflexivity | assumption ].
Qed.

(* The [match] is forced: [obj[1]] is [poly_unit], which has no eta here,
   so a component written as a plain function elaborates its second
   projection at the wrong object and the definition is rejected. *)
Program Definition one_from_comp
  (g : @exponent_obj Sets Sets_Cartesian Sets_Closed
         (fobj[P] ttt) (fobj[Q] ttt)) (d : obj[_1^op])
  : fobj[@product_obj _ OneCart (Curried_CoHom _1 ttt) P] d
      ~{Sets}~> fobj[Q] d :=
  match d with
  | ttt => {| morphism := fun hp => g (snd hp) |}
  end.
Next Obligation. proper. now apply proper_morphism. Qed.

Program Definition one_exp_from :
  @exponent_obj Sets Sets_Cartesian Sets_Closed (fobj[P] ttt) (fobj[Q] ttt)
    ~{Sets}~> fobj[PshExp P Q] ttt :=
  {| morphism := fun g => {| transform := one_from_comp g |} |}.
Next Obligation.
  destruct x, y, f, p; simpl.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation.
  destruct x, y, f, p; simpl.
  symmetry.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation. proper; destruct x0; exact (X H). Qed.

Program Definition one_exp_iso :
  @Isomorphism Sets (fobj[PshExp P Q] ttt)
    (@exponent_obj Sets Sets_Cartesian Sets_Closed
       (fobj[P] ttt) (fobj[Q] ttt)) :=
  {| to := one_exp_to; from := one_exp_from |}.
Next Obligation. destruct x0, p; reflexivity. Qed.
End AtOne.
