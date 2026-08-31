(** * The components functor and its right adjoint *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Construction.Comma.Special.

Generalizable All Variables.

(* Book:      Mac Lane, "Categories for the Working Mathematician",
              Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
              (maclane:IV.2:ex9), where the result is attributed to
              N. Smythe.
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
              printed p. 35 (connected categories) and §4.1
   nLab:      https://ncatlab.org/nlab/show/connected+component
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   nLab:      https://ncatlab.org/nlab/show/adjoint+string
   nLab:      https://ncatlab.org/nlab/show/reflective+subcategory
   nLab:      https://ncatlab.org/nlab/show/Cat
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Mac Lane's exercise asks for the adjoint string carried by the functor
   sending a category to its set of objects:

     Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

   This file delivers the LEFTMOST adjunction, [Pi0 ⊣ Cat_Disc], and it
   delivers it OVER A DIFFERENT PAIR OF CATEGORIES from the one its
   right-hand neighbour lives over.  That is the file's principal
   finding and §7 proves the half of it that is provable; the rest of
   this header says exactly which half.

   Delivered here:

     (a) [Cat_Disc : Sets ⟶ Cat], the discrete functor.  This is the
         FIRST functor of that type in the tree, and the claim is a
         measurement by TYPE rather than by name: no constant of type
         [Sets ⟶ Cat] or [Sets ⟶ StrictCat] is declared in any `.v`
         file, the only occurrences of those two tokens being prose --
         Theory/Connected/Components.v:293 recording the absence, and
         Instance/Indiscrete.v's item II anticipating this file by
         name.  The only [Cat ⟶ Sets] is [Pi0] itself.

     (b) [pi0_adj_iso], the hom-setoid isomorphism, and the packaged
         record [Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc].

     (c) [Cat_Disc_Full], [Cat_Disc_Faithful], and [pi0_counit_iso] --
         the counit is an isomorphism, which is Mac Lane's "the
         components of a discrete category are its objects" and which
         exhibits [Sets] as a REFLECTIVE subcategory of [Cat] with
         reflector π₀.

     (d) The refutation that fixes the right adjoint:
         [DiscreteCat_carrier_not_functorial], with its general form
         [no_skeletal_carrier_functor_Sets_Cat] and the discriminating
         [Cat_Disc_not_skeletal].

     (e) Non-vacuity over [Roof]: [Pi0_not_Faithful] and
         [unit_not_Full], so π₀ genuinely forgets and the adjunction is
         not an equivalence.

   I. A PRIOR-ART CORRECTION, ON THREE COUNTS, EACH MEASURED.

      FIRST, the catalog issue's work item 4 asks that the
      connected-components functor be defined.  That is FALSE.
      Theory/Connected/Components.v:579 declares [Pi0 : Cat ⟶ Sets]
      with [fobj := pi0] and [fmap := pi0_fmap], and proves its three
      functor laws.  It is CONSUMED here and nothing rebuilds it: the
      names [pi0], [pi0_fmap], [ZigZag], [hom_zigzag] and [zigzag_fmap]
      are used exactly as that file and Structure/Groupoid/Connected.v
      declare them, and this file declares no zig-zag machinery of its
      own.  What was missing is the ADJUNCTION, and that absence is
      recorded in the donor's own NOT-delivered list, at
      Theory/Connected/Components.v:292-293: "NO LEFT ADJOINT.
      [Pi0 : Cat ⟶ Sets] is built, but the discrete functor
      [Sets ⟶ Cat] and the adjunction π₀ ⊣ discrete are not."  That
      standing deferral is what this file discharges.

      SECOND, the discrete category on a SETOID already exists too:
      Construction/Comma/Special.v:218's [DiscreteSetoidCat], built
      there so that the comma of two constant functors could be
      identified.  It is CONSUMED here and gets its first consumer
      outside its own file (measured: before this commit the token
      [DiscreteSetoidCat] occurred in exactly one `.v` file).  What was
      absent is its arrow action and any functor built on it; both are
      new here, and the arrow action is three lines, since a morphism of
      [DiscreteSetoidCat S] IS a proof of [≈] and [proper_morphism] IS
      the required action on it.

      THIRD, the same correction the sibling module records applies:
      Instance/Discrete/Reconstruct.v:416's [Indiscrete] exists.  It
      plays no part below -- the indiscrete half of Mac Lane's string is
      the OTHER wing -- and is named here only so that this header does
      not appear to contradict the sibling's.

   II. THE STRING SPLITS, AND THE SPLIT IS NOT A NAMING ACCIDENT.

      Instance/Cat/Objects.v settles the middle adjunction over
      [StrictCat] and [Coq], and both of its settlements are forced by
      refutation: no objects functor exists over [Cat] into a
      Leibniz-comparing target (its §6,
      the swap endofunctor of [Indiscrete bool] being [≈] to the
      identity in [Cat] while their object maps differ), and no
      carrier-based object map [Sets → StrictCat] respects [≈] (its §7).
      Its discrete functor is therefore [StrictCat_Disc : Coq ⟶
      StrictCat], built on Instance/Discrete.v's [DiscreteCat].

      [Pi0] shares NEITHER end with that: its source is [Cat] and its
      target is [Sets].  So [Pi0 ⊣ Cat_Disc] is a statement about a
      different pair of categories, and Mac Lane's four adjoints do not
      form one string in this library -- they exist as TWO strings of
      two, meeting nowhere.  Instance/Indiscrete.v's [adjoint_string]
      packages the other one, and packages only two components for
      exactly this reason; the three headers agree, and each says so.
      (That file is cited by NAME rather than by line: it landed
      alongside this one and its line numbers were still moving.)

      What is PROVED here rather than observed is the sharper half: even
      after moving to [Cat] and [Sets], the right adjoint CANNOT be the
      plain discrete category.  [DiscreteCat_carrier_not_functorial]
      (§7) refutes the [fmap_respects] field of the only candidate,
      exhibiting [bool] under the everywhere-true setoid, where
      [id ≈ negb] holds in [Sets] while a natural isomorphism between
      the induced functors would give [true = false].  So the two
      [Discrete]s of the string are different functors on different
      categories, not one functor described twice.

      SCOPE THAT CLAIM EXACTLY.  What is refuted is the carrier-based
      DISCRETE object map.  Nothing here proves that no [Coq]-valued π₀
      exists, nor that the two wings could not be reconciled by some
      construction not attempted here; the sibling module disclaims the
      same thing from its side.  The general form
      [no_skeletal_carrier_functor_Sets_Cat] says what the obstruction
      is: a right adjoint to π₀ whose objects are the CARRIER cannot have
      SKELETAL fibres.  [Cat_Disc] escapes it, and escapes it by exactly that
      clause -- [Cat_Disc_not_skeletal] proves the skeletality hypothesis is
      the one it fails, while [cat_disc_Kobj] and [cat_disc_Kinj] discharge
      the other two (the first at [eq_refl], the second by the identity
      function).  So the refutation is not vacuous and the escape is located
      rather than assumed.

      THIS FILE DOES NOT REQUIRE Instance/Cat/Objects.v, and the reason
      is measured rather than stylistic: importing it adds 24 modules to
      a 54-module closure (among them Instance/Coq.v, Theory/Monad.v and
      the eight Structure/Monoidal ones), and it would buy nothing, the
      two developments having no category in common.  Its refutations
      are therefore CITED above, not re-derived, and the citations are
      marked as citations.

      NAMING.  [Objects], [Discrete] and [Indiscrete] are all taken -- by
      Solver/Expr.v:38's reification class, by Structure/Discrete.v:33's
      predicate and by Instance/Discrete/Reconstruct.v:416's category
      respectively -- so the sibling module adopted the
      Instance/Top/Forgetful.v convention of prefixing with the structured
      category.  This file follows it: [Cat_Disc] for the functor into [Cat],
      reserving [Cat_Indisc] should the indiscrete half ever be wanted at this
      pair.  [Cat_Disc], [Cat_Disc_map], [disc_setoid_iso],
      [zigzag_setoid_contract], [pi0_to], [pi0_from], [pi0_adj_iso] and
      [Components_Disc_Adjunction] were each verified to have zero tree-wide
      occurrences first.

   III. STRENGTHS, MEASURED STRICT-FIRST.

      Ten readbacks hold at [eq_refl] and are shipped as [Example]s: the
      object action of [Cat_Disc], its object type and hom type
      ([cat_disc_obj], [cat_disc_obj_carrier], [cat_disc_hom]), the object
      action of its arrow action ([cat_disc_fmap]); both legs of the
      transposition ([pi0_adj_to_at], [pi0_adj_from_at]); THE UNIT IS THE
      IDENTITY FUNCTION ON THE NOSE ([pi0_unit_is_id]) and so is the counit
      ([pi0_counit_is_id]); and both legs of [pi0_counit_iso].  Four
      FURTHER [eq_refl]s appear below as CONTROLS localizing the two
      refuted round trips and the [Kobj] clause of §7 -- eighteen
      occurrences of [:= eq_refl] in all, of which four sit inside a
      [Fail] and are refutations rather than readbacks.

      NEITHER ROUND TRIP IS STRICT, AND THE TWO FAIL FOR DIFFERENT
      REASONS, EACH LOCALIZED BY A CONTROL.

      On the [Sets] side the residue is a CERTIFICATE.
      [pi0_rt_from_to_strict] is refuted at [eq_refl], while
      [pi0_rt_from_to_at] (the value at each point) and [pi0_rt_from_to_fn]
      (the whole [morphism] FIELD) both hold on the nose.  [SetoidMorphism] is
      a [Record] under [Set Primitive Projections] (Lib/Setoid.v:9,
      Instance/Sets.v:126), so it has eta and record equality IS field
      equality: what differs is therefore exactly [proper_morphism], which
      [pi0_from] rebuilds from [zigzag_setoid_contract].

      On the [Cat] side the residue is PROOF-RELEVANT DATA, and this is the
      sharper of the two.  [pi0_rt_to_from_strict] is refuted, and the OBJECT
      action returns on the nose ([pi0_rt_to_from_obj]) while the ARROW action
      does not ([pi0_rt_to_from_map], also refuted).  The cause is structural
      rather than incidental: a morphism of [DiscreteSetoidCat S] IS a proof
      of [≈], and two proofs of one [≈] need not be Leibniz-equal, so a round
      trip through that category cannot recover a proof term.

      AND THE [≈] THAT REPLACES IT IS VACUOUS, WHICH IS WORTH SAYING RATHER
      THAN GLOSSING.  [DiscreteSetoidCat]'s hom-setoid identifies ALL parallel
      arrows ([cat_disc_hom_trivial], proof [I]), so
      [pi0_rt_to_from_map_equiv] is [I] and holds of any two parallel arrows
      whatever -- it verifies nothing about the round trip.  The whole content
      of [iso_from_to] for [pi0_adj_iso] is therefore the OBJECT family, which
      is [eq_refl].  The same observation explains why the adjunction is so
      cheap: the naturality clause of [≈] in [Cat] is [True] at a thin target.

      THE ADJUNCTION RECORD COSTS TWO OBLIGATIONS IN TOTAL and both are
      in [pi0_adj_iso]'s two [Proper] fields; the two round trips of
      the isomorphism and both naturality clauses demanded by
      [Build_Adjunction'] are discharged by the ambient obligation
      tactic.  [Build_Adjunction'] (Theory/Adjunction.v:159) is used
      rather than [Build_Adjunction] for the same measured economy the
      sibling module records: it asks only for the two [to]-side
      clauses.

      NO ANALOGUE OF THE Instance/Top/Forgetful.v WALL ARISES.  That
      file's [Discrete ⊣ Forget ⊣ Indiscrete] for [Top] is forced into
      transposition isomorphisms because [Top]'s homs sit strictly above
      its points, so no single [Sets] serves both directions.  Here both
      functors run between one [Cat] and one [Sets] and the packaged
      record is built.  There IS a universe restriction, but it is a
      different one and it is the donor's; see the next item.

   IV. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER.

      EXACTLY ONE OF THE 73 CONSTRAINT BLOCKS CONTAINS A UNIVERSE EQUATION,
      and it is the PROBE of §8's third section, whose [hc = hd] is disclosed
      three paragraphs below.  Every entry of every other block is a [<] or a
      [<=]; that was checked constant by constant rather than sampled.
      [Cat_Disc@{u u0}], [pi0_to@{u u0}], [pi0_from@{u u0}], [pi0_adj_iso@{u
      u0}], [Cat_Disc_Full@{u u0}], [Cat_Disc_Faithful@{u u0}] and
      [Components_Disc_Adjunction@{u u0 u1}] all carry [u0 < u] -- which is
      [Sets]' own -- together with bounds against [compose], [projections] and
      [ID], and nothing else.

      TWO BLOCKS ARE LITERALLY EMPTY, AND FOR ONCE THAT IS NOT A TRAP:
      [disc_setoid_iso@{u u0}] and [zigzag_setoid_contract@{u u0}] have
      [(* u u0 |= *)], and their BINDERS read [Setoid@{u u0}] with the
      carrier and relation levels DISTINCT, so reading the block alone
      happens to give the right answer here.  It is recorded because the
      opposite case is the usual one.

      THE RESTRICTION IS THEREFORE NOT IN THE BLOCKS, AND IT IS REAL:
      [Pi0] accepts only categories whose object, hom and proof universes
      COINCIDE.  §8 guards this with a five-command chain that
      attributes it precisely.  At [C : Category@{co ch ch}] with
      [ch < co] declared, three controls succeed -- [C : obj[Cat]],
      [pi0 C], and [pi0_fmap] at that C -- and two commands are
      rejected: [pi0_fmap_respects] and, with it, [fobj[Pi0] C], both
      reporting "Cannot enforce ch = co because ch < co".  So the cause
      is neither [Cat], nor [pi0], nor the arrow action, but the single
      lemma [pi0_fmap_respects] (Theory/Connected/Components.v:538),
      which is declared over [Category@{u0 u0 u0}].

      THAT IDENTIFICATION IS MINIMIZATION AND NOT CONTENT, AND THE CLAIM
      IS GUARDED RATHER THAN ASSERTED.  §8's last section restates that
      lemma with its binders written out -- same statement, same
      one-line proof text -- inside a section declaring the two hom
      universes STRICTLY BELOW the object universe, and it is accepted
      there.  The repair belongs to the DONOR and is NOT performed here;
      the restatement is a probe, is marked as one, and nothing below
      uses it.  Note what the repair does NOT remove: it still carries
      [hc = hd], identifying the two categories' hom universes.

      Correspondingly, the control that the sibling module's §8 can
      offer -- its adjunction TYPE formable with the inner hom universe
      strictly below the inner object universe -- has NO analogue here,
      and that is stated rather than passed over: [Pi0] exposes two
      universe binders, the inner categories' levels are determined by
      them, and the [fobj[Pi0]] probe above says which categories that
      accepts.  A positive control at [Category@{cu cu cu}] shows the
      accepted class is inhabited and is not empty.

      One further identification is inherent rather than inherited and
      is named: the objects of [Sets@{o so}] are [SetoidObject@{o o}],
      carrier and relation at one level, so every category in the image
      of [Cat_Disc] has its objects and its homs at that same level.
      That is [Sets]' own declaration, not this file's.

      NO [Set] APPEARS IN ANY CONSTRAINT BLOCK OR BINDER OF THIS FILE
      -- but that is the result of a repair, not of luck, and the
      measurement that prompted it is worth carrying.  Written without
      binders, [roof_pt] elaborated at [Functor@{u Set Set u0 u1 u1}]
      and [disc_carrier_map] at [Functor@{u0 Set Set u0 Set Set}], both
      in the BINDER with Set-free blocks, and the pin propagated into
      the blocks of [Pi0_not_Faithful] ([Set < u], with [Pi0] itself
      instantiated at [Pi0@{u Set}]) and of
      [DiscreteCat_carrier_not_functorial].  All three donors are FREE
      -- [_1@{o h p}], [Roof@{u u0}] and [DiscreteCat@{o h p}] -- so the
      pin was MINIMIZATION at this file's own two unannotated
      definitions, of the family Construction/Free/Quiver/Examples.v
      records, and writing the binders out lifts it.  Refuting
      faithfulness at a Set-level instance would have sufficed to refute
      it outright, so the repair buys generality rather than
      correctness.

   V. AUDIT.  73 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
      ([Print Module] lists 73; the file declares no [Record], [Class]
      or [Inductive], so there is no unlisted [Build_*]; each was
      queried by fully qualified name, which is what reaches the 31
      [Program] obligations a [.glob] sweep cannot see -- 42 names are
      declared in the source and 42 + 31 = 73).  ZERO of the 73
      names collides anywhere in the tree -- a sweep that FOUND TEN, all
      of which were renamed away before this file landed, and two of
      which were live rather than cosmetic: Instance/Cat/Objects.v:524
      and :526 declare [Disc_Faithful] and [Disc_Full] as
      [#[export] Program Instance]s, so a [Print Assumptions Disc_Full]
      with both modules in one scope would have audited whichever was
      imported last.  The other eight were [disc_obj]
      (Functor/Construction/Postcompose.v:732), [disc_adj_iso],
      [disc_map], [adj_to_forgets], [adj_from_extends], [unit_is_id] and
      [BlurBool] (all Instance/Cat/Objects.v), and [counit_is_id]
      (Instance/Indiscrete.v).

      Six [Fail] probes of TWO KINDS kept lexically apart -- four
      CONVERSION in §4 and §7, reporting "cannot unify" with no universe
      clause, and two FORMABILITY in §8, reporting "universe
      inconsistency: Cannot enforce ch = co because ch < co" -- each
      stripped once and its kind read off the whole error message,
      beside an instrument check, six [Check] controls in §8, five
      [Example] controls beside the §4 negatives, and the two §2
      readbacks that control the §7 negative.
      Rename-simulated 5/5 on an unpadded denominator (the constants a
      NEGATIVE names: [pi0_adj_iso], [Cat_Disc], [DiscreteCat],
      [pi0_fmap_respects] and [Pi0]; the two file-local ones by the
      definition-site method, since a whole-file rename is a no-op),
      every one of them breaking the file at a non-[Fail] line.  That
      exercise FOUND a vacuous guard: [pi0_fmap_respects] was named only
      inside its own [Fail], so a rename of the donor would have turned
      that probe silently green; the control that closes it is the first
      command of §8's second section, and exists for that reason.

      The three section-local [Constraint] declarations were each tested
      by DELETION and they behave differently.  §8's first is
      LOAD-BEARING: without it [ch] unifies with [co] and both negatives
      succeed, so the file stops compiling.  §8's third pair is
      meaning-giving rather than load-bearing: the restated lemma
      elaborates without them, but then the levels could collapse and
      the command would demonstrate nothing.  Stated so that a later
      reader does not delete either as redundant.

   VI. WHAT IS NOT DELIVERED.

      No [Cat_Indisc] and no [Objects ⊣ Indiscrete] at this pair: the
      right-hand wing is the sibling development's, over its own two
      categories, and nothing here claims that wing exists.

      NO ADJOINT STRING.  The three adjunctions of Mac Lane's exercise
      are not exhibited as a chain, and by item II they cannot be at the
      constants this tree has; no comparison functor between [Cat] and
      [StrictCat], or between [Sets] and [Coq], is built or used.

      No [Coq]-valued π₀, and no impossibility proof for one.

      No uniqueness of the left or the right adjoint, no idempotency,
      no (co)monad induced by the adjunction, and nothing about
      preservation or creation of limits.

      No naturality of [pi0_counit_iso] in [A] beyond its being the counit
      of a built adjunction, and no comparison of [Cat_Disc] with
      Theory/Connected/Components.v's [ComponentSub] or
      [ConnectedComponent]: nothing here decomposes a category into its
      components.

      No invariance of π₀ under equivalence, which the donor's own
      NOT-delivered list already records as open, and no repair of
      [pi0_fmap_respects], whose universe identification is guarded in
      §8 and left to the donor.

      No functoriality of the construction in the AMBIENT category:
      neither [Pi0] nor [Cat_Disc] is related to any other category of
      categories, and no 2-categorical statement is attempted. *)

(** ** §1. The discrete category on a setoid: two small lemmas *)

(* An [≈] between two points of [DiscreteSetoidCat S] IS an arrow between
   them, so it is half of an isomorphism and symmetry supplies the other
   half.  Both inverse laws are equations in a thin category and are
   discharged by the ambient obligation tactic.  It is used three times
   below -- at the two [fmap_respects]-shaped obligations of §2 and §3,
   and again in §7's [Cat_Disc_not_skeletal] -- which is why it is
   factored out. *)
Program Definition disc_setoid_iso {A : Type} (S : Setoid A) {x y : A}
  (e : @equiv A S x y) : @Isomorphism (DiscreteSetoidCat S) x y :=
  {| to := e ; from := symmetry e |}.

(* The converse collapse: a zig-zag in [DiscreteSetoidCat S] contracts to
   a single [≈].  This is the only induction in the file, and it is the
   whole reason the backward transpose exists -- the [Sets]-morphism it
   produces must respect [ZigZag], and this is what turns a chain into
   the [≈] the target setoid wants.  Each of the three cases is one law
   of [S]: reflexivity, transitivity, and transitivity after symmetry. *)
Lemma zigzag_setoid_contract {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) : ZigZag x y → @equiv A S x y.
Proof.
  intro s; induction s.
  - reflexivity.
  - now transitivity y.
  - now transitivity y; [ symmetry |].
Qed.

(** ** §2. The discrete functor Sets ⟶ Cat *)

(* The arrow action.  Both the object and the arrow part are READ OFF a
   [Sets]-morphism: [fobj] is its underlying function and [fmap] is its
   [proper_morphism] certificate, since an arrow of the discrete category
   on a setoid is a proof of [≈].  All three functor laws are equations
   in a thin category and cost nothing. *)
Program Definition Cat_Disc_map {A B : Sets} (f : A ~> B) :
  DiscreteSetoidCat (is_setoid A) ⟶ DiscreteSetoidCat (is_setoid B) :=
  {| fobj := f
   ; fmap := fun x y (e : x ≈ y) => proper_morphism f x y e |}.

(* The functor.  Its ONE obligation is [fmap_respects]: two pointwise
   [≈]-equal [Sets]-morphisms induce naturally isomorphic functors, the
   component at [a] being [disc_setoid_iso] of the hypothesis at [a] and the
   naturality clause being [True].  [fmap_id] and [fmap_comp] are
   discharged by the ambient tactic for the same reason. *)
Program Definition Cat_Disc : Sets ⟶ Cat := {|
  fobj := fun A => DiscreteSetoidCat (is_setoid A)
; fmap := fun _ _ f => Cat_Disc_map f
|}.
Next Obligation.
  intros f g H.
  exists (fun a => disc_setoid_iso (is_setoid y) (H a)); intros; exact I.
Defined.

(* Four readbacks, all [eq_refl].  The second and third are the ones a
   consumer needs: the objects of the discrete category ARE the carrier
   and its homs ARE the setoid's own relation. *)
Example cat_disc_obj (A : Sets) :
  fobj[Cat_Disc] A = DiscreteSetoidCat (is_setoid A) := eq_refl.

Example cat_disc_obj_carrier (A : Sets) :
  obj[fobj[Cat_Disc] A] = carrier A := eq_refl.

Example cat_disc_hom (A : Sets) (x y : carrier A) :
  (x ~{fobj[Cat_Disc] A}~> y) = (x ≈ y) := eq_refl.

Example cat_disc_fmap (A B : Sets) (f : A ~> B) (a : carrier A) :
  fobj[fmap[Cat_Disc] f] a = f a := eq_refl.

(** ** §3. The transposition *)

(* Forward: a map on components extends to a functor.  Its object action
   IS the given map -- [carrier (pi0 C)] is [obj[C]] by
   Theory/Connected/Components.v's [pi0_carrier] -- and its arrow action
   is the map's own respectfulness certificate applied to the one-step
   chain [hom_zigzag f].  So no data is invented in this direction; the
   two ingredients are already present in the argument. *)
Program Definition pi0_to {C : Cat} {A : Sets}
  (h : fobj[Pi0] C ~{Sets}~> A) : C ~{Cat}~> fobj[Cat_Disc] A :=
  {| fobj := h
   ; fmap := fun x y (f : x ~> y) =>
       @proper_morphism _ _ _ _ h x y (hom_zigzag f) |}.

(* Backward: a functor into a discrete category restricts to a map on
   components.  Its underlying function is the functor's object action;
   the content is the ONE obligation, which is where [zigzag_fmap] and
   [zigzag_setoid_contract] are spent -- transport the chain along the functor,
   then contract it in the thin target. *)
Program Definition pi0_from {C : Cat} {A : Sets}
  (F : C ~{Cat}~> fobj[Cat_Disc] A) : fobj[Pi0] C ~{Sets}~> A :=
  {| morphism := fobj[F] |}.
Next Obligation.
  intros x y s.
  exact (zigzag_setoid_contract (is_setoid A) _ _ (zigzag_fmap F s)).
Defined.

(* The hom-setoid isomorphism.  Two obligations, both [Proper] fields;
   the two round trips are discharged by the ambient tactic, and §4
   records that the second of them is vacuous on arrows. *)
Program Definition pi0_adj_iso (C : Cat) (A : Sets) :
  @Isomorphism Sets
    {| carrier := @hom Sets (fobj[Pi0] C) A
     ; is_setoid := @homset Sets (fobj[Pi0] C) A |}
    {| carrier := @hom Cat C (fobj[Cat_Disc] A)
     ; is_setoid := @homset Cat C (fobj[Cat_Disc] A) |} :=
  {| to   := {| morphism := fun h => @pi0_to C A h |}
   ; from := {| morphism := fun F => @pi0_from C A F |} |}.
Next Obligation.
  intros h k H.
  exists (fun a => disc_setoid_iso (is_setoid A) (H a)); intros; exact I.
Defined.
Next Obligation. intros F G H a; exact (to (`1 H a)). Defined.

(** ** §4. The adjunction *)

(* Mac Lane's leftmost adjunction, packaged.  ZERO obligations: the two
   naturality clauses [Build_Adjunction'] asks for land in [Cat] at a
   thin target, where [≈] between functors is a family of isomorphisms
   together with a [True], and the object families agree definitionally. *)
Program Definition Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc :=
  Build_Adjunction' pi0_adj_iso _ _.

Example pi0_adj_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : C) :
  fobj[to (pi0_adj_iso C A) h] x = h x := eq_refl.

Example pi0_adj_from_at (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x : C) :
  from (pi0_adj_iso C A) F x = F x := eq_refl.

(* The unit and the counit are both the identity function -- on the nose.
   The unit is [C ⟶ Cat_Disc (Pi0 C)], the projection of an object to its
   component, and the carrier of [pi0 C] IS [obj[C]], so there is nothing
   for it to do on objects. *)
Example pi0_unit_is_id (C : Cat) (x : C) :
  fobj[@unit _ _ _ _ Components_Disc_Adjunction C] x = x := eq_refl.

Example pi0_counit_is_id (A : Sets) (a : carrier A) :
  @counit _ _ _ _ Components_Disc_Adjunction A a = a := eq_refl.

(* NEGATIVE 1 (CONVERSION).  The [Sets]-side round trip is not strict.
   Two controls localize the failure to a single field: the value at each
   point returns on the nose, and so does the whole [morphism] FIELD, so
   -- [SetoidMorphism] being a primitive-projection record with eta --
   what differs is exactly [proper_morphism], which [pi0_from] rebuilds. *)
Fail Example pi0_rt_from_to_strict (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) = h := eq_refl.

Example pi0_rt_from_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : carrier (fobj[Pi0] C)) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) x = h x := eq_refl.

Example pi0_rt_from_to_fn (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  @morphism _ _ _ _ (from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h))
    = @morphism _ _ _ _ h := eq_refl.

(* NEGATIVE 2 and NEGATIVE 3 (CONVERSION).  The [Cat]-side round trip is
   not strict either, and the cause is DIFFERENT: the object action does
   return on the nose (control), the ARROW action does not, and it cannot,
   because an arrow of [DiscreteSetoidCat S] is a PROOF of [≈] and the
   round trip manufactures a fresh one through [zigzag_setoid_contract]. *)
Fail Example pi0_rt_to_from_strict (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F) = F := eq_refl.

Example pi0_rt_to_from_obj (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  fobj[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] = fobj[F]
  := eq_refl.

Fail Example pi0_rt_to_from_map (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f = fmap[F] f
  := eq_refl.

(* ... and the [≈] that replaces it is VACUOUS, which the next two
   commands say together rather than separately: the first holds, and the
   second shows it holds of ANY two parallel arrows, so it verifies
   nothing about the round trip.  The content of [iso_from_to] here is
   the object family, which is [pi0_rt_to_from_obj]. *)
Example pi0_rt_to_from_map_equiv (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f ≈ fmap[F] f
  := I.

Example cat_disc_hom_trivial (A : Sets) (x y : carrier A)
  (p q : x ~{fobj[Cat_Disc] A}~> y) : p ≈ q := I.

(** ** §5. Cat_Disc is fully faithful; Sets is reflective in Cat *)

(* [Full] asks only for a section of [fmap] with no functoriality, and
   here the section is the reverse reading of §2: the underlying function
   of the recovered [Sets]-morphism is the functor's object action and
   its certificate is the functor's arrow action.  Its ONE obligation is
   that certificate, supplied by a one-step script rather than as a field
   for the reason Theory/Connected/Components.v:519 records at
   [sets_quot_proj] -- [Proper (equiv ==> equiv) fobj[F]] is CONVERTIBLE
   with the type of [fmap[F]], but the elaborator does not unfold
   [Proper] and [respectful] during unification, so the field assignment
   is rejected.  (Measured here too, at exactly that spot.)  [fmap_sur]
   is discharged by the ambient tactic. *)
Program Definition Cat_Disc_Full : Full Cat_Disc := {|
  prefmap := fun A B F => {| morphism := fobj[F] |}
|}.
Next Obligation. intros x y e; exact (fmap[F] e). Defined.

Definition Cat_Disc_Faithful : Faithful Cat_Disc.
Proof.
  unshelve econstructor.
  intros A B f g H a; exact (to (`1 H a)).
Defined.

(* Mac Lane's "the components of a discrete category are its objects",
   in the form that carries the most: the COUNIT is an isomorphism.  With
   [Cat_Disc_Full] and [Cat_Disc_Faithful] this exhibits [Sets] as a reflective
   subcategory of [Cat] with reflector π₀ -- the inclusion is the right
   adjoint and is fully faithful.

   Both legs are the identity function; the two obligations are the
   respectfulness of the backward leg (an [≈] IS an arrow, hence a
   one-step chain) and the [ZigZag x x] the second round trip asks for,
   which is the empty chain. *)
Program Definition pi0_counit_iso (A : Sets) :
  @Isomorphism Sets (fobj[Pi0] (fobj[Cat_Disc] A)) A :=
  {| to   := @counit _ _ _ _ Components_Disc_Adjunction A
   ; from := {| morphism := fun a : carrier A => a |} |}.
Next Obligation.
  intros x y e.
  exact (@hom_zigzag (DiscreteSetoidCat (is_setoid A)) x y e).
Defined.
Next Obligation. exact (zz_nil _). Defined.

Example pi0_counit_iso_to (A : Sets) (a : carrier A) :
  to (pi0_counit_iso A) a = a := eq_refl.

Example pi0_counit_iso_from (A : Sets) (a : carrier A) :
  from (pi0_counit_iso A) a = a := eq_refl.

(** ** §6. Non-vacuity: π₀ genuinely forgets *)

(* The constant functors out of the terminal category.  [Roof] is the
   walking span [RNeg ← RZero → RPos]: it is CONNECTED
   ([Roof_Connected], Structure/Groupoid/Connected.v:431), so π₀ merges
   its three objects, while [RoofHom RNeg RPos] is EMPTY
   ([RNeg_RPos_absurd], Instance/Roof.v:70), so [Roof] itself does not.
   That gap is what both refutations below exploit. *)
Program Definition roof_pt@{o h p ru rh} (r : Roof@{ru rh}) :
  _1@{o h p} ⟶ Roof@{ru rh} :=
  {| fobj := fun _ => r ; fmap := fun _ _ _ => id[r] |}.

Example roof_objs_distinct : RNeg <> RPos.
Proof. discriminate. Qed.

Example roof_pi0_merges :
  @equiv _ (fobj[Pi0] Roof) RNeg RPos := Roof_Connected RNeg RPos.

(* π₀ is not faithful: the two constant functors [_1 ⟶ Roof] at [RNeg]
   and at [RPos] have the SAME image under π₀ (both objects lie in one
   component) and are not [≈] in [Cat], since that would give an
   isomorphism [RNeg ≅ RPos] whose forward leg is an arrow that does not
   exist. *)
Theorem Pi0_not_Faithful : Faithful Pi0 → False.
Proof.
  intro H.
  destruct (@fmap_inj _ _ Pi0 H _1 Roof (roof_pt RNeg) (roof_pt RPos)
              (fun _ => Roof_Connected RNeg RPos)) as [iso _].
  exact (RNeg_RPos_absurd (to (iso ttt))).
Qed.

(* ... and the unit is not full, so the adjunction is not an equivalence.
   [Full]'s [prefmap] is a bare section, so applying it to the zig-zag
   arrow that exists upstairs manufactures the missing [Roof]-arrow
   directly.  Read the conclusion at exactly that strength: nothing here
   rules out an equivalence between [Roof] and some discrete category by
   OTHER maps, and no essential-surjectivity statement about [Cat_Disc]
   is proved. *)
Theorem unit_not_Full :
  Full (@unit _ _ _ _ Components_Disc_Adjunction Roof) → False.
Proof.
  intro H.
  exact (RNeg_RPos_absurd
           (@prefmap _ _ _ H RNeg RPos (Roof_Connected RNeg RPos))).
Qed.

(** ** §7. Why the right adjoint is not the plain discrete category *)

(* [bool] under the everywhere-true setoid.  This is the witness for both
   refutations: it makes [id] and [negb] equivalent as [Sets]-morphisms
   while keeping [true] and [false] Leibniz-distinct. *)
Program Definition blur_bool : Sets := {|
  carrier   := bool
; is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition blur_bool_negb : blur_bool ~{Sets}~> blur_bool :=
  {| morphism := negb |}.

Example blur_bool_id_equiv_negb : id[blur_bool] ≈ blur_bool_negb := fun _ => I.

(* The arrow action a carrier-based discrete functor would have to have:
   objects the CARRIER, arrows Leibniz equalities, so the action on
   arrows is [f_equal]. *)
Program Definition disc_carrier_map@{o so dh dp} {A B : Sets@{o so}}
  (f : A ~> B) :
  DiscreteCat@{o dh dp} (carrier A) ⟶ DiscreteCat@{o dh dp} (carrier B) :=
  {| fobj := f ; fmap := fun x y (e : x = y) => f_equal f e |}.

(* REFUTATION.  Its [fmap_respects] field is FALSE.  This is the theorem
   that separates the two [Discrete]s of Mac Lane's string: over [Sets]
   the right adjoint cannot be Instance/Discrete.v's [DiscreteCat] on the
   carrier, which is what the sibling development's [StrictCat_Disc] is
   built from. *)
Theorem DiscreteCat_carrier_not_functorial :
  (∀ (A B : Sets) (f g : A ~> B), f ≈ g →
     @equiv _ (@homset Cat (DiscreteCat (carrier A))
                           (DiscreteCat (carrier B)))
       (disc_carrier_map f) (disc_carrier_map g)) → False.
Proof.
  intro H.
  destruct (H blur_bool blur_bool id[blur_bool] blur_bool_negb (fun _ => I))
    as [iso _].
  exact (Bool.diff_true_false (to (iso true))).
Qed.

(* The general form, which says WHAT the obstruction is rather than
   exhibiting one instance of it: a functor [Sets ⟶ Cat] whose objects
   carry the points of the setoid injectively and naturally cannot have
   SKELETAL fibres.  [Kskel] is Theory/Skeleton.v:243's [Skeletal]
   predicate ([∀ x y : C, x ≅ y → x = y]) spelled out at each fibre;
   that module is not required here, so the hypothesis is written out
   rather than imported.

   Read the argument: [id ≈ negb] gives a natural isomorphism between the
   two induced functors; evaluating it at the point [true] and rewriting
   both ends by naturality turns it into [pt true ≅ pt false];
   skeletality makes that a Leibniz equality and injectivity finishes. *)
Theorem no_skeletal_carrier_functor_Sets_Cat
  (K : Sets ⟶ Cat)
  (pt : ∀ A : Sets, carrier A → obj[fobj[K] A])
  (Kobj : ∀ (A B : Sets) (f : A ~> B) (x : carrier A),
            fobj[fmap[K] f] (pt A x) = pt B (f x))
  (Kskel : ∀ (A : Sets) (x y : obj[fobj[K] A]), x ≅ y → x = y)
  (Kinj : ∀ (A : Sets) (x y : carrier A), pt A x = pt A y → x = y) :
  False.
Proof.
  destruct (@fmap_respects _ _ K blur_bool blur_bool
              id[blur_bool] blur_bool_negb (fun _ => I)) as [iso _].
  pose proof (iso (pt blur_bool true)) as I0.
  rewrite (Kobj blur_bool blur_bool id[blur_bool] true) in I0.
  rewrite (Kobj blur_bool blur_bool blur_bool_negb true) in I0.
  simpl in I0.
  exact (Bool.diff_true_false (Kinj blur_bool true false (Kskel _ _ _ I0))).
Qed.

(* ... and the refutation is not vacuous for [Cat_Disc]: it satisfies
   [Kobj] (at [eq_refl]) and [Kinj] (by the identity function), and fails
   EXACTLY [Kskel].  So the escape is located rather than assumed, and
   the general theorem is genuinely about the shape of the fibres. *)
Definition cat_disc_pt (A : Sets) : carrier A → obj[fobj[Cat_Disc] A] :=
  fun a => a.

Example cat_disc_Kobj (A B : Sets) (f : A ~> B) (x : carrier A) :
  fobj[fmap[Cat_Disc] f] (cat_disc_pt A x) = cat_disc_pt B (f x) := eq_refl.

Definition cat_disc_Kinj (A : Sets) (x y : carrier A) :
  cat_disc_pt A x = cat_disc_pt A y → x = y := fun e => e.

Theorem Cat_Disc_not_skeletal :
  (∀ (A : Sets) (x y : obj[fobj[Cat_Disc] A]), x ≅ y → x = y) → False.
Proof.
  intro Hskel.
  refine (Bool.diff_true_false (Hskel blur_bool true false _)).
  exact (disc_setoid_iso (is_setoid blur_bool) I).
Qed.

(* NEGATIVE 4 (CONVERSION).  The two discrete categories are not even
   convertible, which pins at the level of terms what the refutation
   above establishes at the level of theorems.  The controls are
   [cat_disc_obj] and [cat_disc_obj_carrier] in §2: the object TYPES do
   agree. *)
Fail Example disc_is_DiscreteCat (A : Sets) :
  fobj[Cat_Disc] A = DiscreteCat (carrier A) := eq_refl.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file.  Every negative above
   and below was additionally stripped once and its failure kind read off
   the whole error message -- four CONVERSION failures in §4 and §7,
   reporting "cannot unify" with no universe clause, and two FORMABILITY
   failures here, reporting "universe inconsistency: Cannot enforce ...".
   The two kinds are kept lexically apart. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* Section-local [Universes]/[Constraint] declarations do not leak; the
   Instance/Fun/Group.v precedent applies, so these probes live in the
   library file beside the constants they guard rather than in [Test/].

   FIRST, the restriction and its attribution.  The [Constraint] here is
   LOAD-BEARING and that was measured by deletion: without it [ch]
   unifies with [co] and both negatives succeed.

   The three controls run down the chain and each removes one candidate
   culprit.  [C : obj[Cat]] shows the ambient category of categories is
   innocent -- it accepts a category whose homs sit STRICTLY BELOW its
   objects.  [pi0 C] shows the object map is innocent.  [pi0_fmap] at
   that same C shows the arrow map is innocent.  What is left is
   [pi0_fmap_respects] (Theory/Connected/Components.v:538), declared over
   [Category@{u0 u0 u0}], and it is rejected -- as is [fobj[Pi0] C] with
   it, on the same message.  So [Pi0], and hence every constant of this
   file that mentions it, accepts only categories whose object, hom and
   proof universes COINCIDE. *)
Section Pi0Restriction.
  Universes co ch.
  Constraint ch < co.
  Context (C D : Category@{co ch ch}).

  Check (C : obj[Cat]).
  Check (pi0 C).
  Check (fun F : C ⟶ D => pi0_fmap F).

  Fail Check (fun (F G : C ⟶ D) => @pi0_fmap_respects C D F G).
  Fail Check (fobj[Pi0] C).
End Pi0Restriction.

(* SECOND, the accepted class is inhabited: at a category with all three
   universes at one level [pi0_fmap_respects], [Pi0] and the
   transposition are all formable, so the restriction above cuts rather
   than empties.  There is no [Constraint] here and none is wanted.

   The first control here exists because a rename simulation FOUND A
   VACUOUS GUARD: [pi0_fmap_respects] was named only inside its own
   [Fail], so a rename of the donor would have turned that negative
   silently green.  Naming it in a command that must SUCCEED closes
   that. *)
Section Pi0Accepted.
  Universes cu.
  Context (C : Category@{cu cu cu}).
  Check (fun (F G : C ⟶ C) => @pi0_fmap_respects C C F G).
  Check (fobj[Pi0] C).
  Check (fun A : Sets => pi0_adj_iso C A).
End Pi0Accepted.

(* THIRD, and this is the guard item IV promised: the identification is
   MINIMIZATION AND NOT CONTENT.  The donor's lemma is restated here with
   its binders written out -- same statement, same one-line proof text,
   nothing else changed -- inside a section declaring BOTH categories'
   hom universes STRICTLY BELOW their object universe, and it is
   accepted.  The [Constraint]s are meaning-giving rather than
   load-bearing: the [Lemma] would elaborate without them, but then the
   levels could collapse and the command would demonstrate nothing.

   This is a PROBE.  The repair belongs to
   Theory/Connected/Components.v:538 and is NOT performed here; nothing
   in this file uses the restatement, and no claim is made that [Pi0]
   itself would then be free, which would require rebuilding it.  Note
   also what the repair does not remove: the restated lemma still carries
   [hc = hd] in its own constraint block, identifying the two categories'
   hom universes with each other. *)
Section Pi0RespectsRepairable.
  Universes o hc hd so.
  Constraint hc < o.
  Constraint hd < o.

  Lemma probe_pi0_fmap_respects_annotated
    {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F G : C ⟶ D)
    (H : F ≈ G) : @pi0_fmap@{o so hc hd} C D F ≈ pi0_fmap G.
  Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.
End Pi0RespectsRepairable.
