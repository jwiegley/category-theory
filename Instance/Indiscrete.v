(** * The indiscrete functor and the right half of Smythe's adjoint string *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Cat.Objects.

Generalizable All Variables.

(* Book:      Mac Lane, "Categories for the Working Mathematician",
              Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
              (maclane:IV.2:ex9), where the result is attributed to
              N. Smythe.
   nLab:      https://ncatlab.org/nlab/show/indiscrete+category
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   nLab:      https://ncatlab.org/nlab/show/adjoint+string
   nLab:      https://ncatlab.org/nlab/show/adjoint+triple
   nLab:      https://ncatlab.org/nlab/show/strict+category
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Mac Lane's exercise asks for the adjoint string carried by the functor
   that sends a category to its set of objects:

     Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

   Instance/Cat/Objects.v builds the objects functor, settles the two
   categories, and proves the MIDDLE adjunction.  This file builds the
   RIGHT-HAND wing on top of it: the indiscrete (codiscrete, chaotic)
   functor and [StrictCat_Objects ⊣ StrictCat_Indisc].  With the two
   together, three of Mac Lane's four terms are in place and the fourth
   is shown -- there, not here -- not to belong to this string at all
   (item II).

   Delivered here:

     (a) [indisc_lift]: the co-extension of a function [obj[C] → A] to a
         functor [C ⟶ Indiscrete A].  This is the exact mirror of
         Instance/Cat/Objects.v's [disc_ext], and like it, it is what
         the functor's arrow action is BUILT from rather than an extra
         construction: [obj[Indiscrete A]] IS [A] definitionally
         ([indisc_obj_carrier], §4), so [fmap[StrictCat_Indisc] f] is
         literally [indisc_lift f].

     (b) [StrictCat_Indisc : Coq ⟶ StrictCat], the indiscrete functor --
         the ARROW ACTION that the tree's [Indiscrete] object map has
         never had (item I).

     (c) [indisc_adj_iso], the hom-setoid isomorphism, and the packaged
         record [Objects_Indisc_Adjunction], of type
         [StrictCat_Objects ⊣ StrictCat_Indisc].  As on the left wing,
         no analogue arises of the universe wall that
         Instance/Top/Forgetful.v meets for the corresponding [Top]
         triple; what DOES arise here, and does not there, is a [Set]
         pin inherited from the donor (item V).

     (d) [adjoint_string]: the two adjunctions packaged as one term, so
         that the string is a single artifact rather than two files that
         happen to compile.

     (e) [Indisc_Full] and [Indisc_Faithful]: the indiscrete functor is
         fully faithful, the categorical reading of the fact that the
         COUNIT of this adjunction is the identity function
         ([indisc_counit_is_id], §4) -- the mirror of Objects.v's
         [Disc_Full]/[Disc_Faithful] and of the left wing's unit.

     (f) [disc_indisc_not_iso] and [disc_indisc_not_eq]: the two adjoints
         of the objects functor genuinely differ, and not merely up to
         presentation -- [DiscreteCat bool] and [Indiscrete bool] are not
         isomorphic in [StrictCat].

     (g) [ind_to_disc_constant] and [no_identity_functor_ind_to_disc]:
         why the string stops here on the right, stated at the strength
         it is actually proved (item VII).

   I. A PRIOR-ART CORRECTION, INHERITED AND EXTENDED.

      The catalog issue states that the indiscrete half "has no
      construction at all -- searching for it finds only comments".  That
      is FALSE, and Instance/Cat/Objects.v's item I already records it:
      Instance/Discrete/Reconstruct.v:416 has declared
      [Indiscrete (A : Type) : Category], with [hom := fun _ _ => unit],
      [homset := Morphism_equality] and every category law discharged by
      the ambient obligation tactic, since it was written.  It is
      CONSUMED here and NOTHING REBUILDS IT -- [StrictCat_Indisc]'s
      [fobj] is that constant by name, and [indisc_obj] records the fact
      by [eq_refl].

      What this file supplies is the part that genuinely was missing, and
      Objects.v states it precisely: [Indiscrete] was an OBJECT MAP ONLY.
      Its three prior consumers -- Theory/Skeleton/Separation.v,
      Instance/Cat/Pullback.v:539 (whose [IB := Indiscrete bool] drives
      [FibreProduct_not_Cat_pullback]) and Instance/Cat/Objects.v:§6
      (whose [SwapI] drives [objects_not_functorial_over_Cat]) -- all
      three use it on OBJECTS alone, and each of the latter two uses it
      for a REFUTATION turning on the same fact, that [Cat] cannot tell
      [true] from [false] there.  No arrow action, no functor and no
      adjunction for it existed anywhere.  Those are (a), (b), (c).

      Three further files match a name search and are NOT consumers, so
      that a later reader repeating the search is not misled:
      Instance/Top.v has an unrelated [Section Indiscrete] about the
      indiscrete TOPOLOGY, and Instance/Top/Forgetful.v and
      Instance/Cat/Components.v mention the word in prose only.

      A SECOND, SMALLER PIECE OF PRIOR ART IS DISCLOSED IN PLACE RATHER
      THAN DUPLICATED SILENTLY: §10's [ind_bool_iso] is
      Theory/Skeleton/Separation.v:76's [Indiscrete_iso] -- already
      general in both the type and the two points -- specialized at
      [bool].  That module is not required, for a measured reason: it
      would add TEN modules to this file's 49-module closure, among them
      [Instance/Fun.v], which is in neither this closure nor
      [Instance/Cat.v]'s.  The comment at that definition names the
      donor; nothing there is claimed new.

   II. THE DOMAIN IS INHERITED, AND THE CODOMAIN DECISION WAS ALREADY
      PROVED BINDING ON THIS WING.

      Instance/Cat/Objects.v settles both ends by refutation rather than
      by taste, and this file adds nothing to that argument and repeats
      none of it.  The source must be [StrictCat], because
      [objects_not_functorial_over_Cat] refutes the [fmap_respects]
      obligation that an objects functor owes over [Cat] WHEN ITS TARGET
      COMPARES OBJECT MAPS BY LEIBNIZ EQUALITY (an isomorphism-setoid
      objects functor on [Cat] does exist; see that file's §6).  The target
      must be [Coq], because [no_carrier_functor_Sets_StrictCat] refutes
      it for any pointed, injective, natural object map
      [obj[Sets] → obj[StrictCat]] -- and THAT THEOREM IS ALREADY
      INSTANTIATED AT THE INDISCRETE OBJECT MAP THERE, as
      [ind_carrier_not_Sets_functor].  So the right adjoint's codomain
      was fixed before this file existed, and the work of fixing it is
      not redone here.

      CONSEQUENCE FOR THE FOURTH ADJOINT, REPEATED BECAUSE IT IS WHAT
      "as far as it goes" IN §6 MEANS.  [Pi0] (Theory/Connected/
      Components.v:579) runs [Cat ⟶ Sets] and shares NEITHER end with
      [StrictCat_Objects : StrictCat ⟶ Coq]; by the source refutation it
      cannot be restricted and re-aimed, since there is no objects
      functor over [Cat] to be adjoint to.  So [adjoint_string] has two
      components and not three, and the leftmost adjunction is a
      separate statement over a different pair of categories.

      IT IS NOW A STATEMENT THAT EXISTS.  Instance/Cat/Components.v,
      landed alongside this file, delivers [Pi0 ⊣ Cat_Disc] with
      [Cat_Disc : Sets ⟶ Cat] -- confirming the separation by
      construction rather than by prediction, since its discrete functor
      is not [StrictCat_Disc] and could not be: the two run between
      different categories.  Mac Lane's four terms therefore exist in
      the tree as TWO strings of two, meeting nowhere, and
      [adjoint_string] packages only the pair that shares its
      categories.  NOTHING IN ANY OF THE THREE FILES PROVES that no
      [Coq]-valued π₀ exists; that question is left open in all of
      them.

      NAMING.  [StrictCat_Indisc] is the name Instance/Cat/Objects.v
      reserved for this functor, on the Instance/Top/Forgetful.v
      precedent (prefix = the structured category, whichever way the
      functor runs).  The obvious short names were unavailable there and
      remain so: [Indiscrete] is the category constructor of item I,
      [Discrete] is Structure/Discrete.v:33's predicate (required here,
      and used once, in [disc_indisc_not_eq]), and [Objects] is
      Solver/Expr.v:38's reification class.

   III. WHAT IS CONSUMED, AND WHAT IS BUILT.

      CONSUMED, not rebuilt: Instance/Discrete/Reconstruct.v's
      [Indiscrete] and [Indiscrete_bool_Discrete_absurd];
      Instance/Cat/Objects.v's [StrictCat_Objects], [StrictCat_Disc],
      [disc_ext], [Disc_Objects_Adjunction] and [indiscrete_hom_eq] --
      that last one is the little lemma "any two elements of [unit] are
      equal", declared there for the [Cat] refutation and used here in
      every single obligation, so the two wings share their one piece of
      proof plumbing; Instance/Discrete.v's [DiscreteCat] and
      [DiscreteCat_Discrete]; Structure/Discrete.v's [Discrete];
      Instance/StrictCat.v's [StrictCat] with Theory/Functor.v's
      [Functor_StrictEq_Setoid]; Instance/Coq.v's [Coq];
      Theory/Functor.v's [Build_Functor], [Compose], [Id], [Full] and
      [Faithful]; Theory/Isomorphism.v's [Isomorphism] and
      [iso_to_from]; and Theory/Adjunction.v's [Adjunction],
      [Build_Adjunction'], [unit] and [counit].  Not one category,
      functor or adjunction lemma is re-proved, and no [Cat]-level or
      [Sets]-level refutation is restated.

      BUILT: (a)-(g) above.

   IV. STRENGTHS, MEASURED STRICT-FIRST -- AND THE TWO WINGS COME APART
      HERE, IN THE DIRECTION ONE WOULD NOT GUESS.

      SIXTEEN [Example]s close by [eq_refl].  Twelve of them are general
      readbacks, and the other four are §10's computing witnesses:
      the object action of [StrictCat_Indisc] and the object action of
      its arrow action ([indisc_obj], [indisc_map]); the fact that
      [obj[Indiscrete A]] IS [A] ([indisc_obj_carrier]), which is what
      makes (a) do double duty; both legs of the transposition
      ([adj_to_lifts], [adj_from_forgets]); one of the two round trips
      ([adj_from_to_ind], and note it is the WHOLE record, not merely a
      component); THE COUNIT IS THE IDENTITY FUNCTION ON THE NOSE
      ([indisc_counit_is_id]) and the unit is the identity on objects
      ([unit_obj]) and is [indisc_lift] of the identity as a WHOLE
      FUNCTOR ([unit_is_lift]); the object half of the remaining round
      trip ([rt_obj]); and, one level up, the object and arrow actions
      of [StrictCat_Objects ◯ StrictCat_Indisc] against [Id[Coq]]
      ([comp_obj], [comp_map], §10).

      Everything above is the exact mirror of Instance/Cat/Objects.v's
      §4, with [to] and [from] exchanged: there [to] forgets an arrow
      action and [from] extends, and the round trip that fails is
      [from ∘ to]; here [to] lifts and [from] forgets, and the round trip
      that fails is [to ∘ from].

      THE CAUSE OF THE FAILURE IS NOT THE MIRROR, AND THIS WING COMES
      OUT STRICTLY BETTER AT THE ARROW LEVEL.  On the left wing the
      residue is [fmap_id] and the arrow round trip is [≈]-ONLY.  Here
      it is not a coherence law at all: it is the absence of definitional
      ETA FOR [Datatypes.unit].  [fmap[F] h] inhabits [unit] and the
      round trip produces [tt], and Coq will not identify a variable of
      a one-constructor NON-record inductive with its constructor --
      pinned as [unit_has_no_eta] with [unit_eta_by_destruct] as the
      passing control immediately after.  Consequently
      [rt_map_leibniz] closes the arrow round trip at LEIBNIZ [=] with
      one [destruct], where the left wing reaches only [≈].

      READ THE WHOLE-RECORD NEGATIVE HONESTLY, THOUGH.  It has AT LEAST
      TWO independent causes and only one is isolated: besides the arrow
      field, the three law fields of the rebuilt functor are this file's
      own opaque obligations, and NO probe here separates them.  So
      "eta is the obstruction" is a claim about [rt_map_strict], which is
      pinned, and not about [adj_to_from_ind], which is also pinned but
      whose diagnosis is left incomplete.  The [≈] form is available as
      [adj_to_from_equiv], straight from [iso_to_from].

      The adjunction is packaged through [Build_Adjunction']
      (Theory/Adjunction.v:159) for the same measured reason as on the
      left wing, though the arithmetic differs: the smart constructor
      asks only for the two [to]-side naturality clauses, which here land
      in [StrictCat] rather than in [Coq] -- but both close with an
      [eq_refl] object family and one [indiscrete_hom_eq], because a
      strict functor equality between two functors into an indiscrete
      category has a coherence field valued in [unit].  The full
      constructor would have demanded the two [from]-side squares as
      well.

      Sharpness is proved rather than asserted, in two places.  §7 shows
      the two adjoints of [StrictCat_Objects] are not isomorphic in
      [StrictCat], so the string's two ends are genuinely different
      functors; and Instance/Cat/Objects.v:§9's [Objects_not_Faithful]
      already shows the middle functor genuinely forgets, so neither
      adjunction is an equivalence in disguise.

   V. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER -- AND HERE
      THE BINDER CARRIES A LITERAL, NOT AN IDENTIFICATION.

      NO CONSTRAINT BLOCK IN THIS FILE CONTAINS A UNIVERSE EQUATION.
      Every entry of every block is a [<] or a [<=]; checked constant by
      constant, not sampled.  A reader who stops there concludes that
      the adjunction is universe-free, AND IS WRONG, because the
      restriction is spelled in the BINDER as the literal [Set]:

        Objects_Indisc_Adjunction@{u u0 u1 u2 u3} :
          StrictCat_Objects@{u2 u0 u3 u u3 Set}
            ⊣ StrictCat_Indisc@{u2 u0 u u3}

      The sixth argument of [StrictCat_Objects] is the ambient
      [StrictCat]'s inner hom-and-proof level, and it is [Set] on the
      nose.  So THE ADJUNCTION IS A STATEMENT ABOUT CATEGORIES WHOSE HOM
      AND PROOF UNIVERSES ARE THE LITERAL [Set].  This is the one place
      the right wing is worse behaved than the left, whose two functors
      spread six distinct levels and pin nothing.

      THE PIN IS THE DONOR'S, AND ITS PROPAGATION IS TRACKED RATHER THAN
      ASSERTED.  [Indiscrete@{u} : Type@{u} → Category@{u Set Set}] takes
      ONE universe binder where [Class Category] has three, so its hom
      and proof universes minimize to [Set].  From there it reaches the
      SOURCE as well, which is the part worth knowing:
      [indisc_lift@{u u0}] is over [C : Category@{u0 Set Set}], because
      [Functor] bounds the source's hom universe by the target's and the
      target's is a literal.  §8 pins all three steps -- the donor, this
      file's [indisc_lift], and [indisc_adj_iso] -- as formability
      negatives, each reporting "Cannot enforce Set = uh", against five
      controls of which the sharpest is [Check (C : obj[StrictCat])],
      the SAME ascription the third negative rejects, accepted at the
      very same levels.  So the rejection is attributable to
      [Indiscrete] and not to [StrictCat], to [StrictCat_Objects], or to
      the ability to name the constants at all.

      WHAT IS NOT PINNED IS THE OBJECT UNIVERSE, and that is guarded too
      ([IndiscreteObjectsFree], §8): at [C : Category@{wo Set Set}] with
      [Set < wo] both [indisc_lift] and [indisc_adj_iso] elaborate.  The
      restriction is therefore exactly "hom and proof are [Set]", and
      the class it describes is inhabited -- [DiscreteCat@{o Set Set} A]
      and [Indiscrete A] are both in it, which is why §7 and §10 have
      anything to talk about.

      THE PIN IS NOT CLAIMED UNAVOIDABLE, AND THE REPAIR WAS MEASURED
      BUT DELIBERATELY NOT MADE.  Writing the same body with three
      binders yields [Type@{o} → Category@{o h p}], fully free (measured
      out of tree, not shipped).  It is a change to
      Instance/Discrete/Reconstruct.v, this file's brief is to consume
      that donor rather than to rebuild or amend it, and the donor has
      three other consumers; so the pin is recorded as a repairable
      donor defect of the [Build_Quiver_Standard_Eq] minimization family
      that Construction/Free/Quiver/Examples.v documents, and left where
      it is.

      Two inherited identifications are named rather than repaired, and
      neither is introduced here: [StrictCat] is declared at
      [Category@{u u0 u0}], identifying its OWN hom and proof universes,
      and [Coq]'s own block carries [u0 = u1] and [u0 = u2].  Those are
      claims about those two constants, not about the transitive
      closure, which was not swept.

   VI. AUDIT.  42 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
      ([Print Module] lists 42 and the file declares no [Record], [Class]
      or [Inductive], so there is no unlisted [Build_*]; each was queried
      by fully qualified name, which is what reaches the 10 [Program]
      obligations a [.glob] sweep cannot see; 32 names are declared in
      the source and 32 + 10 = 42).  ZERO of the 42 collides anywhere in
      the tree, by a sweep of this file's own declared names that allows
      attribute prefixes.  THAT SWEEP FOUND A LIVE COLLISION and it is
      recorded rather than quietly fixed: [counit_is_id] -- the mirror of
      Instance/Cat/Objects.v's [unit_is_id], and the obvious name --
      clashes with Instance/Cat/Components.v:447, which landed while
      this file was being written; §4's is renamed
      [indisc_counit_is_id].  The hazard is not cosmetic, since the
      [make print-assumptions] gate reads its targets by bare name in a
      single scope.  DISCLOSED IN THE SAME BREATH, AND NOT FIXED HERE
      BECAUSE NEITHER FILE IS THIS ONE: [Disc_Full], [Disc_Faithful] and
      [disc_adj_iso] are each declared BOTH in Instance/Cat/Objects.v
      and in Instance/Cat/Components.v, at different types over
      different categories.  SEVEN [Fail] probes, of TWO KINDS kept
      lexically apart -- four CONVERSION (three in §4, one in §10) and
      three FORMABILITY (all in §8) -- each stripped once and its kind
      read off the whole error message, beside an instrument check and
      THIRTEEN positive controls: seven [Check]s in §8 (five in the
      pinning section, two in the objects-free one) and six passing
      [Example]s standing beside the §4 and §10 negatives ([rt_obj],
      [rt_map_leibniz], [adj_to_from_equiv], [unit_eta_by_destruct],
      [comp_obj] and [comp_map]).
      Both section-local [Constraint] declarations were additionally
      tested by DELETION, and they differ: the one in [IndiscreteSetPin]
      is INERT (all three negatives still fail, byte-identically, since
      they fire on the donor's literal [Set] meeting a rigid declared
      level), while the one in [IndiscreteObjectsFree] is
      meaning-giving (its [Check]s pass either way, but without it the
      levels could collapse and would demonstrate nothing).  Neither is
      load-bearing in the sense of Instance/Cat/Objects.v's middle
      section, and this is recorded because a reader who assumes a
      [Constraint] does work would be wrong both times here.
      Rename-simulated 5/5 on an UNPADDED denominator -- the constants a
      NEGATIVE names, which are [Indiscrete] and [StrictCat_Objects]
      (renamed throughout, simulating a donor rename) and [indisc_lift],
      [StrictCat_Indisc] and [indisc_adj_iso] (renamed at the definition
      site only, since a whole-file rename of a file-local constant is a
      no-op and would score a false pass) -- every one of them breaking
      the file at a non-[Fail] line.

   VII. WHAT IS NOT DELIVERED.

      No [Components ⊣ StrictCat_Disc] and no [Coq]-valued π₀ -- the
      leftmost adjunction exists, in Instance/Cat/Components.v, but over
      [Cat] and [Sets], so it does not extend [adjoint_string] and is not
      cited as doing so.  Item II records why [Pi0] cannot join this
      string, and records equally that no impossibility is proved for a
      differently-built π₀.  So [adjoint_string] is a string of THREE
      functors, not Mac Lane's four, and it does not claim otherwise.

      NO PROOF THAT THE STRING STOPS ON THE RIGHT.  §9 proves the fact
      the expectation rests on -- every functor from an indiscrete
      category to a discrete one is CONSTANT ([ind_to_disc_constant]),
      so no such functor is the identity on [bool]
      ([no_identity_functor_ind_to_disc]).  That is NOT a refutation of
      [StrictCat_Indisc ⊣ StrictCat_Objects]: an adjunction supplies a
      hom-setoid isomorphism whose two legs are arbitrary setoid maps,
      and nothing here forces either leg to be [fobj], so the counting
      argument one would want does not follow from §9 alone.  No such
      refutation is attempted and none is claimed.

      No uniqueness statement for either adjoint; no naturality of
      [indisc_adj_iso] in [C] or [A] beyond the two clauses
      [Build_Adjunction'] consumes; no (co)monad on either side and hence
      nothing about idempotency; no statement that [StrictCat_Indisc] is
      a coreflective embedding (the tree's reflectivity vocabulary,
      Construction/Reflective.v, is stated over subcategories rather than
      over an arbitrary fully faithful right adjoint, and no bridge is
      built); no preservation, reflection or creation of limits, in
      particular nothing about [StrictCat_Objects] preserving them from
      both sides; no comparison of [StrictCat_Indisc] with
      Instance/Top/Forgetful.v's [Top_Indiscrete] beyond the remark in
      (c); no relation between this [Indiscrete] and Instance/Top.v's
      unrelated [Section Indiscrete] on the indiscrete TOPOLOGY; no
      annotated ([Set]-free) restatement of anything, per item V; and no
      diagnosis of the whole-record negative beyond the one field
      isolated in item IV. *)

(** ** §1. The indiscrete co-extension *)

(* A function [f : obj[C] → A] co-extends to a functor into the
   indiscrete category on [A]: an object goes to its image, and a
   morphism goes to the only morphism there is.  This is the exact
   mirror of Instance/Cat/Objects.v:§1's [disc_ext], and like it, all
   three functor laws are equations in [unit] and close by that file's
   own [indiscrete_hom_eq].

   Unlike [disc_ext] it needs NO universe binders, and the reason is not
   that it is better behaved but that there is nothing left to bind:
   [Indiscrete] has already fixed the target's hom and proof universes
   at [Set], and [Functor] then forces the SOURCE's to agree.  Item V
   and §8 measure that; it is the one place this wing is worse off than
   the left one.  A [Program Definition] cannot be annotated here in any
   case, since its obligations mint fresh universes; hence the [refine],
   again following the donor. *)
Definition indisc_lift {C : Category} {A : Type} (f : obj[C] -> A)
  : C ⟶ Indiscrete A.
Proof.
  unshelve refine (@Build_Functor C (Indiscrete A) f
                     (fun _ _ _ => tt) _ _ _).
  - intros x y f1 g1 H. apply indiscrete_hom_eq.
  - intros x. apply indiscrete_hom_eq.
  - intros x y z g1 h1. apply indiscrete_hom_eq.
Defined.

(** ** §2. The indiscrete functor *)

(* [Indiscrete] on objects, and [indisc_lift] on arrows -- the arrow
   action is not a second construction, because [obj[Indiscrete A]] IS
   [A] ([indisc_obj_carrier], §4), so a [Coq]-morphism [A ~> B] already
   has the type [indisc_lift] wants.  §3's mirror on the left wing is
   Objects.v's [fmap := fun A B f => disc_ext f].

   ONE obligation remains, [fmap_respects]; [fmap_id] and [fmap_comp]
   are discharged by the ambient tactic, since a strict functor equality
   between two functors into an indiscrete category has an [eq_refl]
   object family and a coherence field valued in [unit]. *)
Program Definition StrictCat_Indisc : Coq ⟶ StrictCat := {|
  fobj := Indiscrete;
  fmap := fun A B (f : A ~{Coq}~> B) => indisc_lift (C := Indiscrete A) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §3. The adjunction *)

(* The transposition, and the whole content is that a functor INTO an
   indiscrete category IS its object map: [to] co-extends and [from]
   forgets the arrow action.  On the left wing the two are exchanged --
   there [to] forgets and [from] extends -- which is why the round trip
   that survives on the nose is the other one (§4).

   Two obligations remain, that [to] respects [≈] and one round trip;
   the other round trip and [from]'s [Proper] certificate are discharged
   by the ambient tactic, which is already the strict/[≈] split §4
   measures. *)
Program Definition indisc_adj_iso (C : obj[StrictCat]) (A : obj[Coq]) :
  @Isomorphism Sets
    {| carrier := @hom Coq (StrictCat_Objects C) A
     ; is_setoid := @homset Coq (StrictCat_Objects C) A |}
    {| carrier := @hom StrictCat C (StrictCat_Indisc A)
     ; is_setoid := @homset StrictCat C (StrictCat_Indisc A) |} := {|
  to   := {| morphism := fun (f : obj[C] -> A) => indisc_lift f |};
  from := {| morphism := fun (F : C ⟶ Indiscrete A) => fobj[F] |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. apply indiscrete_hom_eq.
Defined.

(* Mac Lane's right-hand adjunction.  Both naturality clauses close with
   an [eq_refl] object family and one [indiscrete_hom_eq], for the reason
   §2's comment gives.  [Build_Adjunction'] (Theory/Adjunction.v:159)
   asks only for the two [to]-side clauses; see item IV. *)
Definition Objects_Indisc_Adjunction :
  StrictCat_Objects ⊣ StrictCat_Indisc.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact indisc_adj_iso.
  - intros C D A f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
  - intros C A B f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §4. Strengths, strict first *)

Example indisc_obj (A : obj[Coq]) :
  fobj[StrictCat_Indisc] A = Indiscrete A := eq_refl.

Example indisc_obj_carrier (A : obj[Coq]) :
  obj[Indiscrete A] = A := eq_refl.

Example indisc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Indisc] f] x = f x := eq_refl.

Example adj_to_lifts (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  to (indisc_adj_iso C A) f = indisc_lift f := eq_refl.

Example adj_from_forgets (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  from (indisc_adj_iso C A) F = fobj[F] := eq_refl.

Example adj_from_to_ind (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  from (indisc_adj_iso C A) (to (indisc_adj_iso C A) f) = f := eq_refl.

Example indisc_counit_is_id (A : obj[Coq]) (a : A) :
  @counit _ _ _ _ Objects_Indisc_Adjunction A a = a := eq_refl.

Example unit_obj (C : obj[StrictCat]) (x : C) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction C] x = x := eq_refl.

Example unit_is_lift (C : obj[StrictCat]) :
  @unit _ _ _ _ Objects_Indisc_Adjunction C
    = indisc_lift (fun x : obj[C] => x) := eq_refl.

Fail Example adj_to_from_ind (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) = F := eq_refl.

Example rt_obj (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x : C) :
  fobj[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] x
    = fobj[F] x := eq_refl.

Fail Example rt_map_strict (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h := eq_refl.

Example rt_map_leibniz (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h.
Proof. apply indiscrete_hom_eq. Qed.

Example adj_to_from_equiv (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) ≈ F.
Proof. exact (iso_to_from (indisc_adj_iso C A) F). Qed.

Fail Example unit_has_no_eta (u : Datatypes.unit) : u = tt := eq_refl.

Example unit_eta_by_destruct (u : Datatypes.unit) : u = tt.
Proof. now destruct u. Qed.

(** ** §5. The indiscrete functor is fully faithful *)

(* Which is what "the counit is the identity" (§4) says categorically.
   Faithfulness costs NOTHING -- injectivity of [fmap[StrictCat_Indisc]]
   is the first projection of a strict functor equality, and the ambient
   tactic finds it.  Fullness costs exactly the round trip of §4, taken
   at [≈]: the preimage of [G] is [fobj[G]], and [iso_to_from] says the
   co-extension of that is [G] again. *)
#[export] Program Instance Indisc_Faithful : Faithful StrictCat_Indisc.

#[export] Program Instance Indisc_Full : Full StrictCat_Indisc := {|
  prefmap := fun A B (G : StrictCat_Indisc A ~{StrictCat}~> StrictCat_Indisc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_to_from (indisc_adj_iso (StrictCat_Indisc x) y) g).
Defined.

(** ** §6. The adjoint string, as far as it goes *)

(* Three of Mac Lane's four functors, and the two adjunctions between
   them, as ONE term -- so that the string is an artifact rather than two
   files that happen to compile.  It has two components and not three,
   and item II says why: the fourth adjoint lives over a different pair
   of categories, and Instance/Cat/Components.v now proves it there.
   Nothing here claims Mac Lane's full string is in the tree. *)
Definition adjoint_string :
  (StrictCat_Disc ⊣ StrictCat_Objects)
    * (StrictCat_Objects ⊣ StrictCat_Indisc) :=
  (Disc_Objects_Adjunction, Objects_Indisc_Adjunction).

(** ** §7. The two adjoints of the objects functor genuinely differ *)

(* The engine, one line: a morphism of a DISCRETE category is an
   equality proof, and an indiscrete category supplies a morphism
   between any two objects, so the image of [tt] IS the equation. *)
Lemma ind_to_disc_constant {A B : Type}
  (F : Indiscrete A ⟶ DiscreteCat B) (x y : A) : fobj[F] x = fobj[F] y.
Proof. exact (fmap[F] (tt : x ~{Indiscrete A}~> y)). Qed.

Theorem disc_indisc_not_iso :
  @Isomorphism StrictCat (DiscreteCat bool) (Indiscrete bool) -> False.
Proof.
  intro I.
  destruct (iso_to_from I) as [eo _]. simpl in eo.
  pose proof (f_equal (fobj[to I]) (ind_to_disc_constant (from I) true false))
    as H.
  rewrite (eo true), (eo false) in H.
  discriminate.
Qed.

Theorem disc_indisc_not_eq :
  StrictCat_Disc bool = StrictCat_Indisc bool -> False.
Proof.
  intro H.
  refine (Indiscrete_bool_Discrete_absurd _).
  exact (eq_rect _ Discrete (DiscreteCat_Discrete bool) _ H).
Qed.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* The [Set] pin of [Indiscrete], guarded rather than merely measured, and
   then tracked as it propagates -- first into this file's own
   [indisc_lift], then into the adjunction.

   READ THE [Constraint] CORRECTLY: IT IS INERT FOR ALL THREE NEGATIVES,
   AND THAT WAS MEASURED BY DELETION RATHER THAN ASSUMED.  Removing the
   line leaves all three [Fail]s failing with byte-identical messages,
   because what they fire on is the donor's LITERAL [Set] meeting the
   RIGID declared level [uh], not a relation declared between them.  It
   is kept because it states the intended reading and because the last
   control is only interesting above [Set].  (Instance/Cat/Objects.v's
   §8 records the same behaviour for its own [SetPin] section, and
   records beside it a [Constraint] that IS load-bearing, so the
   distinction is not academic.) *)
Section IndiscreteSetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (C : Category@{uo uh uh}) (A : Type@{uo}).

  (* Controls.  The first is the sharpest: the SAME ascription that
     negative 3 rejects is accepted here, so that rejection is
     attributable to [Indiscrete] and not to [StrictCat] or to the
     ability to view [C] as one of its objects.  The next two show the
     LEFT wing reaching these levels, so the pin is this wing's alone.
     The last two are the shapes the negatives are about, formable when
     [Indiscrete] is not in play. *)
  Check (C : obj[StrictCat]).
  Check (fmap[StrictCat_Objects] (Id[C])).
  Check (@disc_ext@{uo uh uh uo}).
  Check (DiscreteCat@{uo uh uh} A).
  Check (@indisc_lift (DiscreteCat@{uo Set Set} A) A).

  (* 1: the donor is pinned.  "Cannot enforce Set = uh". *)
  Fail Check (Indiscrete@{uo} : Type@{uo} -> Category@{uo uh uh}).

  (* 2: and NO annotation of [indisc_lift] can free it, because the pin
     reaches the SOURCE as well: [Functor] bounds the source's hom
     universe by the target's, and the target's is the literal [Set], so
     [C] is reported as needing type [Category@{_ Set Set}]. *)
  Fail Check (@indisc_lift C A).

  (* 3: hence the adjunction is confined too. *)
  Fail Check (@indisc_adj_iso C A).
End IndiscreteSetPin.

(* What is NOT pinned: the OBJECT universe.  The restriction is exactly
   "hom and proof universes are the literal [Set]", and objects may sit
   anywhere above it -- so the adjunction is a statement about a real
   class of categories rather than about [Set]-sized ones.

   The [Constraint] here is neither inert nor load-bearing: the two
   [Check]s pass with or without it (measured by deletion), and what the
   declaration buys is the CONTENT of the controls -- without it [wo]
   could collapse to [Set] and the commands would demonstrate nothing.
   Stated so that a later reader does not delete it as redundant. *)
Section IndiscreteObjectsFree.
  Universes wo.
  Constraint Set < wo.
  Context (C : Category@{wo Set Set}) (A : Type@{wo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsFree.

(** ** §9. Where the string stops on the right *)

(* WHY one expects [StrictCat_Indisc ⊣ StrictCat_Objects] to fail, and
   NOT a proof that it does -- read the two apart, since only the first
   is established here.  §7's [ind_to_disc_constant] says every functor
   out of an indiscrete category into a discrete one is constant; so the
   identity map of [bool] is the object map of NO such functor, while it
   is of course one of four functions [bool → bool].  A counting
   argument from that to the non-existence of an adjunction would need
   the transposition's two legs to BE [fobj] and its inverse, and an
   [Adjunction] supplies only a pair of arbitrary setoid maps, so
   nothing here forces that.  No refutation is attempted and none is
   claimed; item VII repeats the caveat where a reader will meet it. *)
Theorem no_identity_functor_ind_to_disc
  (F : Indiscrete bool ⟶ DiscreteCat bool)
  (H : forall b : bool, fobj[F] b = b) : False.
Proof.
  pose proof (ind_to_disc_constant F true false) as K.
  rewrite (H true), (H false) in K. discriminate.
Qed.

(** ** §10. Non-vacuity *)

(* The composite [Objects ◯ Indisc] returns [Id[Coq]]'s DATA on the nose
   -- object action and arrow action both by [eq_refl] -- which is what
   "the counit is the identity" (§4) says one level up.  The whole record
   is REFUTED, and the cause is the usual one: [Compose] rebuilds
   [fmap_respects], [fmap_id] and [fmap_comp] as its own opaque proofs.
   So this is a CONVERSION negative about the law fields, with the two
   data fields as its passing controls. *)
Example comp_obj (A : obj[Coq]) :
  fobj[StrictCat_Objects ◯ StrictCat_Indisc] A = A := eq_refl.

Example comp_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fmap[StrictCat_Objects ◯ StrictCat_Indisc] f x = f x := eq_refl.

Fail Example comp_is_id :
  StrictCat_Objects ◯ StrictCat_Indisc = Id[Coq] := eq_refl.

(* [Indiscrete bool] is not degenerate in either direction: it has two
   provably DISTINCT objects, and they are nonetheless isomorphic, which
   is what "indiscrete" means and what [DiscreteCat bool] provably is
   not (§7).  So the witnesses below are not applied to a one-object
   category, and the adjunction is not being exercised at a shape where
   its content evaporates. *)
Example ind_bool_objs_distinct : (true : Indiscrete bool) = false -> False.
Proof. discriminate. Qed.

(* PRIOR ART, disclosed rather than duplicated silently: this is
   Theory/Skeleton/Separation.v:76's [Indiscrete_iso] -- which is already
   general in the type and the two points -- specialized at [bool].  That
   module is NOT required, for a measured reason rather than taste:
   through [Theory/Skeleton.v] it would add TEN modules to this file's
   49-module closure ([Construction/Quotient.v],
   [Construction/Subcategory.v], [Instance/Fun.v], [Instance/One.v],
   [Instance/Two.v], the three [Theory/Equivalence*] files,
   [Theory/Skeleton.v] and [Theory/Skeleton/Separation.v] itself), and
   [Instance/Fun.v] in particular is in neither this closure nor
   [Instance/Cat.v]'s.  Nothing here is claimed new. *)
(* Issue #357 work item 5 asks for two sanity checks.  The first --
   components of a discrete category are its objects -- is
   [pi0_counit_iso] in Instance/Cat/Components.v.  This is the second:
   the indiscrete category on a two-element set is CONNECTED.  It is
   pure instantiation of Structure/Groupoid/Connected.v's
   [arrow_connected] at the unique arrow, every hom of [Indiscrete]
   being [unit] -- so no zig-zag induction is performed here. *)

(* THE SHARED-MIDDLE READING COSTS A [Set] PIN, AND THAT IS MEASURED.
   At its DEFAULT universe instance [adjoint_string] does NOT print with
   one [StrictCat_Objects]: the two occurrences elaborate at different
   instances, the second carrying a literal [Set].  So "the two links
   share their middle term" is true only at a shared instance, and the
   shared instance pins an inner level to [Set] -- inherited from
   [Indiscrete], as §4 records.  Pinned here rather than asserted. *)

Section SharedMiddle.
Universes a b.
Constraint Set < a.
Check adjoint_string@{b a Set a a b a Set}.
End SharedMiddle.

Definition ind_bool_connected : Connected (Indiscrete bool) :=
  @arrow_connected (Indiscrete bool) (fun _ _ => tt).

Program Definition ind_bool_iso :
  @Isomorphism (Indiscrete bool) true false := {| to := tt; from := tt |}.

(* The transposition computes.  By [adj_to_lifts] the forward leg IS
   [indisc_lift], so these evaluate the adjunction's own [to] at a
   non-identity function. *)
Example neg_lift_true :
  fobj[indisc_lift (C := DiscreteCat bool) negb] true = false := eq_refl.

Example neg_lift_false :
  fobj[indisc_lift (C := DiscreteCat bool) negb] false = true := eq_refl.

Example counit_bool (b : bool) :
  @counit _ _ _ _ Objects_Indisc_Adjunction bool b = b := eq_refl.

Example unit_disc_bool (b : bool) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction (DiscreteCat bool)] b = b
  := eq_refl.
