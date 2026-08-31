(** * The objects functor on the category of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(* Book:      Mac Lane, "Categories for the Working Mathematician",
              Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
              (maclane:IV.2:ex9), where the result is attributed to
              N. Smythe.
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   nLab:      https://ncatlab.org/nlab/show/indiscrete+category
   nLab:      https://ncatlab.org/nlab/show/adjoint+string
   nLab:      https://ncatlab.org/nlab/show/Cat
   nLab:      https://ncatlab.org/nlab/show/strict+category
   nLab:      https://ncatlab.org/nlab/show/connected+component
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Mac Lane's exercise asks for the adjoint string carried by the functor
   that sends a category to its set of objects:

     Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

   -- four functors between a category of categories and a category of
   sets, each adjoint to the next.  This file is the FOUNDATION of that
   development: it builds the objects functor and the middle adjunction
   [StrictCat_Disc ⊣ StrictCat_Objects], and it SETTLES THE DOMAIN AND
   CODOMAIN, which the two remaining modules inherit.  Both halves of
   that settlement are forced by REFUTATION ONCE THE TARGET IS REQUIRED
   TO COMPARE OBJECT MAPS BY LEIBNIZ EQUALITY, and both refutations are
   proved below (§6 and §7).  Read that qualifier: it is load-bearing.
   An objects functor [Cat ⟶ Sets] DOES exist if the objects are given
   the ISOMORPHISM setoid instead -- it compiles with zero obligations
   and is closed under the global context -- and issue #357's own item 1
   names that alternative ("with equality, or with isomorphism, if a
   choice has to be made -- the exercise wants the strict version").  So
   the strict reading is the EXERCISE'S choice; what §6 and §7 prove is
   that ONCE it is taken, the domain and codomain are forced.
   Throughout, a Roman
   numeral names one of the notes that follow and a [§] names a section
   of the development proper.

   Delivered here:

     (a) [disc_ext]: the extension of a function [A → obj[C]] to a
         functor [DiscreteCat A ⟶ C].  This is NOT the tree's
         [DiscreteCat_Functor], and the difference is a universe pin --
         see item I, THIRD.

     (b) [StrictCat_Objects : StrictCat ⟶ Coq], the objects functor,
         and [StrictCat_Disc : Coq ⟶ StrictCat], the discrete functor.

     (c) [disc_adj_iso], the hom-setoid isomorphism, and the packaged
         record [Disc_Objects_Adjunction], of type
         [StrictCat_Disc ⊣ StrictCat_Objects].  There is no analogue here
         of the universe wall that Instance/Top/Forgetful.v meets for the
         corresponding [Top] triple -- see §8.

     (d) [Disc_Full] and [Disc_Faithful]: the discrete functor is fully
         faithful, which is the categorical reading of the fact that the
         unit of the adjunction is the identity ([unit_is_id], §5).

     (e) The two refutations that force the domain and codomain:
         [objects_not_functorial_over_Cat] and
         [no_carrier_functor_Sets_StrictCat], the latter instantiated at
         BOTH the discrete and the indiscrete object map, so that it is
         binding on the right-hand wing as well as on this file.

     (f) [Objects_not_Faithful]: the objects functor genuinely forgets.

   I. A PRIOR-ART CORRECTION, ON THREE COUNTS, EACH MEASURED.

      FIRST, the catalog issue states that the indiscrete half "has no
      construction at all -- searching for it finds only comments".  That
      is FALSE.  Instance/Discrete/Reconstruct.v:416 has declared
      [Indiscrete (A : Type) : Category], with [hom := fun _ _ => unit],
      [homset := Morphism_equality] and every category law discharged by
      the ambient obligation tactic, since it was written; it is CONSUMED
      here (§6 uses it for the [Cat] refutation) and nothing rebuilds it.
      It has TWO independent consumers already: Theory/Skeleton/
      Separation.v, and -- worth reading beside §6 -- Instance/Cat/
      Pullback.v:539, whose [IB := Indiscrete bool] drives
      [FibreProduct_not_Cat_pullback], a refutation of a DIFFERENT
      statement turning on the SAME fact, that [Cat] cannot see the
      difference between [true] and [false] there.  (Two further files
      match a name search and are not consumers: Instance/Top.v has an
      unrelated [Section Indiscrete] about the indiscrete TOPOLOGY, and
      Instance/Top/Forgetful.v mentions the word only in prose.)

      What is genuinely absent is narrower and worth stating precisely:
      [Indiscrete] is an OBJECT MAP only.  No arrow action, no functor
      and no adjunction exists for it anywhere in the tree -- both
      consumers above use it on objects alone.

      SECOND, the issue's work item 4 asks that the connected-components
      functor be defined.  That is FALSE too: Theory/Connected/
      Components.v:579 declares [Pi0 : Cat ⟶ Sets] with [fobj := pi0]
      and [fmap := pi0_fmap], and its three functor laws are proved
      there.  Only the ADJUNCTION is missing.  Item II below records the
      consequence: [Pi0] cannot join the string built here.

      THIRD -- and this one is a correction to a donor rather than to the
      issue, which flagged the risk correctly -- Instance/Discrete.v:57's
      [DiscreteCat_Functor] is universe-unannotated and PINS ITS SOURCE
      AT [Set]:

        DiscreteCat_Functor@{u u0 u1 u2} :
          ∀ {A : Type@{u}} {C : Category@{u0 u2 u2}},
            (A → obj[C]) → DiscreteCat@{u Set Set} A ⟶ C

      Building [StrictCat_Disc] over it would have propagated a [Set]
      pin on the hom AND proof universes of every discrete category.
      [disc_ext] is the same construction with the binders written out,
      and it is [Set]-free; §8 pins the difference as a formability
      negative against passing controls.  The donor is NOT modified here
      and the pin is NOT claimed unavoidable -- it is a minimization
      artifact of the [Build_Quiver_Standard_Eq] family that
      Construction/Free/Quiver/Examples.v already records.

   II. THE DOMAIN DECISION: [StrictCat] AND [Coq], BOTH FORCED.

      The issue's item 1 asks whether the objects functor should live on
      [StrictCat], and Theory/Connected/Components.v:576-578 already
      flags the question from the other side, noting that [Cat]'s
      hom-setoid is natural isomorphism and that "a functor into [Sets]
      out of a strict category of categories would be a different
      statement and is not built".  The answer is settled here by two
      counterexamples, not by taste.

      THE SOURCE MUST BE [StrictCat].  Any objects functor must send a
      pair of [≈]-equal functors to a pair of [≈]-equal maps, and both
      candidate targets compare object maps by LEIBNIZ equality: the
      [equiv] of [ObjSetoid] (Theory/Connected/Components.v:458) is
      [@eq obj[C]], and [Coq]'s hom-setoid is pointwise [=]
      (Instance/Coq.v).  So [fmap_respects] for any objects functor INTO
      SUCH A TARGET is exactly the proposition [ObjRespectsCat] of §6 --
      and over [Cat] that proposition is FALSE.  It is NOT an obligation
      every conceivable objects functor owes: give the objects the
      isomorphism setoid and [fmap_respects] becomes [fobj_iso], which
      every functor satisfies.  The witness is the swap endofunctor of
      [Indiscrete bool]: every hom-set there is [unit], so the identity
      functor and the negation functor are naturally isomorphic, hence
      [≈] in [Cat], while their object maps differ at [true].  Over
      [StrictCat] the same proposition is the FIRST PROJECTION of the
      hom-setoid ([objects_respects_StrictCat], a [:=] with no tactic),
      because [Functor_StrictEq_Setoid]'s [eq_on_obj] field IS it.

      THE TARGET MUST BE [Coq].  This half is not in the issue at all,
      and it is the mirror image: [StrictCat_Disc] must send a pair of
      [≈]-equal maps to [≈]-equal functors, and [≈] in [StrictCat] again
      demands Leibniz equality of object maps -- which [Sets]-morphisms
      do not supply, [≈] there being the target setoid's own relation.
      §7 proves the general form: NO object map [K : Sets → StrictCat]
      that is pointed, injective on points and natural on points can
      respect [≈], the witness being [bool] under the everywhere-true
      setoid.  It is instantiated at the discrete object map AND at the
      indiscrete one, so it forces the target for the right-hand wing
      too, which is why it is stated generally rather than for
      [StrictCat_Disc] alone.
      [Coq] is AN in-tree category of sets (not the only one -- Instance/Ens.v:47,:69 and Instance/EnsV.v:195 also compare morphisms pointwise by [=]; [Coq] is simply the natural choice here) whose [≈] on morphisms IS
      pointwise Leibniz equality, which is exactly [StrictCat]'s
      [eq_on_obj]; that coincidence is what makes the string possible.

      CONSEQUENCE FOR THE FOURTH ADJOINT, STATED RATHER THAN GLOSSED.
      [Pi0]'s domain is [Cat] and its codomain is [Sets], so it shares
      NEITHER end with [StrictCat_Objects : StrictCat ⟶ Coq], and by §6
      it cannot simply be restricted to [StrictCat] and re-aimed, since the
      objects functor does not exist over [Cat] at all.  What follows is
      that [Components ⊣ StrictCat_Disc] is a SEPARATE statement over a
      different pair of categories, not a fourth term of this string, and any
      module delivering it must either build a [Coq]-valued π₀ or state
      the adjunction elsewhere.  NOTHING HERE PROVES that no such
      [Coq]-valued π₀ exists; that question is left open, and the
      reduction to quotient types that suggests it is hard is an
      argument, not a theorem, and is not made here.

      NAMING, AND WHY THE OBVIOUS NAMES WERE UNAVAILABLE.  Both [Discrete]
      and [Indiscrete] are taken: [Discrete] is Structure/Discrete.v:33's
      PREDICATE on a category (an assertion that it has only identity
      morphisms), and [Indiscrete] is the category constructor of item I
      above.  And [Objects] is taken too, by Solver/Expr.v:38's reification
      CLASS -- a live hazard rather than a cosmetic one, since shadowing it
      would break the Solver's typeclass resolution wherever both modules
      are imported.  This file therefore follows the Instance/Top/
      Forgetful.v precedent and prefixes the functors with the structured
      category, whichever way they run: [StrictCat_Objects] and
      [StrictCat_Disc] here, and [StrictCat_Indisc] for the right-hand
      wing's mirror.  These names are binding on the remaining modules;
      all three were verified to have zero tree-wide occurrences first.

   III. WHAT IS CONSUMED, AND WHAT IS BUILT.

      CONSUMED, not rebuilt: Instance/Discrete.v's [DiscreteCat] -- the
      SHAPE, whose three universes are already free, so only the FUNCTOR
      [DiscreteCat_Functor] is replaced and only for the reason in item I
      (it is still named here, in §8, as the subject of a probe);
      Instance/Discrete/Reconstruct.v's [Indiscrete];
      Instance/StrictCat.v's [StrictCat] with Theory/Functor.v's
      [Functor_StrictEq_Setoid]; Instance/Coq.v's [Coq];
      Instance/Cat.v's [Cat]; Theory/Functor.v's [Build_Functor],
      [fmap_id], [Full] and [Faithful]; Theory/Isomorphism.v's
      [Isomorphism] and [iso_from_to]; Theory/Adjunction.v's
      [Adjunction], [Build_Adjunction'], [unit] and [counit]; and
      [Eqdep_dec.UIP_dec], which is Hedberg and axiom-free, in §9 alone.
      Not one category, functor-category or adjunction lemma is
      re-proved.

      BUILT: [disc_ext], [StrictCat_Objects], [StrictCat_Disc],
      [disc_adj_iso], [Disc_Objects_Adjunction], [Disc_Full],
      [Disc_Faithful], the two refutations with their witnesses, and
      [Objects_not_Faithful].

   IV. STRENGTHS, MEASURED STRICT-FIRST.  Ten readbacks hold at [eq_refl]
      and are shipped as [Example]s: the object and arrow actions of
      [StrictCat_Objects] ([objects_obj], [objects_map]); the object
      action of [StrictCat_Disc] and the object action of its arrow
      action ([disc_on_obj], [disc_map]); both legs of the transposition
      ([adj_to_forgets] and [adj_from_extends]); one of the two round
      trips ([adj_to_from]); THE UNIT IS THE IDENTITY FUNCTION ON THE
      NOSE ([unit_is_id]) and the counit is the identity on objects
      ([counit_obj]); and the object half of the remaining round trip
      ([roundtrip_obj]).

      EXACTLY ONE STEP IS [≈]-ONLY, AND ITS CAUSE IS EXHIBITED RATHER
      THAN DESCRIBED.  The round trip [disc_ext (fobj[F]) ≈ F] is
      REFUTED at [eq_refl] ([adj_from_to_strict], §5), and the failure is
      localized to a single field by a pair of probes with a passing
      control between them: the OBJECT map returns on the nose
      ([roundtrip_obj]), the ARROW map does not ([roundtrip_map]), and
      what separates them is precisely [fmap_id] -- [disc_ext] sends the
      only morphism of a discrete hom-set to [id], while [F] sends it to
      [fmap[F] id], and [roundtrip_map_equiv] closes the gap by
      [symmetry; exact (fmap_id)] and nothing else.  This is also why
      [Disc_Full] costs one line and [Disc_Faithful] costs none.

      An engineering note on that step, worth carrying: [apply fmap_id]
      FAILS there, reporting that it cannot unify [fmap[?F] id{?C}] with
      [fmap[x] eq_refl] -- the elaborator will not unify [id{?C}] against
      the [eq_refl] that IS the identity of a discrete category.  The
      fully applied [exact (@fmap_id _ _ x a)] works.

      The adjunction is packaged through [Build_Adjunction']
      (Theory/Adjunction.v:159) rather than [Build_Adjunction], and that
      is a measured economy rather than a style choice: the smart
      constructor asks only for the two [to]-side naturality clauses,
      which live in [Coq], where [≈] is pointwise [=] -- so BOTH CLOSE BY
      [reflexivity].  The full constructor would have put the same two
      naturality squares in [StrictCat], i.e. as transport-laden
      strict-equality-of-functors goals.

   V. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER.

      NO CONSTRAINT BLOCK IN THIS FILE CONTAINS A UNIVERSE EQUATION.
      Every entry of every block is a [<] or a [<=]; that was checked
      constant by constant, not sampled.  [disc_ext@{o h p q}] carries
      only [DiscreteCat]'s own bounds together with [h <= p], which is
      [Class Category]'s, and contains no [Set] -- which is the whole
      point of item I.3.  [StrictCat_Objects] and [StrictCat_Disc]
      each take six universe binders, spread six DISTINCT levels across
      them, and identify nothing.

      BUT THE BINDER IS WHERE THE IDENTIFICATION HIDES, AND THIS FILE
      REPORTS IT AGAINST ITSELF.  [Disc_Objects_Adjunction@{u u0 u1}]
      displays as

        StrictCat_Disc@{u u1 u u1 u u1}
          ⊣ StrictCat_Objects@{u u u1 u u1 u1}

      -- twelve slots filled from two levels, so the inner categories
      come out as [Category@{u1 u1 u1}], objects, homs and proofs
      identified, on a block whose only strict entry is [u1 < u].  A
      reader who inspects the block alone concludes "no identification"
      and is WRONG.  That identification is MINIMIZATION AND NOT CONTENT,
      and §8 guards the claim rather than asserting it: the adjunction
      TYPE is formable with the inner hom universe declared STRICTLY
      BELOW the inner object universe.  Producing the annotated
      constants is not attempted here -- [Program]'s obligations mint
      fresh universes, so the annotation cannot simply be written on --
      and the gap is recorded as repairable, not as unavoidable.

      Two donor identifications are named rather than repaired, and
      neither is introduced here: [StrictCat@{u u0 u1 u2 u3}] is declared
      at [Category@{u u0 u0}], so it identifies its OWN hom and proof
      universes; and [Coq@{u u0 u1 u2}] carries [u0 = u1] and [u0 = u2]
      in its own block.  Those are the only universe equations in the two
      ambient categories' OWN declarations -- a claim about those two
      constants, not about the whole transitive closure, which was not
      swept.  Neither is claimed unavoidable.

   VI. AUDIT.  68 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
      ([Print Module] lists 68 and the file declares no [Record], [Class]
      or [Inductive], so there is no unlisted [Build_*]; each was queried
      by fully qualified name, which is what reaches the 25 [Program]
      obligations a [.glob] sweep cannot see; 43 names are declared in
      the source and 43 + 25 = 68).  ZERO of the 68 names collides
      anywhere in the tree -- a sweep that FOUND one, and it was live:
      [Objects] is Solver/Expr.v:38's reification class, which is why the
      functors carry the [StrictCat_] prefix (item II).  Five [Fail]
      probes, of TWO KINDS kept lexically apart -- two CONVERSION
      in §5, three FORMABILITY in §8 -- each stripped once and its kind
      read off the whole error message, beside an instrument check and
      ten positive controls -- seven [Check]s in §8 and three passing
      [Example]s beside the §5 negatives.  Each of the three section-local
      [Constraint] declarations was additionally tested by deletion, and
      they behave differently -- one INERT, one LOAD-BEARING, one
      meaning-giving; §8 records which is which, since a reader who
      assumes a [Constraint] is doing work is wrong a third of the
      time here.  Rename-simulated 6/6 on an unpadded
      denominator (the constants a NEGATIVE names, file-local ones by the
      definition-site method since a whole-file rename is a no-op), every
      one of them breaking the file at a non-[Fail] line.  That exercise
      FOUND a vacuous guard: [DiscreteCat_Functor] was named only inside
      its own [Fail], so a rename of the donor would have turned that
      probe silently green; the control that closes it exists for that
      reason.

   VII. WHAT IS NOT DELIVERED.

      No [StrictCat_Indisc], and no [StrictCat_Objects ⊣ StrictCat_Indisc]:
      that is the right-hand wing, which this file only makes possible --
      by fixing the two categories, and by proving in §7 that the
      indiscrete object map cannot be aimed at [Sets] either.  In
      particular NOTHING here claims that the right adjoint exists.

      No [Components ⊣ StrictCat_Disc], and no [Coq]-valued π₀ at all:
      item II records why [Pi0] cannot be reused, and records equally
      that no impossibility is proved for a differently-built π₀.

      No comparison with Theory/Connected/Components.v's [ObjSetoid],
      which is the [Sets]-valued object map: §7 shows the [Sets]-valued
      STRING is unavailable, but nothing here states a functor
      [StrictCat ⟶ Sets] (which does exist) nor relates it to this one.

      No uniqueness statement for either adjoint; no naturality of
      [disc_adj_iso] in [A] or [C] beyond the two clauses
      [Build_Adjunction'] consumes; no monad or comonad on either side of
      the adjunction and hence nothing about idempotency; no statement
      that [StrictCat_Disc] is a reflective or coreflective embedding; no
      preservation, reflection or creation of limits; no [Full] or
      [Faithful] for [StrictCat_Objects] beyond §9's REFUTATION of
      faithfulness; no equivalence between [StrictCat] and anything; and
      no annotated ([Set]-free-inner-universe) restatement of the packaged
      adjunction, per §5. *)

(** ** §1. The discrete extension, with its universes written out *)

(* A function [f : A → obj[C]] extends to a functor out of the discrete
   category on [A]: an object goes to its image, and the only morphism of
   a discrete hom-set -- an equality proof -- goes to the identity,
   transported along that proof.

   This is Instance/Discrete.v:57's [DiscreteCat_Functor] with the
   universe binders written out and the setoid [rewrite] avoided.  BOTH
   changes are load-bearing and were measured separately.  Written
   without the binders, minimization pins the source at
   [DiscreteCat@{o Set Set}], which is the donor's actual signature and
   the pin §8 exhibits.  And discharging the [fmap_comp] branch with
   [now rewrite id_left] instead of [symmetry; apply id_left] drags
   [Morphisms] universes in that no annotation can bind (the elaborator
   reports an unbound universe, and adding further binders only renames
   it).  A [Program Definition] cannot be annotated here at all, since
   its obligations mint fresh universes; hence the [refine]. *)
Definition disc_ext@{o h p q} {A : Type@{o}} {C : Category@{q h p}}
  (f : A → obj[C]) : DiscreteCat@{o h p} A ⟶ C.
Proof.
  unshelve refine (@Build_Functor (DiscreteCat@{o h p} A) C f
                    (fun x y (e : x = y) =>
                       match e in _ = z return f x ~{C}~> f z with
                       | eq_refl => id end) _ _ _).
  - intros x y e1 e2 He. destruct He. reflexivity.
  - intros x. reflexivity.
  - intros x y z g e. destruct g, e. simpl. symmetry; apply id_left.
Defined.

(** ** §2. The objects functor *)

(* [obj[-]] on objects and [fobj[-]] on arrows.  All three functor laws
   are discharged by the ambient obligation tactic, and there is a reason
   rather than an accident behind that: [fmap_respects] is the FIRST
   PROJECTION of [Functor_StrictEq_Setoid]'s pair, whose first component
   [eq_on_obj] IS the required pointwise Leibniz equality of object maps
   (§6's [objects_respects_StrictCat] writes that projection out as a
   [:=] with no tactic), and the identity and composition laws ask only
   for [∀ x, x = x] on the underlying object maps. *)
Program Definition StrictCat_Objects : StrictCat ⟶ Coq := {|
  fobj := fun C => obj[C];
  fmap := fun _ _ F => fobj[F]
|}.

(** ** §3. The discrete functor *)

(* The three obligations are [fmap_respects], [fmap_id] and [fmap_comp],
   each a strict equality of functors between discrete categories: the
   object component is supplied by the hypothesis (respectively by
   [eq_refl]) and the coherence field vanishes once the discrete
   morphism -- an equality proof -- is destructed. *)
Program Definition StrictCat_Disc : Coq ⟶ StrictCat := {|
  fobj := fun A => DiscreteCat A;
  fmap := fun A B (f : A ~{Coq}~> B) => disc_ext (C := DiscreteCat B) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.

(** ** §4. The adjunction *)

(* The transposition.  A functor out of a discrete category IS its object
   map, and that is the whole content: [to] forgets the arrow action and
   [from] is [disc_ext].  Two obligations remain -- that [from] respects
   [≈], and the round trip [from ∘ to ≈ id]; the other round trip and
   the [Proper] certificate for [to] are discharged by the ambient
   tactic, which is already the strict/[≈] split §5 measures. *)
Program Definition disc_adj_iso (A : obj[Coq]) (C : obj[StrictCat]) :
  @Isomorphism Sets
    {| carrier := @hom StrictCat (StrictCat_Disc A) C
     ; is_setoid := @homset StrictCat (StrictCat_Disc A) C |}
    {| carrier := @hom Coq A (StrictCat_Objects C)
     ; is_setoid := @homset Coq A (StrictCat_Objects C) |} := {|
  to   := {| morphism := fun (F : DiscreteCat A ⟶ C) => fobj[F] |};
  from := {| morphism := fun (f : A → obj[C]) => disc_ext f |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. destruct e.
  unfold Logic.transport, Logic.transport_r, Logic.transport; simpl.
  symmetry; exact (@fmap_id _ _ x a).
Defined.

(* Mac Lane's middle adjunction.  Both naturality clauses close by
   [reflexivity]: [Build_Adjunction'] states them for the FORWARD
   transpose, which lands in [Coq], where [≈] is pointwise [=] and where
   forgetting the arrow action of a composite is forgetting it twice. *)
Definition Disc_Objects_Adjunction : StrictCat_Disc ⊣ StrictCat_Objects.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact disc_adj_iso.
  - intros A B C f g. reflexivity.
  - intros A B C f g. reflexivity.
Defined.

(** ** §5. Strengths, strict first *)

Example objects_obj (C : obj[StrictCat]) :
  fobj[StrictCat_Objects] C = obj[C] := eq_refl.

Example objects_map (C D : obj[StrictCat]) (F : C ~{StrictCat}~> D)
  (x : C) : fmap[StrictCat_Objects] F x = F x := eq_refl.

Example disc_on_obj (A : obj[Coq]) :
  fobj[StrictCat_Disc] A = DiscreteCat A := eq_refl.

Example disc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Disc] f] x = f x := eq_refl.

Example adj_to_forgets (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  to (disc_adj_iso A C) F = fobj[F] := eq_refl.

Example adj_from_extends (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) (x : A) :
  fobj[from (disc_adj_iso A C) f] x = f x := eq_refl.

Example adj_to_from (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) :
  to (disc_adj_iso A C) (from (disc_adj_iso A C) f) = f := eq_refl.

(* The unit is the IDENTITY FUNCTION, not merely a natural isomorphism:
   the transpose of [id] at [StrictCat_Disc A] is [fobj[Id]], which is
   [fun x => x] on the nose.  The counit is the identity on objects, and
   cannot be the identity functor, for the same reason
   Adjunction/Diagonal/Finite.v
   records for the diagonal: [counit] at [C] is a functor
   [StrictCat_Disc (StrictCat_Objects C) ⟶ C] between two DIFFERENT
   categories. *)
Example unit_is_id (A : obj[Coq]) (a : A) :
  @unit _ _ _ _ Disc_Objects_Adjunction A a = a := eq_refl.

Example counit_obj (C : obj[StrictCat])
  (x : StrictCat_Disc (StrictCat_Objects C)) :
  fobj[@counit _ _ _ _ Disc_Objects_Adjunction C] x = x := eq_refl.

(* THE ONE [≈]-ONLY STEP, REFUTED AT [eq_refl] AND THEN LOCALIZED.  The
   two probes below sit either side of a passing control, so the cause is
   read off rather than guessed: the OBJECT map returns on the nose, the
   ARROW map does not, and the residue is exactly [fmap_id]. *)
Fail Example adj_from_to_strict (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) = F := eq_refl.

Example adj_from_to_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) ≈ F.
Proof. exact (iso_from_to (disc_adj_iso A C) F). Qed.

Example roundtrip_obj (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fobj[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] x = fobj[F] x
  := eq_refl.

Fail Example roundtrip_map (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    = fmap[F] (eq_refl : x = x) := eq_refl.

Example roundtrip_map_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    ≈ fmap[F] (eq_refl : x = x).
Proof. symmetry; exact (@fmap_id _ _ F x). Qed.

(* [StrictCat_Disc] is fully faithful, which is what "the unit is the identity"
   says categorically.  Faithfulness costs NOTHING -- the ambient tactic
   discharges it, since injectivity of [fmap[StrictCat_Disc]] is the first
   projection of a strict functor equality.  Fullness costs exactly the
   round trip above, i.e. exactly one [fmap_id]. *)
#[export] Program Instance Disc_Faithful : Faithful StrictCat_Disc.

#[export] Program Instance Disc_Full : Full StrictCat_Disc := {|
  prefmap := fun A B (G : StrictCat_Disc A ~{StrictCat}~> StrictCat_Disc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_from_to (disc_adj_iso x (StrictCat_Disc y)) g).
Defined.

(** ** §6. Why the source is [StrictCat] and not [Cat] *)

(* [ObjRespectsCat] is exactly the [fmap_respects] obligation that ANY
   objects functor owes, at either candidate target: both [Coq]'s
   hom-setoid and [ObjSetoid]'s [equiv] are Leibniz equality of objects,
   so respecting [≈] means carrying [≈]-equal functors to POINTWISE
   LEIBNIZ-EQUAL object maps. *)
Definition ObjRespectsCat : Type :=
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset Cat C D) F G → ∀ x : C, F x = G x.

(* Over [StrictCat] it is the FIRST PROJECTION of the hom-setoid: a [:=]
   with no tactic. *)
Definition objects_respects_StrictCat :
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset StrictCat C D) F G → ∀ x : C, F x = G x :=
  fun C D F G H => `1 H.

Lemma indiscrete_hom_eq (a b : Datatypes.unit) : a = b.
Proof. now destruct a, b. Qed.

(* The witness.  In [Indiscrete bool] every hom-set is [unit], so the
   negation endofunctor is naturally isomorphic to the identity -- the
   component at each object is [tt], invertible by [tt] -- while its
   object map differs from the identity's at [true]. *)
Program Definition SwapI : Indiscrete bool ⟶ Indiscrete bool := {|
  fobj := negb;
  fmap := fun _ _ _ => tt
|}.

Lemma swap_iso_in_Cat :
  @equiv _ (@homset Cat (Indiscrete bool) (Indiscrete bool))
         (Id[Indiscrete bool]) SwapI.
Proof.
  unshelve eexists.
  - intro x. unshelve eexists; simpl; try exact tt; apply indiscrete_hom_eq.
  - intros x y f; simpl; apply indiscrete_hom_eq.
Qed.

(* Hence there is no objects functor over [Cat] INTO A TARGET WHOSE
   MORPHISM [≈] IS POINTWISE LEIBNIZ EQUALITY OF OBJECTS -- [Coq], or
   [Sets] at [ObjSetoid] -- and not merely that this one construction
   fails there.  The qualifier is necessary and is not a hedge: an
   objects functor [Cat ⟶ Sets] over the ISOMORPHISM setoid exists, with
   [fmap_respects] discharged by [fobj_iso].  That is the alternative
   issue #357 item 1 itself offers, and it is excluded here by the
   exercise's request for the strict version, NOT by this theorem. *)
Theorem objects_not_functorial_over_Cat : ObjRespectsCat → False.
Proof.
  intro K.
  exact (eq_ind true (fun b : bool => if b then True else False) I false
           (K _ _ (Id[Indiscrete bool]) SwapI swap_iso_in_Cat true)).
Qed.

(** ** §7. Why the target is [Coq] and not [Sets] *)

(* The mirror-image refutation.  It is stated for an ARBITRARY object map
   [K : obj[Sets] → obj[StrictCat]] rather than for [StrictCat_Disc], because it
   has to be binding on the right-hand wing too: the two instantiations
   at the end of this section are the discrete and the INDISCRETE object
   maps, and both are refuted by the same theorem.

   The hypotheses are the least that make [K] deserve the name: it is
   POINTED (each object of [K A] is named by a point of [A]), that naming
   is INJECTIVE, and it is NATURAL (the arrow action carries the name of
   [x] to the name of [f x]).  Both [DiscreteCat ∘ carrier] and
   [Indiscrete ∘ carrier] satisfy all three with [Kpt] the identity. *)
Definition PointedObjectMap
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A]) : Type :=
  (∀ (A : obj[Sets]) (x y : carrier A), Kpt A x = Kpt A y → x = y)
    * (∀ (A B : obj[Sets]) (f : A ~{Sets}~> B) (x : carrier A),
         fobj[Kmap A B f] (Kpt A x) = Kpt B (f x)).

(* The separating object: [bool] under the everywhere-true setoid.  Two
   constant maps out of it are [≈] without being pointwise equal, which
   is precisely what a [Sets]-morphism may do and a [StrictCat]-morphism
   may not. *)
Program Definition BlurBool : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition kTrue : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => true |}.

Program Definition kFalse : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => false |}.

Lemma k_equiv : kTrue ≈ kFalse.
Proof. intro x; exact I. Qed.

Theorem no_carrier_functor_Sets_StrictCat
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A])
  (HK : PointedObjectMap K Kmap Kpt)
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat (K A) (K B)) (Kmap A B f) (Kmap A B g))
  : False.
Proof.
  destruct HK as [Kinj Kobj].
  pose proof (`1 (Kresp _ _ kTrue kFalse k_equiv) (Kpt BlurBool true)) as H.
  rewrite (Kobj BlurBool BlurBool kTrue true) in H.
  rewrite (Kobj BlurBool BlurBool kFalse true) in H.
  apply Kinj in H.
  discriminate.
Qed.

(* Instantiation 1: the DISCRETE object map on carriers, i.e. §3's
   [StrictCat_Disc] re-aimed at [Sets].  It is refuted. *)
Definition disc_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  DiscreteCat (carrier A) ~{StrictCat}~> DiscreteCat (carrier B) :=
  disc_ext (C := DiscreteCat (carrier B)) f.

Definition disc_carrier_pointed :
  PointedObjectMap (fun A => DiscreteCat (carrier A)) disc_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem disc_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (disc_carrier_Kmap A B f) (disc_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ disc_carrier_pointed Kresp).
Qed.

(* Instantiation 2: the INDISCRETE object map on carriers -- the right
   adjoint of the right-hand wing, re-aimed at [Sets].  It is refuted by
   the SAME theorem, which is why §7 is stated generally.  This is the
   sense in which the codomain decision is binding on that module. *)
Program Definition ind_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  Indiscrete (carrier A) ~{StrictCat}~> Indiscrete (carrier B) := {|
  fobj := f;
  fmap := fun _ _ _ => tt
|}.

Definition ind_carrier_pointed :
  PointedObjectMap (fun A => Indiscrete (carrier A)) ind_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem ind_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (ind_carrier_Kmap A B f) (ind_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ ind_carrier_pointed Kresp).
Qed.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file.  Every negative below
   and in §5 was additionally stripped once and its failure kind read off
   the whole error message -- two CONVERSION failures in §5 (reporting
   "cannot unify", with no universe clause) and three FORMABILITY
   failures here (reporting "universe inconsistency: Cannot enforce ...").
   The two kinds are kept lexically apart. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* Section-local [Universes]/[Constraint] declarations do not leak; the
   Instance/Fun/Group.v precedent applies, so these probes live in the
   library file beside the constants they guard rather than in [Test/].

   FIRST: the [Set] pin of item I.3, guarded rather than merely
   measured.  Four controls fix the levels, the two donors are rejected
   there, and [disc_ext] is accepted at those very levels -- so the
   rejection is attributable to the donors and not to the shape, the
   target, or the ability to name the donor at all.  Stripping either
   [Fail] yields a genuine universe inconsistency reading "Cannot enforce
   Set = uh", naming the culprit on the nose; neither is a typing or a
   conversion failure.

   READ THE [Constraint] BELOW CORRECTLY: IT IS INERT FOR THESE TWO
   NEGATIVES, AND THAT WAS MEASURED RATHER THAN ASSUMED.  Deleting the
   line leaves both [Fail]s still failing, with byte-identical messages,
   because what they fire on is the donors' LITERAL [Set] meeting the
   RIGID declared level [uh] -- not on any relation declared between
   them.  The declaration is kept because it states the intended reading
   and because the last control ([disc_ext] accepted) is only interesting
   above [Set].  Contrast the section after next, where the analogous
   [Constraint] IS load-bearing: deleting it makes that negative succeed
   and the file stops compiling. *)
Section SetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (A : Type@{uo}) (C : Category@{uo uh uh}) (f : A → obj[C]).

  (* controls: the shape and the functor type ARE formable here, and both
     donors ARE nameable -- so the two rejections below are attributable
     to the ASCRIPTION and to nothing else.  The first control is the
     sharpest: it is the very same term as the first negative, minus the
     ascription. *)
  Check (DiscreteCat@{uo uh uh} A).
  Check (DiscreteCat@{uo uh uh} A ⟶ C).
  Check (DiscreteCat_Functor f).
  Check (Indiscrete A).

  (* the two donors are pinned at [Set] and cannot reach them *)
  Fail Check (DiscreteCat_Functor f : DiscreteCat@{uo uh uh} A ⟶ C).
  Fail Check (Indiscrete@{uo} : Type@{uo} → Category@{uo uh uh}).

  (* the replacement does *)
  Check (disc_ext@{uo uh uh uo} f : DiscreteCat@{uo uh uh} A ⟶ C).
End SetPin.

(* SECOND: a DONOR identification, named and not repaired.  An object of
   [StrictCat] has its hom and proof universes identified -- the fourth
   and fifth universe arguments of [StrictCat] are the inner category's
   object and hom-and-proof levels -- so the rejection below reports
   "Cannot enforce cp = ch".  Here the [Constraint] IS load-bearing:
   without it [cp] unifies with [ch] and the negative succeeds.  What is
   NOT identified is object against hom, which is what the following
   section's control shows, its homs sitting strictly BELOW its
   objects. *)
Section StrictCatObjects.
  Universes co ch cp.
  Constraint ch < cp.
  Context (C : Category@{co ch cp}).
  Fail Check (C : obj[StrictCat]).
End StrictCatObjects.

Section StrictCatHomsBelow.
  Universes co ch.
  Constraint ch < co.
  Context (C : Category@{co ch ch}).
  Check (C : obj[StrictCat]).
End StrictCatHomsBelow.

(* THIRD, and this is the guard §5 promised: the identification visible
   in [Disc_Objects_Adjunction]'s BINDER is minimization and not content.
   The adjunction TYPE is formable with the inner categories' hom
   universe declared STRICTLY BELOW their object universe -- here the
   two functors run between [Coq@{e f f f}] and [StrictCat@{c f a f b}],
   whose objects are categories with objects at [f] and homs at [b].

   This is also where the comparison with Instance/Top/Forgetful.v
   belongs.  That file's [Discrete ⊣ Forget ⊣ Indiscrete] for [Top] is
   forced into transposition isomorphisms because [Top]'s homs sit
   strictly above its points, so no single [Sets] serves both directions
   and the packaged [Adjunction] record is unformable at every level.
   NO ANALOGUE OF THAT WALL ARISES HERE: the two functors of this file
   run between one [StrictCat] and one [Coq] in both directions, the record
   is built above, and the check below shows it is not even confined to
   a degenerate universe assignment.

   The [Constraint] here is neither inert nor load-bearing in the sense
   of the two sections above: the [Check] passes with or without it, and
   what the declaration buys is the CONTENT of the control -- without it
   the levels could collapse and the command would demonstrate nothing.
   Stated so that a later reader does not delete it as redundant. *)
Section AdjunctionUniversesSeparated.
  Universes a b c e f.
  Constraint b < f.
  Check (StrictCat_Disc@{a b c f e f} ⊣ StrictCat_Objects@{a c f e f b}).
End AdjunctionUniversesSeparated.

(** ** §9. The objects functor genuinely forgets *)

(* Sharpness for [StrictCat_Objects], proved rather than asserted: it is NOT
   faithful.  The witness is the delooping of the two-element xor monoid
   -- one object, [bool] as its hom-set, [false] as the identity -- which
   carries exactly two endomorphisms as a monoid, the identity and the
   constant.  Both are functors, both have the SAME object map (there is
   only one object), and they differ at the arrow [true]. *)
#[local] Ltac bool_cases :=
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  reflexivity.

Program Definition BoolMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := @eq bool |};
  id      := fun _ => false;
  compose := fun _ _ _ f g => xorb f g
|}.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.

Program Definition ZeroF : BoolMon ⟶ BoolMon := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => false
|}.

(* [poly_unit] has decidable equality, so Hedberg applies and the
   transport in [Functor_StrictEq_Setoid]'s coherence field can be
   eliminated; the argument is axiom-free. *)
Lemma poly_unit_uip (p : @eq poly_unit ttt ttt) : p = eq_refl.
Proof.
  apply (Eqdep_dec.UIP_dec (fun x y : poly_unit => left
    (match x, y with ttt, ttt => eq_refl end))).
Qed.

Lemma Id_neq_ZeroF :
  @equiv _ (@homset StrictCat BoolMon BoolMon) (Id[BoolMon]) ZeroF → False.
Proof.
  intros [eo co].
  pose proof (co ttt ttt true) as H.
  rewrite (poly_unit_uip (eo ttt)) in H.
  simpl in H. discriminate.
Qed.

Example objects_merges :
  fmap[StrictCat_Objects] (Id[BoolMon]) ≈ fmap[StrictCat_Objects] ZeroF.
Proof. intro x; reflexivity. Qed.

Theorem Objects_not_Faithful : Faithful StrictCat_Objects → False.
Proof.
  intro F. exact (Id_neq_ZeroF (fmap_inj _ _ objects_merges)).
Qed.
