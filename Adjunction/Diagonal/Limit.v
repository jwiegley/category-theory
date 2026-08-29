(** * Limits and colimits as adjoints of the diagonal functor *)

(* nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   Mac Lane, "Categories for the Working Mathematician", Springer GTM 5,
   2nd ed., §IV.2 (p. 87) tabulates the adjoints of the diagonal functor:
   for a fixed index category J the constant-diagram functor
   Δ = Diagonal J : C ⟶ [J, C] has a right adjoint exactly when C has all
   J-shaped limits, and a left adjoint exactly when it has all J-shaped
   colimits, so that the three functors sit in the sandwich

       colim ⊣ Δ ⊣ lim.

   Riehl, "Category Theory in Context", Dover 2016, states the same as
   Proposition 4.6.1, with exercises 4.6.i and 4.6.ii asking respectively
   for the degenerate rows of the table (the unique functor to the point)
   and for the identification of the unit and counit with the universal
   cocone and cone.  Awodey, "Category Theory", Oxford 2nd ed. 2010, §9.3
   runs the same argument for the special shapes, and Mac Lane's §V.2
   Exercise 3 asks for the arrow part: a natural transformation β : F ⟹ F'
   induces lim β : lim F ~> lim F', the unique arrow commuting with the two
   limiting cones.

   The content is entirely the observation that a cone over F with apex x
   IS a natural transformation Δ(x) ⟹ F -- the equivalence Wikipedia
   records under "Cone (category theory)" and which this library already
   proves as [Cone_Natural_Transform] in Structure/Cone/Const.v.  Given
   that identification, the hom-set form of the adjunction

       (Δ(x) ~{[J,C]}~> F)  ≅  (x ~{C}~> lim F)

   is literally the universal property of the limit, read as a bijection
   rather than as unique existence; naturality in both variables is the
   uniqueness clause applied twice.  Everything below is that one move,
   plus its dual, plus the bookkeeping that makes both directions of
   Riehl's proposition into a genuine biconditional.

   Why this presentation earns its keep.  The elementary statement
   "every diagram of shape J has a limit" is a family of unrelated
   universal properties; the adjoint statement packages them into a single
   functor with a single universal property, after which every general
   theorem about adjunctions applies at once -- uniqueness of adjoints,
   composition of adjunctions, and (the reason the sandwich is quoted so
   often) the fact that left adjoints preserve colimits and right adjoints
   preserve limits.  It is also the shape in which Kan introduced the
   subject: Structure/Limit/Kan/Extension.v records the other reading,
   lim F = Ran_(Erase J) F, which is the same universal property with the
   terminal category in place of the point of Cat. *)

(* What is consumed here, and what is built

   CONSUMED, not rebuilt:

     - Functor/Diagonal.v: [Diagonal] and the notation Δ[J](c).
     - Structure/Cone.v: [ACone], [Cone], [Cocone].
     - Structure/Cone/Const.v: [Cone_Natural_Transform], the hom-set
       identification on which the whole file rests.  This is its first
       consumer outside its own module (measured PRE-COMMIT: exactly ONE
       file, its own, mentioned the name; this commit makes it three,
       counting the probe).  It is [Defined], and BOTH directions are
       definitional on components -- pinned in-file as the two [eq_refl]
       Examples [cone_natural_transform_to_component] and
       [cone_natural_transform_from_component].
     - Structure/Limit.v: [Limit], [IsALimit], [Colimit].
     - Structure/Complete.v: [Complete], [Cocomplete].
     - Structure/Limit/Preservation.v: the covariant accessor layer --
       [cone_leg], [limit_leg], [limit_leg_coherence], [limit_med],
       [limit_med_commutes], [limit_med_unique], [limit_med_eq],
       [limit_is_alimit], and dually [cocone_inj], [cocone_inj_coherence],
       [IsAColimit], [colimit_inj], [colimit_inj_coherence],
       [colimit_med], [colimit_med_commutes], [colimit_med_unique],
       [colimit_med_eq], [colimit_apex], [colimit_is_acolimit].  This is
       the single largest saving in the file: it is what lets the colimit
       half be stated and proved covariantly.  Read the covariance claim
       exactly: [Colimit_Diagonal_Adjunction], [ColimitFunctor],
       [Colim_map], [colim_unit], [colimits_iff_diagonal_left_adjoint],
       [colim_unit_is_colimit_inj] and [cocone_apex] carry no [^op] in
       their types, but [Cocone_Natural_Transform] DOES -- its right-hand
       side is an [ACone] over the opposites -- so "no [^op] anywhere a
       consumer can see" would be false, and an audit caught an earlier
       draft saying it.
     - Theory/Adjunction.v: [Adjunction], [unit], [counit],
       [adj_univ_impl], [to_adj_unit], [to_adj_comp_law],
       [from_adj_comp_law], [to_adj_respects], [from_adj_respects].
     - Theory/Kan/Extension.v: [Induced], [Ran], [RightKan];
       Structure/Limit/Kan/Extension.v: [Kan_Limit].
     - Structure/Limit/Terminal.v: [Terminal_Limit].
     - Instance/One.v: [_1], [Erase]; Instance/Zero.v: [_0], [From_0].
     - Instance/Sets/Complete.v: [Sets_Complete];
       Instance/Sets/Cocomplete.v: [Sets_Cocomplete].

   BUILT here:

     - [HasLimitsOfShape J C] / [HasColimitsOfShape J C], the per-shape
       hypotheses.  These, rather than [Complete], because the adjunction
       is about ONE fixed J and taking all shapes would over-assume;
       [Complete_HasLimitsOfShape] and its dual instantiate [Complete] to
       them in one line, so nothing is lost.
     - [LimitFunctor] / [ColimitFunctor] with their arrow parts [Lim_map]
       and [Colim_map] (Mac Lane §V.2 Ex 3), each with its defining
       commuting square ([Lim_map_commutes], [Colim_map_commutes]) and its
       uniqueness clause ([Lim_map_unique], [Colim_map_unique]) as
       separately named lemmas.  All three functor laws come from
       uniqueness of the mediator; none inspects an element.
     - [Diagonal_Limit_Adjunction : Δ[J] ⊣ LimitFunctor] and
       [Colimit_Diagonal_Adjunction : ColimitFunctor ⊣ Δ[J]], both in the
       hom-set form of Theory/Adjunction.v.  The colimit statement is
       COVARIANT: no [^op] occurs in its type.
     - [Cocone_Natural_Transform], the dual of the donor lemma.  The tree
       carries only the cone orientation (measured: [Structure/Cone/Const.v]
       proves [Cone_Natural_Transform] and [Cone_Comma] and nothing else,
       and no file in the tree mentions a cocone counterpart), so it is
       built here out of [cocone_of_transform] and [transform_of_cocone],
       whose component-level round trips hold at [eq_refl] both ways.
     - Riehl Proposition 4.6.1 as a genuine biconditional in both
       variances: [limits_iff_diagonal_right_adjoint] and
       [colimits_iff_diagonal_left_adjoint].  The converse directions are
       [Diagonal_right_adjoint_HasLimits] and
       [Diagonal_left_adjoint_HasColimits], which read the limit cone off
       the counit and the colimit cocone off the unit.
     - Riehl exercise 4.6.ii: [lim_counit_is_limit_leg] and
       [colim_unit_is_colimit_inj].
     - Riehl exercise 4.6.i / Awodey §9.3: the degenerate rows, as
       [Erase_right_adjoint_iff_Terminal] and
       [Erase_left_adjoint_iff_Initial], together with the empty-shape
       corollaries [HasLimitsOfShape_0_iff_Terminal] and
       [Terminal_iff_Diagonal_0_right_adjoint].
     - The Kan comparison [lim_Ran_iso], plus the on-the-nose
       identification of Δ[J](c) with the restriction of the constant
       functor along [Erase J]. *)

(* Strengths, measured strict-first

   TWENTY-FIVE identifications hold at Leibniz [eq] and are shipped as
   [eq_refl] Examples; two further Leibniz equalities,
   [lim_transpose_from_component] and [colim_transpose_to_component], are
   proved by [reflexivity] because they are used as rewrite rules.  The
   ones worth knowing:

     - the donor bijection is definitional on components in both
       directions (the two [cone_natural_transform_*] Examples, and their
       cocone counterparts [cocone_of_transform_inj] and
       [transform_of_cocone_component]);
     - [fobj[LimitFunctor] F] IS [vertex_obj[limit_cone (L F)]], and
       [fobj[ColimitFunctor] F] IS [colimit_apex (L F)];
     - the two transposes of each adjunction ARE the named maps
       ([lim_transpose_to_is_adj] and its three siblings), so a consumer
       who unfolds [adj] meets the construction rather than a repackaging;
     - [transform[lim_counit L F] j = lim_leg L F j ∘ id] and
       [transform[colim_unit M F] j = id ∘ colim_inj M F j];
     - [fobj[Δ[J](c)] j] and [fmap[Δ[J](c)] f] agree on the nose with the
       restriction along [Erase J] of the constant functor [1 ⟶ C];
     - the adjoint produced from a terminal object has that object as its
       value at [ttt], and conversely [terminal_obj] of the recovered
       [Terminal] IS [R ttt].

   FOUR strict attempts were made and REJECTED; each is a CONVERSION
   failure ("cannot unify"), verified by stripping the guard and reading
   the error, and each is stated here so it can be pinned as a probe:

     R1. [transform[lim_counit L F] j = lim_leg L F j] -- the counit
         component carries a residual [∘ id] (the control at
         [lim_leg L F j ∘ id] succeeds), so Riehl 4.6.ii lands at [≈] and
         not at [eq].
     R2. [transform[colim_unit M F] j = colim_inj M F j] -- dually, an
         [id ∘] residue.
     R3. [Δ[J](c) = fobj[Induced (Erase J)] (Diagonal 1 c)] as whole
         records -- both ACTIONS agree at [eq_refl] (shipped as
         [diagonal_is_induced_obj] and [diagonal_is_induced_map]); what
         differs is the three [Functor] law fields, [Compose]'s
         obligations against [Diagonal]'s.  [diagonal_induced_iso] gives
         the identity-component isomorphism instead.
     R4. [_0^op = _0] -- the empty category is not its own opposite on the
         nose (the law fields are rebuilt).  This is why the colimit
         analogue of [Terminal_Limit] is not available by instantiation;
         see the not-delivered list.

   The one place a [Qed] blocks further measurement is [Kan_Limit], which
   Structure/Limit/Kan/Extension.v closes opaquely; consequently
   [lim_Ran_iso] is opaque too (reported by [About]) and neither of its
   legs reduces, so no componentwise statement about it is available. *)

(* Universes, measured off BOTH the binder and the constraint block

   The two readings genuinely disagree in this file, in both directions,
   which is why both are reported.

     - [HasLimitsOfShape@{u u0 u1 u2 u3}] has a constraint block of BOUNDS
       ONLY, with no equation anywhere -- yet its BINDER reads
       [Category@{u1 u2 u2} -> Category@{u3 u2 u2} -> Type@{u}], reusing
       the single level [u2] for J's homs, J's proofs, C's homs and C's
       proofs.  A reader who checks only the block concludes "nothing is
       identified" and is wrong.
     - [LimitFunctor], [Diagonal_Limit_Adjunction], [ColimitFunctor],
       [Colimit_Diagonal_Adjunction], [lim_obj], [Lim_map],
       [Cocone_Natural_Transform], [radj_Limit] and
       [Diagonal_right_adjoint_HasLimits] run the other way: their BINDERS
       read [{J : Category@{u u0 u0}} {C : Category@{u1 u2 u2}}], which
       looks as though J's and C's hom levels are independent, while the
       BLOCK carries [u0 = u2].  So the identification of the two hom
       universes is in the block here and in the binder there.
     - The two headline biconditionals are stated over
       [J : Category@{u u u}] and [C : Category@{u0 u u}]: the index
       category's OBJECT universe additionally collapses onto the shared
       hom level, leaving only C's object universe free.  It enters at the
       PACKAGING and not in either direction: both
       [Diagonal_Limit_Adjunction] and [Diagonal_right_adjoint_HasLimits]
       keep J's object universe free of its hom universe, measured
       separately.  Which of [iffT] and [sigT] is responsible is NOT
       separated -- the packaged statement mentions both -- and nothing
       here says the collapse is unavoidable.
     - The [Erase] rows carry NO [Set].  They did when first written --
       [Terminal_Erase_Adjunction] elaborated at [C : Category@{u3 Set Set}]
       -- and the cause was located rather than guessed: the TYPE
       [Erase C ⊣ Diagonal 1 (terminal_obj)] is formable in a section
       declaring [Constraint Set < ch] (checked), and the same proof text
       compiles there, so the pin was universe minimization at an
       unannotated [Context {C : Category}] and not content.  Declaring
       [Universes eo eh ep] on the section lifts it.  Annotating
       [one_arrow_eq] alone does NOT lift it -- that was tried first and
       the pin persisted, which is what rules the obvious alternative out.
     - [HasLimitsOfShape_0_iff_Terminal] and
       [Terminal_iff_Diagonal_0_right_adjoint] DO carry [Set]:
       [C : Category@{u7 Set Set}].  This is INHERITED, not introduced --
       [Instance/Zero.v]'s own signature is
       [_0@{u u0 u1 u2 u3 u4 u5} : Category@{u Set Set}], its hom type
       being [Empty_set : Set] under an unannotated declaration -- and it
       is not repaired here.  Nothing says it is unavoidable.
     - [Sets_Diagonal_Limit_Adjunction@{u u0 u1}] is over
       [J : Category@{u1 u1 u1}], inherited from
       [Sets_Complete@{u u0} : Complete@{u u u u0}].
     - [sets_bool_lim_two_elements@{u}] carries the single constraint
       [Set < u], from [bool : Set]. *)

(* Non-vacuity

   [Sets] is both complete and cocomplete in tree, so the whole sandwich
   is inhabited there at every shape:
   [Sets_Diagonal_Limit_Adjunction] and [Sets_Colimit_Diagonal_Adjunction].
   That the witness is not degenerate is proved rather than asserted.
   [lim_one_iso] shows that over ANY C with limits of shape [1] the limit
   apex is isomorphic to the value of the diagram at the point; instantiated
   at [Sets] with the constant diagram at the two-element discrete setoid,
   [sets_bool_lim_two_elements] exhibits two elements of the limit apex
   that are provably not [≈]-equal, so the limit functor does not collapse
   its argument to a subsingleton.  The two elements are obtained by
   transporting [true] and [false] backwards along the isomorphism, and
   the separation is discharged by [discriminate] on the underlying
   [bool]; no induction on a limit construction could yield a negative. *)

(* What is NOT delivered

     - No naturality for the Kan comparison.  [lim_Ran_iso] is a FAMILY of
       isomorphisms [lim F ≅ Ran (Erase J) F ttt], not a natural
       isomorphism of functors.  AN EARLIER DRAFT OF THIS BULLET STATED
       THE OBSTRUCTION WRONGLY IN BOTH CLAUSES; an audit refuted each, and
       what follows is the measured position.  An evaluation functor DOES
       exist: Theory/Shapes.v:254's [One_Eval : [_1, C] ⟶ C], whose
       constraint block contains no [Set] and leaves C's three levels
       free.  And [Sets] DOES meet [Category@{o Set Set}] --
       [Check (@One_Fun_iso Sets)] SUCCEEDS, universe polymorphism
       instantiating it at [Sets@{Set _}], the same trap Theory/Size.v's
       erratum records for [Check (Cat : obj[Cat])] -- so "which [Sets]
       does not meet" was false.  What stands: the transport needs the
       OTHER variance, [C ⟶ [1, C]], since
       [Induced (Erase J) : [1,C] ⟶ [J,C]], and both in-tree candidates
       for that direction ([One_Const], [One_Fun_iso]) ARE pinned at
       [Category@{_ Set Set}]; and [Kan_Limit] is [Qed], so [lim_Ran_iso]
       is opaque (confirmed by [About]) and no componentwise access
       exists.  The transport was NOT attempted; neither obstruction is
       claimed unavoidable.
     - No colimit counterpart of the Kan comparison: the tree has no
       [Kan_Colimit], so nothing relates [ColimitFunctor] to [Lan].
     - NO RESTRICTED LIMIT FUNCTOR, and the source issue asks for it in
       its own checkbox: the limit functor on the FULL SUBCATEGORY of
       [[J, C]] spanned by the diagrams that have limits -- the form
       Riehl uses for Corollary 3.3.3, and the one that does NOT require C
       to have all J-shaped limits.  Everything here takes
       [HasLimitsOfShape J C] as a hypothesis, so that checkbox is NOT
       discharged.  Theory/Equivalence/Colimit.v's [limit_induced] is the
       nearest thing in tree -- it needs only the two limits handed to it
       -- but it is a morphism between two supplied limits, not a functor
       on a subcategory, and nothing assembles it into one.
     - No dual of [Terminal_Limit].  Structure/Limit/Terminal.v proves
       only the limit half, and the obvious instantiation does not
       typecheck because [_0^op] is not [_0] (rejection R4 above).  So
       there is no [HasColimitsOfShape 0 C ↔ Initial C] and no
       [Initial_iff_Diagonal_0_left_adjoint]; the initial-object row is
       delivered only in its [Erase] form.
     - No identification of [[0, C]] with [1], hence [Δ[0]] is NOT shown
       to be [Erase C]; the two degenerate readings are connected only
       through [Terminal C], via the composite
       [Terminal_iff_Diagonal_0_right_adjoint].
     - No uniqueness of the adjoint: [left_adjoint_iso] and
       [right_adjoint_iso] are not instantiated, so nothing here says
       [LimitFunctor] is THE right adjoint up to natural isomorphism.
     - No preservation, reflection or creation results, and no
       instantiation of RAPL/LAPC at this sandwich.
     - [LimitFunctor] and [ColimitFunctor] are plain [Definition]s, not
       registered [Instance]s: they take a [HasLimitsOfShape] parameter,
       which is not a class, so resolution could never produce it.
     - The round trips of [Cocone_Natural_Transform] are not proved at the
       level of the packaged bijection -- only the component-level
       identities, which are [eq_refl].  The donor lemma is in the same
       position.
     - The non-vacuity witness lives at the shape [1] only.  Nothing here
       exhibits a non-degenerate limit over a shape with more than one
       object, and the colimit side has no element-level witness at all.
     - No functoriality of [LimitFunctor] in the shape [J], no comparison
       with Instance/Cones/Limit.v's [Limit_Cones], and no connection to
       Structure/Limit/Unique.v. *)

(* Axiom status and counts

   177/177 constants report "Closed under the global context".  Method:
   [Print Module Category.Adjunction.Diagonal.Limit] enumerates 177 names
   (90 printed as [Definition], 87 as [Parameter], the latter being the
   display convention for [Qed] constants, not axioms); the file declares
   no [Record], [Class] or [Inductive], so there is no unlisted [Build_*]
   constructor, and the count includes the 60 [Program] obligations that a
   [.glob] sweep does not record -- the [.glob] shows 117 names, and
   177 - 117 = 60 is exactly the number of [_obligation_] entries in the
   module listing.  Each name was queried by its FULLY QUALIFIED name.
   One measurement anomaly is recorded rather than hidden: a single run of
   all 177 queries reports 176 occurrences of the message, while nine
   chunked runs of at most 20 queries each report exactly one per query
   and cover every name once (20*8 + 17 = 177), as do two halves of 89 and
   88; the chunked counts are the reliable ones. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * Shape-indexed limit and colimit hypotheses *)

Definition HasLimitsOfShape (J C : Category) : Type := ∀ F : J ⟶ C, Limit F.

Definition HasColimitsOfShape (J C : Category) : Type :=
  ∀ F : J ⟶ C, Colimit F.

Definition Complete_HasLimitsOfShape {C : Category} (H : @Complete C)
  (J : Category) : HasLimitsOfShape J C := H J.

Definition Cocomplete_HasColimitsOfShape {C : Category} (H : @Cocomplete C)
  (J : Category) : HasColimitsOfShape J C := H J.

(** * The limit functor and the adjunction Δ ⊣ lim *)

Section LimitAdjunction.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Definition lim_obj (F : J ⟶ C) : C := vertex_obj[@limit_cone J C F (L F)].

Definition lim_alimit (F : J ⟶ C) : IsALimit F (lim_obj F) :=
  limit_is_alimit (L F).

Definition lim_leg (F : J ⟶ C) (j : J) : lim_obj F ~{C}~> F j :=
  limit_leg (lim_alimit F) j.

Lemma lim_leg_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ lim_leg F x ≈ lim_leg F y.
Proof. exact (limit_leg_coherence (lim_alimit F) f). Qed.

Definition lim_med {F : J ⟶ C} (N : Cone F) :
  vertex_obj[N] ~{C}~> lim_obj F := limit_med (lim_alimit F) N.

Lemma lim_med_commutes {F : J ⟶ C} (N : Cone F) (j : J) :
  lim_leg F j ∘ lim_med N ≈ cone_leg N j.
Proof. exact (limit_med_commutes (lim_alimit F) N j). Qed.

Lemma lim_med_unique {F : J ⟶ C} (N : Cone F)
  (u : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) → lim_med N ≈ u.
Proof. exact (limit_med_unique (lim_alimit F) N u). Qed.

Lemma lim_med_eq {F : J ⟶ C} (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ cone_leg N j) →
  (∀ j : J, lim_leg F j ∘ v ≈ cone_leg N j) → u ≈ v.
Proof. exact (limit_med_eq (lim_alimit F) N u v). Qed.

(** ** The action on natural transformations *)

Program Definition Lim_cone {F G : J ⟶ C} (b : F ⟹ G) : Cone G := {|
  vertex_obj := lim_obj F;
  coneFrom := {| vertex_map := fun j => transform[b] j ∘ lim_leg F j |}
|}.
Next Obligation.
  rewrite comp_assoc, naturality, <- comp_assoc, lim_leg_coherence.
  reflexivity.
Qed.

Definition Lim_map {F G : J ⟶ C} (b : F ⟹ G) : lim_obj F ~{C}~> lim_obj G :=
  lim_med (Lim_cone b).

Lemma Lim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  lim_leg G j ∘ Lim_map b ≈ transform[b] j ∘ lim_leg F j.
Proof. exact (lim_med_commutes (Lim_cone b) j). Qed.

Lemma Lim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : lim_obj F ~{C}~> lim_obj G) :
  (∀ j : J, lim_leg G j ∘ u ≈ transform[b] j ∘ lim_leg F j) → Lim_map b ≈ u.
Proof. exact (lim_med_unique (Lim_cone b) u). Qed.

Program Definition LimitFunctor : [J, C] ⟶ C := {|
  fobj := lim_obj;
  fmap := fun _ _ b => Lim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Lim_map_unique; intro j.
  rewrite Lim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  simpl.
  now rewrite id_right, fmap_id, id_left.
Qed.
Next Obligation.
  apply Lim_map_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, Lim_map_commutes.
  now rewrite comp_assoc.
Qed.

(** ** The hom-set bijection Δ(x) ⟹ F  ≅  x ~> lim F *)

Program Definition lim_precone {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : ACone x F := {|
  vertex_map := fun j => lim_leg F j ∘ h
|}.
Next Obligation. now rewrite comp_assoc, lim_leg_coherence. Qed.

Definition lim_transpose_from {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) : Δ[J](x) ⟹ F :=
  snd (Cone_Natural_Transform F x) (lim_precone h).

Definition lim_transpose_cone {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : Cone F :=
  {| vertex_obj := x; coneFrom := fst (Cone_Natural_Transform F x) t |}.

Definition lim_transpose_to {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) : x ~{C}~> lim_obj F := lim_med (lim_transpose_cone t).

Lemma lim_transpose_to_commutes {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  lim_leg F j ∘ lim_transpose_to t ≈ transform[t] j.
Proof. exact (lim_med_commutes (lim_transpose_cone t) j). Qed.

Lemma lim_transpose_to_unique {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (u : x ~{C}~> lim_obj F) :
  (∀ j : J, lim_leg F j ∘ u ≈ transform[t] j) → lim_transpose_to t ≈ u.
Proof. exact (lim_med_unique (lim_transpose_cone t) u). Qed.

Lemma lim_transpose_from_component {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) (j : J) :
  transform[lim_transpose_from h] j = lim_leg F j ∘ h.
Proof. reflexivity. Qed.

(** The donor's bijection is definitional on components, in both
    directions; the whole construction rests on these two. *)

Example cone_natural_transform_to_component {F : J ⟶ C} {x : C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  @vertex_map J C x F (fst (Cone_Natural_Transform F x) t) j
    = transform[t] j := eq_refl.

Example cone_natural_transform_from_component {F : J ⟶ C} {x : C}
  (a : ACone x F) (j : J) :
  transform[snd (Cone_Natural_Transform F x) a] j
    = @vertex_map J C x F a j := eq_refl.

Program Definition lim_adj_iso (x : C) (F : J ⟶ C) :
  @Isomorphism Sets
    {| carrier   := @hom ([J, C]) (Δ[J](x)) F
     ; is_setoid := @homset ([J, C]) (Δ[J](x)) F |}
    {| carrier   := @hom C x (lim_obj F)
     ; is_setoid := @homset C x (lim_obj F) |} := {|
  to   := {| morphism := fun t => lim_transpose_to t |};
  from := {| morphism := fun h => lim_transpose_from h |}
|}.
Next Obligation.
  proper.
  apply lim_transpose_to_unique; intro j.
  rewrite lim_transpose_to_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  now rewrite lim_transpose_from_component.
Qed.
Next Obligation.
  apply lim_transpose_to_commutes.
Qed.

Program Definition Diagonal_Limit_Adjunction : @Diagonal C J ⊣ LimitFunctor :=
  {| adj := lim_adj_iso |}.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  apply lim_transpose_to_unique; intro j.
  rewrite comp_assoc, Lim_map_commutes.
  rewrite <- comp_assoc, lim_transpose_to_commutes.
  reflexivity.
Qed.
Next Obligation.
  rewrite !comp_assoc, Lim_map_commutes.
  reflexivity.
Qed.

(** ** Riehl §4.6 exercise ii: the counit is the limiting cone *)

Definition lim_counit (F : J ⟶ C) : Δ[J](lim_obj F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) LimitFunctor
          Diagonal_Limit_Adjunction F.

Example lim_counit_component_strict (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j = lim_leg F j ∘ id := eq_refl.

Lemma lim_counit_is_limit_leg (F : J ⟶ C) (j : J) :
  transform[lim_counit F] j ≈ lim_leg F j.
Proof. rewrite lim_counit_component_strict; now rewrite id_right. Qed.

(** ** Readbacks against the donor vocabulary *)

Example lim_obj_is_limit_apex (F : J ⟶ C) :
  fobj[LimitFunctor] F = vertex_obj[@limit_cone J C F (L F)] := eq_refl.

Example lim_leg_is_limit_leg (F : J ⟶ C) (j : J) :
  lim_leg F j = limit_leg (lim_alimit F) j := eq_refl.

Example lim_med_is_limit_med {F : J ⟶ C} (N : Cone F) :
  lim_med N = limit_med (lim_alimit F) N := eq_refl.

Example Lim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[LimitFunctor] b = Lim_map b := eq_refl.

Example lim_transpose_to_is_adj {F : J ⟶ C} {x : C} (t : Δ[J](x) ⟹ F) :
  to (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
           Diagonal_Limit_Adjunction x F) t = lim_transpose_to t := eq_refl.

Example lim_transpose_from_is_adj {F : J ⟶ C} {x : C}
  (h : x ~{C}~> lim_obj F) :
  from (@adj ([J, C]) C (@Diagonal C J) LimitFunctor
             Diagonal_Limit_Adjunction x F) h = lim_transpose_from h
  := eq_refl.

End LimitAdjunction.

(** * The colimit functor and the adjunction colim ⊣ Δ *)

Section ColimitAdjunction.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).

Definition colim_obj (F : J ⟶ C) : C := colimit_apex (L F).

Definition colim_acolimit (F : J ⟶ C) : IsAColimit F (colim_obj F) :=
  colimit_is_acolimit (L F).

Definition colim_inj (F : J ⟶ C) (j : J) : F j ~{C}~> colim_obj F :=
  colimit_inj (colim_acolimit F) j.

Lemma colim_inj_coherence (F : J ⟶ C) {x y : J} (f : x ~{J}~> y) :
  colim_inj F y ∘ fmap[F] f ≈ colim_inj F x.
Proof. exact (colimit_inj_coherence (colim_acolimit F) f). Qed.

Definition colim_med {F : J ⟶ C} (N : Cocone F) :
  colim_obj F ~{C}~> vertex_obj[N] := colimit_med (colim_acolimit F) N.

Lemma colim_med_commutes {F : J ⟶ C} (N : Cocone F) (j : J) :
  colim_med N ∘ colim_inj F j ≈ cocone_inj N j.
Proof. exact (colimit_med_commutes (colim_acolimit F) N j). Qed.

Lemma colim_med_unique {F : J ⟶ C} (N : Cocone F)
  (u : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) → colim_med N ≈ u.
Proof. exact (colimit_med_unique (colim_acolimit F) N u). Qed.

Lemma colim_med_eq {F : J ⟶ C} (N : Cocone F)
  (u v : colim_obj F ~{C}~> vertex_obj[N]) :
  (∀ j : J, u ∘ colim_inj F j ≈ cocone_inj N j) →
  (∀ j : J, v ∘ colim_inj F j ≈ cocone_inj N j) → u ≈ v.
Proof. exact (colimit_med_eq (colim_acolimit F) N u v). Qed.

(** ** Building cocones covariantly *)

Program Definition Cocone_of {F : J ⟶ C} (c : C)
  (i : ∀ j : J, F j ~{C}~> c)
  (Hi : ∀ (x y : J) (f : x ~{J}~> y), i y ∘ fmap[F] f ≈ i x) : Cocone F := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := i |}
|}.

Example cocone_of_inj {F : J ⟶ C} (c : C) i Hi (j : J) :
  cocone_inj (@Cocone_of F c i Hi) j = i j := eq_refl.

(** ** The dual of [Cone_Natural_Transform] *)

Program Definition cocone_of_transform {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) : Cocone F :=
  Cocone_of N (fun j => transform[t] j) _.
Next Obligation.
  pose proof (@naturality_sym J C F (Δ[J](N)) t x y f) as HN.
  rewrite HN.
  apply id_left.
Qed.

Definition cocone_apex {F : J ⟶ C} (N : Cocone F) : C :=
  @vertex_obj (J^op) (C^op) (F^op) N.

Program Definition transform_of_cocone {F : J ⟶ C} (N : Cocone F) :
  F ⟹ Δ[J](cocone_apex N) := {|
  transform := fun j => cocone_inj N j
|}.
Next Obligation.
  rewrite (cocone_inj_coherence N f); apply id_left.
Qed.
Next Obligation.
  rewrite (cocone_inj_coherence N f); symmetry; apply id_left.
Qed.

Example cocone_of_transform_inj {F : J ⟶ C} {N : C}
  (t : F ⟹ Δ[J](N)) (j : J) :
  cocone_inj (cocone_of_transform t) j = transform[t] j := eq_refl.

Example transform_of_cocone_component {F : J ⟶ C} (N : Cocone F) (j : J) :
  transform[transform_of_cocone N] j = cocone_inj N j := eq_refl.

Lemma Cocone_Natural_Transform (F : J ⟶ C) (N : C) :
  (F ⟹ Δ[J](N)) ↔ @ACone (J^op) (C^op) N (F^op).
Proof.
  split; intro t.
  - exact (@coneFrom (J^op) (C^op) (F^op) (cocone_of_transform t)).
  - exact (transform_of_cocone (@Build_Cone (J^op) (C^op) (F^op) N t)).
Defined.

(** ** The action on natural transformations *)

Program Definition Colim_cocone {F G : J ⟶ C} (b : F ⟹ G) : Cocone F :=
  Cocone_of (colim_obj G) (fun j => colim_inj G j ∘ transform[b] j) _.
Next Obligation.
  pose proof (@naturality J C F G b x y f) as HN.
  rewrite <- comp_assoc, <- HN.
  now rewrite comp_assoc, colim_inj_coherence.
Qed.

Definition Colim_map {F G : J ⟶ C} (b : F ⟹ G) :
  colim_obj F ~{C}~> colim_obj G := colim_med (Colim_cocone b).

Lemma Colim_map_commutes {F G : J ⟶ C} (b : F ⟹ G) (j : J) :
  Colim_map b ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j.
Proof. exact (colim_med_commutes (Colim_cocone b) j). Qed.

Lemma Colim_map_unique {F G : J ⟶ C} (b : F ⟹ G)
  (u : colim_obj F ~{C}~> colim_obj G) :
  (∀ j : J, u ∘ colim_inj F j ≈ colim_inj G j ∘ transform[b] j) →
  Colim_map b ≈ u.
Proof. exact (colim_med_unique (Colim_cocone b) u). Qed.

Program Definition ColimitFunctor : [J, C] ⟶ C := {|
  fobj := colim_obj;
  fmap := fun _ _ b => Colim_map b
|}.
Next Obligation.
  proper.
  symmetry.
  apply Colim_map_unique; intro j.
  rewrite Colim_map_commutes.
  now rewrite (X j).
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  simpl.
  now rewrite id_left, fmap_id, id_right.
Qed.
Next Obligation.
  apply Colim_map_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  rewrite comp_assoc, Colim_map_commutes.
  now rewrite <- comp_assoc.
Qed.

(** ** The hom-set bijection colim F ~> y  ≅  F ⟹ Δ(y) *)

Program Definition colim_transpose_to {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) : F ⟹ Δ[J](y) := {|
  transform := fun j => u ∘ colim_inj F j
|}.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.
Next Obligation.
  now rewrite <- comp_assoc, (colim_inj_coherence F f), id_left.
Qed.

Definition colim_transpose_from {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  colim_obj F ~{C}~> y := colim_med (cocone_of_transform t).

Lemma colim_transpose_from_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  colim_transpose_from t ∘ colim_inj F j ≈ transform[t] j.
Proof. exact (colim_med_commutes (cocone_of_transform t) j). Qed.

Lemma colim_transpose_from_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (u : colim_obj F ~{C}~> y) :
  (∀ j : J, u ∘ colim_inj F j ≈ transform[t] j) → colim_transpose_from t ≈ u.
Proof. exact (colim_med_unique (cocone_of_transform t) u). Qed.

Lemma colim_transpose_to_component {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) (j : J) :
  transform[colim_transpose_to u] j = u ∘ colim_inj F j.
Proof. reflexivity. Qed.

Program Definition colim_adj_iso (F : J ⟶ C) (y : C) :
  @Isomorphism Sets
    {| carrier   := @hom C (colim_obj F) y
     ; is_setoid := @homset C (colim_obj F) y |}
    {| carrier   := @hom ([J, C]) F (Δ[J](y))
     ; is_setoid := @homset ([J, C]) F (Δ[J](y)) |} := {|
  to   := {| morphism := fun u => colim_transpose_to u |};
  from := {| morphism := fun t => colim_transpose_from t |}
|}.
Next Obligation.
  proper.
  apply colim_transpose_from_unique; intro j.
  rewrite colim_transpose_from_commutes.
  now rewrite (X j).
Qed.
Next Obligation. apply colim_transpose_from_commutes. Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite colim_transpose_to_component.
Qed.

Program Definition Colimit_Diagonal_Adjunction :
  ColimitFunctor ⊣ @Diagonal C J := {| adj := colim_adj_iso |}.
Next Obligation.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  rewrite <- comp_assoc, Colim_map_commutes.
  now rewrite comp_assoc, colim_transpose_from_commutes.
Qed.
Next Obligation.
  apply colim_transpose_from_unique; intro j.
  now rewrite <- comp_assoc, colim_transpose_from_commutes.
Qed.

(** ** Riehl §4.6 exercise ii: the unit is the colimiting cocone *)

Definition colim_unit (F : J ⟶ C) : F ⟹ Δ[J](colim_obj F) :=
  @unit C ([J, C]) ColimitFunctor (@Diagonal C J)
        Colimit_Diagonal_Adjunction F.

Example colim_unit_component_strict (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j = id ∘ colim_inj F j := eq_refl.

Lemma colim_unit_is_colimit_inj (F : J ⟶ C) (j : J) :
  transform[colim_unit F] j ≈ colim_inj F j.
Proof. rewrite colim_unit_component_strict; now rewrite id_left. Qed.

(** ** Readbacks against the donor vocabulary *)

Example colim_obj_is_colimit_apex (F : J ⟶ C) :
  fobj[ColimitFunctor] F = colimit_apex (L F) := eq_refl.

Example colim_inj_is_colimit_inj (F : J ⟶ C) (j : J) :
  colim_inj F j = colimit_inj (colim_acolimit F) j := eq_refl.

Example colim_med_is_colimit_med {F : J ⟶ C} (N : Cocone F) :
  colim_med N = colimit_med (colim_acolimit F) N := eq_refl.

Example Colim_map_is_fmap {F G : J ⟶ C} (b : F ⟹ G) :
  fmap[ColimitFunctor] b = Colim_map b := eq_refl.

Example colim_transpose_to_is_adj {F : J ⟶ C} {y : C}
  (u : colim_obj F ~{C}~> y) :
  to (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
           Colimit_Diagonal_Adjunction F y) u = colim_transpose_to u
  := eq_refl.

Example colim_transpose_from_is_adj {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) :
  from (@adj C ([J, C]) ColimitFunctor (@Diagonal C J)
             Colimit_Diagonal_Adjunction F y) t = colim_transpose_from t
  := eq_refl.

End ColimitAdjunction.

(** * Riehl §4.6 Proposition 4.6.1, the converse directions *)

Section RightAdjointGivesLimits.

Context {J C : Category}.
Context {R : [J, C] ⟶ C}.
Context (A : @Diagonal C J ⊣ R).

Definition radj_counit (F : J ⟶ C) : Δ[J](R F) ⟹ F :=
  @counit ([J, C]) C (@Diagonal C J) R A F.

Definition radj_transpose {x : C} {F : J ⟶ C} (t : Δ[J](x) ⟹ F) :
  x ~{C}~> R F := to (@adj ([J, C]) C (@Diagonal C J) R A x F) t.

Lemma radj_transpose_commutes {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (j : J) :
  transform[radj_counit F] j ∘ radj_transpose t ≈ transform[t] j.
Proof.
  pose proof (snd (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t
                     (radj_transpose t)) (reflexivity _)) as HU.
  symmetry; exact (HU j).
Qed.

Lemma radj_transpose_unique {x : C} {F : J ⟶ C}
  (t : Δ[J](x) ⟹ F) (v : x ~{C}~> R F) :
  (∀ j : J, transform[radj_counit F] j ∘ v ≈ transform[t] j) →
  radj_transpose t ≈ v.
Proof.
  intro Hv.
  apply (fst (@adj_univ_impl ([J, C]) C (@Diagonal C J) R A x F t v)).
  intro j; symmetry; exact (Hv j).
Qed.

Program Definition radj_cone (F : J ⟶ C) : Cone F := {|
  vertex_obj := R F;
  coneFrom := fst (Cone_Natural_Transform F (R F)) (radj_counit F)
|}.

Program Definition radj_Limit (F : J ⟶ C) : Limit F := {|
  limit_cone := radj_cone F
|}.
Next Obligation.
  unshelve econstructor.
  - exact (radj_transpose
             (snd (Cone_Natural_Transform F (vertex_obj[N]))
                  (@coneFrom J C F N))).
  - intro j; apply radj_transpose_commutes.
  - intros v Hv; apply radj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_right_adjoint_HasLimits : HasLimitsOfShape J C :=
  radj_Limit.

End RightAdjointGivesLimits.

Section LeftAdjointGivesColimits.

Context {J C : Category}.
Context {K : [J, C] ⟶ C}.
Context (A : K ⊣ @Diagonal C J).

Definition ladj_unit (F : J ⟶ C) : F ⟹ Δ[J](K F) :=
  @unit C ([J, C]) K (@Diagonal C J) A F.

Definition ladj_transpose {F : J ⟶ C} {y : C} (t : F ⟹ Δ[J](y)) :
  K F ~{C}~> y := from (@adj C ([J, C]) K (@Diagonal C J) A F y) t.

Lemma ladj_transpose_commutes {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (j : J) :
  ladj_transpose t ∘ transform[ladj_unit F] j ≈ transform[t] j.
Proof.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y
                (ladj_transpose t)) as H1.
  pose proof (@from_adj_comp_law C ([J, C]) K (@Diagonal C J) A F y t) as H2.
  rewrite <- (H1 j); exact (H2 j).
Qed.

Lemma ladj_transpose_unique {F : J ⟶ C} {y : C}
  (t : F ⟹ Δ[J](y)) (v : K F ~{C}~> y) :
  (∀ j : J, v ∘ transform[ladj_unit F] j ≈ transform[t] j) →
  ladj_transpose t ≈ v.
Proof.
  intro Hv.
  pose proof (@to_adj_unit C ([J, C]) K (@Diagonal C J) A F y v) as H1.
  assert (Ht : to (@adj C ([J, C]) K (@Diagonal C J) A F y) v ≈ t).
  { intro j; rewrite (H1 j); exact (Hv j). }
  transitivity (from (@adj C ([J, C]) K (@Diagonal C J) A F y)
                     (to (@adj C ([J, C]) K (@Diagonal C J) A F y) v)).
  - apply from_adj_respects; symmetry; exact Ht.
  - apply to_adj_comp_law.
Qed.

Program Definition ladj_Colimit (F : J ⟶ C) : Colimit F := {|
  limit_cone := cocone_of_transform (ladj_unit F)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (ladj_transpose (transform_of_cocone N)).
  - intro j; apply ladj_transpose_commutes.
  - intros v Hv; apply ladj_transpose_unique; exact Hv.
Qed.

Definition Diagonal_left_adjoint_HasColimits : HasColimitsOfShape J C :=
  ladj_Colimit.

End LeftAdjointGivesColimits.

Theorem limits_iff_diagonal_right_adjoint (J C : Category) :
  HasLimitsOfShape J C ↔ { R : [J, C] ⟶ C & @Diagonal C J ⊣ R }.
Proof.
  split.
  - intro L; exists (LimitFunctor L); exact (Diagonal_Limit_Adjunction L).
  - intros [R A]; exact (Diagonal_right_adjoint_HasLimits A).
Defined.

Theorem colimits_iff_diagonal_left_adjoint (J C : Category) :
  HasColimitsOfShape J C ↔ { K : [J, C] ⟶ C & K ⊣ @Diagonal C J }.
Proof.
  split.
  - intro L; exists (ColimitFunctor L); exact (Colimit_Diagonal_Adjunction L).
  - intros [K A]; exact (Diagonal_left_adjoint_HasColimits A).
Defined.

(** * Awodey §9.3 / Riehl §4.6 exercise i: the degenerate rows *)

Lemma one_arrow_eq@{u} (a b : poly_unit@{u}) : a = b.
Proof. now destruct a, b. Qed.

Section EraseAdjunctions.

(* The universe binders are declared explicitly: written against an
   unannotated [Context {C : Category}] the two definitions below minimize
   C's hom and proof universes to [Set] (measured), which the statement
   itself does not require. *)
Universes eo eh ep.
Context {C : Category@{eo eh ep}}.

Program Definition Terminal_Erase_Adjunction (T : @Terminal C) :
  Erase C ⊣ @Diagonal C _1 (@terminal_obj C T) := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => @one C T x |}
     ; from := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply one_unique | apply one_arrow_eq ]. Qed.

Program Definition Initial_Erase_Adjunction (I : @Initial C) :
  @Diagonal C _1 (@initial_obj C I) ⊣ Erase C := {|
  adj := fun x y =>
    {| to   := {| morphism := fun _ => ttt |}
     ; from := {| morphism := fun _ => @zero C I y |} |}
|}.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.
Next Obligation. first [ apply zero_unique | apply one_arrow_eq ]. Qed.

End EraseAdjunctions.

Program Definition Erase_right_adjoint_Terminal {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) : @Terminal C := {|
  terminal_obj := R ttt;
  one := fun x => to (@adj _1 C (Erase C) R A x ttt) ttt
|}.
Next Obligation.
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt f).
  rewrite <- (@from_adj_comp_law _1 C (Erase C) R A x ttt g).
  apply to_adj_respects, one_arrow_eq.
Qed.

Program Definition Erase_left_adjoint_Initial {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) : @Initial C := {|
  terminal_obj := K ttt;
  one := fun x => from (@adj C _1 K (Erase C) A ttt x) ttt
|}.
Next Obligation.
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x f).
  rewrite <- (@to_adj_comp_law C _1 K (Erase C) A ttt x g).
  apply from_adj_respects, one_arrow_eq.
Qed.

Theorem Erase_right_adjoint_iff_Terminal (C : Category) :
  @Terminal C ↔ { R : _1 ⟶ C & Erase C ⊣ R }.
Proof.
  split.
  - intro T.
    exists (@Diagonal C _1 (@terminal_obj C T)).
    exact (Terminal_Erase_Adjunction T).
  - intros [R A]; exact (Erase_right_adjoint_Terminal A).
Defined.

Theorem Erase_left_adjoint_iff_Initial (C : Category) :
  @Initial C ↔ { K : _1 ⟶ C & K ⊣ Erase C }.
Proof.
  split.
  - intro I.
    exists (@Diagonal C _1 (@initial_obj C I)).
    exact (Initial_Erase_Adjunction I).
  - intros [K A]; exact (Erase_left_adjoint_Initial A).
Defined.

(** The adjoint's value at the unique object IS the (co)terminal object. *)

Example Erase_right_adjoint_value {C : Category} {R : _1 ⟶ C}
  (A : Erase C ⊣ R) :
  @terminal_obj C (Erase_right_adjoint_Terminal A) = R ttt := eq_refl.

Example Erase_left_adjoint_value {C : Category} {K : _1 ⟶ C}
  (A : K ⊣ Erase C) :
  @initial_obj C (Erase_left_adjoint_Initial A) = K ttt := eq_refl.

Example Terminal_Erase_value {C : Category} (T : @Terminal C) :
  fobj[@Diagonal C _1 (@terminal_obj C T)] ttt = @terminal_obj C T := eq_refl.

Example Initial_Erase_value {C : Category} (I : @Initial C) :
  fobj[@Diagonal C _1 (@initial_obj C I)] ttt = @initial_obj C I := eq_refl.

(** The empty shape: limits of shape 0 are exactly terminal objects. *)

Theorem HasLimitsOfShape_0_iff_Terminal (C : Category) :
  HasLimitsOfShape 0 C ↔ @Terminal C.
Proof.
  split.
  - intro H; exact (fst (Terminal_Limit C (From_0 C)) (H (From_0 C))).
  - intros T F; exact (snd (Terminal_Limit C F) T).
Defined.

Corollary Terminal_iff_Diagonal_0_right_adjoint (C : Category) :
  @Terminal C ↔ { R : [0, C] ⟶ C & @Diagonal C 0 ⊣ R }.
Proof.
  split.
  - intro T.
    exact (fst (limits_iff_diagonal_right_adjoint 0 C)
               (snd (HasLimitsOfShape_0_iff_Terminal C) T)).
  - intro H.
    exact (fst (HasLimitsOfShape_0_iff_Terminal C)
               (snd (limits_iff_diagonal_right_adjoint 0 C) H)).
Defined.

(** * Comparison with the right Kan extension along Erase J *)

Section KanComparison.

Context {J C : Category}.

(** The diagonal is the restriction along [Erase J] of the constant
    functor [1 ⟶ C], on both actions and on the nose. *)

Example diagonal_is_induced_obj (c : C) (j : J) :
  fobj[Δ[J](c)] j
    = fobj[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] j := eq_refl.

Example diagonal_is_induced_map (c : C) (x y : J) (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f
    = fmap[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] f := eq_refl.

Program Definition diagonal_induced_iso (c : C) :
  @Isomorphism ([J, C]) (Δ[J](c))
    (fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)) := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

Context (L : HasLimitsOfShape J C).
Context `{RK : @RightKan J _1 (Erase J) C}.

Corollary lim_Ran_iso (F : J ⟶ C) : lim_obj L F ≅ Ran (Erase J) F ttt.
Proof. exact (@Kan_Limit J C F (L F) RK). Qed.

End KanComparison.

(** * Non-vacuity: the shape 1, and the sandwich at Sets *)

Section OneShapeLimit.

Context {C : Category}.
Context (L : HasLimitsOfShape _1 C).

Program Definition lim_one_acone (F : _1 ⟶ C) : ACone (F ttt) F := {|
  vertex_map := fun x => match x as x' return (F ttt ~{C}~> F x') with
                         | ttt => id
                         end
|}.
Next Obligation.
  destruct x, y, f.
  pose proof (@fmap_id _1 C F ttt) as HI; simpl in HI.
  now rewrite HI, id_left.
Qed.

Definition lim_one_cone (F : _1 ⟶ C) : Cone F :=
  {| vertex_obj := F ttt; coneFrom := lim_one_acone F |}.

Program Definition lim_one_iso (F : _1 ⟶ C) : lim_obj L F ≅ F ttt := {|
  to   := lim_leg L F ttt;
  from := lim_med L (lim_one_cone F)
|}.
Next Obligation. exact (lim_med_commutes L (lim_one_cone F) ttt). Qed.
Next Obligation.
  apply (lim_med_eq L (@limit_cone _1 C F (L F))); intro j; destruct j.
  - rewrite comp_assoc, (lim_med_commutes L (lim_one_cone F) ttt).
    now rewrite id_left.
  - now rewrite id_right.
Qed.

End OneShapeLimit.

Definition Sets_HasLimitsOfShape (J : Category) : HasLimitsOfShape J Sets :=
  Complete_HasLimitsOfShape Sets_Complete J.

Definition Sets_HasColimitsOfShape (J : Category) :
  HasColimitsOfShape J Sets :=
  Cocomplete_HasColimitsOfShape Sets_Cocomplete J.

Definition Sets_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (Sets_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (Sets_HasLimitsOfShape J).

Definition Sets_Colimit_Diagonal_Adjunction (J : Category) :
  ColimitFunctor (Sets_HasColimitsOfShape J) ⊣ @Diagonal Sets J :=
  Colimit_Diagonal_Adjunction (Sets_HasColimitsOfShape J).

Definition DiagBoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition SetsBoolDiagram : _1 ⟶ Sets := @Diagonal Sets _1 DiagBoolSet.

Definition sets_bool_lim_iso :
  lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram ≅ DiagBoolSet :=
  lim_one_iso (Sets_HasLimitsOfShape _1) SetsBoolDiagram.

Lemma sets_bool_lim_two_elements :
  { a : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
  & { b : carrier (lim_obj (Sets_HasLimitsOfShape _1) SetsBoolDiagram)
    & a ≈ b → False } }.
Proof.
  exists (from sets_bool_lim_iso true).
  exists (from sets_bool_lim_iso false).
  intro H.
  pose proof (iso_to_from sets_bool_lim_iso true) as H1.
  pose proof (iso_to_from sets_bool_lim_iso false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso true)).
    - symmetry; exact H1.
    - transitivity (to sets_bool_lim_iso (from sets_bool_lim_iso false)).
      + apply (proper_morphism (to sets_bool_lim_iso)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.
