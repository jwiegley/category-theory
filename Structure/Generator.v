Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* Generating (separating) families of objects, and single separators

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/generator

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7 ("Subobjects and Generators"), book p. 127 (PDF p. 136),
   Definition 4, is the source: a set of objects GENERATES C when two
   parallel arrows that agree after every arrow out of a member of the
   set are equal.  Mac Lane remarks that "separates" would be the better
   word -- the set separates the arrows of C, it does not build them --
   and this file follows him, keeping "generator" only in the names the
   literature has fixed.  His two illustrations are the one-point set
   for Set and the additive group of integers for Ab; neither is
   discharged IN THIS FILE -- the witnesses are Instance/Sets/Generator.v
   (the singleton and the terminal object), Instance/Grp/Generator.v
   (Awodey's free group on one generator) and Instance/Ab/Generator.v
   (the free abelian group on one generator, Mac Lane's ℤ up to an
   isomorphism that is not in tree), and the NOT DELIVERED paragraph
   below says what each leaves open.

   Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print,
   September 2005), §7.2, printed p. 154 (PDF p. 163), states the
   single-object case and the characterization this file proves: an
   object c of a locally small category is a generator (separator)
   exactly when the covariant representable Hom(c, -) is faithful, that
   is, when arrows out of x are determined by their effect on the
   generalized elements of x based at c.

   Riehl, "Category Theory in Context", 2nd ed., Definition 4.7.7,
   printed p. 177 (PDF p. 197), calls the family a SEPARATING SET and
   defines a COSEPARATING set to be a separating set in the opposite
   category -- the duality that Structure/Generator/Dual.v carries out
   on the nose.  Riehl's Epilogue §E.4, printed p. 257 (PDF p. 277),
   recalls the same notion as clause (vi) of Giraud's theorem, and
   states the joint-faithfulness reading alongside it.

   THE TWO FORMS.  [Generator C] is the family form: a small [Type] of
   indices, an object for each index, and the separation clause.  It is
   shaped field for field after Adjunction/SAFT.v's [Cogenerator],
   its dual, so that the bridge between them moves no data (that bridge
   is Structure/Generator/Dual.v, kept in a separate file because
   SAFT.v's requirement closure must not be pulled into Structure/).
   [IsSeparator c] is Awodey's single-object form, and
   [Generator_of_separator] packages a separator as a family over the
   index [unit].  [separator_of_generator] is the converse, over any
   index type whose elements are all the one index named.

   THE CONSTRUCTIVE READING.  Both clauses are stated POSITIVELY, as
   cancellation laws: if all the tests agree then the arrows agree.
   Riehl's Definition 4.7.7 and the §E.4 recollection are written the
   other way round -- for parallel f ≠ g there are a member G and an
   arrow h : G ~> B with f ∘ h ≠ g ∘ h -- which is the CONTRAPOSITIVE.
   The two readings are not interderivable in this library, and the
   reason is not a shortage of effort.  ≈ is a [crelation], Type-valued
   (Lib/Setoid.v), with no decision procedure and no double-negation
   elimination: from the ≠ form one gets ¬¬(f ≈ g) and stops, and from
   the positive form one gets ¬(∀ tests agree) and stops, an explicit
   witnessing pair (j, k) being exactly what constructive logic does not
   hand back from a negated universal.  What IS free is that last step,
   and it is landed rather than described: [gen_separates_contra] and
   [separator_contra] below take f ≉ g to the statement that the tests
   cannot all agree.  A reader who wants Riehl's form as written must
   supply a decider -- Structure/Complete/Freyd.v's [DecHom] is the
   tree's vocabulary for that -- and nothing here assumes one.  The
   weakened ≠ form is NOT stated as though it were the definition.

   THE IN-TREE SITUATION, MEASURED, AND WHAT THE ISSUE GOT WRONG.
   Issue #447 recorded, as its verified current state, that a search for
   Generator / Separator / SeparatingFamily / Generates finds exactly
   one [Cogenerator] record and nothing else.  That is STALE, and the
   correction is recorded here rather than silently: with
   grep -rn 'Separator' --include='*.v' over this worktree,
   Theory/Concrete.v carries a whole single-object development already.
   [Class Separator (t : C)] is the same condition as [IsSeparator]
   with the two objects implicit; [Separator_of_Faithful] is one half
   of Awodey's characterization, already proved;
   [Concrete_of_Separator] contains the OTHER half, not as a
   named lemma but as the [underlying_faithful] obligation of the
   concretization it builds; and the Sets witness the issue asks for
   is [Sets_Separator], with [Sets_WellPointed] and the
   non-vacuity refutation [Sets_empty_not_Separator] beside it.
   So what is genuinely new here is the FAMILY notion, the joint-
   faithfulness characterization in both directions, the transport
   lemmas, and the duality file -- not the single-object condition.
   [IsSeparator] is kept anyway, and is not a rival: it is the frozen
   interface this issue was built against in parallel, it is Type-valued
   rather than a class (so it composes as a function, which is what
   every characterization below consumes), and
   Structure/Generator/Concrete.v carries the two bridges
   [Separator_of_IsSeparator] / [IsSeparator_of_Separator] in both
   directions, so the tree does not end with two unrelated notions.
   That bridge is a THIRD file for a measured reason: Theory/Concrete.v
   defines [bool_setoid_object] and Instance/Sets.v defines a
   different [bool_setoid_object], so requiring Concrete here
   would shadow the Sets one for every later file, and the witnesses
   built against this interface use Sets.

   The dual side is as the issue described it.  Adjunction/SAFT.v's
   [Cogenerator] is the only cogenerating vocabulary, its header says
   "Equivalently the representables [C(-, cog_obj j)] are jointly
   faithful" as PROSE and proves it nowhere, and exactly one site
   really consumes the field (apply (cog_separates G g1 g2) inside
   [cogenerator_canonical_monic]).  Structure/Generator/Dual.v proves
   that prose, both ways.

   WHAT THE CHARACTERIZATIONS COST: UNPACKING, NOT PROOF.  Every
   equivalence below is a term, never a tactic script, because the two
   sides have literally the same hypothesis once two definitions are
   unfolded.  [Hom c,─] is Functor/Hom.v's [Curried_Hom C] applied to
   c, whose [fmap] at f : x ~> y is the setoid map k ↦ f ∘ k
   (post-composition); the Sets hom-setoid is Instance/Sets.v's
   [SetoidMorphism_equiv], which is pointwise -- f ≈ g means ∀ a, f a ≈
   g a with ≈ taken in the codomain.  So the faithfulness hypothesis
   [fmap[[Hom c,─]] f ≈ fmap[[Hom c,─]] g] unfolds to
   [∀ k : c ~> x, f ∘ k ≈ g ∘ k], which IS the separation hypothesis,
   and the proof term on each side is the identity up to eta.  What is
   NOT free is the packaging: [Faithful] is a one-field CLASS, so
   [Faithful [Hom c,─] := H] with H an [IsSeparator] is REFUSED --
   measured, with the same requirement list:
     Example f2_eq (H : IsSeparator c) : Faithful [Hom c,─] := H.
   is rejected with
     "The term "H" has type "IsSeparator c" while it is expected to have
      type "Faithful (fobj[C] c)"" --
   a class record is not a function.  Hence [Build_Faithful] one way and
   [fmap_inj] the other, and the same for the family form through
   [JointlyFaithful].

   VARIANCE IS THE WHOLE CONTENT, AND THE WRONG ONE IS NOT REFUTED BY
   TYPING ALONE.  For a family [F : J -> C], the statement
   [JointlyFaithful (fun j => [Hom ─, F j])] -- the CONTRAVARIANT
   representables -- is perfectly well formed: [Hom ─, A] is
   Functor/Hom.v's [Curried_CoHom C] at A, a functor C^op ⟶ Sets, so
   the joint-faithfulness statement is about C^op arrows and says that
   the family COseparates.  It is a different statement, not a
   malformed one.  What is refused is deriving it from [Generator C]:
   with the identical proof term, Rocq reports
     "The term "k" has type "gen_obj G j ~{ C }~> y" while it is
      expected to have type
      "carrier (fobj[fobj[Curried_CoHom C] (gen_obj G j)] x)"" --
   the probe object sits at the wrong end of the arrow.  So the reading
   proved below, [generator_jointly_faithful], is the covariant one and
   only that, and the contravariant one is Dual.v's
   [cogenerator_jointly_faithful] over a [Cogenerator].

   WHY THE ISOMORPHISM TRANSPORT IS HERE.  [separator_iso] moves
   [IsSeparator] along c ≅ d.  It is not decoration: the Sets witness
   needs it.  The singleton [unit_setoid_object] (Instance/Sets.v)
   takes its setoid field from Lib/Setoid.v's [unit_setoid], while
   the terminal object of [Sets_Terminal] (Instance/Sets.v) takes
   its from [Unit_Setoid] -- measured, not read off the source:
     Example t1 : @terminal_obj Sets Sets_Terminal
       = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl.
   is ACCEPTED, while
     Example f3_term :
       @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl.
   is rejected with (cannot unify "1" and "unit_setoid_object") -- so
   "the terminal object separates Sets" and "the singleton separates
   Sets" are two statements, and whichever is proved reaches the other
   only along an isomorphism.  [hom_test_iso] is the shared step: it
   carries a family of tests out of d to a family of tests out of c, and
   [separator_iso], [gen_iso] and [gen_family_mono] are its three
   consumers.

   UNIVERSES, measured with [Set Printing Universes. About ...] rather
   than read off the source, which carries no annotation.  [Generator]
   prints as
     Generator@{u u0 u1} : Category@{u0 u1 u1} → Type@{max(u+1,u0,u1)}
   with an EMPTY constraint block, [u] being the level of the index
   [Type]; [IsSeparator@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}},
   obj[C] → Type@{u}] carries only [u0 <= u] and [u1 <= u].  Every
   constant in this file binds its category as [Category@{_ u0 u0}],
   the hom level identified with the proof level.  [JointlyFaithful]
   goes one step further and identifies the two CATEGORIES' hom and
   proof levels with EACH OTHER -- it prints
   [∀ {C : Category@{u1 u2 u2}} {D : Category@{u3 u2 u2}} ...] -- which
   is the shape Theory/Functor.v's [Faithful] already prints and is
   NOT forced by the [Functor] record (Theory/Functor.v prints six
   independent levels with only ≤ bounds between them), so the collapse
   belongs to the faithfulness layer rather than being introduced here.
   The constants that mention [Sets] ([separator_faithful],
   [faithful_separator], [generator_jointly_faithful],
   [jointly_faithful_generator], [generator_iff_jointly_faithful]) carry
   in addition the block of Instance/Sets.v's
   [Sets@{o so} : Category@{so o o}] -- the strict [u0 < u2], the
   setoid-object level above the carrier level, and [u0 <= compose.u0],
   [u0 <= compose.u1], [u0 <= compose.u2], [u0 <= ID.u0] -- together
   with the ≤-bounds [IsSeparator] and [Faithful] contribute themselves
   ([u <= u1], [u0 <= u1], [u <= u3], [u2 <= u3]; an earlier revision of
   this sentence said "exactly the Sets block", which an audit measured
   as four bounds short).  Inherited, and attributed by [About] on
   [Sets], [IsSeparator] and [Faithful] rather than guessed.
   [hom_test_iso] and its three consumers
   carry the stdlib [u0 <= prod_rect.u0/u1/u2]; [gen_extend] adds the
   strict [u0 < u4], which is [iso_id]'s own (Theory/Isomorphism.v
   prints [p < u]); [separator_of_generator] carries
   [u0 <= eq_rect_r.u1] and [u2 <= eq_rect_r.u0], the price of the
   [rewrite] on the index equation.  [gen_separates_contra] has an
   EMPTY block.  No constant in this file is pinned to [Set].

   NOT DELIVERED.  No example in this file: the witnesses live in
   Instance/Sets/Generator.v, Instance/Grp/Generator.v and
   Instance/Ab/Generator.v, and Mac Lane's one-point set for Set was IN
   TREE already under another name (Theory/Concrete.v's
   [Sets_Separator], for the class; Structure/Generator/Concrete.v's
   bridge reads it as an [IsSeparator], and the Sets witness file proves
   the terminal-object statement directly as well).  Mac Lane's integers
   for Ab are delivered only up to the isomorphism ℤ ≅ F_ab(1), which is
   not in tree (Instance/Ab/Generator.v says what it would cost).  No
   name [generator_iff_jointly_faithful] over a BUNDLED [Generator]: the
   issue's pinned name is landed for an unbundled family [F : J -> C]
   ([Separates F]), because a biconditional between [Generator C] and a
   [JointlyFaithful] statement would have to quantify the index on one
   side only.  No collapse of a family to a single
   object: the classical remark that a generating family with a
   coproduct yields the single generator ∐_j G_j is NOT proved, and the
   reason is not cost -- IT IS UNSOUND AS STATED.  Arrows out of a
   coproduct are families of arrows out of the summands, so if one
   summand has no arrow at all into x then no arrow out of ∐_j G_j does
   either, and the separation hypothesis at x is vacuously satisfied
   while the family's is not.  A concrete refutation, in the topos
   Set × Set: {(1, ∅), (∅, 1)} separates (the first factor tests the
   first components, the second the second), its coproduct is (1, 1),
   and Hom((1,1), (2, ∅)) is empty while (2, ∅) carries two distinct
   parallel endomorphisms.  That argument is prose here and is NOT
   formalized -- the tree has no Set × Set instance wired to this file
   -- but it is the reason no [gen_collapse] appears below, and a future
   issue wanting one must first find the hypothesis that repairs it.
   No dense or strong generator: density (Theory/Density.v) and the
   extremal / strong / regular strengthenings of separation are not
   defined, and nothing here says a separating family detects
   isomorphisms or epimorphisms.  No Giraud clause: Riehl §E.4 (vi) is
   cited as the source of the vocabulary only, and no part of Giraud's
   theorem is stated.  No smallness: [gen_index] is a bare [Type] with
   no smallness condition attached, exactly as [cog_index] is in SAFT.v,
   so "set of objects" is read as "family indexed by a Type" throughout.
   No setoid structure on generators: [Generator C] carries no
   equivalence and nothing below respects one; [gen_iso] builds a new
   generator from an old one, it does not identify them.  No adjunction,
   no functoriality, no transport of separation along a functor in
   either direction. *)

(** ** Generating (separating) families and objects *)

(* Mac Lane §V.7 p. 127 / Riehl 4.7.7 / Awodey §7.2: a family of objects
   SEPARATES (generates) C when parallel arrows agreeing after every arrow
   OUT of a member are equal.  Stated positively as a cancellation law,
   the constructively correct reading, exactly as [Cogenerator] states its
   dual. *)
Record Generator {C : Category} := {
  gen_index : Type;
  gen_obj : gen_index -> C;
  gen_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : gen_index) (k : gen_obj j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g
}.

Arguments Generator : clear implicits.
Arguments gen_index {C} _.
Arguments gen_obj {C} _ _.
Arguments gen_separates {C} _ {x y} f g _.

(* Awodey's single-object form: one object whose generalized elements
   distinguish parallel arrows. *)
Definition IsSeparator {C : Category} (c : C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition Generator_of_separator {C : Category} (c : C) (H : IsSeparator c) :
  Generator C := {|
  gen_index := unit;
  gen_obj := fun _ => c;
  gen_separates := fun x y f g Hk => H x y f g (fun k => Hk tt k)
|}.

(* Joint faithfulness of a family of functors: the arrows are told apart
   by SOME member.  For the representables [Hom (gen_obj j), ─] this is
   the separation condition read through [fmap]. *)
Definition JointlyFaithful {C D : Category} {J : Type}
  (F : J -> C ⟶ D) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall j : J, fmap[F j] f ≈ fmap[F j] g) -> f ≈ g.

(** ** Awodey §7.2: separation IS faithfulness of the representable *)

Section Characterizations.

Context {C : Category}.

(* Forward.  The hypothesis of [Faithful [Hom c,─]] at f, g is
   [fmap[[Hom c,─]] f ≈ fmap[[Hom c,─]] g], which unfolds -- through
   Instance/Sets.v's pointwise hom-setoid and Functor/Hom.v's
   post-composition [fmap] -- to [∀ k : c ~> x, f ∘ k ≈ g ∘ k], the
   hypothesis of [IsSeparator c].  Only the packaging moves: [Faithful]
   is a class, so the term is built with its constructor. *)
Definition separator_faithful (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @Build_Faithful C Sets [Hom c,─] (fun x y f g E => H x y f g (fun k => E k)).

(* Backward, by the same unfolding read the other way: [fmap_inj] is the
   field of [Faithful], and its hypothesis is already the separation
   hypothesis. *)
Definition faithful_separator (c : C) (F : Faithful [Hom c,─]) :
  IsSeparator c :=
  fun x y f g H => @fmap_inj _ _ [Hom c,─] F x y f g (fun k => H k).

(** ** Mac Lane §V.7 / Riehl §E.4: the family form is joint faithfulness *)

(* The family of covariant representables on the members of a generating
   family is jointly faithful, and conversely.  The index of the functor
   family is the generator's own index, so the two statements quantify
   over the same [Type]. *)
Definition generator_jointly_faithful (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom gen_obj G j,─]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

Definition jointly_faithful_generator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom F j,─])) : Generator C :=
  @Build_Generator C J F (fun x y f g Hk => H x y f g (fun j k => Hk j k)).

(** ** The single-object / family bridge *)

(* [Generator_of_separator] above is one direction.  This is its converse,
   for a family whose index has only the one element named: the object at
   that index separates by itself.  The transport is on the INDEX, by
   [rewrite] on a Leibniz equation between indices (data, not morphisms),
   after reverting the test arrow whose type mentions it. *)
Definition separator_of_generator (G : Generator C) (j0 : gen_index G)
  (Hsing : forall j : gen_index G, j = j0) : IsSeparator (gen_obj G j0).
Proof.
  intros x y f g H.
  apply (gen_separates G f g); intros j k.
  revert k; rewrite (Hsing j); intros k; apply H.
Defined.

(* The round trip on a separator: packaging it as a [unit]-indexed family
   and reading the object back off gives the separator one started with
   ON THE NOSE -- the composite is [H] at [eq_refl], the index singleton
   condition on [unit] being [eq_refl] at [tt].  This equation is what
   makes the [Defined] above load-bearing: with [separator_of_generator]
   closed by [Qed] the same [eq_refl] is refused (measured).  A first
   draft stated only the TYPE [IsSeparator c], which [H] itself inhabits;
   an audit caught the vacuity and the equation replaced it. *)
Example separator_generator_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(* The issue's pinned name, as the biconditional it names, for an
   UNBUNDLED family [F : J -> C]: [Separates F] is the separation clause
   of [Generator] with the family held fixed, and the two directions are
   the two terms above read at that family.  Type-valued, so the "iff" is
   a pair. *)
Definition Separates {J : Type} (F : J -> C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall (j : J) (k : F j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition generator_iff_jointly_faithful {J : Type} (F : J -> C) :
  (Separates F -> JointlyFaithful (fun j : J => [Hom F j,─])) *
  (JointlyFaithful (fun j : J => [Hom F j,─]) -> Separates F) :=
  (fun H x y f g E => H x y f g (fun j k => E j k),
   fun H x y f g E => H x y f g (fun j k => E j k)).

(* The same bridge one level up, between the two faithfulness notions:
   [JointlyFaithful] over a [unit] index is [Faithful]. *)
Definition jointly_faithful_faithful {D : Category} (F : C ⟶ D)
  (H : Faithful F) : JointlyFaithful (fun _ : unit => F) :=
  fun x y f g E => @fmap_inj _ _ F H x y f g (E tt).

Definition faithful_jointly_faithful {D : Category} (F : C ⟶ D)
  (H : JointlyFaithful (fun _ : unit => F)) : Faithful F :=
  @Build_Faithful C D F (fun x y f g E => H x y f g (fun _ => E)).

End Characterizations.

(** ** Transport along isomorphisms and along maps of index types *)

Section Transport.

Context {C : Category}.

(* The shared step of all three transports below.  If the arrows out of d
   already separate the pair (f, g), so do the arrows out of an isomorphic
   c: test with k ∘ from i and cancel [to i] on the right.  Stated for a
   FIXED pair, because that is what every consumer has in hand. *)
Lemma hom_test_iso {x y : C} (f g : x ~> y) {c d : C} (i : c ≅ d)
  (H : forall k : d ~> x, f ∘ k ≈ g ∘ k) (k : c ~> x) : f ∘ k ≈ g ∘ k.
Proof.
  specialize (H (k ∘ from i)).
  rewrite !comp_assoc in H.
  rewrite <- (id_right (f ∘ k)), <- (id_right (g ∘ k)).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite H.
Qed.

(* Separation is an isomorphism-invariant property of an object.  This is
   what moves a witness between two presentations of the same object --
   see the header on the terminal object of [Sets] and the singleton. *)
Definition separator_iso {c d : C} (H : IsSeparator c) (i : c ≅ d) :
  IsSeparator d :=
  fun x y f g Hk => H x y f g (hom_test_iso f g i Hk).

(* Monotonicity along a map of index types: a family that CONTAINS a
   separating family, each member up to isomorphism, separates.  The new
   family is indexed by K and the old index is carried into it by u. *)
Definition gen_family_mono (G : Generator C) {K : Type} (ob : K -> C)
  (u : gen_index G -> K) (i : forall j, gen_obj G j ≅ ob (u j)) :
  Generator C :=
  @Build_Generator C K ob
    (fun x y f g H =>
       gen_separates G f g (fun j => hom_test_iso f g (i j) (H (u j)))).

(* Replacing each member by an isomorphic object, the index kept. *)
Definition gen_iso (G : Generator C) (d : gen_index G -> C)
  (i : forall j, gen_obj G j ≅ d j) : Generator C :=
  gen_family_mono G d (fun j => j) i.

(* Adding objects to a separating family keeps it separating.  The
   isomorphisms are [iso_id]: on the [inl] summand the two families are
   convertible, so this is the definitional case of [gen_family_mono]. *)
Definition gen_extend (G : Generator C) {K : Type} (ob : K -> C) :
  Generator C :=
  gen_family_mono G (fun jk => match jk with
                               | inl j => gen_obj G j
                               | inr k => ob k
                               end) inl (fun _ => iso_id).

End Transport.

(** ** Riehl's contrapositive reading, as far as it is free *)

Section Contrapositive.

Context {C : Category}.

(* Riehl 4.7.7 states separation as: f ≉ g yields a member and an arrow
   out of it that the two arrows treat differently.  Constructively only
   this much comes back -- the tests cannot ALL agree -- and the step
   from there to an explicit witnessing pair is the one this library
   cannot take without a decider (see the header). *)
Definition gen_separates_contra (G : Generator C) {x y : C} (f g : x ~> y)
  (Hne : f ≈ g -> False) :
  (forall (j : gen_index G) (k : gen_obj G j ~> x), f ∘ k ≈ g ∘ k) -> False :=
  fun H => Hne (gen_separates G f g H).

Definition separator_contra {c : C} (H : IsSeparator c) {x y : C}
  (f g : x ~> y) (Hne : f ≈ g -> False) :
  (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> False :=
  fun Hk => Hne (H x y f g Hk).

End Contrapositive.
