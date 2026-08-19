Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.

Generalizable All Variables.

(** * Postcomposition, and the invariance of naturality under enlargement *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §III.2, Exercise 4 and the
              large-categories remark, printed p. 62 (PDF p. 71) —
              catalog items `maclane:III.2:ex4`, `maclane:III.2:remark1`
   nLab:      https://ncatlab.org/nlab/show/full+subcategory
   nLab:      https://ncatlab.org/nlab/show/whiskering
   Wikipedia: https://en.wikipedia.org/wiki/Full_subcategory

   Mac Lane's exercise.  Let J : E ↪ E′ be the inclusion of a full
   subcategory and let K, L : D ⟶ E be two functors.  A natural
   transformation K ⟹ L, computed inside E, is the same thing as a natural
   transformation J◯K ⟹ J◯L, computed inside the larger E′.  Nothing about
   naturality changes when the ambient category is enlarged, as long as the
   enlargement adds no new arrows between the objects already present.  That
   is the reason a size-conscious reader of the Yoneda lemma need not worry
   about WHICH category of sets the presheaves land in.

   What is delivered here, and at what strength
   --------------------------------------------

     [Postcompose J : [D, E] ⟶ [D, E′]]
         the postcomposition functor J ◯ −, for an ARBITRARY functor
         J : E ⟶ E′ (no fullness, no faithfulness, no subcategory).  Its
         action on 2-cells is left whiskering, [J ⊳ θ], on the nose.

     [Postcompose_Faithful]   J faithful ⟹ [Postcompose J] faithful.
     [Postcompose_Full]       J full AND faithful ⟹ [Postcompose J] full.

     [postcompose_hom_iso]    the Nat-setoid isomorphism
                                (K ⟹ L) ≊ (J◯K ⟹ J◯L)
                              in [Sets], for J full and faithful.  This is
                              Mac Lane's statement; the two legs are left
                              whiskering and [prefmap].

     [sub_postcompose_hom_iso]
                              the same at a FULL SUBCATEGORY inclusion, over
                              Construction/Subcategory.v's [Incl_Faithful]
                              and [Full_Implies_Full_Functor] — Mac Lane's
                              own hypothesis.

     [finpost_hom_iso] and the [finpost_*] family
                              the concrete witness: J := [FinSets_Incl], the
                              inclusion of the finite setoids into [Sets]
                              (Construction/Subcategory/Finite.v, which is
                              Mac Lane's §I.3 example of a full
                              subcategory), with both Nat-setoids proved to
                              have at least two elements and the fullness
                              direction exercised on a transformation
                              exhibited DOWNSTAIRS in [Sets].

     [postcompose_full_needs_full]
                              a boundary: fullness of [Postcompose J] is not
                              automatic.  For the inclusion of the discrete
                              two-object category into the walking arrow —
                              faithful, and provably not full — the
                              postcomposition functor is not full either.

   The status of the pre-existing artifacts (a correction)
   -------------------------------------------------------

   Issue #318 states that "no postcomposition functor [D, E] ⟶ [D, E′] along
   a functor J is defined anywhere".  That is NOT accurate, and this file
   does not repeat it.  Two artifacts already in the tree compose to give
   exactly such a functor:

     - Instance/Cat/Bicategory.v's [Cat_Hcompose {C D E} :
       ([D,E] ∏ [C,D]) ⟶ [C,E]], horizontal composition as a bifunctor; and
     - Functor/Bifunctor/Partial.v's [Partial_r F b], which freezes a
       bifunctor's first argument.

   So [Partial_r Cat_Hcompose J] IS a postcomposition functor, and it is
   built here as [PostcomposeViaHcompose] and COMPARED with [Postcompose]
   rather than ignored.  The comparison was measured strict-first and the
   result decided the design:

     - the OBJECT actions agree by [eq_refl]
       ([postcompose_via_hcompose_obj]);
     - the ARROW actions do NOT.  The Hcompose route's component at x is
       [fmap[J] id ∘ fmap[J] (θ x)] — recorded on the nose by
       [postcompose_via_hcompose_component] — because [bimap F id g] feeds
       an identity 2-cell into the Godement product, whose component
       [transform[nat_id] (L x)] is [fmap[J] id] rather than [id].  The
       Leibniz identification of the two [fmap]s is REFUTED, and pinned as a
       conversion negative in Test/ProbePostcompose.v.
     - they agree up to `≈` ([postcompose_via_hcompose_fmap]), and hence in
       [Cat]'s hom-setoid with identity comparison components
       ([postcompose_via_hcompose_equiv]) — a functor is a MORPHISM of [Cat],
       not an object of it.

   The unit is not cosmetic: it would sit inside every naturality
   computation below, and in particular [Full]'s section law [fmap_sur]
   would no longer be [fmap_sur] of J applied at a component.  So
   [Postcompose] is built directly.  Note what "directly" means here — the
   [fmap] field IS Theory/Natural/Transformation.v's existing [whisker_left],
   so the arrow action is reused verbatim and only the three functor laws
   are new (one line each).  What is declined is [Cat_Hcompose]'s PACKAGING,
   for the measured reason above, together with its dependency on the
   bicategory tower; the tower is nevertheless required by this file, since
   the comparison is stated rather than merely asserted.

   The mirror, which the issue does not mention: Theory/Kan/Extension.v:131's
   [Induced : [B,C] ⟶ [A,C]] is the PREcomposition functor (− ◯ F), the
   restriction along which Kan extensions are the adjoints.  [Postcompose] is
   its companion in the other variable, and the two together are the two
   partial functors of [Cat_Hcompose].  No fullness or faithfulness result is
   proved about [Induced] anywhere, and none is proved here.

   What was actually absent (measured, not assumed)
   ------------------------------------------------

   The tree DOES carry [Full]/[Faithful] results about functors whose TARGET
   is a functor category — [Yoneda_Full] and [Yoneda_Faithful] for
   [Curried_Hom C : C^op ⟶ [C, Sets]] (Functor/Hom.v), and their
   contravariant twins in Functor/Hom/Yoneda/Iso.v — and at least two about a
   functor whose SOURCE is a full subcategory of a functor category:
   [ReprObj_Full]/[ReprObj_Faithful] (Functor/Representable/Functorial.v), and
   — closer to this file's subject, since its TARGET is a functor category
   too — [Sheaves_Full]/[Sheaves_Faithful] for
   [Sheaves_Incl : Sheaves ⟶ @Presheaves C Sets] (Theory/Sheaf/Category.v:94
   and :103, over [Sheaves := Sub (@Presheaves C Sets) Sheaves_sub] at :81).
   What the tree does not carry is any such result about a functor whose
   source AND target are both functor categories — note that [Sub X P] is a
   subcategory of a functor category, not one itself, which is what keeps
   that claim alive.  Scope the enumeration behind it precisely: among
   functors DECLARED with an explicit [X ⟶ Y] type whose two sides are both
   functor categories, the tree has [Induced] and the [Ran]/[Lan] fields of
   Theory/Kan/Extension.v, and no [Full] or [Faithful] statement mentions any
   of them.  Functors of that shape reached otherwise are deliberately
   outside that enumeration and are NOT claimed absent — the legs of
   [Cat_exp_prod_l : @Isomorphism Cat ([C ∏ D, E]) ([C, [D, E]])]
   (Instance/Cat/Exponential.v:57) are two such, as is
   [Partial_r Cat_Hcompose J] above; none carries a [Full]/[Faithful] result
   either, but the enumeration is not what establishes that.

   Nor does any in-tree isomorphism of transformation setoids have this
   shape.  The closest relatives are [left_adjoint_impl]
   (Theory/Kan/Extension.v:333, a Nat-setoid ≊ Nat-setoid isomorphism that
   does involve postcomposition) and [Cat_conj_padL_iso]
   (Instance/Cat/Bicategory/Conjugate.v:183); then [Discrete_hom_iso] and
   [One_hom_iso] (Instance/Fun/Discrete.v), [conjugate_bijection]
   (Adjunction/Conjugate.v), [mate_iso] (Theory/Bicategory/Mates.v) and the
   arrows-only correspondence of Theory/Natural/Transformation/Arrows.v.
   None of them compares a Nat-setoid with a Nat-setoid over a POSTCOMPOSED
   PAIR — which is the operative clause, several of them being Nat-setoid to
   Nat-setoid otherwise.  [Cat_unitl_cast] (Instance/Cat/TwoCategory.v:118)
   is literally the backward leg at J = Id, but it is a map rather than an
   isomorphism and so falls outside.

   The crux, and why faithfulness is spent twice
   ----------------------------------------------

   In this library [Full] (Theory/Functor.v:332) carries a chosen section
   [prefmap] of [fmap] and NOTHING ELSE: its own header says "no
   functoriality is demanded of [prefmap] itself — it need not respect ≈ nor
   preserve identities/composition".  So building the backward leg of the
   correspondence is not a matter of applying a given inverse.  Given
   φ : J◯K ⟹ J◯L, the candidate family is α x := prefmap (φ x), and TWO
   separate things about it have to be proved rather than assumed:

     - NATURALITY of α.  Apply the injective [fmap[J]] to both sides of the
       square, push it through the composites with [fmap_comp], cancel the
       four sections with [fmap_sur], and what remains is exactly φ's own
       naturality square.  This is [post_prefmap] below.
     - RESPECTFULNESS of α in φ, i.e. that the backward leg is a
       [SetoidMorphism] at all.  Same move: [fmap_inj], then [fmap_sur] on
       both sides.  This is the third obligation of [postcompose_hom_iso].

   Both are the argument that Structure/Groupoid/Basepoint.v runs for
   [deloop_ff_moniso], where the same [prefmap] has to be shown a monoid
   homomorphism ([deloop_bwd_respects], [deloop_bwd_unit], [deloop_bwd_op])
   by applying the forward map and cancelling.  That file is the in-tree
   precedent and this one follows it deliberately.

   Consequently [Postcompose_Full] takes BOTH hypotheses, and the second is
   not decoration: it is what discharges [post_prefmap]'s two naturality
   obligations (one equation in two orientations), and it is spent a second,
   independent time in [postcompose_hom_iso]'s respectfulness obligation and
   in one of its two round trips.  Whether fullness of
   [Postcompose J] follows from fullness of J alone is NOT settled here —
   no proof and no counterexample is offered — and the boundary that IS
   established runs the other way ([postcompose_full_needs_full]: fullness
   of J cannot simply be dropped).

   Strict attempts, measured and refuted
   --------------------------------------

   Every comparison below was tried at [eq_refl] first.  Five were REFUTED,
   each with its cause diagnosed, and all five are pinned as CONVERSION
   negatives in Test/ProbePostcompose.v (which also carries four FORMABILITY
   negatives about the universes and twelve positive controls):

     - [fmap[PostcomposeViaHcompose] θ = fmap[Postcompose J] θ], and its
       whole-functor and componentwise variants — the [fmap[J] id] unit
       described above;
     - [transform[from finpost_hom_iso finpost_phi] x = FinSets_negb] — the
       [prefmap] in play comes from Construction/Subcategory.v:104's
       [Full_Implies_Full_Functor], which is a `Qed` lemma, so NO component
       of it reduces.  This is the donor's opacity, not a fact about [Full],
       and it is not observed here first: Theory/Sheaf/Category.v:86-93
       already records it, in the same words and about the same donor;
     - the round trip [from (to θ) = θ] — same cause, one step further out.

   What DOES hold strictly: both actions of [Postcompose]
   ([postcompose_fobj], [postcompose_fmap], [postcompose_fmap_component]),
   both legs of the isomorphism ([postcompose_hom_iso_to],
   [postcompose_hom_iso_from]), the identification of the forward leg with
   the functor's own [fmap] ([postcompose_hom_iso_to_is_fmap]), the object
   action of the Hcompose route ([postcompose_via_hcompose_obj]) and its
   component including the offending unit
   ([postcompose_via_hcompose_component]), the coincidence of [NatSetoid]
   with [Transform_Setoid] ([nat_setoid_is_Transform_Setoid]), and the
   witness's component readings ([finpost_theta_component],
   [finpost_phi_component]).

   Universes (measured in the constraint blocks, not read off the binders)
   ----------------------------------------------------------------------

   [Postcompose] identifies the hom and proof universes of all three
   categories into ONE level, leaving the three OBJECT universes free.  The
   pin is a donor's and is stated here so a consumer is not surprised:

     - Theory/Functor.v's [Compose@{u u0 u1 u2 u3}] is declared over
       [Category@{u0 u3 u3}], [Category@{u1 u3 u3}] and [Category@{u u3 u3}]
       — one shared hom-and-proof level across all three of its categories.
       The object action [fun K => J ◯ K] alone therefore forces the whole
       identification.
     - Instance/Fun.v's [Fun@{...}] independently carries the constraint
       [u0 = u2] between its source and target hom levels, and is itself
       declared at categories whose hom and proof levels coincide.  So even
       without [Compose] the two functor categories [D,E] and [D,E′] would
       share a hom level.

   Neither pin is introduced here and neither is claimed unavoidable.  The
   [Full] and [Faithful] classes add their own three-parameter shape
   (source objects, one shared hom level, target objects), which is the
   restriction Construction/Comma/Special.v also records.

   The size remark, and a measured negative
   -----------------------------------------

   Mac Lane's remark 1 is that this invariance is what lets one work with
   "the" category of sets without fixing its size.  In THIS library that
   worry is discharged foundationally rather than by the present theorem:
   Lib/Setoid.v is universe-polymorphic throughout, [Sets@{o so}] is a
   FAMILY of categories rather than one, every theorem about it is available
   at each member of the family, and Theory/Size.v supplies the
   [Small]/[LocallySmall] vocabulary and the resizing statements.  The
   theorem below does NOT discharge the remark, and no claim is made that it
   does.

   The relationship is sharper than a disclaimer, and it runs the
   uncomfortable way, so it is stated as a measurement rather than glossed.
   Instance/Sets/Powerset.v:262 DOES construct a functor between two levels
   of [Sets]:

       Sets_Lift@{o so sso} : Sets@{o so} ⟶ Sets@{so sso}

   the identity on carriers, re-typed one universe up.  (No fullness or
   faithfulness result about it exists anywhere in the tree, and none is
   proved here.)  Nevertheless [Postcompose Sets_Lift] IS NOT FORMABLE — and
   the obstruction is not this file's, nor need one even reach the functor
   category to meet it: already the bare object action [Sets_Lift ◯ K] is
   rejected, because
   Theory/Functor.v's [Compose] demands ONE shared hom-and-proof level across
   its three categories while [Sets@{o so}] has hom level [o] and
   [Sets@{so sso}] has hom level [so], with [o < so] forced by [Sets]' own
   declaration.  Both refusals are pinned as formability negatives in
   Test/ProbePostcompose.v, each against a positive control.

   Read that precisely: it says [Compose] ALONE suffices, not that the
   functor category is innocent.  It is not — per the Universes section
   above, [Fun] independently identifies its source and target hom levels, so
   [Sets@{o so}] and [Sets@{so sso}] could not both index one functor
   category either.  The wall here is met earlier, not only there.

   So this theorem does not reach Mac Lane's own motivating instance, and no
   route to it is offered.  What it does cover is his Exercise 4 as stated —
   a full subcategory inclusion inside one universe level, which is where the
   exercise's E ↪ E′ lives and where the [FinSets_Incl] witness lives.

   Not delivered
   -------------

     - no functoriality of [Postcompose] in J: neither
       [Postcompose Id ≈ Id] nor [Postcompose (J' ◯ J) ≈ Postcompose J' ◯
       Postcompose J] is stated (both would need comparison isomorphisms
       rather than equations, [Id ◯ K] and [K] being distinct functor
       records), and no bifunctor [[E,E′] ∏ [D,E] ⟶ [D,E′]] is built here —
       that is [Cat_Hcompose], which already exists;
     - no essential surjectivity, hence no statement that [Postcompose J] is
       an equivalence when J is;
     - nothing about [Induced], the precomposition companion;
     - no claim that faithfulness of J is NECESSARY for [Postcompose J] to
       be full;
     - no fullness or faithfulness of [Sets_Lift], and no route around the
       [Compose] universe wall that blocks postcomposition along it, per the
       paragraph above. *)

(** ** The transformation setoid, named *)

(* The hom-setoid of a functor category, packaged as an object of [Sets].
   [NatSetoid K L] is stated through [homset ([A, B])] so that it is
   manifestly the functor category's own hom-setoid rather than a
   re-declaration; [nat_setoid_is_Transform_Setoid] below records by
   [eq_refl] that this coincides with [Transform_Setoid], which is the
   setoid instance resolution picks for the `≊` notation of
   Instance/Sets.v:210. *)

Definition NatSetoid {A B : Category} (K L : A ⟶ B) : SetoidObject :=
  {| carrier   := K ~{[A, B]}~> L
   ; is_setoid := @homset ([A, B]) K L |}.

Example nat_setoid_is_Transform_Setoid {A B : Category} (K L : A ⟶ B) :
  @homset ([A, B]) K L = @Transform_Setoid A B K L := eq_refl.

(** ** The postcomposition functor *)

Section Postcompose.

Universes do dh dp eo eh ep fo fh fp.

Context {D : Category@{do dh dp}}.
Context {E : Category@{eo eh ep}}.
Context {E' : Category@{fo fh fp}}.
Context (J : E ⟶ E').

#[local] Obligation Tactic := idtac.

(* J ◯ − on objects, left whiskering on arrows.  The three laws are the
   three laws of J read componentwise: respectfulness is [fmap_respects],
   [fmap_id] is [reflexivity] (the identity transformation's component is
   already [fmap[K] id], so both sides are [fmap[J] (fmap[K] id)]), and
   [fmap_comp] is [fmap_comp] of J. *)
Program Definition Postcompose : [D, E] ⟶ [D, E'] := {|
  fobj := fun K => J ◯ K;
  fmap := fun K L θ => J ⊳ θ
|}.
Next Obligation.
  simpl; intros K L θ θ' Hθ x; apply fmap_respects; exact (Hθ x).
Qed.
Next Obligation.
  simpl; intros K x; reflexivity.
Qed.
Next Obligation.
  simpl; intros K L M θ θ' x; apply fmap_comp.
Qed.

(* Both actions on the nose. *)
Example postcompose_fobj (K : D ⟶ E) : fobj[Postcompose] K = J ◯ K := eq_refl.

Example postcompose_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  fmap[Postcompose] θ = J ⊳ θ := eq_refl.

Example postcompose_fmap_component (K L : D ⟶ E) (θ : K ⟹ L) (x : D) :
  transform[fmap[Postcompose] θ] x = fmap[J] (transform[θ] x) := eq_refl.

(** ** Faithfulness *)

(* Componentwise injectivity of [fmap[J]] is componentwise injectivity of
   the whiskering, and the hom-setoid of a functor category is
   componentwise, so there is nothing else to check. *)
Lemma Postcompose_Faithful : Faithful J → Faithful Postcompose.
Proof.
  intro JF; constructor; simpl; intros K L θ θ' Hθ x.
  apply (@fmap_inj _ _ J JF).
  exact (Hθ x).
Qed.

End Postcompose.

Arguments Postcompose {D E E'} J.

(** ** Fullness, and the Nat-setoid isomorphism *)

Section PostcomposeFullyFaithful.

Universes do dh dp eo eh ep fo fh fp.

Context {D : Category@{do dh dp}}.
Context {E : Category@{eo eh ep}}.
Context {E' : Category@{fo fh fp}}.
Context (J : E ⟶ E').
Context (JFull : Full J).
Context (JFaith : Faithful J).

#[local] Obligation Tactic := idtac.

(* The candidate preimage of φ : J◯K ⟹ J◯L: take the chosen preimage of each
   component.  [prefmap] is a bare section, so NATURALITY of the resulting
   family is a theorem, not a field — and faithfulness of J is what proves
   it.  Applying [fmap[J]] to both sides of the square turns it, after
   [fmap_comp] and the four cancellations of [fmap_sur], into φ's own
   naturality square; [naturality_sym] is the same argument in the other
   orientation. *)
Program Definition post_prefmap {K L : D ⟶ E} (φ : J ◯ K ⟹ J ◯ L) :
  K ⟹ L := {|
  transform := fun x => @prefmap _ _ J JFull (K x) (L x) (transform[φ] x)
|}.
Next Obligation.
  intros K L φ x y f; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_comp, !fmap_sur.
  exact (@naturality _ _ _ _ φ x y f).
Qed.
Next Obligation.
  intros K L φ x y f; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_comp, !fmap_sur.
  exact (@naturality_sym _ _ _ _ φ x y f).
Qed.

(* The section law is J's own, applied at each component. *)
Program Definition Postcompose_Full : Full (Postcompose (D:=D) J) := {|
  prefmap := fun K L φ => post_prefmap φ
|}.
Next Obligation.
  simpl; intros K L φ x; apply fmap_sur.
Qed.

(* Mac Lane's statement.  The forward leg is left whiskering; the backward
   leg is [post_prefmap].  Respectfulness of the BACKWARD leg is the second
   place faithfulness is spent: [prefmap] is not assumed to respect `≈`, so
   the obligation is discharged by applying the injective [fmap[J]] and
   cancelling both sections.  Of the two round trips, one is [fmap_sur]
   componentwise and the other is faithfulness applied to it. *)
Program Definition postcompose_hom_iso (K L : D ⟶ E) :
  @Isomorphism Sets (NatSetoid K L) (NatSetoid (J ◯ K) (J ◯ L)) := {|
  to   := {| morphism := fun θ => J ⊳ θ |};
  from := {| morphism := fun φ => post_prefmap φ |}
|}.
Next Obligation.
  intros K L θ θ' Hθ x; simpl; apply fmap_respects; exact (Hθ x).
Qed.
Next Obligation.
  intros K L φ φ' Hφ x; simpl.
  apply (@fmap_inj _ _ J JFaith).
  rewrite !fmap_sur.
  exact (Hφ x).
Qed.
Next Obligation.
  intros K L φ x; simpl; apply fmap_sur.
Qed.
Next Obligation.
  intros K L θ x; simpl.
  apply (@fmap_inj _ _ J JFaith).
  apply fmap_sur.
Qed.

(* The two legs, on the nose. *)
Example postcompose_hom_iso_to (K L : D ⟶ E) (θ : K ⟹ L) :
  to (postcompose_hom_iso K L) θ = J ⊳ θ := eq_refl.

Example postcompose_hom_iso_from (K L : D ⟶ E) (φ : J ◯ K ⟹ J ◯ L) :
  from (postcompose_hom_iso K L) φ = post_prefmap φ := eq_refl.

(* The forward leg IS the functor's own action on 2-cells; this is the
   sentence "the isomorphism is [Postcompose J] restricted to a hom-setoid",
   machine-checked rather than asserted. *)
Example postcompose_hom_iso_to_is_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  to (postcompose_hom_iso K L) θ = fmap[Postcompose J] θ := eq_refl.

(* The `≊` reading of Instance/Sets.v:210, where the setoid on each carrier
   is left to instance resolution.  It agrees with the [NatSetoid]
   packaging because resolution finds [Transform_Setoid], which
   [nat_setoid_is_Transform_Setoid] records is [homset ([D, E])]. *)
Definition postcompose_nat_bijection (K L : D ⟶ E) :
  (K ⟹ L) ≊ (J ◯ K ⟹ J ◯ L) := postcompose_hom_iso K L.

End PostcomposeFullyFaithful.

Arguments post_prefmap {D E E'} J JFull JFaith {K L} φ.
Arguments Postcompose_Full {D E E'} J JFull JFaith.
Arguments postcompose_hom_iso {D E E'} J JFull JFaith K L.
Arguments postcompose_nat_bijection {D E E'} J JFull JFaith K L.

(** ** Comparison with the horizontal-composition bifunctor *)

Section ViaHcompose.

Context {D E E' : Category}.
Context (J : E ⟶ E').

#[local] Obligation Tactic := idtac.

(* The postcomposition functor that the tree already had, assembled: freeze
   the first argument of horizontal composition at J. *)
Definition PostcomposeViaHcompose : [D, E] ⟶ [D, E'] :=
  Partial_r (@Cat_Hcompose D E E') J.

(* The object actions agree definitionally. *)
Example postcompose_via_hcompose_obj (K : D ⟶ E) :
  fobj[PostcomposeViaHcompose] K = fobj[Postcompose J] K := eq_refl.

(* The arrow action does not, and this records exactly what it is: an
   identity 2-cell fed into the Godement product contributes
   [transform[nat_id] (L x)], which is [fmap[J] id] and not [id].  The
   Leibniz identification with [fmap[Postcompose J] θ] is pinned as a
   conversion negative in Test/ProbePostcompose.v. *)
Example postcompose_via_hcompose_component
        (K L : D ⟶ E) (θ : K ⟹ L) (x : D) :
  transform[fmap[PostcomposeViaHcompose] θ] x
    = fmap[J] (@id E (L x)) ∘ fmap[J] (transform[θ] x) := eq_refl.

(* Up to `≈` the two agree, the unit being discharged by [fmap_id]. *)
Lemma postcompose_via_hcompose_fmap (K L : D ⟶ E) (θ : K ⟹ L) :
  fmap[PostcomposeViaHcompose] θ ≈ fmap[Postcompose J] θ.
Proof.
  intro x; simpl.
  rewrite fmap_id; cat.
Qed.

(* Hence the two functors are equal in [Cat]'s hom-setoid, with identity
   comparison components.  Leibniz equality of the two records is strictly
   stronger and is REFUTED — pinned as negative 2 of
   Test/ProbePostcompose.v — so this is the strongest available comparison
   between them. *)
Program Definition postcompose_via_hcompose_equiv :
  PostcomposeViaHcompose ≈ Postcompose J := (fun _ => iso_id; _).
Next Obligation.
  simpl; intros K L θ x.
  rewrite !fmap_id; cat.
Qed.

End ViaHcompose.

(** ** Mac Lane's own hypothesis: a full subcategory inclusion *)

(* NOTATION GUARD.  Construction/Subcategory.v exports its own [Full] — the
   fullness of the SELECTION DATA, whose first argument is a [Category] —
   which shadows Theory/Functor.v's [Full] on a functor.  Both are needed
   below, so the two requires are deferred to here rather than placed at the
   head of the file (the mid-file [Require] idiom of Functor/Diagonal.v),
   keeping every [Full] above unambiguous, and from this point on
   functor-level fullness is written out as [Category.Theory.Functor.Full]
   (the spelling Instance/Field/Frac.v settled on for the same collision). *)

Require Import Category.Theory.Concrete.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Finite.

Section FullSubcategory.

Context {C : Category}.
Context (S : Subcategory C).
Context (full : Subcategory.Full C S).
Context {D : Category}.

(* The two donors, by name: every subcategory inclusion is faithful, and a
   full one is a full functor. *)
Definition sub_Incl_Full : Category.Theory.Functor.Full (Incl C S) :=
  Full_Implies_Full_Functor C S full.

Definition sub_Incl_Faithful : Faithful (Incl C S) :=
  Incl_Faithful C S.

Definition SubPostcompose : [D, Sub C S] ⟶ [D, C] :=
  Postcompose (Incl C S).

Definition sub_postcompose_Faithful : Faithful SubPostcompose :=
  Postcompose_Faithful (Incl C S) sub_Incl_Faithful.

Definition sub_postcompose_Full :
  Category.Theory.Functor.Full SubPostcompose :=
  Postcompose_Full (Incl C S) sub_Incl_Full sub_Incl_Faithful.

(* Mac Lane §III.2 Exercise 4 under its own hypothesis: for K, L : D ⟶ E
   with E a full subcategory of E′, transformations K ⟹ L and J◯K ⟹ J◯L are
   the same thing — "the same" here being an isomorphism of the two setoids
   in [Sets], which is the setoid-theoretic rendering of his equality of
   sets. *)
Definition sub_postcompose_hom_iso (K L : D ⟶ Sub C S) :
  (K ⟹ L) ≊ (Incl C S ◯ K ⟹ Incl C S ◯ L) :=
  postcompose_nat_bijection (Incl C S) sub_Incl_Full sub_Incl_Faithful K L.

End FullSubcategory.

Arguments SubPostcompose {C} S {D}.
Arguments sub_postcompose_hom_iso {C} S full {D} K L.

(** ** The concrete witness: finite setoids inside Sets *)

(* Construction/Subcategory/Finite.v is Mac Lane's §I.3 example of a full
   subcategory — the finite sets inside Set, with all functions between them
   — realized over setoids, and it already carries the two facts needed
   here ([FinSets_Full], [FinSets_Faithful]) plus a pair of provably
   distinct parallel arrows ([FinSets_two_arrows]).  So the witness costs no
   new subcategory.

   The shape D is the terminal category, and that choice is disclosed
   rather than dressed up: over [_1] the naturality condition is degenerate,
   so what this witness exercises is the HOM-SETOIDS and the fullness
   construction, not the naturality argument.  The naturality argument is
   exercised by the general theorem, whose D is arbitrary. *)

Section FinSetsWitness.

#[local] Obligation Tactic := idtac.

Definition finpost_K : _1 ⟶ FinSetsCat := Diagonal _1 FinSets_bool.

Definition finpost_hom_iso :
  (finpost_K ⟹ finpost_K) ≊ (FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K) :=
  sub_postcompose_hom_iso FinSets FinSets_Full finpost_K finpost_K.

(* A non-identity transformation upstairs: negation of the two-element
   setoid, constant over the point. *)
Definition finpost_theta : finpost_K ⟹ finpost_K :=
  fmap[Diagonal _1] FinSets_negb.

Example finpost_theta_component (x : _1) :
  transform[finpost_theta] x = FinSets_negb := eq_refl.

(* A transformation exhibited DOWNSTAIRS, in [Sets], with no reference to
   the subcategory: its component is [Sets_negb].  Naturality over the point
   reduces to [Sets_negb ∘ fmap[J] id ≈ fmap[J] id ∘ Sets_negb]. *)
Program Definition finpost_phi :
  FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K := {|
  transform := fun _ => Sets_negb
|}.
Next Obligation. intros x y f; destruct f; simpl; cat. Qed.
Next Obligation. intros x y f; destruct f; simpl; cat. Qed.

Example finpost_phi_component (x : _1) :
  transform[finpost_phi] x = Sets_negb := eq_refl.

(* Fullness at work: the preimage of [finpost_phi] has [FinSets_negb] as its
   component.  MEASURED STRICT-FIRST AND REFUTED at [eq_refl], with the cause
   diagnosed and pinned in Test/ProbePostcompose.v: the [prefmap] in play is
   the one produced by Construction/Subcategory.v:104's
   [Full_Implies_Full_Functor], which is a `Qed` lemma, so no component of it
   reduces — the obstruction is the donor's opacity and not anything about
   this construction.  What does hold, and is what the statement is about, is
   `≈`, and its proof is [fmap_sur] verbatim: [Sub]'s hom-setoid IS `≈` of
   first projections, which is `≈` of the images under [Incl]. *)
Lemma finpost_preimage_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x ≈ FinSets_negb.
Proof.
  exact (@fmap_sur _ _ _ (sub_Incl_Full FinSets FinSets_Full)
           _ _ (transform[finpost_phi] x)).
Qed.

(* Non-degeneracy, upstairs: the source Nat-setoid has at least two
   elements.  [FinSets_two_arrows] is Construction/Subcategory/Finite.v's
   separation of [id] from [FinSets_negb] in the subcategory's own
   hom-setoid. *)
Lemma finpost_theta_not_id : @nat_id _1 FinSetsCat finpost_K ≈ finpost_theta → False.
Proof.
  intro H.
  apply FinSets_two_arrows.
  exact (H ttt).
Qed.

(* Non-degeneracy, downstairs: so does the target Nat-setoid, and the
   witness is the image of [finpost_theta] under the isomorphism. *)
Lemma finpost_image_not_id :
  @nat_id _1 Sets (FinSets_Incl ◯ finpost_K) ≈ to finpost_hom_iso finpost_theta → False.
Proof.
  intro H.
  apply Sets_two_arrows.
  exact (H ttt).
Qed.

(* And the backward leg genuinely produces a non-identity: the preimage of
   [finpost_phi] is not the identity transformation. *)
Lemma finpost_preimage_not_id :
  @nat_id _1 FinSetsCat finpost_K ≈ from finpost_hom_iso finpost_phi → False.
Proof.
  intro H.
  apply FinSets_two_arrows.
  transitivity (transform[from finpost_hom_iso finpost_phi] ttt).
  - exact (H ttt).
  - exact (finpost_preimage_component ttt).
Qed.

(* The two exhibited transformations correspond under the isomorphism. *)
Lemma finpost_theta_phi : to finpost_hom_iso finpost_theta ≈ finpost_phi.
Proof. intro x; simpl; reflexivity. Qed.

End FinSetsWitness.

(** ** A boundary: fullness of J cannot be dropped *)

(* The inclusion of the discrete two-object category into the walking arrow.
   It is faithful — parallel arrows of [Two_Discrete] are equal, both being
   the unique identity constructor at their endpoints — and it is not full,
   since [TwoXY : TwoX ~> TwoY] has no preimage.  Postcomposing along it is
   therefore faithful and not full: over the point, a transformation between
   the two constant functors at [TwoDX] and [TwoDY] would BE an arrow
   [TwoDX ~> TwoDY], of which there is none, while downstairs [TwoXY]
   supplies one.

   This says only that fullness of J is used; it does not say that
   faithfulness is. *)

Section FullnessNeeded.

#[local] Obligation Tactic := idtac.

(* The object and arrow actions as ordinary definitions.  [Program] is
   deliberately not used to elaborate the two [match]es: [TwoDHom] is an
   INDEXED inductive, and inside a [Program Definition] the branches are
   compiled through a dependent eliminator carrying [eq] and [JMeq]
   arguments, after which the functor-law obligations mention that
   eliminator rather than [disc_fmap] and are not provable by any
   case analysis one would want to write.  Elaborating the actions as
   ordinary [Definition]s first is the same accommodation
   Structure/Cartesian/Closed/Natural.v reaches for — there because
   [Program] defers an unresolved instance into an obligation that
   [Unset Transparent Obligations] then makes opaque, a different cause with
   the same remedy. *)
Definition disc_obj (x : TwoDObj) : TwoObj :=
  match x with TwoDX => TwoX | TwoDY => TwoY end.

Definition disc_fmap {x y : TwoDObj} (f : TwoDHom x y) :
  TwoHom (disc_obj x) (disc_obj y) :=
  match f with TwoDIdX => TwoIdX | TwoDIdY => TwoIdY end.

Program Definition DiscToTwo : Two_Discrete ⟶ _2 := {|
  fobj := disc_obj;
  fmap := @disc_fmap
|}.
(* Two obligations only: [fmap_respects] is discharged by resolution, both
   hom-setoids here being [Morphism_equality], i.e. Leibniz. *)
Next Obligation.
  intros x; destruct x; reflexivity.
Qed.
Next Obligation.
  intros x y z f g; destruct x, y, z;
    try (exact (False_rect _ (TwoDHom_X_Y_absurd f)));
    try (exact (False_rect _ (TwoDHom_X_Y_absurd g)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd f)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd g)));
    pose proof (TwoDHom_inv _ _ f) as Hf;
    pose proof (TwoDHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; reflexivity.
Qed.

(* Faithful: parallel arrows of the discrete category are equal, both being
   the unique identity constructor at their common endpoint, so the
   hypothesis is never even consulted. *)
Lemma DiscToTwo_Faithful : Faithful DiscToTwo.
Proof.
  constructor; intros x y f g Hfg; destruct x, y;
    try (exact (False_rect _ (TwoDHom_X_Y_absurd f)));
    try (exact (False_rect _ (TwoDHom_Y_X_absurd f)));
    pose proof (TwoDHom_inv _ _ f) as Hf;
    pose proof (TwoDHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; reflexivity.
Qed.

Lemma DiscToTwo_not_Full : Category.Theory.Functor.Full DiscToTwo → False.
Proof.
  intro HF.
  exact (TwoDHom_X_Y_absurd (@prefmap _ _ DiscToTwo HF TwoDX TwoDY TwoXY)).
Qed.

(* The two constant diagrams over the point. *)
Definition DiscX : _1 ⟶ Two_Discrete := @Diagonal Two_Discrete _1 TwoDX.
Definition DiscY : _1 ⟶ Two_Discrete := @Diagonal Two_Discrete _1 TwoDY.

(* Downstairs the arrow exists, so the target Nat-setoid is inhabited. *)
Program Definition disc_phi : DiscToTwo ◯ DiscX ⟹ DiscToTwo ◯ DiscY := {|
  transform := fun _ => TwoXY
|}.
Next Obligation. intros x y f; destruct f; reflexivity. Qed.
Next Obligation. intros x y f; destruct f; reflexivity. Qed.

(* Upstairs it does not, so [Postcompose DiscToTwo] is not full. *)
Theorem postcompose_full_needs_full :
  Category.Theory.Functor.Full (Postcompose (D:=_1) DiscToTwo) → False.
Proof.
  intro HF.
  exact (TwoDHom_X_Y_absurd
           (transform[@prefmap _ _ _ HF DiscX DiscY disc_phi] ttt)).
Qed.

(* Faithfulness, by contrast, does transfer: the postcomposition functor
   along the same J is faithful. *)
Definition postcompose_disc_Faithful : Faithful (Postcompose (D:=_1) DiscToTwo) :=
  Postcompose_Faithful DiscToTwo DiscToTwo_Faithful.

End FullnessNeeded.
