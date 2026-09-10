Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Construction.Postcompose.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Adjunctions and limits in functor categories *)

(* Mac Lane §V.5, construction 1 and Remark 1 (book p. 119;
   maclane:V.5:construction1, maclane:V.5:remark1); Riehl §4.3 Proposition
   4.3.6 with Exercises 4.3.ii and 4.3.iii (riehl:4.3:prop6, riehl:4.3:exii,
   riehl:4.3:exiii).
   nLab: https://ncatlab.org/nlab/show/adjoint+functor
         https://ncatlab.org/nlab/show/limit

   BACKGROUND.  An adjunction [F ⊣ G : X ⇄ A] lifts to the functor
   categories over any shape [J] by postcomposition, [F ◯ − ⊣ G ◯ −], the
   induced unit and counit being the originals whiskered by the diagram;
   Riehl's proposition adds the precomposition half, [− ◯ G ⊣ − ◯ F].  Mac
   Lane's remark combines the first with the diagonal-limit adjunctions
   [Δ ⊣ Lim] into a square of adjoint pairs whose left adjoints commute,
   [F^J ∘ Δ = Δ ∘ F], so that by uniqueness of adjoints the right adjoints
   agree up to natural isomorphism, [Lim ◯ G^J ≅ G ◯ Lim] — a
   "sophisticated" restatement of the theorem that right adjoints preserve
   limits.

   STALE PREMISES, RE-MEASURED.
     - "The postcomposition functors [F ◯ −] are not defined anywhere; the
       only functor between functor categories is precomposition": FALSE.
       Functor/Construction/Postcompose.v:355's [Postcompose : [D, E] ⟶
       [D, E']] (#318) is [J ◯ −] on objects and left whiskering on arrows,
       with its three laws; docs/INDEX.md's Adjunction/Diagonal/Limit.v
       bullet lists eleven constants typed [[X, Y] ⟶ _].  Work item 1 was
       done by #318; [postcompose] below is that functor at a fixed shape.
     - "[Cat_Hcompose] is a bifunctor never partially applied": FALSE
       (Postcompose.v:509's [PostcomposeViaHcompose]; and it sits at
       Instance/Cat/Bicategory.v:64, [Induced] at Theory/Kan/
       Extension.v:131).
     - "[Lim] is never a functor [[J, C] ⟶ C]; the general [Δ ⊣ Lim] exists
       only in the binary-product case": STALE since #353.
       Adjunction/Diagonal/Limit.v has [HasLimitsOfShape] (:363),
       [LimitFunctor : [J, C] ⟶ C] (:434), [Diagonal_Limit_Adjunction : Δ ⊣
       LimitFunctor] (:527) and [lim_counit] (:547), whose components ARE
       the limit legs (:551 at [eq_refl], :554 at [≈]) — the "cone being
       the value of the [Δ ⊣ Lim] counit" of work item 3.
     - "[right_adjoint_iso] at Theory/Adjunction.v:364": :367 ([Qed]);
       [left_adjoint_iso] :407.  The Riehl clauses' citations are off by a
       few lines each ([left_adjoint_impl] :332, the Kan class fields
       [ran_adjoint] :149 and [lan_adjoint] :229, [precomp_zig_id]
       Theory/Bicategory/Mates.v:209); their substance holds: before this
       file no standalone [Adjunction] term had both functors between
       functor categories.
     - Work item 3 writes the square as an EQUALITY, [F^J ∘ Δ = Δ ∘ F].  It
       is not one: [(postcompose F ◯ Δ) x] carries [fmap := fun _ _ _ =>
       fmap[F] id] where [Δ (F x)] carries [id] (probe N1).  It holds as a
       natural isomorphism with identity components, [square_iso], which
       is all the argument needs.

   WHAT IS DELIVERED (39 named constants plus 32 [Program] obligations,
   every one closed under the global context).
     (1) [postcompose F : [J, X] ⟶ [J, A]] — #318's [Postcompose] at the
         shape [J], with [postcompose_obj] and [postcompose_component] at
         [eq_refl]; and [precompose F : [D, E] ⟶ [C, E]] — Theory/Kan/
         Extension.v's [Induced], with [precompose_obj] and
         [precompose_component] at [eq_refl].  Neither is a new functor.
     (2) MAC LANE'S CONSTRUCTION 1 / RIEHL 4.3.6 (a), by the unit-counit
         route of Exercise 4.3.ii: [postcompose_unit], [postcompose_counit]
         (Adjunction/Natural/Transformation.v transformations whose
         naturality in the diagram is the naturality of the original unit
         and counit — taken from [Adjunction_to_Transform]'s two
         [Transform] fields, Adjunction/Natural/Transformation/
         Universal.v:84, so nothing about them is re-derived), the two
         triangle identities componentwise from the originals in
         [postcompose_adjunction_transform], and
         [postcompose_adjunction : postcompose F ⊣ postcompose G] through
         [Adjunction_from_Transform] (Universal.v:42).  The readbacks
         [postcompose_unit_component] and [postcompose_counit_component]
         say, at [eq_refl], that the CONSTRUCTED unit and counit ARE the
         whiskered originals.  The delivered adjunction's own accessors
         [unit] and [counit] (Theory/Adjunction.v:217-218, the transposes
         of identities) carry a [fmap_id] residue — [⌊id⌋] is [fmap
         [postcompose G] id ∘ postcompose_unit] — so THEY are the whiskered
         originals at [≈] only ([postcompose_adjunction_unit],
         [postcompose_adjunction_counit]; the [eq_refl] form is refused,
         probe N5).  An earlier revision glossed the [eq_refl] readbacks
         as the reviewer's condition on the nose; the condition holds on
         the nose for the construction and at [≈] for the adjunction.
     (3) RIEHL 4.3.6 (b), the precomposition half: [precompose_unit] with
         components [fmap[S] (η c)], [precompose_counit] with components
         [fmap[T] (ε d)], the triangle identities through [fmap_comp] and
         [fmap_id], and [precompose_adjunction : precompose G ⊣ precompose
         F] — the direction reverses (probe N3).  Nothing here is obtained
         from (2) by duality: it is the mirror construction, written out.
     (4) THE SQUARE.  [square_at x], [square_iso : postcompose F ◯ Δ ≅[Fun]
         Δ ◯ F] (every component an identity) and [square_equiv], the same
         as functor equality in the orientation the transport wants.
     (5) MAC LANE'S REMARK 1.  [left_route : postcompose F ◯ Δ ⊣ LimitFunctor
         ◯ postcompose G] and [right_route : Δ ◯ F ⊣ G ◯ LimitFunctor] by
         Adjunction/Compose.v:173's [Adjunction_Compose]; [left_route'] by
         transporting the first across the square with Theory/Adjunction.v's
         [adjunction_along_left_iso] (see RELOCATION); then
         [Lim_commutes_right_adjoint : LimitFunctor LX ◯ postcompose G ≈ G ◯
         LimitFunctor LA] is ONE application of [right_adjoint_iso] — the
         uniqueness of right adjoints, not a re-proof — with the readings
         [Lim_commutes_nat_iso] (in [[[J, A], X]]) and, pointwise,
         [lim_of_right_adjoint T : lim_obj LX (G ◯ T) ≅ G (lim_obj LA T)].
     (6) THE CONE-LEVEL CLAUSE.  [right_adjoint_carries_lim_counit T :
         IsLimitCone (FCone G (limit_cone (LA T)))] — a right adjoint carries
         the limiting cone of [T], whose legs are the components of the
         [Δ ⊣ Lim] counit ([carried_leg_is_counit], at [≈] through
         Adjunction/Diagonal/Limit.v:554), to a limiting cone.  Its proof
         is Adjunction/Continuity.v:205's [right_adjoint_PreservesLimitCone]
         (an earlier revision cited :209, [right_adjoint_Continuous]),
         the tree's DIRECT proof of RAPL, and NOT a consequence drawn from
         (5): [right_adjoint_iso] is [Qed], so the components of the
         remark's isomorphism cannot be identified with the canonical
         comparison, and the passage from "the right adjoints are
         isomorphic" to "the image cone is limiting" is not formalized.
         Mac Lane's remark is delivered as the isomorphism it states; the
         limit-preservation it restates is supplied by the existing
         theorem beside it.

   RELOCATION.  The transport [adjunction_along_left_iso : F ≈ F' → F' ⊣ G
   → F ⊣ G] existed only in Instance/Mod/Bimodule.v (#401), whose header
   declared it there "because part (c) is its first consumer" and said it
   "belongs beside Theory/Adjunction.v"; requiring Bimodule.v from this
   file would have added 44 files to the closure (an earlier revision said
   48; measured 74 → 118 by coqdep and by [Print Libraries]).  The section
   [AdjunctionAlongIso] is moved verbatim to the end of Theory/Adjunction.v
   (Section at :477, [adjunction_along_left_iso] at :542; it needs a
   section-local [Obligation Tactic := idtac], Bimodule.v's file-wide
   setting, or Lib's global [cat_simpl] runs on its obligations first);
   Bimodule.v keeps a pointer comment at :2462-2469 and its
   header figures are corrected in place (427 constants, 213 [Qed], five
   [Defined], 82 [eq_refl] — 440, 220, six and 83 before); the gate
   entries for the thirteen moved constants are requalified; the one
   outside citation of a later Bimodule.v line (docs/INDEX.md's
   Instance/InnerProduct/Galois.v bullet) is repointed.  No statement or
   proof of the moved section changes, and it stays [Defined].

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 39
   constants).  Every block identifies the hom levels of the shape and the
   two categories ([u0 = u2], [u0 = u4]; the two naturality lemmas, in
   which [J] does not occur, carry [u2 = u4] alone; the four [≈] accessor
   lemmas carry the same blocks as their adjunctions and no cap) — the identification
   is Instance/Fun.v:127's [Fun] ([u0 = u2]) and [Postcompose]'s /
   [Induced]'s own, exactly as Postcompose.v:237-258 records, and bare and
   annotated binders give the same blocks; nothing minimizes and no block
   or type names [Set].  Stdlib caps, each attributed by [About] on the
   donor: [prod_rect] is first carried by [square_at]'s own obligations
   (no donor of the square carries it) and inherited by [square_iso] and
   [square_equiv]; [eq_rect_r] comes from [Diagonal_Limit_Adjunction] into
   [left_route] and [right_route], and from [lim_counit_is_limit_leg] into
   [carried_leg_is_counit]; [Logic_lemmas.equality] and [prod_rect] come
   from [adjunction_along_left_iso] into [left_route'] and the three
   remark constants — [right_adjoint_iso] itself carries no cap.

   COUNTS AND CONVENTIONS.
     - 39 [.glob] declaration heads (32 [def], 7 [prf]) plus 32 [Program]
       obligations, all "Closed under the global context", zero [Axioms:]
       lines; the gate carries the 39 heads, fully qualified, the issue's
       [postcompose_adjunction] and [Lim_commutes_right_adjoint] among them.
     - No [Defined]: every construction is a [:=] term or a [Program]
       record, and every proof is [Qed] — 40 [Qed] tokens (32 obligations,
       the two naturality lemmas, the four [≈] accessor lemmas,
       [Lim_commutes_right_adjoint] and [carried_leg_is_counit]).  Nothing that computes is hidden behind a
       [Qed]: the eight [eq_refl] readbacks of (1)-(3) reduce through
       [:=] definitions and [Program] records alone.  [Lim_commutes_right_
       adjoint] is opaque by its donor already ([right_adjoint_iso], [Qed]).
     - Closure 74 files excluding self: Adjunction/Diagonal/Limit.v costs
       31 at the margin, Functor/Construction/Postcompose.v 8,
       Adjunction/Compose.v 2, Adjunction/Continuity.v 2,
       Adjunction/Natural/Transformation/Universal.v 1, the other fourteen
       [Require]s 0.  Name collisions: [postcompose] and [precompose] occur
       as WORDS in the prose of 3 and 8 files (Theory/Natural/
       Transformation.v:341/:323, Theory/Equivalence/Colimit.v:451, …),
       never as declarations; the other 37 names have 0 occurrences.
     - Test/ProbeFunctorCategory431.v mirrors the [Require] list and carries
       6 refutation commands (1 instrument + N1 and N5 CONVERSION + N2-N3
       TYPING + N4 UNIVERSE), each stripped one at a time in a copy of the
       whole file beside its accepted controls; N4's message reads "The
       term Xw has type Category@{xo xh xh} while it is expected to have
       type Category@{_ jh jh} (universe inconsistency: Cannot enforce xh =
       jh because jh < xh)", and the pin is [Fun]'s, not this file's; six
       [eq_refl] readbacks; guard coverage 29 identifier tokens
       inside the refutations / 25 also named outside, comments
       stripped, with four exhaustive exceptions (the keyword, the two
       refuted declarations' names, the absent name); rename-simulated over
       the seven library names the refutations use — [postcompose],
       [precompose], [postcompose_adjunction], [precompose_adjunction],
       [Diagonal], [eq_refl], [transform]; module-path components and the
       section binders excluded — every first break on a positive line (an earlier revision said "11/11"
       over a set it did not name).  [make todo] grows by those 6 lines
       only (2255 → 2261 over master 1be50678; the relocation adds none),
       so the issue's "adds no new hits" box is not met as written;
       disclosed.

   NOT DELIVERED.
     - The passage from the remark's isomorphism to limit preservation
       (see (6)); a transparent uniqueness-of-adjoints; the right-hand
       transport [G ≈ G' → F ⊣ G → F ⊣ G'].
     - Continuity or cocontinuity of [postcompose] and [precompose]
       themselves; the Kan adjunctions [Induced ⊣ Ran] and [Lan ⊣ Induced],
       which stay Theory/Kan/Extension.v's class fields.
     - Riehl's Exercise 4.3.iii route (the adjunction from the hom-set
       bijection, [left_adjoint_impl]): the unit-counit route produces the
       same artifact, so no separate constant is built.
     - A concrete instance: every result here is conditional on an
       abstract [F ⊣ G] (and [HasLimitsOfShape]); nothing in the tree
       instantiates [postcompose_adjunction], [precompose_adjunction] or
       [Lim_commutes_right_adjoint] at a named adjunction, and
       docs/INHABITATION.md is not touched (the donor
       Adjunction/Diagonal/Limit.v carries [Sets_Diagonal_Limit_Adjunction];
       composing with it would need a named [F ⊣ G] into or out of Sets).
     - No edit to Functor/Construction/Postcompose.v, Theory/Kan/
       Extension.v, Adjunction/Diagonal/Limit.v or Adjunction/Compose.v. *)

(** ** Postcomposition: [F ◯ −] as a functor between functor categories *)

Section Postcomposition.

Context {J X A : Category}.

(* Work item 1 was already discharged by #318: Functor/Construction/
   Postcompose.v's [Postcompose] is [F ◯ −] on objects and left
   whiskering on arrows, with its three laws.  This is the issue's name
   for it at a fixed shape [J]. *)
Definition postcompose (F : X ⟶ A) : [J, X] ⟶ [J, A] := Postcompose (D:=J) F.

Example postcompose_obj (F : X ⟶ A) (S : J ⟶ X) :
  postcompose F S = F ◯ S := eq_refl.

Example postcompose_component (F : X ⟶ A) {S T : J ⟶ X} (θ : S ⟹ T) (j : J) :
  transform[fmap[postcompose F] θ] j = fmap[F] (transform[θ] j) := eq_refl.

End Postcomposition.

(** ** Mac Lane V.5 construction 1: [F ⊣ G] gives [postcompose F ⊣ postcompose G] *)

Section PostcomposeAdjunction.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

#[local] Obligation Tactic := idtac.

(* The unit and counit of [Adj] as natural transformations, with their
   naturality unrestricted in the codomain: Adjunction/Natural/
   Transformation/Universal.v's [Adjunction_to_Transform] already proves
   it, and its components ARE Theory/Adjunction.v's [unit] and [counit]. *)
Let η : Id ⟹ G ◯ F := @Transformation.unit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).
Let ε : F ◯ G ⟹ Id := @Transformation.counit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).

Lemma postcompose_unit_natural {x y : X} (f : x ~> y) :
  fmap[G] (fmap[F] f) ∘ @Category.Theory.Adjunction.unit _ _ F G Adj x
    ≈ @Category.Theory.Adjunction.unit _ _ F G Adj y ∘ f.
Proof. exact (naturality[η] _ _ f). Qed.

Lemma postcompose_counit_natural {x y : A} (f : x ~> y) :
  @Category.Theory.Adjunction.counit _ _ F G Adj y ∘ fmap[F] (fmap[G] f)
    ≈ f ∘ @Category.Theory.Adjunction.counit _ _ F G Adj x.
Proof. exact (@naturality_sym _ _ _ _ ε _ _ f). Qed.

(* The induced unit: at a diagram [S], the original unit whiskered by [S]
   — component [η (S j)]. *)
Program Definition postcompose_unit_at (S : J ⟶ X) : S ⟹ G ◯ (F ◯ S) := {|
  transform := fun j => @Category.Theory.Adjunction.unit _ _ F G Adj (S j)
|}.
Next Obligation. intros S x y f; simpl; apply postcompose_unit_natural. Qed.
Next Obligation.
  intros S x y f; simpl; symmetry; apply postcompose_unit_natural.
Qed.

Program Definition postcompose_unit :
  Id ⟹ postcompose (J:=J) G ◯ postcompose (J:=J) F := {|
  transform := postcompose_unit_at
|}.
Next Obligation. intros S T θ j; simpl; apply postcompose_unit_natural. Qed.
Next Obligation.
  intros S T θ j; simpl; symmetry; apply postcompose_unit_natural.
Qed.

(* The induced counit: at [T], the original counit whiskered by [T] —
   component [ε (T j)]. *)
Program Definition postcompose_counit_at (T : J ⟶ A) : F ◯ (G ◯ T) ⟹ T := {|
  transform := fun j => @Category.Theory.Adjunction.counit _ _ F G Adj (T j)
|}.
Next Obligation.
  intros T x y f; simpl; symmetry; apply postcompose_counit_natural.
Qed.
Next Obligation. intros T x y f; simpl; apply postcompose_counit_natural. Qed.

Program Definition postcompose_counit :
  postcompose (J:=J) F ◯ postcompose (J:=J) G ⟹ Id := {|
  transform := postcompose_counit_at
|}.
Next Obligation.
  intros S T θ j; simpl; symmetry; apply postcompose_counit_natural.
Qed.
Next Obligation. intros S T θ j; simpl; apply postcompose_counit_natural. Qed.

(* The triangle identities hold componentwise from the originals; the
   identity of [[J, A]] at [F ◯ S] has component [fmap[F] (fmap[S] id)],
   not [id], so each obligation first folds it with [fmap_id]. *)
Program Definition postcompose_adjunction_transform :
  postcompose (J:=J) F ∹ postcompose (J:=J) G := {|
  Transformation.unit   := postcompose_unit;
  Transformation.counit := postcompose_counit
|}.
Next Obligation.
  intros S j; simpl; rewrite !fmap_id.
  apply (@Category.Theory.Adjunction.counit_fmap_unit _ _ F G Adj).
Qed.
Next Obligation.
  intros T j; simpl; rewrite !fmap_id.
  apply (@Category.Theory.Adjunction.fmap_counit_unit _ _ F G Adj).
Qed.

Definition postcompose_adjunction : postcompose (J:=J) F ⊣ postcompose (J:=J) G :=
  Adjunction_from_Transform postcompose_adjunction_transform.

(* Readbacks: the induced unit and counit are the whiskered originals on
   the nose. *)
Example postcompose_unit_component (S : J ⟶ X) (j : J) :
  transform[transform[postcompose_unit] S] j
    = @Category.Theory.Adjunction.unit _ _ F G Adj (S j) := eq_refl.

Example postcompose_counit_component (T : J ⟶ A) (j : J) :
  transform[transform[postcompose_counit] T] j
    = @Category.Theory.Adjunction.counit _ _ F G Adj (T j) := eq_refl.

(* The delivered adjunction's own accessors are the transposes of
   identities, [⌊id⌋] and [⌈id⌉], which carry a [fmap_id] residue over the
   constructed transformations; they agree with the whiskered originals
   at [≈] (the [eq_refl] form is refused, probe N5). *)
Lemma postcompose_adjunction_unit (S : J ⟶ X) (j : J) :
  transform[@Category.Theory.Adjunction.unit _ _ _ _ postcompose_adjunction S] j
    ≈ @Category.Theory.Adjunction.unit _ _ F G Adj (S j).
Proof. simpl; rewrite !fmap_id; apply id_left. Qed.

Lemma postcompose_adjunction_counit (T : J ⟶ A) (j : J) :
  transform[@Category.Theory.Adjunction.counit _ _ _ _ postcompose_adjunction T] j
    ≈ @Category.Theory.Adjunction.counit _ _ F G Adj (T j).
Proof. simpl; rewrite !fmap_id; apply id_right. Qed.

End PostcomposeAdjunction.

(** ** Riehl 4.3.6 (b): precomposition, [F ⊣ G] gives [precompose G ⊣ precompose F] *)

Section Precomposition.

Context {C D E : Category}.

(* Theory/Kan/Extension.v's [Induced] is [− ◯ F]; this is its name in the
   proposition's notation, [F^*]. *)
Definition precompose (F : C ⟶ D) : [D, E] ⟶ [C, E] := @Induced C D F E.

Example precompose_obj (F : C ⟶ D) (S : D ⟶ E) :
  precompose F S = S ◯ F := eq_refl.

Example precompose_component (F : C ⟶ D) {S T : D ⟶ E} (θ : S ⟹ T) (c : C) :
  transform[fmap[precompose F] θ] c = transform[θ] (F c) := eq_refl.

End Precomposition.

Section PrecomposeAdjunction.

Context {C D E : Category}.
Context {F : C ⟶ D} {G : D ⟶ C}.
Context (Adj : F ⊣ G).

#[local] Obligation Tactic := idtac.

Let η : Id ⟹ G ◯ F := @Transformation.unit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).
Let ε : F ◯ G ⟹ Id := @Transformation.counit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).

(* The unit: at [S : C ⟶ E] it is [S] whiskered onto the original unit,
   component [fmap[S] (η c)]. *)
Program Definition precompose_unit_at (S : C ⟶ E) : S ⟹ (S ◯ G) ◯ F := {|
  transform := fun c => fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c)
|}.
Next Obligation.
  intros S x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects; exact (naturality[η] _ _ f).
Qed.
Next Obligation.
  intros S x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects;
  exact (@naturality_sym _ _ _ _ η _ _ f).
Qed.

Program Definition precompose_unit :
  Id ⟹ precompose (E:=E) F ◯ precompose (E:=E) G := {|
  transform := precompose_unit_at
|}.
Next Obligation. intros S T θ c; simpl; apply naturality_sym. Qed.
Next Obligation. intros S T θ c; simpl; apply naturality. Qed.

(* The counit: at [T : D ⟶ E] it is [fmap[T] (ε d)]. *)
Program Definition precompose_counit_at (T : D ⟶ E) : (T ◯ F) ◯ G ⟹ T := {|
  transform := fun d => fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d)
|}.
Next Obligation.
  intros T x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects; exact (naturality[ε] _ _ f).
Qed.
Next Obligation.
  intros T x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects;
  exact (@naturality_sym _ _ _ _ ε _ _ f).
Qed.

Program Definition precompose_counit :
  precompose (E:=E) G ◯ precompose (E:=E) F ⟹ Id := {|
  transform := precompose_counit_at
|}.
Next Obligation. intros S T θ d; simpl; apply naturality_sym. Qed.
Next Obligation. intros S T θ d; simpl; apply naturality. Qed.

(* The triangle identities are the originals under [fmap[S]] / [fmap[T]],
   through [fmap_comp] and [fmap_id]. *)
Program Definition precompose_adjunction_transform :
  precompose (E:=E) G ∹ precompose (E:=E) F := {|
  Transformation.unit   := precompose_unit;
  Transformation.counit := precompose_counit
|}.
Next Obligation.
  intros S d; simpl.
  rewrite <- fmap_comp,
    (@Category.Theory.Adjunction.fmap_counit_unit _ _ F G Adj), !fmap_id.
  reflexivity.
Qed.
Next Obligation.
  intros T c; simpl.
  rewrite <- fmap_comp,
    (@Category.Theory.Adjunction.counit_fmap_unit _ _ F G Adj), !fmap_id.
  reflexivity.
Qed.

Definition precompose_adjunction : precompose (E:=E) G ⊣ precompose (E:=E) F :=
  Adjunction_from_Transform precompose_adjunction_transform.

Example precompose_unit_component (S : C ⟶ E) (c : C) :
  transform[transform[precompose_unit] S] c
    = fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c) := eq_refl.

Example precompose_counit_component (T : D ⟶ E) (d : D) :
  transform[transform[precompose_counit] T] d
    = fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d) := eq_refl.

(* Likewise for the delivered adjunction's own accessors. *)
Lemma precompose_adjunction_unit (S : C ⟶ E) (c : C) :
  transform[@Category.Theory.Adjunction.unit _ _ _ _ precompose_adjunction S] c
    ≈ fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c).
Proof. simpl; rewrite !fmap_id; apply id_left. Qed.

Lemma precompose_adjunction_counit (T : D ⟶ E) (d : D) :
  transform[@Category.Theory.Adjunction.counit _ _ _ _ precompose_adjunction T] d
    ≈ fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d).
Proof. simpl; rewrite !fmap_id; apply id_right. Qed.

End PrecomposeAdjunction.

(** ** Mac Lane V.5 Remark 1: the square of adjoint pairs *)

Section Square.

Context {J X A : Category}.
Context (F : X ⟶ A).

#[local] Obligation Tactic := idtac.

(* The left adjoints commute — but NOT on the nose: [(postcompose F ◯ Δ) x]
   has [fmap := fun _ _ _ => fmap[F] id] where [Δ (F x)] has [id] (probe
   N1).  They agree up to a natural isomorphism whose every component is
   an identity. *)
Program Definition square_at (x : X) :
  (postcompose (J:=J) F ◯ @Diagonal X J) x ≅[Fun] (@Diagonal A J ◯ F) x := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.

Program Definition square_iso :
  postcompose (J:=J) F ◯ @Diagonal X J ≅[Fun] @Diagonal A J ◯ F := {|
  to   := {| transform := fun x => to   (square_at x) |};
  from := {| transform := fun x => from (square_at x) |}
|}.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.

(* The same square as functor equality, oriented for the transport below. *)
Definition square_equiv :
  @Diagonal A J ◯ F ≈ postcompose (J:=J) F ◯ @Diagonal X J :=
  iso_equiv (iso_sym square_iso).

End Square.

Section Remark.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (LX : HasLimitsOfShape J X).
Context (LA : HasLimitsOfShape J A).

(* Left column then top row: [Δ_X ⊣ Lim_X] composed with
   [postcompose F ⊣ postcompose G]. *)
Definition left_route :
  (postcompose (J:=J) F ◯ @Diagonal X J)
    ⊣ (LimitFunctor LX ◯ postcompose (J:=J) G) :=
  Adjunction_Compose (Diagonal_Limit_Adjunction LX) (postcompose_adjunction Adj).

(* Bottom row then right column: [F ⊣ G] composed with [Δ_A ⊣ Lim_A]. *)
Definition right_route :
  (@Diagonal A J ◯ F) ⊣ (G ◯ LimitFunctor LA) :=
  Adjunction_Compose Adj (Diagonal_Limit_Adjunction LA).

(* Transport the left route across the square, so that both routes are
   adjunctions of the SAME left adjoint. *)
Definition left_route' :
  (@Diagonal A J ◯ F) ⊣ (LimitFunctor LX ◯ postcompose (J:=J) G) :=
  adjunction_along_left_iso (square_equiv F) left_route.

(* Uniqueness of right adjoints (Theory/Adjunction.v's [right_adjoint_iso])
   — not a re-proof. *)
Theorem Lim_commutes_right_adjoint :
  LimitFunctor LX ◯ postcompose (J:=J) G ≈ G ◯ LimitFunctor LA.
Proof using A Adj F G J LA LX X.
  exact (right_adjoint_iso _ _ _ left_route' right_route).
Qed.

(* The same statement as a natural isomorphism in [[[J, A], X]]. *)
Definition Lim_commutes_nat_iso :
  LimitFunctor LX ◯ postcompose (J:=J) G ≅[Fun] G ◯ LimitFunctor LA :=
  equiv_iso Lim_commutes_right_adjoint.

(* Pointwise: [lim (G ◯ T) ≅ G (lim T)], the classical reading of RAPL. *)
Definition lim_of_right_adjoint (T : J ⟶ A) :
  lim_obj LX (G ◯ T) ≅ G (lim_obj LA T) :=
  projT1 Lim_commutes_right_adjoint T.

End Remark.

(** ** The cone-level conclusion *)

Section ConeLevel.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (LA : HasLimitsOfShape J A).

(* "A right adjoint carries a limiting cone to a limiting cone, the cone
   being the value of the [Δ ⊣ Lim] counit": the limiting cone of [T] is
   [limit_cone (LA T)], whose legs are the components of [lim_counit LA T]
   ([lim_counit_is_limit_leg]), and [G] carries it to a limiting cone over
   [G ◯ T].  The proof is Adjunction/Continuity.v's direct RAPL
   ([right_adjoint_PreservesLimitCone]); see the header for why it is not
   derived from [Lim_commutes_right_adjoint]. *)
Definition right_adjoint_carries_lim_counit (T : J ⟶ A) :
  IsLimitCone (FCone G (@limit_cone _ _ _ (LA T))) :=
  right_adjoint_PreservesLimitCone Adj T (@limit_cone _ _ _ (LA T))
    (limit_limitcone (LA T)).

Example carried_leg_is_counit (T : J ⟶ A) (j : J) :
  cone_leg (FCone G (@limit_cone _ _ _ (LA T))) j
    ≈ fmap[G] (transform[lim_counit LA T] j).
Proof.
  rewrite FCone_leg, lim_counit_is_limit_leg; reflexivity.
Qed.

End ConeLevel.
