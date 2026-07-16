Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Kan extensions *)

(* nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   Given a functor F : A ⟶ B, precomposition with F induces the restriction
   functor Induced := (− ◯ F) : [B, C] ⟶ [A, C]. The Kan extensions along F
   are its adjoints, when they exist: the left Kan extension Lan is the LEFT
   adjoint to Induced (Lan ⊣ Induced), and the right Kan extension Ran is the
   RIGHT adjoint to Induced (Induced ⊣ Ran). Equivalently, by the hom-set
   adjunctions, [A,C](X, M ◯ F) ≅ [B,C](Lan X, M) naturally in M, and
   [A,C](M ◯ F, X) ≅ [B,C](M, Ran X) naturally in M.

   These are the GLOBAL Kan extensions (the adjoint functors). The LOCAL Kan
   extension of a single functor X : A ⟶ C can exist even when the global
   adjoint does not; it is the universal pair given by a unit X ⟹ LocalLan ◯ F
   (left, initial) or a counit LocalRan ◯ F ⟹ X (right, terminal). When C' = 1
   the left/right Kan extensions specialise to colimits/limits of X. The
   slogan "all concepts are Kan extensions" (Mac Lane) records that limits,
   colimits, adjoints, ends, and coends are all instances. *)

(* Where Kan extensions come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/codensity+monad
   nLab:  https://ncatlab.org/nlab/show/nerve+and+realization
   Paper: Kan, "Adjoint functors", Transactions of the American
          Mathematical Society 87, 1958
   Paper: Leinster, "Codensity and the ultrafilter monad", Theory and
          Applications of Categories 28, 2013
   Paper: Hinze, "Kan Extensions for Program Optimisation — Or: Art and
          Dan Explain an Old Trick", MPC 2012

   Adjoint functors and Kan extensions entered mathematics in the same
   paper.  Daniel Kan, after whom Kan complexes and Kan fibrations are
   named, wrote "Adjoint functors" (1958) to codify the formal
   properties of the passage between spaces and simplicial sets; the
   memorial note of Barwick, Hopkins, Miller and Moerdijk ("Daniel M.
   Kan (1927–2013)") records that Eilenberg insisted on the name
   "adjoint", that the same paper defines limits, colimits, and what
   are now called Kan extensions, and that Mac Lane's dictum is "only a
   mild exaggeration".  The word "extension" is homotopical in origin:
   Kan had defined homotopy groups of cubical sets by extending maps
   from the boundary of a cube minus one face, the extension condition
   now named after him.  Mac Lane devotes Chapter X of Categories for
   the Working Mathematician to the concept, with §X.7 titled "All
   Concepts Are Kan Extensions"; Riehl titles Chapter 6 of Category
   Theory in Context (2016) the same way; the Lehner thesis quoted
   later in this file works that program out in detail.

   The problem the definitions answer is extension along a change of
   index: given X : A ⟶ C and F : A ⟶ B, produce the functor B ⟶ C
   that best extends X through F, "best" splitting into a free (left,
   initial) and a cofree (right, terminal) answer.  Because the global
   forms are the two adjoints of [Induced], a Kan extension is an
   adjunction one level up, and the slogan becomes a theorem schedule.
   The header's specialization to (co)limits is realized in-tree by
   [Kan_Limit] in Structure/Limit/Kan/Extension.v — a limit is a right
   Kan extension along the functor erasing the diagram shape — and a
   functor has a left adjoint precisely when the right Kan extension of
   the identity along it exists and is preserved by it (Wikipedia, "Kan
   extension"), the adjoint functor theorem of Lehner's thesis and the
   reason [preserves_left_Kan], [preserves_right_Kan] and
   [left_adjoint_impl] appear below.  Pointwise, the left extension at
   b is a colimit over the comma category F ↓ b and the right a limit
   over b ↓ F, equivalently Kelly's coend and end formulas (nLab, "Kan
   extension"); the coend calculus of Structure/Coend.v and
   Instance/Sets/{End,Coend}.v is the in-tree machinery those formulas
   would rest on, a bridge not yet formalized.

   Much of the utility lies where adjoints do not exist.  The right Kan
   extension of a functor G along itself is always a monad — the
   codensity monad, Mac Lane's Exercise X.7.3 — the monad G induces
   even in the absence of a left adjoint, measuring how far G is from
   being codense (nLab, "codensity monad").  For the inclusion of
   finite sets into sets it is the ultrafilter monad (Kennison,
   Gildenhuys, "Equational completion, model induced triples and
   pro-objects", JPAA 1, 1971), a result Leinster revived, adding that
   for finite-dimensional vector spaces in all vector spaces it is
   double dualization.  Geometric realization is the left Kan extension
   of a cosimplicial space along the Yoneda embedding, the nerve its
   restricted-Yoneda right adjoint — already §3 of Kan's companion
   paper "Functors involving c.s.s. complexes" (1958; nLab, "nerve and
   realization") — and total derived functors are Kan extensions along
   localization at the weak equivalences (Riehl, Category Theory in
   Context, §6.4).  In-tree, Construction/Day.v exhibits Day
   convolution as the left Kan extension of the external tensor of two
   presheaves along the tensor of the base.

   The computational reading is continuation-passing style.  Hinze (MPC
   2012) states it directly: continuations implement a right Kan
   extension — the end formula is the rank-2 type of a CPS computation,
   and the codensity monad the case where answer types live under the
   extended functor itself.  Re-representing a free-monad program in
   its codensity monad right-associates its binds and can improve
   quadratic running time to linear (Voigtländer, "Asymptotic
   Improvement of Computations over Free Monads", MPC 2008); Kmett's
   kan-extensions Haskell package ships Ran, Lan, Yoneda and Codensity
   in this rank-2 form.  This file proves against what Hinze calls the
   specification — the adjunctions [ran_adjoint] and [lan_adjoint] —
   rather than those rank-2 implementations. *)

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

(* The restriction (precomposition) functor Induced := (− ◯ F) : [B,C] ⟶ [A,C],
   written F* or p* in the literature.  On objects it sends G : B ⟶ C to G ◯ F;
   on a natural transformation f : G ⟹ H it whiskers by F, giving the component
   (Induced f)_z = f_(F z).  The Kan extensions along F are the adjoints of this
   functor.
   nLab: https://ncatlab.org/nlab/show/Kan+extension *)

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.
Next Obligation. apply naturality. Qed.
Next Obligation. apply naturality_sym. Qed.

(* Global right Kan extension along F: the right adjoint Ran of the restriction
   functor Induced = (− ◯ F).  The adjunction Induced ⊣ Ran corresponds to the
   hom-set isomorphism [A,C](M ◯ F, X) ≅ [B,C](M, Ran X), natural in M.
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension *)

Class RightKan := {
  (* jww (2017-06-09): Rename this to ran_functor, RightKan to Ran, and then a
     coercion from Ran to functor? *)
  Ran : [A, C] ⟶ [B, C];           (* the right Kan extension functor       *)

  ran_adjoint : Induced ⊣ Ran      (* universal property: Induced ⊣ Ran     *)
}.

(* Local (pointwise-free) right Kan extension of a single functor X : A ⟶ C
   along F.  This is the terminal object among pairs (functor, counit), and can
   exist even when the global adjoint Ran above does not.  The counit
   ran_transform : LocalRan ◯ F ⟹ X is universal: every μ : M ◯ F ⟹ X factors
   through it via a unique δ : M ⟹ LocalRan. *)

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;                       (* the extending functor R : B ⟶ C *)

  ran_transform : LocalRan ◯ F ⟹ X;       (* counit ε : R ◯ F ⟹ X            *)

  (* terminality / universal property: μ factors uniquely through the counit
     as μ ≈ ran_transform ∙ (δ ⊲ F), with δ the unique mediating arrow *)
  ump_ran (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
    (∃! δ, μ ≈ ran_transform ∙ δ ⊲ F);
}.

(* Wikipedia: "There is also a local definition of 'the Kan extension of a
   given functor F along p' which can exist even if the entire functor defined
   above [global Kan extension] does not. This is a generalization of the fact
   that a particular diagram of shape C can have a limit even if not every
   such diagram does. It is also a special case of the fact discussed at
   adjoint functor that an adjoint functor can fail to exist completely, but
   may still be partially defined. If the local Kan extension of every single
   functor exists for some given p : C → C' and D, then these local Kan
   extensions fit together to define a functor which is the global Kan
   extension." *)

(* A global right Kan extension restricts to a local one at each X: take the
   extending functor to be Ran X and the counit to be the image of the identity
   under the adjunction iso (the counit of Induced ⊣ Ran at X). *)

#[export] Program Instance RightKan_to_LocalRightKan {R : RightKan} (X : A ⟶ C) :
  LocalRightKan X := {|
  LocalRan := Ran X;
  ran_transform := from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_id
|}.
Next Obligation.
  exists (to (@adj _ _ _ _ (@ran_adjoint R) M X) μ).
  - intros.
    spose (@from_adj_nat_l _ _ _ _ ran_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_from_to _ _ _ (@adj _ _ _ _ ran_adjoint M X) μ x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@from _ _ _ (@adj _ _ _ _ ran_adjoint M X))).
    simpl; intros; cat.
  - intros.
    assert (μ ≈ (adj[ran_adjoint])⁻¹ v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint).
      destruct (adj[ran_adjoint]); simpl in *.
      destruct from; simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_left.
    }
    clear -X1.
    destruct (adj[ran_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_to_from v).
    destruct to; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

(* Global left Kan extension along F: the left adjoint Lan of the restriction
   functor Induced = (− ◯ F).  The adjunction Lan ⊣ Induced corresponds to the
   hom-set isomorphism [A,C](X, M ◯ F) ≅ [B,C](Lan X, M), natural in M.
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension *)

Class LeftKan := {
  Lan : [A, C] ⟶ [B, C];           (* the left Kan extension functor        *)

  lan_adjoint : Lan ⊣ Induced      (* universal property: Lan ⊣ Induced     *)
}.

(* Local left Kan extension of a single functor X : A ⟶ C along F.  This is the
   initial object among pairs (functor, unit), and can exist even when the
   global adjoint Lan above does not.  The unit lan_transform : X ⟹ LocalLan ◯ F
   is universal: every ε : X ⟹ M ◯ F factors through it via a unique
   δ : LocalLan ⟹ M. *)

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;                       (* the extending functor L : B ⟶ C *)

  lan_transform : X ⟹ LocalLan ◯ F;       (* unit η : X ⟹ L ◯ F              *)

  (* initiality / universal property: ε factors uniquely through the unit as
     ε ≈ (δ ⊲ F) ∙ lan_transform, with δ the unique mediating arrow *)
  ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
    ∃! δ, ε ≈ δ ⊲ F ∙ lan_transform;
}.

(* A global left Kan extension restricts to a local one at each X: take the
   extending functor to be Lan X and the unit to be the image of the identity
   under the adjunction iso (the unit of Lan ⊣ Induced at X). *)

#[export] Program Instance LeftKan_to_LocalLeftKan {R : LeftKan} (X : A ⟶ C) :
  LocalLeftKan X := {|
  LocalLan := Lan X;
  lan_transform := to (@adj _ _ _ _ lan_adjoint X (Lan X)) nat_id
|}.
Next Obligation.
  exists (from (@adj _ _ _ _ (@lan_adjoint R) X M) ε).
  - intros.
    spose (@to_adj_nat_r _ _ _ _ lan_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_to_from _ _ _ (@adj _ _ _ _ lan_adjoint X M) ε x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@to _ _ _ (@adj _ _ _ _ lan_adjoint X M))).
    simpl; intros; cat.
  - intros.
    assert (ε ≈ (to adj[lan_adjoint]) v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@to_adj_nat_r _ _ _ _ lan_adjoint).
      destruct (to adj[lan_adjoint]); simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_right.
    }
    clear -X1.
    destruct (adj[lan_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_from_to v).
    destruct from; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

End KanExtension.

Arguments RightKan {_ _} F _.
Arguments Ran {_ _} F {_ _}.

Arguments LocalRightKan {_ _} F {_} _.
Arguments LocalRan {_ _} F {_} _ {_}.

Arguments LeftKan {_ _} F _.
Arguments Lan {_ _} F {_ _}.

Arguments LocalLeftKan {_ _} F {_} _.
Arguments LocalLan {_ _} F {_} _ {_}.

(* From "All Concepts are Kan Extensions", by Marina Christina Lehner:

   "A functor preserves a Kan extension when composing then extending is
   equivalent to extending then composing." *)

(* A functor L preserves left Kan extensions when applying L after extending
   agrees with extending after applying L, i.e. L ◯ Lan K G ≈ Lan K (L ◯ G).
   The two LeftKan hypotheses supply the extensions on each side. *)

Definition preserves_left_Kan `(L : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!LeftKan K E) `(!LeftKan K F), L ◯ Lan K G ≈ Lan K (L ◯ G).

(* Dual: R preserves right Kan extensions when R ◯ Ran K G ≈ Ran K (R ◯ G). *)

Definition preserves_right_Kan `(R : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!RightKan K E) `(!RightKan K F), R ◯ Ran K G ≈ Ran K (R ◯ G).

(* "We show that left adjoints preserve left Kan extensions, while right
   adjoints will preserve right adjoints [sic]. These connections with
   adjoints run deeper. We will show an adjoint functor theorem which says
   the existence of an adjoint is conditional on a functor having and
   preserving certain Kan extensions." *)

(* If L ⊣ R then precomposition by L is hom-isomorphic to postcomposition by R:
   [E,D](L ◯ G, H) ≊ [E,C](G, R ◯ H), the functor-category lift of the
   defining hom-set adjunction.  This is the lemma used to show that left
   adjoints preserve left Kan extensions. *)

Theorem left_adjoint_impl `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R ->
  ∀ {E} (G : E ⟶ C) (H : E ⟶ D),
    [[[E,D]]](L ◯ G, H) ≊ [[[E,C]]](G, R ◯ H).
Proof.
  intros.
  simpl.
  isomorphism; simpl.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply to_adj_respects.
      now apply X0.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply from_adj_respects.
      now apply X0.
  - simpl.
    now apply from_adj_comp_law.
  - simpl.
    now apply to_adj_comp_law.
Qed.

(* Work in progress: left adjoints preserve left Kan extensions (Lehner, "All
   Concepts are Kan Extensions").  The proof is incomplete — three obligations
   are left open and the proof script is abandoned before `Qed`, so the theorem
   is NOT added to the environment and introduces no axioms.  Retained as a
   proof sketch.  jww: complete the remaining isomorphism/identity obligations.
   The adjoint-continuity machinery this wants now exists —
   [right_adjoint_preserves_limits] and the preservation vocabulary in
   Adjunction/Continuity.v and Structure/Limit/Preservation.v — and is the
   natural toolkit for a future completion of this sketch. *)

Theorem left_adjoints_preserve `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R → preserves_left_Kan L.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply X; simpl.
      rewrite <- fobj_Compose.
      apply LeftKan0; simpl.
      spose (left_adjoint_impl _ _ X G (Lan K (L ◯ G) ◯ K)) as X0.
      transitivity (R ◯ (Lan K (L ◯ G) ◯ K)).
      * apply (to X0); simpl.
        apply LeftKan1; simpl.
        exact nat_id.
      * now apply fun_comp_assoc.
    + rewrite <- fobj_Compose.
      apply LeftKan1; simpl.
      spose (left_adjoint_impl _ _ X G (L ◯ Lan K G ◯ K)) as X0.
      apply X0; simpl; clear X0.
      transitivity (R ◯ L ◯ fobj[Lan _] G ◯ K). {
        apply LeftKan0; simpl.
        transform.
        - intros.
          apply unit.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
      }
      pose proof (@fun_comp_assoc_sym _ _ _ _ R L (Lan K G ◯ K)).
      pose proof (@fun_comp_assoc_sym _ _ _ _ R (L ◯ Lan K G) K).
      pose proof (@fun_comp_assoc_sym _ _ _ _ (R ◯ L) (Lan K G) K).
      transitivity ((R ◯ L) ◯ ((fobj[Lan _] G) ◯ K)); auto.
      transitivity (R ◯ (L ◯ ((fobj[Lan _] G) ◯ K))); auto.
      transitivity (R ◯ ((L ◯ (fobj[Lan _] G)) ◯ K)).
      * apply whisker_left.
        apply fun_comp_assoc.
      * exact nat_id.
    + simpl.
      admit.
    + simpl.
      admit.
  - simpl.
    admit.
Abort.
