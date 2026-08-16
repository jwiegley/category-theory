Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.StrictCat.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Theory.DoubleCategory.
Require Import Category.Construction.Sq.
Require Import Category.Construction.Deloop.
Require Import Category.Theory.TwoCategory.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Cat as a strict 2-category *)

(* nLab:      https://ncatlab.org/nlab/show/Cat
   nLab:      https://ncatlab.org/nlab/show/Godement+product
   Wikipedia: https://en.wikipedia.org/wiki/Strict_2-category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §II.5, printed pp. 42-45 (Theorem 1, and the
              definitions of a double category and of a 2-category)
   Book:      Mac Lane, ibid., §XII.3, printed p. 273
   Book:      Riehl, "Category Theory in Context", Definition 1.7.8

   Mac Lane's §II.5 Theorem 1 says that the natural transformations form
   two interlocking categories — one whose objects are functors, one whose
   objects are categories — satisfying the interchange law, with every
   identity for the second composition an identity for the first.
   [Cat_TwoCategory] is that theorem in the globular presentation of
   Theory/TwoCategory.v: 0-cells are categories, 1-cells are functors,
   2-cells are natural transformations, vertical composition is
   [nat_compose] and horizontal composition is the Godement product
   [nat_hcompose].

   WHERE THE PIECES COME FROM.  Nothing here is re-proved that the tree
   already carries.  The 1-cell layer is [StrictCat], whose hom-setoid is
   the STRICT equality of functors [Functor_StrictEq_Setoid] — the
   deliberate use of a strict relation where the mathematical content is
   strictness, per that file's own note.  The vertical laws are the
   category laws of the functor category `[C, D]` ([id_left], [id_right],
   [comp_assoc] at `Fun`), used by name.  The interchange law is the
   `fmap_comp` obligation of Instance/Cat/Bicategory.v's [Cat_Hcompose],
   whose comment already identifies it as the middle-four exchange; it is
   applied here rather than reproved ([Cat_tinterchange]).

   WHAT IS DEFINITIONAL, AND WHY THAT IS THE POINT.  A [Transform] mentions
   only `fobj` and `fmap` of the two functors it lies between, and those
   agree definitionally across re-bracketing and unit adjustment of a
   functor composite: `((H ◯ G) ◯ F) x` and `(H ◯ (G ◯ F)) x` are the same
   term, as are the two `fmap`s.  The three boundary identifications the
   class asks for are therefore the identity on components — the
   `transform` field is passed through unchanged, and only the two
   naturality proofs are re-typed ([Cat_assoc_cast], [Cat_unitl_cast],
   [Cat_unitr_cast], with the pass-through recorded by `eq_refl` in
   [Cat_assoc_cast_component] and its siblings).  What is NOT definitional
   is the corresponding statement one level down: `(H ◯ G) ◯ F` and
   `H ◯ (G ◯ F)` are distinct terms of type `A ⟶ D`, since their
   `fmap_respects`, `fmap_id` and `fmap_comp` fields are built differently
   and those fields are `crelation`-valued, so no proof irrelevance
   identifies them.  `Cat` is thus not strictly associative at the level of
   1-CELLS in this library, and the class does not ask it to be; it asks
   only that re-bracketing identify the 2-cells, which it does, on the
   nose.  See the header of Theory/TwoCategory.v for the general
   discussion.

   THE WEAK AND THE STRICT PICTURE, RECONCILED.  Instance/Cat/Bicategory.v
   presents the same data as a BICATEGORY, with unitors [nat_ρ], [nat_λ]
   and associator `(nat_α)⁻¹` as genuine coherence 2-isomorphisms.  A
   section below proves that every one of those coherence cells has
   IDENTITY COMPONENTS ([Cat_bicat_hunit_left_id], [Cat_bicat_hunit_right_id],
   [Cat_bicat_hassoc_id], and the inverses), so the bicategory structure on
   `Cat` is weak only in its bookkeeping: the cells that a bicategory
   permits to be non-trivial are, here, componentwise identities.  That is
   the precise content of the folklore statement that `Cat` is a strict
   2-category, stated in a form this library can prove.

   MAC LANE'S NEGATIVE EXAMPLE.  §II.5's definition of a 2-category records
   that the commutative squares of Set form a double category which is NOT
   one.  Theory/TwoCategory.v builds the smallest faithful witness — the
   commuting squares of a ONE-OBJECT category, so that composability never
   asks for an equation between objects — as a genuine
   [StrictDoubleCategory], and refutes Mac Lane's def-3 condition for it
   ([NatSq_not_a_two_category]).  The base is the delooping of the additive
   monoid of naturals, so a square is a quadruple with `bot + left =
   right + top`; the offending cell is the horizontal identity on the
   vertical arrow 1, which is no vertical identity because pasting it under
   itself doubles its vertical edges.  A section below ties that model to
   Construction/Sq.v: its cells ARE the squares of `Sq` at that base
   (definitionally, with the round trip), and its two pastings agree
   with that model's EDGE BY EDGE — the recorded Examples equate the
   pasted square's edges with [Sq]'s composites; [dsq] there being a
   proposition, the boundary is the whole content — and
   the offending cell is [Sq_hid 1] — the horizontal identity square on a
   vertical morphism, whose vertical edges are `u` where a vertical
   identity square has vertical edges `id`. *)

(** ** The boundary identifications at Cat

    Each is the identity on components; only the naturality proofs are
    re-typed, and they are re-typed by conversion, the two statements being
    the same up to unfolding functor composition. *)

Definition Cat_assoc_cast {A B C D : Category}
  {F F' : A ⟶ B} {G G' : B ⟶ C} {H H' : C ⟶ D}
  (s : (H ◯ (G ◯ F)) ⟹ (H' ◯ (G' ◯ F'))) :
  ((H ◯ G) ◯ F) ⟹ ((H' ◯ G') ◯ F') :=
  @Build_Transform A D ((H ◯ G) ◯ F) ((H' ◯ G') ◯ F')
    (fun x => @transform _ _ _ _ s x)
    (fun x y f => @naturality _ _ _ _ s x y f)
    (fun x y f => @naturality_sym _ _ _ _ s x y f).

Definition Cat_unitl_cast {A B : Category} {F F' : A ⟶ B}
  (s : (Id ◯ F) ⟹ (Id ◯ F')) : F ⟹ F' :=
  @Build_Transform A B F F'
    (fun x => @transform _ _ _ _ s x)
    (fun x y f => @naturality _ _ _ _ s x y f)
    (fun x y f => @naturality_sym _ _ _ _ s x y f).

Definition Cat_unitr_cast {A B : Category} {F F' : A ⟶ B}
  (s : (F ◯ Id) ⟹ (F' ◯ Id)) : F ⟹ F' :=
  @Build_Transform A B F F'
    (fun x => @transform _ _ _ _ s x)
    (fun x y f => @naturality _ _ _ _ s x y f)
    (fun x y f => @naturality_sym _ _ _ _ s x y f).

(* The pass-through, recorded rather than asserted. *)

Example Cat_assoc_cast_component {A B C D : Category}
  {F F' : A ⟶ B} {G G' : B ⟶ C} {H H' : C ⟶ D}
  (s : (H ◯ (G ◯ F)) ⟹ (H' ◯ (G' ◯ F'))) (x : A) :
  transform[Cat_assoc_cast s] x = transform[s] x := eq_refl.

Example Cat_unitl_cast_component {A B : Category} {F F' : A ⟶ B}
  (s : (Id ◯ F) ⟹ (Id ◯ F')) (x : A) :
  transform[Cat_unitl_cast s] x = transform[s] x := eq_refl.

Example Cat_unitr_cast_component {A B : Category} {F F' : A ⟶ B}
  (s : (F ◯ Id) ⟹ (F' ◯ Id)) (x : A) :
  transform[Cat_unitr_cast s] x = transform[s] x := eq_refl.

(** ** The 2-cell laws at Cat *)

Lemma Cat_thcomp_respects {A B C : Category} {F F' : A ⟶ B}
  {G G' : B ⟶ C} :
  Proper (equiv ==> equiv ==> equiv) (@nat_hcompose A B C F F' G G').
Proof.
  intros ε ε' Hε η η' Hη; simpl; intro x.
  now rewrite (Hε (F' x)), (Hη x).
Qed.

Lemma Cat_thcomp_id {A B C : Category} (F : A ⟶ B) (G : B ⟶ C) :
  nat_hcompose (nat_id (F:=G)) (nat_id (F:=F)) ≈ nat_id (F:=G ◯ F).
Proof. simpl; intros; cat. Qed.

(* The middle-four interchange IS the `fmap_comp` obligation of
   [Cat_Hcompose] (Instance/Cat/Bicategory.v:76-83), whose own comment
   names it as such; it is applied, not repeated. *)
Lemma Cat_tinterchange {A B C : Category} {F F' F'' : A ⟶ B}
  {G G' G'' : B ⟶ C}
  (δ : G' ⟹ G'') (γ : G ⟹ G') (β : F' ⟹ F'') (α : F ⟹ F') :
  nat_hcompose (nat_compose δ γ) (nat_compose β α)
    ≈ nat_compose (nat_hcompose δ β) (nat_hcompose γ α).
Proof.
  exact (@fmap_comp _ _ (@Cat_Hcompose A B C)
           (G, F) (G', F') (G'', F'') (δ, β) (γ, α)).
Qed.

Lemma Cat_thassoc {A B C D : Category} {F F' : A ⟶ B} {G G' : B ⟶ C}
  {H H' : C ⟶ D} (γ : H ⟹ H') (β : G ⟹ G') (α : F ⟹ F') :
  Cat_assoc_cast (nat_hcompose γ (nat_hcompose β α))
    ≈ nat_hcompose (nat_hcompose γ β) α.
Proof.
  simpl; intro x.
  now rewrite fmap_comp, comp_assoc.
Qed.

Lemma Cat_thunit_left {A B : Category} {F F' : A ⟶ B} (α : F ⟹ F') :
  Cat_unitl_cast (nat_hcompose (nat_id (F:=Id)) α) ≈ α.
Proof. simpl; intros; cat. Qed.

Lemma Cat_thunit_right {A B : Category} {F F' : A ⟶ B} (α : F ⟹ F') :
  Cat_unitr_cast (nat_hcompose α (nat_id (F:=Id))) ≈ α.
Proof. simpl; intros; cat. Qed.

(** ** Cat as a strict 2-category

    The pinned name.  Every field is either a projection of the functor
    category `[C, D]`, a construction of Theory/Natural/Transformation.v, or
    one of the lemmas above; nothing is left to automation. *)

Definition Cat_TwoCategory : TwoCategory := {|
  tcat                 := StrictCat;
  tcell                := fun A B F G => @Transform A B F G;
  tcell_setoid         := fun A B F G => @homset (@Fun A B) F G;
  tid2                 := fun A B F => @nat_id A B F;
  tvcomp               := fun A B F G H => @nat_compose A B F G H;
  tvcomp_respects      := fun A B F G H => @nat_compose_respects A B F G H;
  tvid_left            := fun A B F G α => @id_left (@Fun A B) F G α;
  tvid_right           := fun A B F G α => @id_right (@Fun A B) F G α;
  tvassoc              := fun A B F G H K γ β α =>
                            @comp_assoc (@Fun A B) F G H K γ β α;
  thcomp               := fun A B C F F' G G' => @nat_hcompose A B C F F' G G';
  thcomp_respects      := fun A B C F F' G G' =>
                            @Cat_thcomp_respects A B C F F' G G';
  thcomp_id            := fun A B C F G => @Cat_thcomp_id A B C F G;
  tinterchange         := fun A B C F F' F'' G G' G'' =>
                            @Cat_tinterchange A B C F F' F'' G G' G'';
  tassoc_cast          := fun A B C D F F' G G' H H' =>
                            @Cat_assoc_cast A B C D F F' G G' H H';
  tunitl_cast          := fun A B F F' => @Cat_unitl_cast A B F F';
  tunitr_cast          := fun A B F F' => @Cat_unitr_cast A B F F';
  tassoc_cast_respects := fun A B C D F F' G G' H H' s t Hst x => Hst x;
  tunitl_cast_respects := fun A B F F' s t Hst x => Hst x;
  tunitr_cast_respects := fun A B F F' s t Hst x => Hst x;
  tassoc_cast_vcomp    := fun A B C D F F' F'' G G' G'' H H' H'' β α x =>
                            reflexivity _;
  tunitl_cast_vcomp    := fun A B F F' F'' β α x => reflexivity _;
  tunitr_cast_vcomp    := fun A B F F' F'' β α x => reflexivity _;
  thassoc              := fun A B C D F F' G G' H H' γ β α =>
                            @Cat_thassoc A B C D F F' G G' H H' γ β α;
  thunit_left          := fun A B F F' α => @Cat_thunit_left A B F F' α;
  thunit_right         := fun A B F F' α => @Cat_thunit_right A B F F' α
|}.

(** ** Acceptance tests

    The structural fields reduce to the constructions they were built
    from, so consumers of the class compute with the ordinary vocabulary of
    functor categories. *)

Example Cat_TwoCategory_tcat : @tcat Cat_TwoCategory = StrictCat := eq_refl.

Example Cat_TwoCategory_tvcomp {A B : Category} {F G H : A ⟶ B}
  (β : G ⟹ H) (α : F ⟹ G) :
  @tvcomp Cat_TwoCategory A B F G H β α = nat_compose β α := eq_refl.

Example Cat_TwoCategory_thcomp {A B C : Category} {F F' : A ⟶ B}
  {G G' : B ⟶ C} (β : G ⟹ G') (α : F ⟹ F') :
  @thcomp Cat_TwoCategory A B C F F' G G' β α = nat_hcompose β α := eq_refl.

Example Cat_TwoCategory_tid2 {A B : Category} (F : A ⟶ B) :
  @tid2 Cat_TwoCategory A B F = nat_id := eq_refl.

(* The hom-category of Theory/TwoCategory.v is the functor category, on all
   its structural fields. *)

Example Cat_thom_obj (A B : Category) :
  obj[thom (K:=Cat_TwoCategory) A B] = obj[[A, B]] := eq_refl.

Example Cat_thom_hom (A B : Category) (F G : A ⟶ B) :
  (F ~{thom (K:=Cat_TwoCategory) A B}~> G) = (F ~{[A, B]}~> G) := eq_refl.

(* Whiskering computes to the two whiskerings of Theory/Natural/
   Transformation.v up to `≈` — Mac Lane's convention that a functor symbol
   denotes its identity transformation. *)

Lemma Cat_twhisker_l_is_whisker_left {A B C : Category} (G : B ⟶ C)
  {F F' : A ⟶ B} (α : F ⟹ F') :
  twhisker_l (K:=Cat_TwoCategory) G α ≈ whisker_left G α.
Proof. simpl; intros; cat. Qed.

Lemma Cat_twhisker_r_is_whisker_right {A B C : Category} {G G' : B ⟶ C}
  (β : G ⟹ G') (F : A ⟶ B) :
  twhisker_r (K:=Cat_TwoCategory) β F ≈ whisker_right β F.
Proof. simpl; intros; cat. Qed.

(** ** The weak and the strict picture, reconciled

    Instance/Cat/Bicategory.v equips the same data with the coherence cells
    of a bicategory.  Those cells are not merely invertible: every one of
    them has identity components, which is what makes `Cat` strict rather
    than merely coherent.  The unitor and associator fields of
    [Cat_Bicategory] are `nat_ρ`, `nat_λ` and `(nat_α)⁻¹` on the nose
    (recorded by `eq_refl` below, under the crossed dictionary that file's
    header explains), so it suffices to compute the components of those. *)

Example Cat_bicat_hunit_left_is_nat_ρ {C D : Category} (f : C ⟶ D) :
  @hunit_left Cat_Bicategory C D f = nat_ρ f := eq_refl.

Example Cat_bicat_hunit_right_is_nat_λ {C D : Category} (f : C ⟶ D) :
  @hunit_right Cat_Bicategory C D f = nat_λ f := eq_refl.

Example Cat_bicat_hassoc_is_nat_α {W X Y Z : Category}
  (h : Y ⟶ Z) (g : X ⟶ Y) (f : W ⟶ X) :
  @hassoc Cat_Bicategory W X Y Z h g f = iso_sym (nat_α f g h) := eq_refl.

Lemma Cat_bicat_hunit_left_id {C D : Category} (f : C ⟶ D) (x : C) :
  transform[to (@hunit_left Cat_Bicategory C D f)] x ≈ id.
Proof. simpl; cat. Qed.

Lemma Cat_bicat_hunit_left_from_id {C D : Category} (f : C ⟶ D) (x : C) :
  transform[from (@hunit_left Cat_Bicategory C D f)] x ≈ id.
Proof. simpl; cat. Qed.

Lemma Cat_bicat_hunit_right_id {C D : Category} (f : C ⟶ D) (x : C) :
  transform[to (@hunit_right Cat_Bicategory C D f)] x ≈ id.
Proof. simpl; cat. Qed.

Lemma Cat_bicat_hunit_right_from_id {C D : Category} (f : C ⟶ D) (x : C) :
  transform[from (@hunit_right Cat_Bicategory C D f)] x ≈ id.
Proof. simpl; cat. Qed.

Lemma Cat_bicat_hassoc_id {W X Y Z : Category}
  (h : Y ⟶ Z) (g : X ⟶ Y) (f : W ⟶ X) (x : W) :
  transform[to (@hassoc Cat_Bicategory W X Y Z h g f)] x ≈ id.
Proof. simpl; cat. Qed.

Lemma Cat_bicat_hassoc_from_id {W X Y Z : Category}
  (h : Y ⟶ Z) (g : X ⟶ Y) (f : W ⟶ X) (x : W) :
  transform[from (@hassoc Cat_Bicategory W X Y Z h g f)] x ≈ id.
Proof. simpl; cat. Qed.

(* The strict laws of [Cat_TwoCategory] are therefore the bicategory's
   coherence laws with the coherence cells erased: horizontal composition
   in the bicategory, [hcomp2], is the class's [thcomp] on the nose. *)

Example Cat_hcomp2_is_thcomp {A B C : Category} {F F' : A ⟶ B}
  {G G' : B ⟶ C} (β : G ⟹ G') (α : F ⟹ F') :
  @hcomp2 Cat_Bicategory A B C G G' F F' β α
    = @thcomp Cat_TwoCategory A B C F F' G G' β α := eq_refl.

(** ** Mac Lane's negative example, tied to Construction/Sq.v

    Theory/TwoCategory.v refutes definition 3 at [NatSq_Double], the
    commuting squares of the delooping of the additive monoid of naturals.
    That model is not a private invention: its cells ARE the squares of
    Construction/Sq.v's [Sq] at that base, and its two pastings agree
    with that model's edge by edge.  The identifications below are
    definitional at cell level and edge-level for the pastings,
    which is what licenses reading the refutation as a statement about
    [Sq]. *)

Local Notation NatBase := (Deloop Nat_Plus).

(* A cell of [NatSq_Double] is a square of [Sq NatBase], and conversely.
   Both directions are the identity on the data; only the packaging
   differs. *)

Definition NatSq_to_Sq (x : NatSq) :
  @dsq (Sq NatBase) ttt ttt ttt ttt
    (nsq_top x) (nsq_left x) (nsq_right x) (nsq_bot x) :=
  nsq_comm x.

Definition Sq_to_NatSq (h u v k : ttt ~{NatBase}~> ttt)
  (s : @dsq (Sq NatBase) ttt ttt ttt ttt h u v k) : NatSq :=
  mkNatSq h u v k s.

Example NatSq_Sq_roundtrip (x : NatSq) :
  NatSq_eq (Sq_to_NatSq _ _ _ _ (NatSq_to_Sq x)) x.
Proof. now repeat split. Qed.

(* The two pastings agree with [Sq]'s on every edge: vertical pasting
   composes the vertical edges of the base, horizontal pasting the
   horizontal ones.  Recorded by `eq_refl`, composition in the delooping
   being the monoid operation. *)

Example NatSq_vpaste_edges (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  nsq_left (NatSq_vpaste g f Hm)
    = @compose NatBase ttt ttt ttt (nsq_left g) (nsq_left f) := eq_refl.

Example NatSq_vpaste_edges_right (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  nsq_right (NatSq_vpaste g f Hm)
    = @compose NatBase ttt ttt ttt (nsq_right g) (nsq_right f) := eq_refl.

Example NatSq_hpaste_edges (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  nsq_top (NatSq_hpaste g f Hm)
    = @compose NatBase ttt ttt ttt (nsq_top g) (nsq_top f) := eq_refl.

Example NatSq_hpaste_edges_bot (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  nsq_bot (NatSq_hpaste g f Hm)
    = @compose NatBase ttt ttt ttt (nsq_bot g) (nsq_bot f) := eq_refl.

(** *** The horizontal identity square of an arbitrary base

    Theory/DoubleCategory.v's SCOPE note records that horizontal identity
    squares on general VERTICAL morphisms are not fields of the pseudo
    class.  In [Sq C] the square exists for every vertical morphism, and
    its type displays the whole of Mac Lane's point: its vertical edges are
    [u], where a vertical identity square [dsq_vid] has vertical edges
    [id].  The two families therefore meet only where [u] is an identity,
    and a base with a non-identity arrow separates them. *)

Definition Sq_hid {C : Category} {a c : C} (u : a ~{C}~> c) :
  @dsq (Sq C) a a c c (@dhid (Sq C) a) u u (@dhid (Sq C) c).
Proof. simpl; cat. Defined.

(* The vertical identity square on a horizontal 1-cell, for contrast: its
   vertical edges are identities, which is exactly what [Sq_hid u] has only
   when [u] is one. *)
Definition Sq_vid {C : Category} {a b : C} (h : a ~{C}~> b) :
  @dsq (Sq C) a b a b h id id h := @dsq_vid (Sq C) a b h.

(* At the base above, the separating arrow is 1: the horizontal identity
   square on it is the cell Theory/TwoCategory.v refutes definition 3
   with, and 1 is not the identity of the delooping. *)

Example NatSq_bad_is_Sq_hid :
  NatSq_eq NatSq_bad
    (Sq_to_NatSq (@dhid (Sq NatBase) ttt) 1%nat 1%nat (@dhid (Sq NatBase) ttt)
       (Sq_hid (C:=NatBase) (a:=ttt) (c:=ttt) 1%nat)).
Proof. now repeat split. Qed.

Lemma NatBase_one_not_id : (1%nat : ttt ~{NatBase}~> ttt) ≈ id → False.
Proof. simpl; discriminate. Qed.

(** ** A concrete exercise of the class

    Nothing above is vacuous.  The delooping of the additive monoid of
    naturals carries genuinely non-identity 2-cells over its identity
    functor: a natural transformation `Id ⟹ Id` is an element of the
    CENTRE (Mac Lane §II.5 Exercise 8), and here the monoid is commutative,
    so every natural number gives one.  Their vertical and horizontal
    composites agree and both compute to addition — the Eckmann-Hilton
    collapse of Exercise 5, at the one place where the two units genuinely
    coincide, namely 2-cells on an identity 1-cell. *)

Program Definition NatBase_centre (n : nat) : (@Id NatBase) ⟹ (@Id NatBase)
  := {| transform := fun _ => n |}.
Next Obligation. simpl; lia. Qed.
Next Obligation. simpl; lia. Qed.

Example NatBase_centre_vcomp (m n : nat) (x : NatBase) :
  transform[@tvcomp Cat_TwoCategory NatBase NatBase _ _ _
              (NatBase_centre m) (NatBase_centre n)] x = (m + n)%nat
  := eq_refl.

Example NatBase_centre_hcomp (m n : nat) (x : NatBase) :
  transform[@thcomp Cat_TwoCategory NatBase NatBase NatBase _ _ _ _
              (NatBase_centre m) (NatBase_centre n)] x = (m + n)%nat
  := eq_refl.

(* One whiskering, computed: whiskering by the identity 1-cell leaves the
   component alone, the identity of the base being 0. *)
Example NatBase_whisker (n : nat) (x : NatBase) :
  transform[twhisker_l (K:=Cat_TwoCategory) (@Id NatBase)
              (NatBase_centre n)] x = n := eq_refl.

Example NatBase_centre_nontrivial :
  @equiv _ (@tcell_setoid Cat_TwoCategory NatBase NatBase (@Id NatBase)
              (@Id NatBase))
    (NatBase_centre 1) nat_id → False.
Proof. intro H; specialize (H ttt); simpl in H; discriminate. Qed.
