Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(** * Collapsing a subset to a point: X/A as a wide coequalizer in [Top] *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, book p. 134 (PDF p. 143), read from the page image: "Another
     coequalizer is the space X/A obtained from the space X by collapsing
     the subset A to a point.  It is the coequalizer [...] of the set of
     all the arrows sending the one point space * to one of the points
     a ∈ A.  It is used in homotopy theory." (catalog id
     maclane:V.9:construction5; the book numbers it not)
   nLab:      https://ncatlab.org/nlab/show/Top
   nLab:      https://ncatlab.org/nlab/show/quotient+space
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
   Book:      A. Hatcher, "Algebraic Topology", Cambridge University Press
              (2002), Chapter 0 (quotient spaces X/A, cones, suspensions,
              wedge and smash products)

   BACKGROUND.  Collapsing a subspace to a point is the basic gluing move
   of homotopy theory: Hatcher's Chapter 0 builds the cone, the
   suspension and the smash product X ∧ Y = (X × Y)/(X ∨ Y) with it.
   Wikipedia's quotient-space page lists X/A among its examples, with the
   2-sphere as the disc with its boundary collapsed, D²/∂D²; the nLab
   page on quotient spaces gives the quotient topology as the final
   topology induced by the projection.  Mac Lane places the construction
   in §V.9 among the colimits of Top, after the coequalizers and general
   colimits of catalog id maclane:V.9:remark2 (the book numbers no
   remarks) and that paragraph's open-cover example, and makes one
   categorical observation about it: X/A is a coequalizer, not of a
   parallel PAIR but of a whole parallel family of arrows * → X, one per
   point of A.  His §III.3 provides for that on book pp. 64-65 (PDF
   pp. 73-74), read from the page images.  He DEFINES the coequalizer of
   a pair elementarily, in display (6) of p. 64: an arrow u : b → e with
   uf = ug, through which every h : b → c with hf = hg factors uniquely.
   He then says that a coequalizer "can be interpreted as a universal
   arrow", and p. 65 reads it as one, "just a universal arrow from
   ⟨f, g⟩ to the functor Δ"; then "Coequalizers of any set of maps from
   a to b are defined in the same way."  For a set of maps a → b the two
   readings are Structure/Coequalizer/Wide.v's elementary record
   [IsWideCoequalizer], an arrow out of b alone, which is (6) extended
   and the reading that file's header adopts, and its colimit form
   [WideCoequalizer], a colimit over the shape that has a as a vertex.
   They agree on every nonempty set of maps.  At the empty set the
   colimit is the coproduct of a and b, and the elementary record pins
   down b itself (that file's header, which states the coproduct without
   formalizing it, and its [wide_coround_trip_needs_point]); the book
   does not treat that case.  Here a is * and b is X: read as the
   universal arrow, X/∅ is X ⊔ * (at [Top], Pairs.v's
   [pquot_wide_coequalizer_colimit_empty]); read elementarily, it is X.
   The header of Instance/Top/Cocomplete.v lists the collapse among the
   worked colimits of book p. 134 that it does not build; this file
   builds it, and Instance/Top/Quotient/Pairs.v the other half of the
   book's paragraph, the category of pairs and the adjunction.

   WHAT IS HERE.
     - The collapse along a FAMILY [p : I → X] of points, I at the points'
       universe.  [Top_collapse X I p] has the points of X, two of them
       identified when they are equal or when both lie in the image of
       [p] up to the points' equality ([collapse_image], the SATURATED
       image, so nothing is asked of [p]), with the quotient topology
       [TQuot] of Instance/Top/Subspace/TypeValued.v.  [Top_collapse_equiv]
       reads the points' equality back as [collapse_rel] at [eq_refl].
       [collapse_family X I p i] is the point-inclusion
       [top_point X (p i) : Point_Top ~> X], and
       [collapse_family_coequalizer] proves [X ~> X/A] an elementary
       [IsWideCoequalizer] of that family, over ARBITRARY spaces mapping
       out, for EVERY family, the empty one included; the mediator is the
       competing map itself on points ([collapse_desc_map_points], at
       [eq_refl]).
     - Mac Lane's subset form.  A subset is a Type-valued predicate
       [A : X → Type], indexed by its points [collapse_sub_points X A];
       [Top_collapse_sub X A] is X/A, [collapse_sub_family X A] the
       book's "set of all the arrows sending * to one of the points
       a ∈ A", and [collapse_coequalizer], the issue's pinned name,
       Construction 5 in the elementary form, for every subset.  The
       saturated image makes a properness hypothesis on [A] unnecessary
       here.  Pairs.v's pairs carry one by a design choice, a subset of a
       setoid being taken closed under the points' equality; that file's
       header names this saturation as the alternative.
     - The colimit form, the universal-arrow reading, at this file's apex,
       [collapse_family_colimit] and [collapse_colimit], takes a member of
       the family: it is Structure/Coequalizer/Wide.v's round trip
       [is_wide_coequalizer_colimit] from the elementary record, which
       takes one, and that file's [wide_coround_trip_needs_point] proves
       the member cannot be dropped from the round trip in general.  At
       this apex it cannot be dropped either: at ⟨∅, ∅⟩ no colimit's apex
       carries an elementary wide coequalizer of the family, which this
       file's X/∅ does (Pairs.v's [empty_colimit_not_elementary]).  The
       colimit itself needs no member: for every subset closed under the
       points' equality, the empty one included, it is Pairs.v's
       [pquot_wide_coequalizer_colimit], at the apex (X ⊔ {∗})/(A ∼ ∗).
     - At the empty subset the elementary X/∅ is X ([collapse_empty_iso],
       X/∅ ≅ X, through [wide_empty_id_IsWideCoequalizer]), an
       isomorphism, refused at [eq_refl] as an equation of spaces
       (Test/ProbeCollapse459.v's N9).  So at X = ∅ an elementary wide
       coequalizer of the empty family has no point at all, whatever its
       construction ([empty_wide_coequalizer_pointless]: the identity of
       the empty space descends along every one, and would carry a point
       of it into ∅).  [collapse_empty_pointless] is only a readback of
       [Empty_Top]'s carrier for this file's X/∅; a proof closes for every
       subset of ∅.  That is where the two readings of Mac Lane's
       coequalizer part.  Read as the universal arrow, his X/∅ is X ⊔ *,
       which has a point, and Pairs.v proves that coequalizer and
       Construction 6's X/A one space for every subset closed under the
       points' equality, so Constructions 5 and 6 agree at every A.  Read
       elementarily, X/∅ is X, and the two constructions part at A = ∅.
     - Small wide coequalizers of [Top].  [wcoeq_rel] is the relation a
       family of setoid maps generates (all the pairs (f_i a, f_j a)),
       the wide analogue of Instance/Sets/Coequalizer.v's [coeq_rel];
       [WSetsCoeq] is its quotient setoid; [twcoeq_obj] is [TQuot] on it,
       built directly as Instance/Top/Cocomplete/TypeValued.v builds
       [Top_HasCoequalizers]; and [Top_HasWideCoequalizers_small] is
       [HasWideCoequalizers] for [Top] at every index universe at or
       below the points', with its object read back at [eq_refl]
       ([Top_wide_coequalizer_obj]).  Before this file the tree had no
       inhabitant of [HasWideCoequalizers] (a word grep over the tree's
       .v files found the class only in its declaring file); that file's
       header carries a CORRECTION (#459).  [collapse_iso_generic] compares
       the direct collapse with the generic wide coequalizer of its family
       by [wide_coequalizer_unique]: the isomorphism is the identity on
       points in both directions ([collapse_iso_generic_to],
       [collapse_iso_generic_from], at [eq_refl]).
     - [collapse_proj_epic], from [wide_coequalizer_epic].

   THE WALLS, pinned in Test/ProbeCollapse459.v (its N1-N6), which
   carries this file's import list; each refusal was read in a copy of
   that WHOLE file with its one guarded command unguarded, each beside a
   positive control that is accepted; a universe the message generates is
   written <1>, <2>, numbered in order of first appearance.
     W-b.  [wcoeq_rel] over an index at [Type@{h}], read as a relation at
       [Type@{o}], is refused, "universe inconsistency: Cannot enforce
       o = <1> because o < h <= <2> <= <1>": the relation's index
       universe <2> sits at or below its points' universe <1>, so an index
       at [h] drags the relation above the points.  Control: the index at
       [o].  The mechanism is of the family that the header of
       Instance/Top/Cocomplete/TypeValued.v records as its W2 (a glue
       constructor quantifying over data at [h]); the two are not claimed
       to be one wall.
     W-a.  Not a wall of its own: the bound [i <= o] in the binder of
       [Top_HasWideCoequalizers_small] is W-b's, forced by the relation
       and inferred when a binder omits it.  The glue constructor
       [wcq_glue] quantifies over the index, so under the closed
       constraint list [@{i o|}] the relation is refused, "Universe
       constraints are not implied by the ones declared: i <= o", and so
       is the inductive itself declared there, while the same inductive
       without [wcq_glue] is accepted.  Read with its index at the hom
       universe the instance is refused accordingly, "Universe
       inconsistency. Cannot enforce h <= o because o < h".  Control: the
       reading at an index [i <= o].
     W-c.  [IsWideCoequalizer] is not cumulative, and the round trip
       [is_wide_coequalizer_colimit] needs the index at the hom universe
       (Structure/Coequalizer/Wide.v's header: [u0 = u1]).  Handing it the
       record read at index [o] is refused, "universe inconsistency:
       Cannot enforce o = h because o < h".  So the index universe of
       [collapse_family_coequalizer] and [collapse_coequalizer] is a
       binder of its own, [i] with [o <= i]: read at [@{o h h}] it feeds
       the round trip (the control, and [collapse_family_colimit]), read
       at [@{o h o}] it is Mac Lane's index, the points of A.
   Neither wall blocks Construction 5, whose index is the points of A, at
   [o].

   STRENGTHS.  At [eq_refl]: [Top_collapse_equiv],
   [collapse_desc_map_points], [Top_wide_coequalizer_obj],
   [collapse_iso_generic_to], [collapse_iso_generic_from].  Up to [≈]:
   the universal properties [collapse_desc] and [twcoeq_desc] and
   everything built from them.  Two [Defined], counted by token
   ([collapse_desc], [twcoeq_desc]), and both load-bearing: each closed
   [Qed] alone in a scratch copy of this file leaves an [eq_refl]
   readback refused, [collapse_iso_generic_to] ("cannot unify
   "collapse_iso_generic X I p x" and "x"") and [collapse_iso_generic_from]
   respectively.  Of the nine [Qed], counted by token in the code, seven
   are the equivalence, respect and cofork lemmas, one is the readback
   [collapse_empty_pointless] and one the refutation
   [empty_wide_coequalizer_pointless].

   UNIVERSES, read by [About] under [Set Printing Universes] on all 54
   constants of this file's [Print Module] listing (the inductive, its
   four constructors and four generated schemes included).
     - [collapse_image], [collapse_rel], [collapse_setoid],
       [collapse_carrier], [collapse_q], [Top_collapse],
       [collapse_sub_points], [collapse_sub_incl], [Top_collapse_sub]:
       [@{o}], with no constraint beyond stdlib caps (the pair-projection
       caps [TQuot] carries); X/A is a [TopSpace@{o}], an object of the
       same [Top@{h o}] as X.
     - The maps and their universal properties ([collapse_proj],
       [collapse_family], [collapse_wcofork], [collapse_med],
       [collapse_desc], [collapse_family_colimit], [collapse_proj_epic],
       [collapse_sub_proj], [collapse_sub_family], [collapse_colimit]):
       [@{o h}] with [o < h], [Top]'s own bound, and stdlib caps.
       [collapse_family_coequalizer] and
       [collapse_coequalizer]: [@{o h i}] with [o < h] and [o <= i], at
       [IsWideCoequalizer@{i h h}]; so is
       [empty_wide_coequalizer_pointless].
     - [collapse_iso_generic] and [collapse_empty_iso]: [@{o h u}] with
       [o < h] and [h < u], where [u] is not in the statement: it is
       [wide_coequalizer_unique]'s own binder [u2], bounded in that
       lemma's block by [u0 < u2] with [u0] the hom universe.  With [u]
       dropped from the binder each body is refused ("Universe <1> ... is
       unbound"; Test/ProbeCollapse459.v's N7 and N8).
     - [wcoeq_rel], its constructors and the setoid constants over it:
       [@{i o}] with [i <= o] (the generated schemes name their own
       binders: [wcoeq_rel_rect@{u u0 u1}], [wcoeq_rel_ind@{u u0}] and
       [wcoeq_rel_sind@{u u0}] carry [u <= u0], and
       [wcoeq_rel_rec@{u u0}] has an empty block, its statement being at
       [wcoeq_rel@{u u}]); [twcoeq_obj] through
       [Top_HasWideCoequalizers_small]:
       [@{i o h}] with [i <= o] and [o < h], the instance at
       [HasWideCoequalizers@{i h h} Top@{h o}].
     - [collapse_empty_pointless@{o}] and
       [empty_wide_coequalizer_pointless] carry the file's only STRICT
       stdlib cap, [o < False_rect.u0], which is [Empty_Top]'s own (its
       About: [u < False_rect.u0]).
     - No block carries an equation.  A word count of [Set] over the
       [About] output of the 54 constants reads 1: the sort of the motive
       of the generated scheme [wcoeq_rel_rec], not a universe bound.

   NOT DELIVERED.  Wide coequalizers of [Top] indexed above the points'
   universe (walled by W-b, not refuted); an instance of
   [HasWideCoequalizers] for [Sets], though [WSetsCoeq] is the setoid
   quotient it would need; the colimit form without a member of the
   family, for a family other than the point-inclusions of a subset
   closed under the points' equality (for those it is Pairs.v's
   [pquot_wide_coequalizer_colimit]); a comparison of the wide
   coequalizer at a two-element index with
   Instance/Top/Cocomplete/TypeValued.v's binary [Top_HasCoequalizers];
   X/A as a POINTED space, which is Instance/Top/Quotient/Pairs.v's; and
   any of the homotopy theory the construction serves (cones,
   suspensions, smash products, relative homology). *)

#[local] Obligation Tactic := idtac.

(** ** Small wide coequalizers of the Type-valued [Top] *)

(* The relation a family of setoid maps generates: the wide analogue of
   Instance/Sets/Coequalizer.v's [coeq_rel]. *)
Inductive wcoeq_rel@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : B → B → Type@{o} :=
  | wcq_base  : ∀ b1 b2 : B, b1 ≈ b2 → wcoeq_rel b1 b2
  | wcq_glue  : ∀ (i j : I) (a : A), wcoeq_rel (fs i a) (fs j a)
  | wcq_sym   : ∀ b1 b2 : B, wcoeq_rel b1 b2 → wcoeq_rel b2 b1
  | wcq_trans : ∀ b1 b2 b3 : B,
      wcoeq_rel b1 b2 → wcoeq_rel b2 b3 → wcoeq_rel b1 b3.

Lemma wcoeq_rel_Equivalence@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : Equivalence (wcoeq_rel@{i o} fs).
Proof.
  constructor.
  - intro b; apply wcq_base; reflexivity.
  - intros b1 b2 H; exact (wcq_sym _ _ _ H).
  - intros b1 b2 b3 H1 H2; exact (wcq_trans _ _ _ _ H1 H2).
Qed.

(* The quotient setoid: the points of [B] under the generated relation. *)
Definition WSetsCoeq@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : SetoidObject@{o o} := {|
  carrier := carrier B;
  is_setoid := {| equiv := wcoeq_rel@{i o} fs;
                  setoid_equiv := wcoeq_rel_Equivalence@{i o} fs |}
|}.

Definition wsets_coeq_proj@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) :
  SetoidMorphism@{o o o} B (WSetsCoeq@{i o} fs) :=
  @Build_SetoidMorphism _ (is_setoid B) _ (is_setoid (WSetsCoeq@{i o} fs))
    (fun b => b) (fun b1 b2 (e : b1 ≈ b2) => wcq_base fs b1 b2 e).

(* A map absorbing the family respects the generated relation. *)
Lemma wcoeq_rel_of_cofork@{i o} {I : Type@{i}} {A B Z : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) (k : SetoidMorphism@{o o o} B Z)
  (Hk : ∀ i j a, k (fs i a) ≈ k (fs j a)) :
  ∀ b1 b2, wcoeq_rel@{i o} fs b1 b2 → k b1 ≈ k b2.
Proof.
  intros b1 b2 H; induction H.
  - apply proper_morphism; assumption.
  - apply Hk.
  - symmetry; assumption.
  - transitivity (k b2); assumption.
Qed.

Section TWide.

Universes i o h.
Constraint i <= o, o < h.

Context {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y).

Definition twcoeq_obj : TopSpace@{o} :=
  TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
    (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))).

Definition twcoeq_proj : y ~{Top@{h o}}~> twcoeq_obj := tquot_proj y _ _.

Lemma twcoeq_cofork (i j : I) : twcoeq_proj ∘ fs i ≈ twcoeq_proj ∘ fs j.
Proof. intro a; simpl. exact (wcq_glue _ i j a). Qed.

Definition twcoeq_med {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : ∀ i j : I, k ∘ fs i ≈ k ∘ fs j) :
  SetoidMorphism@{o o o} (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
    (top_carrier z) :=
  @Build_SetoidMorphism _
    (is_setoid (WSetsCoeq@{i o} (fun i => continuous_map (fs i))))
    _ (is_setoid (top_carrier z)) (continuous_map k)
    (wcoeq_rel_of_cofork@{i o} _ (continuous_map k) (fun i j a => Hk i j a)).

Definition twcoeq_desc {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : ∀ i j : I, k ∘ fs i ≈ k ∘ fs j) :
  ∃! u : twcoeq_obj ~{Top@{h o}}~> z, u ∘ twcoeq_proj ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tquot_desc y _ _ z k (twcoeq_med k Hk) (fun b => reflexivity _)).
  - intro b; reflexivity.
  - intros v Hv b. simpl. symmetry. exact (Hv b).
Defined.

Definition twcoeq_IsWideCoequalizer :
  IsWideCoequalizer (C := Top@{h o}) fs twcoeq_obj twcoeq_proj :=
  @Build_IsWideCoequalizer Top@{h o} I x y fs twcoeq_obj twcoeq_proj
    twcoeq_cofork (fun z k Hk => twcoeq_desc k Hk).

End TWide.

Definition Top_HasWideCoequalizers_small@{i o h | i <= o, o < h +} :
  HasWideCoequalizers@{i h h} Top@{h o} :=
  {| wide_coeq := fun I x y fs =>
       (twcoeq_obj@{i o h} fs; (twcoeq_proj@{i o h} fs;
          twcoeq_IsWideCoequalizer@{i o h} fs)) |}.

Example Top_wide_coequalizer_obj@{i o h | i <= o, o < h +}
  {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y) :
  `1 (@wide_coeq Top@{h o} Top_HasWideCoequalizers_small@{i o h} I x y fs)
    = TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
        (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))) := eq_refl.

(** ** Construction 5: collapsing the image of a family of points *)

(* [x] lies in the image of [p], up to the points' equality: the saturated
   image, so no properness hypothesis on the family is needed. *)
Definition collapse_image@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x : X) : Type@{o} := { i : I & p i ≈ x }.

Lemma collapse_image_respects@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (x x' : X) :
  x ≈ x' → collapse_image X I p x → collapse_image X I p x'.
Proof. intros e [i ei]. exists i. exact (transitivity ei e). Qed.

(* Two points are identified when they are equal, or when both lie in the
   image. *)
Definition collapse_rel@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x x' : X) : Type@{o} :=
  ((x ≈ x') + (collapse_image X I p x * collapse_image X I p x'))%type.

Lemma collapse_rel_Equivalence@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : Equivalence (collapse_rel X I p).
Proof.
  constructor.
  - intro x; left; reflexivity.
  - intros x y [e|[a b]].
    + left; symmetry; exact e.
    + right; exact (b, a).
  - intros x y z [e1|[a1 b1]] [e2|[a2 b2]].
    + left; transitivity y; assumption.
    + right; exact (collapse_image_respects X I p y x (symmetry e1) a2, b2).
    + right; exact (a1, collapse_image_respects X I p y z e2 b1).
    + right; exact (a1, b2).
Qed.

Definition collapse_setoid@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  Setoid@{o o} (carrier (top_carrier X)) := {|
  equiv := collapse_rel X I p;
  setoid_equiv := collapse_rel_Equivalence X I p
|}.

Definition collapse_carrier@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : SetoidObject@{o o} := {|
  carrier := carrier (top_carrier X);
  is_setoid := collapse_setoid X I p
|}.

(* The instances are named: the collapsed carrier has the same underlying
   type as [X], and resolution would otherwise pick [X]'s equality. *)
Definition collapse_q@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  SetoidMorphism@{o o o} (top_carrier X) (collapse_carrier X I p) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier X)) _ (collapse_setoid X I p)
    (fun x => x) (fun x x' (e : x ≈ x') => (inl e : collapse_rel X I p x x')).

(* X/A: the quotient topology of Instance/Top/Subspace/TypeValued.v. *)
Definition Top_collapse@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  TopSpace@{o} := TQuot X (collapse_carrier X I p) (collapse_q X I p).

(* The points of X/A are those of X, and their equality IS [collapse_rel]. *)
Example Top_collapse_equiv@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x y : X) :
  @equiv _ (is_setoid (top_carrier (Top_collapse X I p))) x y
    = collapse_rel X I p x y := eq_refl.

Definition collapse_proj@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : X ~{Top@{h o}}~> Top_collapse X I p :=
  tquot_proj X (collapse_carrier X I p) (collapse_q X I p).

(* The family of point-inclusions [* ~> X], one for each index. *)
Definition collapse_family@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (i : I) : Point_Top@{o} ~{Top@{h o}}~> X :=
  top_point@{h o} X (p i).

Lemma collapse_wcofork@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (i j : I) :
  collapse_proj X I p ∘ collapse_family X I p i
    ≈ collapse_proj X I p ∘ collapse_family X I p j.
Proof.
  intro t; simpl.
  right; split.
  - exists i. reflexivity.
  - exists j. reflexivity.
Qed.

Lemma collapse_med_proper@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  Proper (respectful (collapse_rel X I p) equiv) (continuous_map k).
Proof.
  intros x x' [e|[[i ei] [j ej]]].
  - exact (proper_morphism (continuous_map k) x x' e).
  - transitivity (continuous_map k (p i)).
    + symmetry; exact (proper_morphism (continuous_map k) _ _ ei).
    + transitivity (continuous_map k (p j)).
      * exact (Hk i j ttt).
      * exact (proper_morphism (continuous_map k) _ _ ej).
Qed.

Definition collapse_med@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  SetoidMorphism@{o o o} (collapse_carrier X I p) (top_carrier Z) :=
  @Build_SetoidMorphism _ (collapse_setoid X I p) _ (is_setoid (top_carrier Z))
    (continuous_map k) (collapse_med_proper X I p k Hk).

Definition collapse_desc_map@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  Top_collapse X I p ~{Top@{h o}}~> Z :=
  tquot_desc X (collapse_carrier X I p) (collapse_q X I p) Z k
    (collapse_med X I p k Hk) (fun x => reflexivity _).

(* The mediator is [k] itself on points, on the nose. *)
Example collapse_desc_map_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  continuous_map (collapse_desc_map X I p k Hk) = collapse_med X I p k Hk
  := eq_refl.

Definition collapse_desc@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  ∃! u : Top_collapse X I p ~{Top@{h o}}~> Z, u ∘ collapse_proj X I p ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (collapse_desc_map X I p k Hk).
  - intro x; reflexivity.
  - intros v Hv x. simpl. symmetry. exact (Hv x).
Defined.

(* X ~> X/A is an elementary wide coequalizer of the point-inclusions,
   for EVERY family, the empty one included.  The index universe [i] of
   the record is a binder of its own: the record is not cumulative, and
   the colimit round trip below reads it at the hom universe. *)
Definition collapse_family_coequalizer@{o h i | o < h, o <= i +}
  (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  @Build_IsWideCoequalizer Top@{h o} I Point_Top@{o} X (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p)
    (collapse_wcofork X I p)
    (fun Z k Hk => collapse_desc X I p k Hk).

(* The colimit form at this apex, through Structure/Coequalizer/Wide.v's
   round trip, which needs a member of the family: at the empty family
   the colimit is X ⊔ *, not X (Pairs.v's [pquot_wide_coequalizer_colimit]
   and [empty_colimit_not_elementary]). *)
Definition collapse_family_colimit@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_family X I p)) :=
  is_wide_coequalizer_colimit (collapse_family X I p) i0
    (collapse_family_coequalizer@{o h h} X I p).

(* The collapse map is epic, from the wide-coequalizer vocabulary. *)
Definition collapse_proj_epic@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) : Epic (collapse_proj X I p) :=
  wide_coequalizer_epic _ (collapse_family_coequalizer@{o h o} X I p).

(* The direct collapse and the generic small wide coequalizer of its
   family agree, and the comparison is the identity on points. *)
Definition collapse_iso_generic@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

Example collapse_iso_generic_to@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (to (collapse_iso_generic X I p)) x = x := eq_refl.

Example collapse_iso_generic_from@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (from (collapse_iso_generic X I p)) x = x := eq_refl.

(** ** Mac Lane's subset form *)

(* A subset of the points of X, as a Type-valued predicate; its points
   index the family. *)
Definition collapse_sub_points@{o} (X : TopSpace@{o}) (A : X → Type@{o}) :
  Type@{o} := { x : X & A x }.

Definition collapse_sub_incl@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (a : collapse_sub_points X A) : X := projT1 a.

(* X/A. *)
Definition Top_collapse_sub@{o} (X : TopSpace@{o}) (A : X → Type@{o}) :
  TopSpace@{o} :=
  Top_collapse X (collapse_sub_points X A) (collapse_sub_incl X A).

Definition collapse_sub_proj@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) : X ~{Top@{h o}}~> Top_collapse_sub X A :=
  collapse_proj X (collapse_sub_points X A) (collapse_sub_incl X A).

(* "the set of all the arrows sending the one point space * to one of the
   points a ∈ A" *)
Definition collapse_sub_family@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a : collapse_sub_points X A) :
  Point_Top@{o} ~{Top@{h o}}~> X :=
  collapse_family X (collapse_sub_points X A) (collapse_sub_incl X A) a.

(* Construction 5 in the elementary form: X ~> X/A is an elementary wide
   coequalizer of that family, for every subset. *)
Definition collapse_coequalizer@{o h i | o < h, o <= i +} (X : TopSpace@{o})
  (A : X → Type@{o}) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_family_coequalizer@{o h i} X (collapse_sub_points X A)
    (collapse_sub_incl X A).

Definition collapse_colimit@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a0 : collapse_sub_points X A) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_sub_family X A)) :=
  collapse_family_colimit X (collapse_sub_points X A) (collapse_sub_incl X A)
    a0.

(* In the elementary form collapsing the empty subset changes nothing:
   X/∅ ≅ X ... *)
Definition collapse_empty_iso@{o h u | o < h, h < u +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(* A readback of [Empty_Top]'s carrier: the collapse of the empty space has
   no point.  The proof reads the point as a point of [Empty_Top] and uses
   nothing about the subset or the coequalizer. *)
Lemma collapse_empty_pointless@{o} :
  top_carrier (Top_collapse_sub Empty_Top@{o} (fun _ => False)) → False.
Proof. intro z. exact z. Qed.

(* The statement about the elementary record, whatever its construction:
   no elementary wide coequalizer of the empty family at the empty space
   has a point, since the identity of the empty space descends along it.
   Every colimit of that family has one (Pairs.v's
   [collapse_colimit_point]). *)
Lemma empty_wide_coequalizer_pointless@{o h i | o < h, o <= i +}
  (Q : Top@{h o}) (e : Empty_Top@{o} ~{Top@{h o}}~> Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) Q e →
  top_carrier Q → False.
Proof.
  intros E q.
  destruct (wcoeq_desc E (@id Top@{h o} Empty_Top@{o})
              (fun a => match projT2 a with end)) as [u _ _].
  exact (continuous_map u q).
Qed.
