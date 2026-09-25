Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(** * Colimits of the Type-valued [Top]: what is formable, and the walls *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, book p. 134 (PDF p. 143), "Similar constructions yield
     coproducts (= disjoint unions) and general colimits in Top"
     (maclane:V.9:remark2), as in Instance/Top/Cocomplete.v's header
   nLab: https://ncatlab.org/nlab/show/Top
   nLab: https://ncatlab.org/nlab/show/quotient+space

   BACKGROUND.  Instance/Top/Cocomplete.v proves Mac Lane's Remark 2 over
   the Prop-valued [PTopCat], by the maintainer's decision of 2026-09-24
   on #458.  This file records what the tree's Type-valued [Top@{h o}]
   (Instance/Top.v) supports, whose homs sit strictly above its points
   ([o < h]) and whose opens are Type-valued predicates at [o].  Two
   constructions are formable and are built; three steps of the route
   to cocompleteness are refused, and the refusals are recorded below;
   above the points cocompleteness is refuted under informative excluded
   middle, or under decidable equality of spaces
   (Instance/Top/Cocomplete/Refutations.v's [Top_not_cocomplete_IEM] and
   [Top_not_cocomplete_ObjDecEq], Freyd's argument through an arrow index
   moved between hom universes, and [Top_not_cocomplete_Cantor_IEM] and
   [Top_not_cocomplete_Cantor_ObjDecEq], Cantor's, the last needing
   [Set < o]).  At shapes at or below the points it is left open.

   WHAT IS HERE.
     - [TSigma Ix X], the disjoint union of a family of spaces indexed by
       a type at or below the points' universe, with the final topology
       for its injections: [tsig_open] asks that a Type-valued predicate
       respect the points' equality and that its restriction to every
       summand be open ([TSigma_open], at [eq_refl]).  [tsig_inj],
       [tsig_case], [tsig_desc], and [Top_HasIndexedCoproducts_small],
       the coproducts of [Top] at those index universes.
     - [Top_HasCoequalizers]: the coequalizer of [f g : x ~> y] is
       Instance/Top/Subspace/TypeValued.v's quotient space [TQuot] on
       Instance/Sets/Coequalizer.v's [SetsCoeq] of the underlying maps
       ([Top_coequalizer_obj], at [eq_refl]); the descended map respects
       the generated relation by [coeq_rel_of_cofork].  It is built
       DIRECTLY, not by the dual of Proposition 1: over [Top] the
       quotient construction is not an adjunction record (Instance/Top/
       Subspace/TypeValued.v's header quotes the refusal, "Cannot enforce
       h = o").  So it is NOT a witness of Remark 2's sentence "this dual
       proposition and the above adjunction prove that Top has
       coequalizers"; that witness is Instance/Top/Subspace.v's
       [PTop_HasCoequalizers], over [PTopCat].

   THE WALLS, measured in a scratch file carrying the six files of #458
   after the union of their import lists (Structure/Limit/FromProducts.v
   and Structure/Complete.v among them), each refusal read in a full copy
   of that file with its one guarded command unguarded; a universe the
   message generates is written <1>, <2>, <3>.
     W1, the book's route.  [Cocomplete_from_coproducts_coequalizers]
       fed [Top_HasIndexedCoproducts_small] and [Top_HasCoequalizers] is
       refused, with the universes annotated [@{o h +| o < h +}] and with
       all of them left to inference alike: "universe inconsistency:
       Cannot enforce <1> = <2> because <1> <= <3> < <2>", where, read
       against the two types the message prints, <1> is the coproducts'
       index universe, <3> the points' and <2> the homs'.  The theorem's
       own type asks for [HasIndexedCoproducts@{u u0 u0 u2 u0}],
       coproducts indexed at the hom universe, and [TSigma]'s index sits
       at or below the points', since the sigma of the family must be a
       setoid there.  Read at an index universe [h],
       [Top_HasIndexedCoproducts_small] is refused the same way ("Cannot
       enforce <1> = h because <1> <= o < h").  Control: both ingredients
       are accepted on their own.
     W2, the direct route's relation.  Instance/Sets/Cocomplete.v's
       [colim_rel], restated for a diagram [F : D ⟶ Top@{h o}] with
       [D : Category@{s h h}] and [s <= o] as a Type-valued relation at
       [Type@{o}], is refused: "Universe inconsistency.  Cannot enforce
       h <= o because o < h".  Its glue constructor quantifies over the
       arrows of [D], which sit at [h].  Control: the same inductive at
       [Type@{h}] is accepted, and reading it as a relation at [Type@{o}]
       is refused with the same message.
     W3, a Prop-valued relation.  The same relation valued in [Prop]
       fits at [Type@{o}] (control), and the mediator into a competing
       apex respects it up to [inhabited] (control, proved by induction
       on the relation).  Eliminating it into the Type-valued [≈] of the
       apex is refused: "Incorrect elimination of "H" in the inductive
       type "tcolim_prel": the return type has sort "Type" while it
       should be SProp or Prop", and so is unwrapping the squash,
       "Incorrect elimination of "w" in the inductive type "inhabited"".
       The points of a [TopSpace] form a [SetoidObject@{o o}] with
       Type-valued [≈], and a colimit apex needs the relation itself, not
       its truth.
   Test/ProbeTopComplete458.v pins this.

   STRENGTHS.  At [eq_refl]: [TSigma_carrier], [TSigma_open] and
   [Top_coequalizer_obj].  Up to [≈]: the universal properties
   [tsig_desc] and [tcoeq_desc].  Two [Defined] ([tsig_desc],
   [tcoeq_desc]), counted by token; neither is load-bearing here (each
   closed [Qed] alone in a scratch copy of this file, which then
   compiled), and they stay transparent so that the mediators compute.

   UNIVERSES, read by [About] under [Set Printing Universes].
     - [TSigma@{o i}]: [i <= o] and stdlib caps.
       [Top_HasIndexedCoproducts_small@{o h u u0 u1} :
       HasIndexedCoproducts@{u u0 h h h} Top@{h o}]: the index universe
       [u0] with [u0 <= o], the class's own [u0 < u], and [o < u1], the
       object universe of the [Sets] in which Instance/Sets/Products.v's
       [Sets_icoprod_inj] (which [tsig_inj] consumes) types its arrow.
     - [Top_HasCoequalizers@{o h} : HasCoequalizers@{h h} Top@{h o}]:
       [o < h] and stdlib caps only.
     - No block of this file's 23 constants (its [Print Module] listing;
       it declares no obligation, record or inductive) mentions [Set],
       and none carries an equation.

   NOT DELIVERED.  Cocompleteness of [Top] at any shape universe: at or
   below the points it is open, the three walls above blocking the two
   routes tried; coproducts indexed at the hom universe (W1); the dual
   of Proposition 1 over [Top]; and any comparison of [TSigma] or of
   [Top_HasCoequalizers] with Instance/Top/Coproduct.v's binary
   [Sum_Top] or Instance/Top/Pushout.v's pushouts. *)

#[local] Obligation Tactic := idtac.

(** ** Coproducts at an index universe at or below the points *)

Section TSigma.

Universes o i.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → TopSpace@{o}).

Definition tsig_setoid : SetoidObject@{o o} :=
  Sets_icoprod_obj (fun k => top_carrier (X k)).

(* The final topology for the injections, Type-valued: a predicate is open
   when it respects the points' equality and every restriction to a
   summand is open. *)
Definition tsig_open (W : tsig_setoid → Type@{o}) : Type@{o} :=
  ((∀ p q : tsig_setoid, p ≈ q → W p → W q) ∧
   (∀ k : Ix, IsOpen (X k) (fun x => W (existT _ k x))))%type.

Lemma tsig_open_respects (U V : tsig_setoid → Type@{o}) :
  (∀ p, U p ↔ V p) → tsig_open U → tsig_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros p q e v. apply (fst (H q)), (Hp p q e), (snd (H p)), v.
  - intro k.
    exact (open_respects (X k) _ _ (fun x => H (existT _ k x)) (Ho k)).
Qed.

Lemma tsig_open_proper (U : tsig_setoid → Type@{o}) :
  tsig_open U → ∀ p q : tsig_setoid, p ≈ q → U p → U q.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma tsig_open_union (I : Type@{o}) (U : I → tsig_setoid → Type@{o}) :
  (∀ j, tsig_open (U j)) → tsig_open (fun p => { j : I & U j p }).
Proof.
  intro HU; split.
  - intros p q e [j u]; exact (j; fst (HU j) p q e u).
  - intro k. exact (open_union (X k) I (fun j x => U j (existT _ k x))
                      (fun j => snd (HU j) k)).
Qed.

Lemma tsig_open_whole : tsig_open (fun _ => poly_unit@{o}).
Proof. split; [intros; exact ttt|intro k; exact (open_whole (X k))]. Qed.

Lemma tsig_open_inter (U V : tsig_setoid → Type@{o}) :
  tsig_open U → tsig_open V → tsig_open (fun p => U p ∧ V p).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros p q e [u v]; exact (HpU p q e u, HpV p q e v).
  - intro k; exact (open_inter (X k) _ _ (HoU k) (HoV k)).
Qed.

Definition TSigma : TopSpace@{o} := {|
  top_carrier   := tsig_setoid;
  IsOpen        := tsig_open;
  open_respects := tsig_open_respects;
  open_proper   := tsig_open_proper;
  open_union    := tsig_open_union;
  open_whole    := tsig_open_whole;
  open_inter    := tsig_open_inter
|}.

Example TSigma_carrier : top_carrier TSigma = tsig_setoid := eq_refl.

Example TSigma_open (W : tsig_setoid → Type@{o}) :
  IsOpen TSigma W = tsig_open W := eq_refl.

End TSigma.

Section TSigmaUMP.

Universes o h i.
Constraint o < h.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → Top@{h o}).

Definition tsig_inj (k : Ix) : X k ~{Top@{h o}}~> TSigma Ix X :=
  Build_ContinuousMorphism (X k) (TSigma Ix X)
    (Sets_icoprod_inj (fun k => top_carrier (X k)) k)
    (fun W HW => snd HW k).

Lemma tsig_case_cont (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  Continuous (TSigma Ix X) Z
    (Sets_icoprod_case (fun k => top_carrier (X k)) (top_carrier Z)
       (fun k => continuous_map (iota k))).
Proof.
  intros W HW; split.
  - intros p q e w.
    exact (open_proper Z W HW _ _
             (proper_morphism (Sets_icoprod_case (fun k => top_carrier (X k))
                (top_carrier Z) (fun k => continuous_map (iota k))) p q e) w).
  - intro k. exact (continuity (iota k) W HW).
Qed.

Definition tsig_case (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  TSigma Ix X ~{Top@{h o}}~> Z :=
  Build_ContinuousMorphism _ _ _ (tsig_case_cont Z iota).

Definition tsig_desc (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  ∃! u : TSigma Ix X ~{Top@{h o}}~> Z, ∀ k, u ∘ tsig_inj k ≈ iota k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tsig_case Z iota).
  - intros k x; reflexivity.
  - intros v Hv [k x]; simpl. symmetry. exact (Hv k x).
Defined.

End TSigmaUMP.

(* Indexed coproducts of the Type-valued [Top], at index types at or below
   the points' universe. *)
Definition Top_HasIndexedCoproducts_small@{o h +| o < h +} :
  HasIndexedCoproducts Top@{h o} :=
  @Build_HasIndexedCoproducts Top@{h o}
    (fun A f => TSigma A f)
    (fun A f k => tsig_inj A f k)
    (fun A f => Build_IsIndexedCoproduct f _ _
                  (fun c iota => tsig_desc A f c iota)).

(** ** Coequalizers: the quotient topology on the [Sets] coequalizer *)

Section TCoeq.

Universes o h.
Constraint o < h.

Context {x y : Top@{h o}} (f g : x ~{Top@{h o}}~> y).

Definition tcoeq_obj : TopSpace@{o} :=
  TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
    (sets_coeq_proj (continuous_map f) (continuous_map g)).

Definition tcoeq_proj : y ~{Top@{h o}}~> tcoeq_obj := tquot_proj y _ _.

Lemma tcoeq_cofork : tcoeq_proj ∘ f ≈ tcoeq_proj ∘ g.
Proof. intro a; simpl. exact (cq_glue _ _ a). Qed.

(* The descended map on points: a coforking map respects the relation the
   pair generates (Instance/Sets/Coequalizer.v's [coeq_rel_of_cofork]). *)
Definition tcoeq_med {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  SetoidMorphism@{o o o} (SetsCoeq (continuous_map f) (continuous_map g))
    (top_carrier z) :=
  @Build_SetoidMorphism _
    (is_setoid (SetsCoeq (continuous_map f) (continuous_map g))) _
    (is_setoid (top_carrier z))
    (continuous_map k)
    (fun b1 b2 H =>
       coeq_rel_of_cofork (continuous_map f) (continuous_map g)
         (continuous_map k) Hk b1 b2 H).

Definition tcoeq_desc {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  ∃! u : tcoeq_obj ~{Top@{h o}}~> z, u ∘ tcoeq_proj ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tquot_desc y (SetsCoeq (continuous_map f) (continuous_map g))
      (sets_coeq_proj (continuous_map f) (continuous_map g)) z k
      (tcoeq_med k Hk) (fun b => reflexivity _)).
  - intro b; reflexivity.
  - intros v Hv b. simpl. symmetry. exact (Hv b).
Defined.

Definition tcoeq_IsCoequalizer :
  IsCoequalizer f g tcoeq_obj tcoeq_proj :=
  @Build_IsCoequalizer Top@{h o} x y f g tcoeq_obj tcoeq_proj tcoeq_cofork
    (fun z k Hk => tcoeq_desc k Hk).

End TCoeq.

Definition Top_HasCoequalizers@{o h +| o < h +} : HasCoequalizers Top@{h o} :=
  @Build_HasCoequalizers Top@{h o}
    (fun x y f g =>
       (tcoeq_obj f g; (tcoeq_proj f g; tcoeq_IsCoequalizer f g))).

(* The coequalizer IS the quotient topology on the [Sets] coequalizer of
   the underlying maps, on the nose. *)
Example Top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.
