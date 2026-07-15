Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Generalizable All Variables.

(** * Categories enriched over 2 are exactly preorders.

    Regard the walking arrow [_2] as the poset of truth values
    {TwoX < TwoY} with its cartesian monoidal structure [Two_Monoidal]
    (tensor := meet, unit := the top TwoY).  A category enriched over
    this monoidal category assigns to every pair of objects a truth
    value [ehom x y : TwoObj], read as the proposition "x ≤ y" (true
    when [ehom x y = TwoY], equivalently when there is an arrow
    [TwoY ~> ehom x y] in [_2]).

    - [eid : TwoY ~> (x ⟿ x)] forces [ehom x x = TwoY]: REFLEXIVITY.
    - [ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z)], with the tensor
      the meet, forces [ehom y z = TwoY → ehom x y = TwoY →
      ehom x z = TwoY]: TRANSITIVITY.
    - The three enrichment laws are equations between parallel arrows
      of the thin category [_2], hence hold automatically.

    Conversely a (decidable) preorder yields an enrichment by letting
    [ehom x y] be the truth value of "x ≤ y".  Enriched functors
    between such enrichments are exactly the monotone maps.

    This mirrors [Category_is_Enriched_over_Set] in
    Construction/Enriched.v, which recovers ordinary categories by
    enriching over [Sets]. *)

(* In 2, an object receiving an arrow from the top is itself the top. *)
Lemma two_from_top {z : TwoObj} : TwoHom TwoY z → z = TwoY.
Proof.
  destruct z; intro f.
  - destruct (TwoHom_Y_X_absurd f).
  - reflexivity.
Qed.

(* The bottom TwoX has an arrow into every object of 2. *)
Definition two_bot (z : TwoObj) : TwoHom TwoX z :=
  match z with
  | TwoX => TwoIdX
  | TwoY => TwoXY
  end.

(** A small, self-contained notion of (decidable) preorder.  We keep it
    local and lightweight instead of pulling in stdlib order-theoretic
    typeclasses.  The relation is [Type]-valued; decidability is part of
    the data because building the enrichment requires computing, for
    each pair of carrier elements, an object of [_2] — a truth value —
    from the relation.  Direction (a) below supplies decidability
    automatically, since equality of [TwoObj] is decidable. *)

Record TwoPreorder := {
  tpre_carrier : Type;
  tpre_le : tpre_carrier → tpre_carrier → Type;
  tpre_refl x : tpre_le x x;
  tpre_trans x y z : tpre_le y z → tpre_le x y → tpre_le x z;
  tpre_dec x y : tpre_le x y + (tpre_le x y → False)
}.

(** (a) Every category enriched over 2 gives a preorder on its objects:
    x ≤ y iff the hom truth value is the top. *)

Definition TwoPreorder_of_Enriched (E : @Enriched _2 Two_Monoidal) :
  TwoPreorder.
Proof.
  unshelve refine {|
    tpre_carrier := @eobj _ _ E;
    tpre_le x y := @ehom _ _ E x y = TwoY
  |}.
  - (* reflexivity, from eid : TwoY ~> (x ⟿ x) *)
    intro x.
    exact (two_from_top (@eid _ _ E x)).
  - (* transitivity, from ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z) *)
    intros x y z Hyz Hxy.
    apply two_from_top.
    pose proof (@ecompose _ _ E x y z) as f.
    simpl in f.
    rewrite Hyz, Hxy in f.
    exact f.
  - (* decidability, since TwoObj has decidable equality *)
    intros x y.
    destruct (@ehom _ _ E x y).
    + right; intro H; discriminate H.
    + left; reflexivity.
Defined.

(** (b) Every preorder gives a category enriched over 2, with hom
    truth values computed by the decision procedure. *)

Definition ehom_of_le (P : TwoPreorder) (x y : tpre_carrier P) : TwoObj :=
  match tpre_dec P x y with
  | Datatypes.inl _ => TwoY
  | Datatypes.inr _ => TwoX
  end.

Lemma ehom_of_le_complete {P : TwoPreorder} {x y : tpre_carrier P} :
  tpre_le P x y → ehom_of_le P x y = TwoY.
Proof.
  intro l; unfold ehom_of_le.
  destruct (tpre_dec P x y) as [_|n].
  - reflexivity.
  - destruct (n l).
Qed.

Lemma ehom_of_le_sound {P : TwoPreorder} {x y : tpre_carrier P} :
  TwoHom TwoY (ehom_of_le P x y) → tpre_le P x y.
Proof.
  unfold ehom_of_le.
  destruct (tpre_dec P x y) as [l|n]; intro f.
  - exact l.
  - destruct (TwoHom_Y_X_absurd f).
Qed.

Lemma ehom_of_le_empty {P : TwoPreorder} {x y : tpre_carrier P} :
  (tpre_le P x y → False) → ehom_of_le P x y = TwoX.
Proof.
  intro n; unfold ehom_of_le.
  destruct (tpre_dec P x y) as [l|_].
  - destruct (n l).
  - reflexivity.
Qed.

Definition Enriched_of_TwoPreorder (P : TwoPreorder) :
  @Enriched _2 Two_Monoidal.
Proof.
  unshelve refine
    (@Build_Enriched _2 Two_Monoidal
       (tpre_carrier P) (ehom_of_le P) _ _ _ _ _).
  - (* eid : TwoY ~> (x ⟿ x), from reflexivity *)
    intro x.
    rewrite (ehom_of_le_complete (tpre_refl P x)).
    exact TwoIdY.
  - (* ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z), from transitivity;
       when either factor is the bottom, so is the meet, and the bottom
       maps into everything *)
    intros x y z; simpl.
    destruct (tpre_dec P y z) as [lyz|nyz];
    destruct (tpre_dec P x y) as [lxy|nxy].
    + rewrite (ehom_of_le_complete lyz), (ehom_of_le_complete lxy),
        (ehom_of_le_complete (tpre_trans P x y z lyz lxy)).
      exact TwoIdY.
    + rewrite (ehom_of_le_empty nxy), (ehom_of_le_complete lyz).
      exact (two_bot _).
    + rewrite (ehom_of_le_empty nyz).
      exact (two_bot _).
    + rewrite (ehom_of_le_empty nyz).
      exact (two_bot _).
  - (* the three coherence laws hold by thinness of 2 *)
    intros; apply two_thin.
  - intros; apply two_thin.
  - intros; apply two_thin.
Defined.

(** The promised correspondence: enrichments over 2 on one side,
    preorders on the other, with maps in both directions. *)

Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder.
Proof.
  split.
  - exact TwoPreorder_of_Enriched.
  - exact Enriched_of_TwoPreorder.
Defined.

(** The morphism leg: enriched functors between the enrichments built
    from preorders are exactly the monotone maps. *)

Record MonotoneMap (P Q : TwoPreorder) := {
  mono_map : tpre_carrier P → tpre_carrier Q;
  mono_le x y : tpre_le P x y → tpre_le Q (mono_map x) (mono_map y)
}.

Arguments mono_map {P Q}.
Arguments mono_le {P Q}.

Theorem EnrichedFunctor_Two_monotone (P Q : TwoPreorder) :
  EnrichedFunctor _2
    (snd Enriched_Two_preorder P)
    (snd Enriched_Two_preorder Q)
    ↔ MonotoneMap P Q.
Proof.
  split; intro X.
  - (* an enriched functor is monotone: efmap at (x, y) is an arrow
       between the corresponding truth values *)
    destruct X as [f fm _ _]; simpl in *.
    unshelve refine {| mono_map := f |}.
    intros x y l.
    apply ehom_of_le_sound.
    specialize (fm x y).
    rewrite (ehom_of_le_complete l) in fm.
    exact fm.
  - (* a monotone map is an enriched functor *)
    unshelve refine
      (@Build_EnrichedFunctor _2 Two_Monoidal
         (Enriched_of_TwoPreorder P) (Enriched_of_TwoPreorder Q)
         (mono_map X) _ _ _).
    + (* efmap, by cases on whether x ≤ y holds in P *)
      intros x y; simpl.
      destruct (tpre_dec P x y) as [l|n].
      * rewrite (ehom_of_le_complete l),
          (ehom_of_le_complete (mono_le X x y l)).
        exact TwoIdY.
      * rewrite (ehom_of_le_empty n).
        exact (two_bot _).
    + (* preservation of eid and ecompose hold by thinness of 2 *)
      intros; apply two_thin.
    + intros; apply two_thin.
Defined.
