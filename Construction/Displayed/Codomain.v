Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Structure.Pullback.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The codomain displayed category *)

(* nLab:      https://ncatlab.org/nlab/show/codomain+fibration
   nLab:      https://ncatlab.org/nlab/show/displayed+category
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

   The codomain displayed category of [C] displays over each object [x : C]
   the maps INTO [x]: an object over [x] is a pair [(d; p)] of an object
   [d : C] and a morphism [p : d ~> x].  A displayed morphism from [(d; p)]
   over [x] to [(d'; p')] over [y], lying over a base morphism [f : x ~> y],
   is a morphism [u : d ~> d'] making the square

       d  --u-->  d'
       |          |
      p|          | p'        commute, i.e.  p' ∘ u ≈ f ∘ p,
       v          v
       x  --f-->  y

   and two displayed morphisms over [f] are equivalent when their underlying
   morphisms [u] are ≈ — the square proof is irrelevant.  Transport along a
   base proof [e : f ≈ g] leaves the morphism [u] untouched and merely
   rewrites the square along [e], so the transport laws ([dtransport_id],
   [dtransport_trans], and the interchange fields) are reflexivity-shaped.

   Fibres and total category.  The fibre of this displayed category over [x]
   has as objects the maps into [x] — the encoding [∃ d, d ~> x] is
   literally the object encoding of the slice category of
   Construction/Slice.v — and as morphisms over [id[x]] the commuting
   triangles over [x], which are the slice's morphisms.  The total category
   (Construction/Displayed/Total.v) has as objects ALL maps of [C] and as
   morphisms all commuting squares: it is the displayed rendering of the
   arrow category.  The comparison with the comma presentation
   [C ⃗ = (Id[C] ↓ Id[C])] of Construction/Arrow.v is delivered below as the
   mutually inverse functors [Codomain_Total_to_Arrow] and
   [Arrow_to_Codomain_Total], packaged as an isomorphism
   [Codomain_Total_Arrow_iso] in Cat.

   The payoff is the classical characterization of the codomain FIBRATION:
   the codomain displayed category has a cleaving exactly when [C] has all
   pullbacks.  [codomain_cleaving] builds the cartesian lift of [f : x ~> y]
   at [(d; p)] from the chosen pullback of [p] along [f], and
   [codomain_cleaving_pullbacks] conversely reads the pullback of a cospan
   [f : x ~> z], [g : y ~> z] off the cartesian lift of [f] at [(y; g)]; in
   both directions the universal properties are exchanged by turning a
   competing pullback cone into a displayed morphism over a composite. *)

#[local] Obligation Tactic := idtac.

Program Definition Codomain_Displayed (C : Category) : Displayed C := {|
  dobj := fun x => ∃ d : C, d ~> x;
  dhom := fun x y dx dy f => ∃ u : `1 dx ~> `1 dy, `2 dy ∘ u ≈ f ∘ `2 dx;
  dhomset := fun x y dx dy f => {| equiv := fun u v => `1 u ≈ `1 v |};
  dtransport := fun x y dx dy f g e ff => (`1 ff; _);
  did := fun x dx => (id; _);
  dcomp := fun x y z dx dy dz f g ff gg => (`1 ff ∘ `1 gg; _)
|}.
Next Obligation.
  (* the displayed hom-setoid compares underlying morphisms *)
  intros C x y dx dy f.
  equivalence.
Qed.
Next Obligation.
  (* transport keeps the morphism and rewrites its square along e *)
  intros C x y dx dy f g e ff; simpl.
  rewrite (`2 ff).
  now rewrite e.
Qed.
Next Obligation.
  (* dtransport_respects: transport is the identity on the morphism *)
  intros C x y dx dy f g e; repeat intro; simpl in *.
  assumption.
Qed.
Next Obligation.
  (* dtransport_id: transport along a loop is the identity *)
  intros C x y dx dy f e ff; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* dtransport_trans: two transports fuse, on the nose *)
  intros C x y dx dy f g h e1 e2 ff; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* the identity square over id *)
  intros C x dx; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  (* squares over f and g paste to a square over f ∘ g *)
  intros C x y z dx dy dz f g ff gg; simpl.
  rewrite comp_assoc.
  rewrite (`2 ff).
  rewrite <- (comp_assoc f (`2 dy) (`1 gg)).
  rewrite (`2 gg).
  apply comp_assoc.
Qed.
Next Obligation.
  (* dcomp_respects: composition of underlying morphisms respects ≈ *)
  intros C x y z dx dy dz f g ff ff' Hff gg gg' Hgg; simpl in *.
  now rewrite Hff, Hgg.
Qed.
Next Obligation.
  (* dtransport_comp_l: transport is invisible to the morphism data *)
  intros C x y z dx dy dz f f' g e e' ff gg; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* dtransport_comp_r: likewise on the right *)
  intros C x y z dx dy dz f g g' e e' ff gg; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* did_left: the base law on underlying morphisms *)
  intros C x y dx dy f ff; simpl.
  apply id_left.
Qed.
Next Obligation.
  (* did_right *)
  intros C x y dx dy f ff; simpl.
  apply id_right.
Qed.
Next Obligation.
  (* dcomp_assoc *)
  intros C w x y z dw dx dy dz f g h ff gg hh; simpl.
  apply comp_assoc.
Qed.

(** ** Cartesian lifts from pullbacks *)

(* The cartesian lift of [f : x ~> y] at [(d; p)] is the chosen pullback of
   [p] along [f]:

       x ×_y d --snd--> d
          |             |
       fst|             | p
          v             v
          x  ----f----> y

   The pullback apex with its first projection is the lift object over [x],
   and the second projection is the lift morphism over [f]; its square is
   the pullback square read backwards.  Cartesianness is exactly the
   pullback's universal property: a displayed morphism over [f ∘ g] from
   [(e; q)] is a morphism [h] with [p ∘ h ≈ (f ∘ g) ∘ q], i.e. a competing
   cone [(g ∘ q, h)] over the cospan, and the mediating morphism into the
   apex is the unique displayed factorization over [g]. *)

Section CodomainCleaving.

Context {C : Category}.

Definition codomain_lift_obj {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  @dobj C (Codomain_Displayed C) x :=
  (Pull f (`2 dy) P; pullback_fst f (`2 dy) P).

Definition codomain_lift_mor {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  @dhom C (Codomain_Displayed C) x y (codomain_lift_obj f dy P) dy f :=
  (pullback_snd f (`2 dy) P; symmetry (pullback_commutes f (`2 dy) P)).

Lemma codomain_lift_cartesian {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  DCartesian (codomain_lift_mor f dy P).
Proof.
  constructor; intros z g dz hh.
  (* [hh] is a square over [f ∘ g]: its underlying morphism [`1 hh]
     satisfies [`2 dy ∘ `1 hh ≈ (f ∘ g) ∘ `2 dz], so [(g ∘ `2 dz, `1 hh)]
     is a competing cone over the pullback's cospan. *)
  assert (Hcone : f ∘ (g ∘ `2 dz) ≈ `2 dy ∘ `1 hh).
  { rewrite (`2 hh).
    apply comp_assoc. }
  pose proof (ump_pullbacks f (`2 dy) P (`1 dz) (g ∘ `2 dz) (`1 hh) Hcone)
    as U.
  destruct (unique_property U) as [Ufst Usnd].
  unshelve refine {| unique_obj := (unique_obj U; Ufst) |}.
  - (* the mediator composes with the lift to give back [hh] *)
    simpl.
    exact Usnd.
  - (* and is the only displayed morphism over [g] that does so *)
    intros v Hv; simpl in Hv.
    apply (uniqueness U); split.
    + exact (`2 v).
    + exact Hv.
Defined.

(* The (⇐) direction of the payoff: pullbacks induce a cleaving of the
   codomain displayed category. *)
Definition codomain_cleaving `{H : @HasPullbacks C} :
  Cleaving (Codomain_Displayed C) := {|
  clift := fun x y f dy =>
    (codomain_lift_obj f dy (pullback f (`2 dy));
     (codomain_lift_mor f dy (pullback f (`2 dy));
      codomain_lift_cartesian f dy (pullback f (`2 dy))))
|}.

(** ** Pullbacks from cartesian lifts *)

(* The (⇒) direction: a cleaving of the codomain displayed category yields
   all pullbacks.  To pull [g : y ~> z] back along [f : x ~> z], regard [g]
   as the displayed object [(y; g)] over [z] and take the chosen cartesian
   lift of [f] at it: the lift object [(P; p1)] over [x] and the lift
   morphism [u] over [f] assemble into the square

          P  ---u--->  y
          |            |
        p1|            | g
          v            v
          x  ---f--->  z .

   For its universal property, a competing cone [(q1, q2)] from [Q] is
   exactly a displayed morphism [(q2; _)] over the composite [f ∘ q1] from
   the displayed object [(Q; id)] — the identity anchors [Q] over itself —
   and [dcart_factor] provides the unique displayed factorization over
   [q1], whose underlying morphism is the mediator. *)

Definition codomain_cleaving_pullbacks
  `{H : @Cleaving C (Codomain_Displayed C)} : HasPullbacks C.
Proof.
  constructor; intros x y z f g.
  destruct (@clift C (Codomain_Displayed C) H x z f (y; g))
    as [dx [ff cart]].
  destruct dx as [P p1].
  destruct ff as [u sq].
  (* sq : g ∘ u ≈ f ∘ p1 — the lift's square is the pullback square *)
  unshelve refine {| Pull := P; pullback_fst := p1; pullback_snd := u |}.
  - (* the square commutes *)
    exact (symmetry sq).
  - (* universal property *)
    intros Q q1 q2 Hq.
    (* the competing square becomes a displayed morphism over [f ∘ q1] *)
    assert (sqh : g ∘ q2 ≈ (f ∘ q1) ∘ id).
    { rewrite id_right.
      symmetry.
      exact Hq. }
    destruct (@dcart_factor C (Codomain_Displayed C) x z f (P; p1) (y; g)
                (u; sq) cart Q q1
                (existT (fun d : C => d ~{ C }~> Q) Q id) (q2; sqh))
      as [w Hw Huniq].
    simpl in Hw.
    unshelve refine {| unique_obj := `1 w |}.
    + split.
      * (* p1 ∘ w ≈ q1: the factorization's own square, sans the id *)
        rewrite <- (id_right q1).
        exact (`2 w).
      * (* u ∘ w ≈ q2: the factorization equation *)
        exact Hw.
    + (* uniqueness: a competing mediator is itself a displayed
         factorization over [q1], so [dcart_factor]'s uniqueness applies *)
      intros v [Hv1 Hv2].
      assert (sqv : p1 ∘ v ≈ q1 ∘ id).
      { rewrite id_right.
        exact Hv1. }
      exact (Huniq (v; sqv) Hv2).
Defined.

End CodomainCleaving.

(** ** Comparison with the comma-based arrow category *)

(* The total category of the codomain displayed category has as objects the
   pairs [(x; (d; p : d ~> x))] — the maps of [C] — and as morphisms the
   pairs [(f; (u; _))] of a base morphism and a square over it.  Reshuffling
   the components yields exactly an object [((d, x); p)] and a morphism
   [((u, f); _)] of the comma category [C ⃗ = (Id[C] ↓ Id[C])] of
   Construction/Arrow.v, with the very same commuting square; and both
   equivalences compare the same two components.  The two reshufflings are
   functorial and mutually inverse on the nose, giving an isomorphism (not
   merely an equivalence) in Cat. *)

#[local] Obligation Tactic := program_simpl.

Program Definition Codomain_Total_to_Arrow {C : Category} :
  Total (Codomain_Displayed C) ⟶ @Arrow C := {|
  fobj := fun x => ((`1 (`2 x), `1 x); `2 (`2 x));
  fmap := fun x y f => ((`1 (`2 f), `1 f); `2 (`2 f))
|}.
Next Obligation.
  (* respects ≈: both sides compare the square's leg and the base *)
  intros f g [e He]; split.
  - exact He.
  - exact e.
Qed.
Next Obligation.
  (* preserves identities, componentwise on the nose *)
  split; reflexivity.
Qed.
Next Obligation.
  (* preserves composition, componentwise on the nose *)
  split; reflexivity.
Qed.

Program Definition Arrow_to_Codomain_Total {C : Category} :
  @Arrow C ⟶ Total (Codomain_Displayed C) := {|
  fobj := fun x => (snd (`1 x); (fst (`1 x); `2 x));
  fmap := fun x y f => (snd (`1 f); (fst (`1 f); `2 f))
|}.
Next Obligation.
  (* respects ≈, with the reflexivity proof carrying the transport *)
  intros f g [e1 e2].
  exists e2; simpl.
  exact e1.
Qed.
Next Obligation.
  (* preserves identities *)
  exists (Equivalence_Reflexive _); simpl.
  reflexivity.
Qed.
Next Obligation.
  (* preserves composition *)
  exists (Equivalence_Reflexive _); simpl.
  reflexivity.
Qed.

Program Definition Codomain_Total_Arrow_iso {C : Category} :
  Total (Codomain_Displayed C) ≅[Cat] @Arrow C := {|
  to := Codomain_Total_to_Arrow;
  from := Arrow_to_Codomain_Total
|}.
Next Obligation.
  (* to ∘ from ≈ id on the arrow category *)
  constructive; simplify; simpl in *; cat.
Qed.
Next Obligation.
  (* from ∘ to ≈ id on the total category *)
  constructive; simplify; simpl in *; cat.
Qed.
