Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * Fibrations *)

(* nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   nLab:      https://ncatlab.org/nlab/show/cartesian+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
              Categories", Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   Fibrations in both presentations, with the bridge between them.

   Displayed presentation (over the primitive of Theory/Displayed.v): a
   displayed morphism [ff : dhom dx dy f] is cartesian ([DCartesian]) when
   every displayed morphism over a composite [f ∘ g] factors uniquely
   through [ff] by a displayed morphism over [g].  A cleaving ([Cleaving])
   chooses, for every base morphism [f : x ~> y] and displayed object [dy]
   over its codomain, an object [dx] over [x] and a cartesian morphism
   [dx ~> dy] over [f].  No object is ever compared for equality here: the
   fibre placement of the lift is carried by the index [x] itself.

   Functor presentation (the classical one): for [P : E ⟶ C], a morphism
   [φ : e ~> e'] of [E] is cartesian ([CartesianMorphism]) when for every
   [ψ : e'' ~> e'], every explicit base-morphism witness [g : P e'' ~> P e],
   and every equation [fmap[P] ψ ≈ fmap[P] φ ∘ g] exhibiting [fmap[P] ψ] as
   factoring through [fmap[P] φ], there is a unique [χ : e'' ~> e] lying
   over [g] — meaning [fmap[P] χ ≈ g] — with [φ ∘ χ ≈ ψ].  Because homs in
   this library are setoids, the classical equations [P ψ = P φ ∘ g] and
   [P χ = g] are stated with [≈]; carrying the witness [g] and the
   factorization equation explicitly is the ≈-honest reading of the
   universal property (the displayed side realises the same reading with
   [dtransport] doing the carrying).

   A cloven fibration ([ClovenFibration]) equips [P] with a chosen
   cartesian lift ([CartesianLift]) of every [f : x ~> P e'].  Here — and
   only here — the fibre placement is strict: the chosen [lift_obj]
   satisfies a propositional object equality [P lift_obj = x], consumed
   through the induced isomorphism [iso_of_eq] of
   Instance/StrictCat/ToCat.v.  Plain [=] on objects is deliberate and
   sanctioned at this single interface: it anchors each chosen lift in an
   honest fibre over [x], which is what the split theory below and the
   round trip with indexed categories
   (Construction/Grothendieck/RoundTrip.v) consume.  A cleavage is split
   ([SplitCleaving]) when the chosen lifts are functorial on the nose: the
   lift of an identity is an identity and the lift of a composite is the
   composite of the lifts, both stated across the strict anchoring's
   transports.

   Bridge: a [Cleaving] on a displayed category [D] makes the projection
   [Total_Proj D : Total D ⟶ C] a cloven fibration
   ([cleaving_total_cloven]); the anchoring is [eq_refl], because the lift
   object is literally the pair [(x; dx)] whose first component is [x].

   Opfibrations arise by duality: [Displayed_op] re-reads a displayed
   category over [C] as one over [C^op] — a displayed morphism from [dx]
   to [dy] over [f : x ~{C^op}~> y] is a displayed morphism from [dy] to
   [dx] over the underlying arrow of [C] — and an opcleaving of [D] is a
   cleaving of the op-displayed category ([OpCleaving]). *)

(** ** Cartesian morphisms and cleavings, displayed presentation *)

(* [ff] is cartesian over its base morphism [f] when every displayed
   morphism over a composite [f ∘ g] factors through [ff] by a unique
   displayed morphism over [g]. *)
Class DCartesian {C : Category} {D : Displayed C} {x y : C} {f : x ~> y}
      {dx : dobj x} {dy : dobj y} (ff : dhom dx dy f) := {
  dcart_factor {z : C} {g : z ~> x} {dz : dobj z}
    (hh : dhom dz dy (f ∘ g)) :
    ∃! gg : dhom dz dx g, dcomp ff gg ≈ hh
}.

(* A cleaving: chosen cartesian lifts.  Given [f : x ~> y] and [dy] over
   the codomain, it selects an object over [x] together with a cartesian
   morphism over [f] into [dy]. *)
Class Cleaving {C : Category} (D : Displayed C) := {
  clift {x y : C} (f : x ~> y) (dy : dobj y) :
    { dx : dobj x & { ff : dhom dx dy f & DCartesian ff } }
}.

(** ** Cartesian morphisms and cloven fibrations, functor presentation *)

(* The ≈-honest universal property: the factorization of [fmap[P] ψ]
   through [fmap[P] φ] is carried by an explicit base-morphism witness [g]
   and an explicit equation, and the mediating lift is unique among
   morphisms lying over [g] up to [≈]. *)
Class CartesianMorphism {C E : Category} (P : E ⟶ C)
      {e e' : E} (φ : e ~> e') := {
  cart_factor {e'' : E} (ψ : e'' ~> e') (g : P e'' ~> P e)
    (factors : fmap[P] ψ ≈ fmap[P] φ ∘ g) :
    ∃! χ : e'' ~> e, (φ ∘ χ ≈ ψ) ∧ (fmap[P] χ ≈ g)
}.

(* A chosen cartesian lift of [f : x ~> P e'].  The lift object is
   anchored in the fibre over [x] STRICTLY, by a propositional object
   equality [P lift_obj = x] (sanctioned here; see the header), and the
   lift lies over [f] up to the isomorphism induced by that equality. *)
Record CartesianLift {C E : Category} (P : E ⟶ C) {x : C} {e' : E}
       (f : x ~> P e') := {
  lift_obj : E;
  lift_anchor : P lift_obj = x;         (* strict fibre anchoring *)
  lift_mor : lift_obj ~> e';
  lift_cartesian : CartesianMorphism P lift_mor;
  lift_over : fmap[P] lift_mor ≈ f ∘ to (iso_of_eq lift_anchor)
}.

Arguments lift_obj {C E P x e' f} _.
Arguments lift_anchor {C E P x e' f} _.
Arguments lift_mor {C E P x e' f} _.
Arguments lift_cartesian {C E P x e' f} _.
Arguments lift_over {C E P x e' f} _.

(* A cloven fibration: a chosen cartesian lift for every [f : x ~> P e']. *)
Class ClovenFibration {C E : Category} (P : E ⟶ C) := {
  cloven_lift {x : C} {e' : E} (f : x ~> P e') : CartesianLift P f
}.

(* A split cleavage: the chosen lifts are functorial on the nose.  Both
   laws live across the strict anchoring's transports, via [iso_of_eq]:

   - the lift of [id[P e']] has lift object equal to [e'] itself, and its
     lift morphism is the corresponding transport isomorphism (an identity
     seen across the object equality [q]);

   - the composite [f ∘ g] is lifted, up to the object equality [q] of the
     two chosen lift objects, by the composite of the lift of [f] with the
     lift of [g] — where [g : y ~> x] is first carried into the fibre over
     [x] along the anchoring of the lift of [f], so that it can be lifted
     with codomain [lift_obj (cloven_lift f)]. *)
Class SplitCleaving {C E : Category} (P : E ⟶ C)
      `{H : @ClovenFibration C E P} := {
  split_lift_id {e' : E} :
    { q : lift_obj (cloven_lift (id[P e'])) = e'
    & lift_mor (cloven_lift (id[P e'])) ≈ to (iso_of_eq q) };

  split_lift_comp {x y : C} {e' : E} (f : x ~> P e') (g : y ~> x) :
    { q : lift_obj (cloven_lift (f ∘ g))
        = lift_obj (cloven_lift
            (from (iso_of_eq (lift_anchor (cloven_lift f))) ∘ g))
    & lift_mor (cloven_lift (f ∘ g))
        ≈ lift_mor (cloven_lift f)
            ∘ lift_mor (cloven_lift
                (from (iso_of_eq (lift_anchor (cloven_lift f))) ∘ g))
            ∘ to (iso_of_eq q) }
}.

(** ** Bridge: a cleaving makes the total projection a cloven fibration *)

(* A displayed-cartesian morphism is cartesian for the projection functor:
   the base factorization is transported into a displayed morphism over
   the composite, which then factors uniquely through [ff]. *)
Lemma total_cartesian {C : Category} {D : Displayed C}
  {t t' : Total D} (φ : t ~> t') (Hφ : DCartesian (`2 φ)) :
  CartesianMorphism (Total_Proj D) φ.
Proof.
  constructor; intros e'' ψ g Hbase; simpl in *.
  destruct (@dcart_factor _ _ _ _ _ _ _ _ Hφ _ g _
              (dtransport Hbase (`2 ψ))) as [gg Hcomm Huniq].
  unshelve refine {| unique_obj := ((g; gg) : e'' ~{ Total D }~> t) |}.
  - split.
    + (* the mediating lift commutes: φ ∘ (g; gg) ≈ ψ *)
      exists (symmetry Hbase); simpl.
      rewrite Hcomm.
      apply dtransport_symm_l.
    + (* and it lies over g *)
      simpl.
      reflexivity.
  - (* uniqueness among lifts over g *)
    intros [v vv] [[e1 He1] Hv2]; simpl in *.
    exists (symmetry Hv2).
    assert (Hu : gg ≈ dtransport Hv2 vv).
    { apply Huniq.
      rewrite (dtransport_comp_r Hv2
                 (compose_respects _ _ (Equivalence_Reflexive _) _ _ Hv2)
                 (`2 φ) vv).
      apply (fst (dtransport_flip _ _ _)) in He1.
      rewrite He1.
      apply dtransport_trans_any. }
    rewrite Hu.
    apply dtransport_symm_l.
Defined.

#[local] Obligation Tactic := program_simpl.

(* The bridge: chosen displayed lifts become chosen functor-level lifts of
   the projection.  The lift of [f : x ~> `1 e'] at [e'] is the pair
   [(x; dx)] over the cleaving's chosen [dx], so the strict anchoring is
   [eq_refl] and its transport isomorphism is an identity. *)
Program Definition cleaving_total_cloven {C : Category} {D : Displayed C}
        `{H : @Cleaving C D} : ClovenFibration (Total_Proj D) := {|
  cloven_lift := fun x e' f =>
    {| lift_obj := (x; `1 (clift f (`2 e')));
       lift_anchor := eq_refl;
       lift_mor := (f; `1 (`2 (clift f (`2 e'))));
       lift_cartesian := @total_cartesian C D (x; `1 (clift f (`2 e'))) e'
                           (f; `1 (`2 (clift f (`2 e'))))
                           (`2 (`2 (clift f (`2 e')))) |}
|}.
Next Obligation.
  (* the chosen lift lies over f: the anchoring is [eq_refl], whose
     induced isomorphism is an identity *)
  now rewrite id_right.
Qed.

(** ** Opfibrations, by duality *)

#[local] Obligation Tactic := idtac.

(* The op-displayed category: same displayed objects; a displayed morphism
   from [dx] to [dy] over [f : x ~{C^op}~> y] is a displayed morphism from
   [dy] to [dx] over the underlying arrow [f : y ~{C}~> x].  Transport is
   unchanged (an op-hom setoid IS the underlying hom setoid), and displayed
   composition flips its arguments, mirroring [Construction/Opposite.v]. *)
Program Definition Displayed_op {C : Category} (D : Displayed C) :
  Displayed (C^op) := {|
  dobj := @dobj C D;
  dhom := fun x y dx dy f => @dhom C D y x dy dx f;
  dhomset := fun x y dx dy f => @dhomset C D y x dy dx f;
  dtransport := fun x y dx dy f g e => @dtransport C D y x dy dx f g e;
  did := fun x dx => @did C D x dx;
  dcomp := fun x y z dx dy dz f g ff gg => @dcomp C D z y x dz dy dx g f gg ff
|}.
(* [dtransport_respects] is resolved during elaboration by the registered
   instance of the underlying displayed category, so it generates no
   obligation; the remaining laws follow in field order. *)
Next Obligation. (* dtransport_id *)
  intros C D x y dx dy f e ff.
  exact (@dtransport_id C D y x dy dx f e ff).
Qed.
Next Obligation. (* dtransport_trans: any proof of the endpoints works *)
  intros C D x y dx dy f g h e1 e2 ff; simpl.
  apply dtransport_trans_any.
Qed.
Next Obligation. (* dcomp_respects: the underlying respectfulness, flipped *)
  intros C D x y z dx dy dz f g ff ff' Hff gg gg' Hgg.
  exact (@dcomp_respects C D z y x dz dy dx g f gg gg' Hgg ff ff' Hff).
Qed.
Next Obligation. (* dtransport_comp_l is the underlying dtransport_comp_r *)
  intros C D x y z dx dy dz f f' g e e' ff gg.
  exact (@dtransport_comp_r C D z y x dz dy dx g f f' e e' gg ff).
Qed.
Next Obligation. (* dtransport_comp_r is the underlying dtransport_comp_l *)
  intros C D x y z dx dy dz f g g' e e' ff gg.
  exact (@dtransport_comp_l C D z y x dz dy dx g g' f e e' gg ff).
Qed.
Next Obligation. (* did_left is the underlying did_right *)
  intros C D x y dx dy f ff.
  exact (@did_right C D y x dy dx f ff).
Qed.
Next Obligation. (* did_right is the underlying did_left *)
  intros C D x y dx dy f ff.
  exact (@did_left C D y x dy dx f ff).
Qed.
Next Obligation. (* dcomp_assoc: the underlying associator, reoriented *)
  intros C D w x y z dw dx dy dz f g h ff gg hh; simpl.
  symmetry.
  apply dtransport_dcomp_assoc.
Qed.

(* An opcleaving of [D] — chosen opcartesian lifts, pushing displayed
   objects forward along base morphisms — is a cleaving of the
   op-displayed category. *)
Definition OpCleaving {C : Category} (D : Displayed C) : Type :=
  Cleaving (Displayed_op D).
