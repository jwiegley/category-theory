Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(** * Initiality and terminality as universal properties *)

(* Seven Sketches, Remark 6.9: the "unique up to unique isomorphism" slogan is
   not a family of ad-hoc arguments but one theorem about representable
   functors, applied to whatever universal property is at hand.  This block
   makes terminality and initiality instances of the library's generic
   packaging [IsUniversalProperty] (Structure/UniversalProperty.v), so that
   [univ_property_unique_up_to_unique_iso] applies to them literally.

   Orientation.  [IsUniversalProperty] is stated against the COVARIANT
   hom-functor `[Hom c,─] = Hom(c, −)`, so an object satisfying the predicate
   is a representing object for a covariant functor `C ⟶ Sets`.  That is the
   INITIAL shape: `c` is initial exactly when `Hom(c, −) ≅ 1`, the constant
   functor at the singleton setoid.  (Two of the three existing instances
   confirm the reading: Structure/UniversalProperty/Cartesian.v and
   Structure/UniversalProperty/Limit.v both instantiate the class at `C^op`,
   because products and limits are LIMIT-shaped.  The third,
   Structure/UniversalProperty/Universal/Arrow.v, instantiates at `D` rather
   than `D^op`, a universal arrow being colimit-shaped, so it agrees with the
   initial reading taken here.)  Terminality is therefore
   obtained here by instantiating at `C^op`, exactly as Structure/Initial.v
   defines `Initial C := Terminal (C^op)` -- only in the other direction. *)

Lemma poly_unit_uniq (u : poly_unit) : u = ttt.
Proof. now destruct u. Qed.

(* The object-level predicates [IsInitialObj] / [IsTerminalObj] now live in
   Structure/Initial.v and Structure/Terminal.v respectively, alongside the
   bundled classes they abstract; this file consumes them. *)

(* [IsUniversalProperty] demands a setoid on the predicate.  The honest choice
   is not the indiscrete relation but the pointwise comparison of the chosen
   arrows; it happens to be total ([IsInitialObj_irrelevant] below), but that
   is a theorem here, not a definition. *)
#[export]
Program Instance IsInitialObj_Setoid {C : Category} (c : C) :
  Setoid (IsInitialObj c) := {|
  equiv := fun u v => ∀ x : C, unique_obj (u x) ≈ unique_obj (v x)
|}.
Next Obligation.
  equivalence.
  now transitivity (unique_obj (y x0)).
Qed.

(* Any two proofs of initiality agree: the chosen arrows are forced. *)
Lemma IsInitialObj_irrelevant {C : Category} (c : C) (u v : IsInitialObj c) :
  u ≈ v.
Proof. intro x; symmetry; apply (uniqueness (v x)); exact I. Qed.

(* The functor being represented: the constant functor at the singleton
   setoid, i.e. the terminal object of [Sets] read as a diagram over C. *)
Program Definition ConstOne (C : Category) : C ⟶ Sets := {|
  fobj := fun _ => {| carrier := poly_unit ; is_setoid := Unit_Setoid |};
  fmap := fun _ _ _ => {| morphism := fun u => u |}
|}.

Section InitialUP.
Context (C : Category).

(* Hom(c, −) ⟹ 1: the only thing a map into the singleton can be. *)
Program Definition hom_to_one (c : C) :
  @Transform C Sets [Hom c,─] (ConstOne C) :=
  @Build_Transform' C Sets [Hom c,─] (ConstOne C)
    (fun x => {| morphism := fun _ => ttt |}) _.

(* 1 ⟹ Hom(c, −): pick out the canonical arrow `c ~> x`.  Naturality is
   precisely uniqueness -- `f ∘ !ₓ ≈ !_y` because both are arrows out of an
   initial object. *)
Program Definition one_to_hom (c : C) (u : IsInitialObj c) :
  @Transform C Sets (ConstOne C) [Hom c,─] :=
  @Build_Transform' C Sets (ConstOne C) [Hom c,─]
    (fun x => {| morphism := fun _ => unique_obj (u x) |}) _.
Next Obligation. simpl; intros; symmetry; now apply (uniqueness (u y)). Qed.

(* Initiality of `c` yields the representation Hom(c, −) ≅ 1. *)
Program Definition initial_to_repr (c : C) (u : IsInitialObj c) :
  @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C) := {|
  to   := hom_to_one c ;
  from := one_to_hom c u
|}.
Next Obligation. simpl; intros; symmetry; apply poly_unit_uniq. Qed.
Next Obligation. simpl; intros; now apply (uniqueness (u x)). Qed.

(* ... and conversely: a representation Hom(c, −) ≅ 1 makes `c` initial.  The
   arrow is the image of the point, and any competitor `v` is pinned by the
   round trip `from ∘ to ≈ id`, since `to _ v` is the point. *)
Program Definition repr_to_initial (c : C)
  (t : @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C)) : IsInitialObj c :=
  fun x => {| unique_obj := from t x ttt ; unique_property := I |}.
Next Obligation.
  assert (K := iso_from_to t x v).
  simpl in K.
  rewrite (poly_unit_uniq (to t x v)) in K.
  rewrite id_left in K; exact K.
Qed.

(* The instance.  Being initial IS representing the constant-singleton
   functor, as an isomorphism of setoids in [Sets]. *)
Definition InitialIsUniversalProperty :
  IsUniversalProperty C (@IsInitialObj C) (@IsInitialObj_Setoid C).
Proof.
  unshelve econstructor; [ exact (ConstOne C) | ].
  intro c; unshelve econstructor.
  - unshelve econstructor.
    + exact (initial_to_repr c).
    + (* both representations have the same `to`, and inverses are unique *)
      abstract (repeat intro; apply to_equiv_implies_iso_equiv;
                intros ? ?; reflexivity).
  - unshelve econstructor.
    + exact (repr_to_initial c).
    + abstract (intros t t' Heq x; exact (snd Heq x ttt)).
  - abstract (simpl; intro t; apply to_equiv_implies_iso_equiv;
              intros ? ?; symmetry; apply poly_unit_uniq).
  - abstract (simpl; intros u x; reflexivity).
Defined.

(* The payoff, and the proof that the instance is usable: the generic
   Remark-6.9 theorem [univ_property_unique_up_to_unique_iso] applied at this
   instance, with its side condition discharged by
   [IsInitialObj_irrelevant].  Two initial objects are joined by exactly one
   isomorphism -- Remark 3.85 obtained from Remark 6.9 rather than proved
   again. *)
Program Definition initial_obj_unique_up_to_unique_iso (c d : C)
  (Hc : IsInitialObj c) (Hd : IsInitialObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj := unique_obj (univ_property_unique_up_to_unique_iso
                              C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                              InitialIsUniversalProperty c d Hc Hd);
  unique_property := I
|}.
Next Obligation.
  apply (uniqueness (univ_property_unique_up_to_unique_iso
                       C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                       InitialIsUniversalProperty c d Hc Hd)).
  apply IsInitialObj_irrelevant.
Qed.

End InitialUP.

(* ---- the terminal case, by instantiation at C^op ---- *)

(* [IsTerminalObj] in C and [IsInitialObj] in C^op are the same type: the
   opposite category is defined with `hom x y := hom y x` and
   `homset x y := homset y x`, so even the [Setoid] argument of [Unique]
   matches definitionally.  Both directions are the identity function. *)
Definition IsTerminalObj_op {C : Category} (c : C) :
  IsTerminalObj c -> @IsInitialObj (C^op) c := fun u => u.

Definition op_IsTerminalObj {C : Category} (c : C) :
  @IsInitialObj (C^op) c -> IsTerminalObj c := fun u => u.

(* Terminality is a universal property: literally the initial instance,
   instantiated at the opposite category. *)
Definition TerminalIsUniversalProperty (C : Category) :
  IsUniversalProperty (C^op) (@IsInitialObj (C^op)) (@IsInitialObj_Setoid (C^op))
  := InitialIsUniversalProperty (C^op).

(* Reading an isomorphism of C^op back as an isomorphism of C.  Both round-trip
   laws are the same terms, since composition in C^op is composition in C with
   the arguments swapped.  (The other direction is [Isomorphism_Opposite] of
   Construction/Opposite.v.) *)
Program Definition iso_from_op {C : Category} {x y : C}
  (i : @Isomorphism (C^op) x y) : @Isomorphism C x y := {|
  to   := from i ;
  from := to i
|}.
Next Obligation. exact (iso_to_from i). Qed.
Next Obligation. exact (iso_from_to i). Qed.

(* The terminal corollary, routed through the instance: exactly one
   isomorphism between any two objects that are terminal.  Transporting from
   C^op is a pure relabelling -- the `to` of the C-isomorphism is the `from`
   of the C^op-isomorphism -- so uniqueness transports componentwise. *)
Program Definition terminal_obj_unique_up_to_unique_iso {C : Category} (c d : C)
  (Hc : IsTerminalObj c) (Hd : IsTerminalObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj :=
    iso_from_op (unique_obj (initial_obj_unique_up_to_unique_iso
                               (C^op) c d (IsTerminalObj_op c Hc)
                                          (IsTerminalObj_op d Hd)));
  unique_property := I
|}.
Next Obligation.
  assert (K := uniqueness (initial_obj_unique_up_to_unique_iso
                             (C^op) c d (IsTerminalObj_op c Hc)
                                        (IsTerminalObj_op d Hd))
                          (Isomorphism_Opposite v) I).
  destruct K as [K1 K2].
  split; [ exact K2 | exact K1 ].
Qed.

(* ---- the bundled structures satisfy the object-level predicates ---- *)

Program Definition Terminal_IsTerminalObj {C : Category} (T : @Terminal C) :
  IsTerminalObj (@terminal_obj C T) :=
  fun x => {| unique_obj := @one C T x ; unique_property := I |}.
Next Obligation. apply (@one_unique C T). Qed.

Program Definition Initial_IsInitialObj {C : Category} (I0 : @Initial C) :
  IsInitialObj (@initial_obj C I0) :=
  fun x => {| unique_obj := @zero C I0 x ; unique_property := I |}.
Next Obligation. apply (@zero_unique C I0). Qed.

(* Finally, Block A and Block B recovered from Block C: the SAME statements as
   [terminal_unique_up_to_unique_iso] / [initial_unique_up_to_unique_iso],
   now derived from the [IsUniversalProperty] instance instead of from
   [one_unique] / [zero_unique] directly.  This is the demonstration that the
   instance is genuinely usable at terminality and initiality. *)
Definition terminal_unique_up_to_unique_iso_via_UP {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) :=
  terminal_obj_unique_up_to_unique_iso _ _
    (Terminal_IsTerminalObj T1) (Terminal_IsTerminalObj T2).

Definition initial_unique_up_to_unique_iso_via_UP {C : Category}
  (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ≅ @initial_obj C I2 => True) :=
  initial_obj_unique_up_to_unique_iso C _ _
    (Initial_IsInitialObj I1) (Initial_IsInitialObj I2).

(** ------------------------------------------------------------------------ *)