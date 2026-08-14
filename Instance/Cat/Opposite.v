Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The op involution as a functor on Cat

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §II.2 (printed p. 33) [maclane:II.2:construction1]: sending each
    category to its opposite and each functor T to T^op is a COVARIANT
    endofunctor of the category of categories, and applying it twice
    is the identity — the duality involution on Cat.
    Riehl, "Category Theory in Context", §1.3 Example 1.3.14(vi)
    [riehl:1.3:example14].
    nLab: https://ncatlab.org/nlab/show/opposite+category

    The pieces have long been in tree — [Opposite], [Opposite_Functor],
    [Opposite_Transform], each with a definitional involution — but no
    bundled [Functor] ever had [Opposite] as its object map.  [Op]
    below is that functor, with [Op_invol : Op ◯ Op ≈ Id], and
    [Op_Strict] the [StrictCat] variant whose laws hold at strict
    functor equality.

    THE 2-CELL CAVEAT, recorded per the issue: oppositization REVERSES
    natural transformations ([Opposite_Transform] sends F ⟹ G to
    G^op ⟹ F^op), so the honest 2-categorical statement is that op is
    a 2-functor Cat^co ⟶ Cat.  The 1-categorical instance below works
    precisely because Cat's hom-equivalence consists of INVERTIBLE
    2-cells ([Functor_Setoid]'s componentwise isomorphisms): a natural
    isomorphism F ≅ G induces F^op ≅ G^op by taking each component's
    INVERSE — [fmap_respects]'s proof does exactly that — whereas a
    non-invertible transformation would come out backwards.

    THE INVOLUTION'S STRENGTH.  (C^op)^op = C holds DEFINITIONALLY at
    an abstract category — record eta makes [eq_refl] typecheck — and
    only the opaque CONSTANT [op_invol] fails to unfold.  The
    identity-on-objects functors [op_invol_to]/[op_invol_from] and the
    packaged [op_invol_iso] are therefore conveniences for downstream
    quotability, not necessities ([iso_id] alone would close
    [Op_invol]); the strict involution [Op_Strict_invol] closes with
    [eq_refl] object components outright.

    RIEHL'S EXERCISE 1.3.v rides the same collapse: the hom-setoid
    bijections (C^op ⟶ D) ≅ (C ⟶ D^op) and (C ⟶ D) ≅ (C^op ⟶ D^op)
    ([op_flip_iso], [op_conjugate_iso]) are oppositization composed
    with the double-op navigation functors, with the 2-cell reversal
    absorbed exactly as in [Op]'s respectfulness. *)

(** ** Double-opposite, navigated definitionally *)

Program Definition op_invol_to {C : Category} :
  Opposite (Opposite C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

Program Definition op_invol_from {C : Category} :
  C ⟶ Opposite (Opposite C) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

(** ** The op endofunctor of Cat *)

Program Definition Op : Cat ⟶ Cat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  (* A natural isomorphism F ≅ G yields F^op ≅ G^op with INVERSE
     components — the 2-cell reversal, tamed by invertibility: the
     coherence square is the original one read at the flipped arrow. *)
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intro C; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D E F G; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The involution *)

(* The component at C: an isomorphism of categories (in Cat's
   equivalence sense) between (C^op)^op and C, with identity round
   trips. *)
Program Definition op_invol_iso {C : Category} :
  @Isomorphism Cat (Opposite (Opposite C)) C := {|
  to := op_invol_to;
  from := op_invol_from
|}.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Theorem Op_invol : Op ◯ Op ≈ Id[Cat].
Proof.
  exists (fun C : Category => op_invol_iso).
  intros C D F; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The strict variant *)

(* The StrictCat variant: same maps, laws at strict functor
   equality. *)
Program Definition Op_Strict : StrictCat ⟶ StrictCat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  intros C D F G [e He].
  exists e.
  intros x y f; simpl.
  (* The op reading swaps which side each transport lands on; freeing
     the two arrow terms lets the object equalities collapse, after
     which the original coherence at the flipped arrow is literal. *)
  pose proof (He y x f) as K; revert K.
  generalize (fmap[G] f).
  generalize (fmap[F] f).
  destruct (e x), (e y); simpl.
  intros h g K; exact K.
Qed.
Next Obligation.
  intro C.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.
Next Obligation.
  intros C D E F G.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.

(* The strict involution, with eq_refl object components — the record
   eta of Category makes the double opposite definitional. *)
Theorem Op_Strict_invol :
  @equiv _ (@Functor_StrictEq_Setoid StrictCat StrictCat)
         (Op_Strict ◯ Op_Strict) (Id[StrictCat]).
Proof.
  exists (fun C : Category => eq_refl).
  intros C D F.
  unfold Logic.transport, Logic.transport_r; simpl.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(** ** Riehl's Exercise 1.3.v: the hom-setoid bijections *)

Program Definition op_flip_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := Opposite C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := C ⟶ Opposite D ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F ◯ op_invol_from |};
  from := {| morphism := fun G => op_invol_to ◯ Opposite_Functor G |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Program Definition op_conjugate_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := Opposite C ⟶ Opposite D
     ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F |};
  from := {| morphism := fun G =>
               op_invol_to ◯ Opposite_Functor G ◯ op_invol_from |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
