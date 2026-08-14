Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Sheaf.
Require Import Category.Functor.Hom.Yoneda.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Representably isomorphic objects

    Riehl, "Category Theory in Context", 2nd ed., §2.3 (printed p. 67):
    the opening definition — two objects are REPRESENTABLY ISOMORPHIC
    when their represented functors are naturally isomorphic, in either
    variance — and Proposition 2.3.1
    [riehl:2.3:def-representable-isomorphism, riehl:2.3:prop1]: the
    three kinds of data
      (i)   an isomorphism x ≅ y,
      (ii)  a natural isomorphism C(−,x) ≅ C(−,y),
      (iii) a natural isomorphism C(y,−) ≅ C(x,−)
    correspond, because the Yoneda embeddings are fully faithful and so
    preserve, reflect, and CREATE isomorphisms — the explicit mutually
    inverse pair underlying an α as in (ii) being α_x(id_x) and
    (α⁻¹)_y(id_y).
    nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

    Everything here is assembly of parts long in tree, composed for the
    first time: [FullyFaithful] (Theory/Functor.v) instantiated at the
    embeddings [Curried_CoHom]/[Curried_Hom] via [Yoneda_Full] and
    [Yoneda_Faithful] (Functor/Hom.v) gives reflection; [fobj_iso]
    (Theory/Functor.v) gives preservation; and the CREATION strength —
    Riehl's actual proposition, a bijection of DATA and not merely a
    pair of implications — is the setoid isomorphism
    [representable_iso_setoid] between isomorphisms x ≅ y and natural
    isomorphisms [Hom ─,x] ≅ [Hom ─,y] — proved for the contravariant
    variance, which is the bijection Riehl's proposition names (the
    covariant leg is delivered as the biconditional
    [iso_iff_corepresentably_iso] only).  One round trip is
    [Yoneda_Embedding]'s [iso_from_to] leg read pointwise at each of
    the two legs; the other is the identity laws.

    The file also exports [repr_pair_iso] — the explicit-inverse-pair
    construction that Structure/UniversalProperty.v had inlined at its
    [univ_property_unique] since that file's beginning (the issue's
    "library defect"): given isomorphisms of both [Hom c,─] and
    [Hom v,─] with one and the same F, the objects c and v are
    isomorphic, by evaluating the composite transformations at the
    identity.  Structure/UniversalProperty.v now consumes it. *)

(** ** The Yoneda embeddings are fully faithful, in both variances *)

Section RepresentablyIso.

Context {C : Category}.

(* [Curried_CoHom C] is [Curried_Hom C^op] by definition, but typeclass
   resolution does not unfold definitions; these instances make the
   contravariant embedding's full faithfulness available by name. *)
#[export] Instance CoYoneda_Faithful : Faithful (Curried_CoHom C) :=
  Yoneda_Faithful C^op.

#[export] Instance CoYoneda_Full : Full (Curried_CoHom C) :=
  Yoneda_Full C^op.

(* An isomorphism read in the opposite category, with the two triangle
   laws exchanged. *)
Definition iso_op {x y : C} (i : x ≅ y) : @Isomorphism C^op y x := {|
  to := to i : @hom C^op y x;
  from := from i;
  iso_to_from := iso_from_to i;
  iso_from_to := iso_to_from i
|}.

(** ** The predicate, in Riehl's orientations *)

(* Two objects are representably isomorphic when both represented
   functors agree up to natural isomorphism: C(−,x) ≅ C(−,y) in
   presheaves AND C(y,−) ≅ C(x,−) in copresheaves (Riehl's directions;
   either component determines the other through x ≅ y below). *)
Definition ContravariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y].

Definition CovariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─].

Definition RepresentablyIsomorphic (x y : C) : Type :=
  ContravariantRepresentableIso x y * CovariantRepresentableIso x y.

(** ** The two biconditionals: reflection composed with preservation *)

(* Contravariant: x ≅ y exactly when [Hom ─,x] ≅ [Hom ─,y].  The
   forward map is the embedding's action on isomorphisms; the backward
   map is [FullyFaithful] at [Curried_CoHom] — the instantiation issue
   #942 records as never before taken. *)
Definition iso_iff_representably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]).
Proof.
  split.
  - exact (@fobj_iso _ _ (Curried_CoHom C) x y).
  - exact (@FullyFaithful _ _ (Curried_CoHom C) _ _ x y).
Defined.

(* Covariant twin: x ≅ y exactly when [Hom y,─] ≅ [Hom x,─], through
   the opposite category. *)
Definition iso_iff_corepresentably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split.
  - intros i.
    exact (@fobj_iso _ _ (Curried_Hom C) y x (iso_op i)).
  - intros α.
    pose (i := @FullyFaithful _ _ (Curried_Hom C) _ _ y x α).
    exact {| to := to i : x ~{C}~> y
           ; from := from i
           ; iso_to_from := iso_from_to i
           ; iso_from_to := iso_to_from i |}.
Defined.

(* Isomorphic objects are representably isomorphic in both variances at
   once, and the two variances agree with each other. *)
Definition representably_isomorphic_of_iso {x y : C} (i : x ≅ y) :
  RepresentablyIsomorphic x y :=
  (fst (iso_iff_representably_iso x y) i,
   fst (iso_iff_corepresentably_iso x y) i).

(* ...and conversely, either representable isomorphism recovers the
   isomorphism of objects. *)
Definition iso_of_representably_isomorphic {x y : C}
  (r : RepresentablyIsomorphic x y) : x ≅ y :=
  snd (iso_iff_representably_iso x y) (fst r).

Definition representably_iso_variances_agree (x y : C) :
  iffT (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y])
       (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split; intros α.
  - exact (fst (iso_iff_corepresentably_iso x y)
             (snd (iso_iff_representably_iso x y) α)).
  - exact (fst (iso_iff_representably_iso x y)
             (snd (iso_iff_corepresentably_iso x y) α)).
Defined.

End RepresentablyIso.

(** ** The reusable inverse pair for representability arguments

    Two representations of one functor have isomorphic representing
    objects, by the explicit inverse pair: compose the legs, pull each
    composite back through [Yoneda_Embedding']'s two-sided inverse —
    evaluation at the identity — and the triangle laws follow from the
    isomorphisms' own round trips.  This is verbatim the construction
    Structure/UniversalProperty.v's [univ_property_unique] had inlined;
    it now lives here, generalized over the represented functor, and
    that file consumes it. *)

Definition repr_pair_iso {C : Category} {F : C ⟶ Sets} {c v : C}
  (b1 : @Isomorphism (@Copresheaves C Sets) [Hom c,─] F)
  (b2 : @Isomorphism (@Copresheaves C Sets) [Hom v,─] F) : c ≅ v.
Proof.
  unshelve econstructor.
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C v c)
             (from b1 ∘ to b2)).
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C c v)
             (from b2 ∘ to b1)).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C v c v (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b1));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b2 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b2));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C c v c (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b2));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b1 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b1));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
Defined.

(** ** Creation: the bijection of data (Riehl's Proposition 2.3.1) *)

(* An isomorphism read back from the opposite category. *)
Definition iso_unop {C : Category} {x y : C}
  (i : @Isomorphism C^op x y) : x ≅ y := {|
  to := from i : x ~{C}~> y;
  from := to i;
  iso_to_from := iso_to_from i;
  iso_from_to := iso_from_to i
|}.

(* The explicit inverse pair carried by a natural isomorphism
   α : [Hom ─,x] ≅ [Hom ─,y] — Riehl's α_x(id_x) and (α⁻¹)_y(id_y) —
   obtained with NO new proof content: [repr_pair_iso] at C^op, with
   the second representation the identity.  [eval_iso_to] and
   [eval_iso_from] record that the components are the evaluations at
   the identity, up to the identity laws. *)
Definition eval_iso {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) : x ≅ y :=
  iso_unop (@repr_pair_iso C^op (fobj[Curried_CoHom C] y) x y α iso_id).

Lemma eval_iso_to {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  to (eval_iso α) ≈ transform[to α] x id.
Proof. simpl; cat. Qed.

Lemma eval_iso_from {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  from (eval_iso α) ≈ transform[from α] y id.
Proof. simpl; cat. Qed.

(* The setoid of isomorphisms x ≅ y is isomorphic IN Sets to the setoid
   of natural isomorphisms [Hom ─,x] ≅ [Hom ─,y]: the embedding
   CREATES isomorphisms, as a bijection of data with both round trips.
   Forward: the embedding's action.  Backward: evaluation at the
   identity ([eval_iso]). *)
Program Definition representable_iso_setoid {C : Category} (x y : C) :
  (x ≅ y) ≊ (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) := {|
  to := {| morphism := fst (iso_iff_representably_iso x y) |};
  from := {| morphism := eval_iso |}
|}.
Next Obligation.
  intros C x y i j [Ht Hf]; split; simpl.
  - intros c g; unfold op; now rewrite Ht.
  - intros c g; unfold op; now rewrite Hf.
Qed.
Next Obligation.
  intros C x y α β [Ht Hf]; split; simpl.
  - now rewrite (Ht x id).
  - exact (Hf y (id ∘ id)).
Qed.
Next Obligation.
  intros C x y α; split; simpl.
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C x y) (to α) c g).
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C y x) (from α) c g).
Qed.
Next Obligation.
  intros C x y i; split; simpl; cat.
Qed.
