Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Comonads on a preorder are interior operators *)

(* nLab: https://ncatlab.org/nlab/show/interior+operator
   nLab: https://ncatlab.org/nlab/show/comonad
   Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
         Example 5.1.7, printed p. 186, and SS 5.2, Example 5.2.6
         (begins p. 189), clause (iv) and footnotes 10–11, printed p. 190
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
         SS 1.4.4, footnote 8, printed p. 33
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, SS VI.1, printed p. 139, and SS VI.2,
         printed p. 141

   WHAT THE BOOKS SAY.  Mac Lane's p. 139 defines a comonad in a category
   (display (1^op)) and the comonad ⟨FG, ε, FηG⟩ of an adjunction, and
   then asks "What is a monad in a preorder P?"; his preorder remarks
   there and on p. 141 (algebras) are about monads only.  Riehl's
   Example 5.1.7 (p. 186) adds the dual for a poset: "Dually, a comonad
   on a poset category (P, ≤) defines a kernel operator: an
   order-preserving function K so that Kp ≤ p and Kp = K²p", and names
   the interior of a subset of a space as the instance.  Example 5.2.6
   (begins p. 189), clause (iv) and footnotes 10–11, printed p. 190, says
   that "a coalgebra for the interior kernel operator is exactly an open
   subset", and its footnote 11 reads coalgebras as
   the algebras "for a monad (T, η, µ) on C^op".  Seven Sketches'
   footnote 8 (p. 33) says that for a Galois connection f ⊣ g the other
   composite g ⨟ f (that is, f after g) "satisfies the dual properties:
   (g ⨟ f)(q) ≤ q and (g ⨟ f ⨟ g ⨟ f)(q) ≅ (g ⨟ f)(q) ... This is called
   an interior operator, though we will not discuss this concept
   further".

   WHICH READING IS IMPLEMENTED.  An interior operator on P IS a closure
   operator on the reversed order: [InteriorOperator P] is
   Instance/Proset/Monad.v's [ClosureOperator] at stdlib's
   [flip_PreOrder P], and no new record is introduced.  Read back in P,
   its fields are deflation [int_defl] and the comultiplication
   inequality [int_comult], by conversion; monotonicity [int_mono] is the
   field [mono_pres] with its two points swapped.  Seven Sketches' ≅ is
   [int_idem], the [cl_idem] of the reversed order read backwards, and
   Riehl's "Kp = K²p" is [int_idem_eq] under an explicit
   [Antisymmetric] hypothesis, since the tree's [Poset] is [Proset] with
   antisymmetry discarded.  Riehl states one direction ("defines") for a
   poset; both directions are proved here, over a preorder.

   BY DUALITY, WITH NO LAW PROVED AGAIN.  The dual is obtained in three
   places, and each is measured.
     - The notion: the reversed order, as above.
     - The comonad: Theory/Monad.v defines [Comonad] as a monad at C^op,
       so [interior_comonad] is a monad on (Proset P)^op whose unit and
       multiplication families are the two fields and whose five laws are
       [I].  It is Structure/Thin/Monad.v's [thin_comonad] written out:
       the counit and comultiplication agree by [eq_refl]
       ([interior_comonad_extract], [interior_comonad_duplicate]).  It is
       not DEFINED through [thin_comonad]: that route is refused bare,
       the sort level of Structure/Thin.v's [Thin] being left in the body
       alone; pinned to u or h it adds h <= u or u <= h (measured); with
       + the thin level stays in the block only (the same reason
       Instance/Proset/Monad.v gives for [closure_monad]).
     - The correspondence, by Riehl's route: a comonad W on P is a monad
       on the reversed order.  [comonad_flip_monad W] is
       Instance/Proset/Monad.v's [closure_monad] at the interior operator
       of W, its unit is extract and its multiplication duplicate
       ([comonad_flip_ret], [comonad_flip_join]), and
       [interior_is_flip_closure] says that the interior operator of W IS
       the closure operator of that monad.  The coalgebras follow the same
       way: [wcoalgebra_iff_flip_talgebra] identifies a W-coalgebra with
       an algebra of the reversed-order monad (footnote 11 at the order
       level), and [wcoalgebra_iff_open] is then Monad.v's
       [talgebra_iff_closed] at the reversed order.  A second route is
       [wcoalgebra_iff_open_via_thin], Structure/Thin/Monad.v's
       [thin_wcoalgebra_iff], which is the monad statement at C^op.
   [open_iff_fixed] is "x ≤ Kx ≤ x" as Kx ≅ x, and under [Antisymmetric]
   [open_eq] makes a coalgebra a fixed point, Kx = x (the dual of
   Monad.v's [closed_eq]); [wlocal_iff_open] reads
   Construction/Reflective/FixedPoints.v's [WLocal_Subcategory] (extract
   invertible) as the open elements, and [proset_open_coreflective] is
   Structure/Thin/Monad.v's [thin_coreflective] at the proset: the open
   elements are coreflective, the dual of Seven Sketches Example 1.122.

   WHY THE REVERSED ORDER AND NOT (Proset P)^op.  The two categories have
   the same objects and homs by [eq_refl] (Instance/Proset/Order.v's
   [Proset_op_obj], [Proset_op_hom]), but the equation
   [(Proset P)^op = Proset (flip_PreOrder P)] is refused by conversion,
   already at the [id] field: stdlib's [flip_PreOrder] is opaque.  With
   Instance/Proset/Limit.v's transparent [op_PreOrder] in its place the
   [id] and [compose] fields agree by [eq_refl] and the equation is still
   refused, at the law fields, which Construction/Opposite.v takes from
   Proset P swapped and [Proset] takes from its own obligations.  So an
   endofunctor of (Proset P)^op is not one of the reversed order (the
   ascription is refused), and the strongest relation is Order.v's
   [Proset_op_iso]: [flip_functor W] agrees with
   [Proset_op_to P ◯ W^op ◯ Proset_op_from P] in [fobj] and [fmap] by
   [eq_refl] ([flip_functor_is_op_fobj], [flip_functor_is_op_fmap]), the
   refusal of [=] being in the law fields alone, and as functors at ≈
   ([flip_functor_is_op]).

   SEVEN SKETCHES SS 1.4.4: BOTH COMPOSITES OF ONE ADJUNCTION.  For
   [Adj : F ⊣ U] between prosets, [adj_closure Adj] is the closure
   operator of Monad/Adjunction.v's [Adjunction_Monad] (the composite U
   after F) and [adj_interior Adj] the interior operator of
   Comonad/Duality.v's [Adjunction_Comonad] (F after U); their maps are
   U (F x) and F (U y) by [eq_refl].  At Instance/Proset/Galois.v's
   truncated shift [nat_shift_adjunction k] (n - k ⊣ m + k on (ℕ, ≤))
   they are (m - k) + k and (m + k) - k by [eq_refl]; the closure is
   Monad.v's [max_closure k] ([shift_closure_is_max]) and the interior is
   the identity ([shift_interior_is_id]), so that witness is degenerate on
   the interior side.  [min_interior k] (n ↦ min n k) is not: its open
   elements are exactly the n ≤ k ([min_open_iff]), and 3 is not open for
   k = 2 ([min_three_not_open]).

   STRENGTHS, measured.
     - interior → comonad → interior: [eq_refl] on the WHOLE record
       ([interior_round_trip]), through primitive-projection eta.
     - comonad → interior → comonad: ≈ of functors with identity
       components ([comonad_round_trip], which IS Monotone.v's
       [Functor_of_monotone_of_Functor]); [fobj], [fmap], [extract] and
       [duplicate] by [eq_refl] ([comonad_round_trip_fobj],
       [comonad_round_trip_fmap], [comonad_round_trip_extract],
       [comonad_round_trip_duplicate]), so the counit and
       comultiplication come back on the nose; the refusal is in the law
       fields alone: [=] is refused by conversion.  Flipped first: with
       the functor's law fields written as transparent [I] and no [Qed],
       it is refused the same way, the law fields of a variable W being
       stuck projections.
     - [interior_is_flip_closure]: [eq_refl] on the whole record.  Since
       [comonad_flip_monad] is defined through [closure_monad], that
       equation is Monad.v's [closure_round_trip] at the interior
       operator; what makes it say something is
       [comonad_flip_monad_is_thin]: the same monad is, on the whole
       record and by [eq_refl], Structure/Thin/Monad.v's [thin_monad]
       built from extract and duplicate alone.
     - [interior_comonad] against [thin_comonad]: counit and
       comultiplication by [eq_refl]; the whole comonad is refused by
       conversion.  Flipped: with Structure/Thin.v's [Thin_Opposite] (a
       [Qed] lemma) restated with a transparent body, and nothing else
       changed, the whole equation is [eq_refl].  The refusal is that
       opacity alone.
     - [flip_functor W] against the opposite read through
       [Proset_op_iso]: [fobj] and [fmap] by [eq_refl]
       ([flip_functor_is_op_fobj], [flip_functor_is_op_fmap]), functors
       at ≈, [=] refused, the refusal in the law fields alone.
       Flipped: in a 30-file copy of its dependency closure with every
       Program obligation transparent ([Set Transparent Obligations] in
       Lib.v, [Compose]'s and [Functor_of_monotone]'s obligations
       [Defined]), it is still refused; the residue is W's
       [fmap_respects] inside stdlib's opaque
       [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1].
     - [(Proset P)^op = Proset (op_PreOrder P)], with
       Instance/Proset/Limit.v's transparent [op_PreOrder]: refused
       structurally at [compose_respects], even in that fully transparent
       copy, where the other fields agree by [eq_refl];
       Construction/Opposite.v swaps the two hypotheses of
       [compose_respects].
     - The coalgebra structure map round-trips by [eq_refl]
       ([wcoalgebra_round]); the [to] leg of [int_idem] is [int_defl] by
       [eq_refl] ([int_idem_to]); [flip_mono] and [unflip_mono] are
       mutually inverse by [eq_refl].
     - Under antisymmetry, ≅ becomes Leibniz [=] on elements: [open_eq]
       (a coalgebra is a fixed point, the dual of Monad.v's [closed_eq])
       and [int_idem_eq].

   UNIVERSES, read off [About] with all instances printed.  No constant
   has a level that occurs in its body only.  Every constant polymorphic
   in the carrier level u that mentions the reversed order carries
   [Set < flip.u2, u <= flip.u0, u <= flip.u1] ([min_mono], whose
   carrier is [nat], carries only [Set < flip.u2]): stdlib's
   [Basics.flip] is not universe polymorphic, so
   these are its global universes, first carried here by
   [InteriorOperator] through [flip_PreOrder].  The caps
   [u <= Defs.u0, u <= Relation_Definition.u0] are stdlib's [PreOrder]
   and [relation], as in Monad.v; [int_idem_eq] and [open_eq] add
   [u <= equality.u0], first carried by Instance/Poset.v's [eq_equiv],
   as Monad.v's [closed_eq] does.  The strict bounds: [h < n] in
   [comonad_round_trip] and [flip_functor_is_op] is first carried by
   Theory/Functor.v's [Functor_Setoid] (its own [u4 < u2]), and in
   [flip_functor_is_op_fobj] and [flip_functor_is_op_fmap] by the same
   file's [Compose] ([u3 < u2]);
   [h < s] in the adjunction constants and the shift witnesses is the
   block of Theory/Adjunction.v's [Adjunction] record itself
   ([h1 < so], the level of the [Sets] hom-set isomorphism), and in
   [proset_open_coreflective] it is inherited from [thin_coreflective].
   [Adjunction_Comonad] has a level, its u4, sixth in its binder, that
   occurs in neither its type nor its block (measured); [adj_interior]
   pins it to h.  The biconditionals
   [@{u h +}] add the free level of [iffT] on their [Prop] side;
   [wcoalgebra_iff_open] names it (p) so that the level of the inner
   [talgebra_iff_closed] is the same one and not a level of the body
   alone.  [wcoalgebra_iff_open_via_thin] is a [Qed] lemma: transparent,
   it would carry [Thin]'s sort level in its body only.  In this file
   [flip] alone would be Lib's [CRelationClasses.flip]; every reversed
   relation is written [Basics.flip], the relation of [flip_PreOrder].
   This file loads both declarations of [Thin] and of [proset_thin]
   (Structure/Thin.v with Instance/Proset/Order.v, and
   Instance/Proset/Galois.v, imported for [nat_shift_adjunction];
   measured by [Locate]) and writes neither name: every thin witness is
   the term [fun _ _ _ _ => I].

   NOT DELIVERED.  No interior operator over [Props] or over spaces here
   (Instance/Props/Modal.v and Instance/Top/Interior.v); no category of
   interior operators and no functoriality in P; no statement that an
   interior operator is determined by its open elements.  The interior
   side of [nat_shift_adjunction] is the identity and is recorded as a
   degenerate witness, not as evidence. *)

(** ** Interior operators: closure operators on the reversed order *)

Definition InteriorOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) : Type@{u} :=
  ClosureOperator@{u} (flip_PreOrder P).

(* Monotone maps for an order are monotone maps for its reverse. *)
Definition flip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S) :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Definition unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}} {R : relation A}
  {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  @MonotoneFun@{u v} A R B S :=
  {| mono_map := f; mono_pres := fun x y h => mono_pres f y x h |}.

Example flip_unflip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B}
  (f : @MonotoneFun@{u v} A (Basics.flip R) B (Basics.flip S)) :
  flip_mono (unflip_mono f) = f := eq_refl.

Example unflip_flip_mono@{u v} {A : Type@{u}} {B : Type@{v}}
  {R : relation A} {S : relation B} (f : @MonotoneFun@{u v} A R B S) :
  unflip_mono (flip_mono f) = f := eq_refl.

(* The fields of the reversed-order record, read in the original order.
   Each is the field itself, by conversion. *)
Definition int_defl@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) : R (cl_fun j x) x :=
  cl_ext j x.

Definition int_comult@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  R (cl_fun j x) (cl_fun j (cl_fun j x)) :=
  cl_mult j x.

Definition int_mono@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x y : A) (h : R x y) :
  R (cl_fun j x) (cl_fun j y) :=
  mono_pres (cl_fun j) y x h.

(* Riehl's "K p = K² p", up to ≅ over a preorder: the isomorphism
   [cl_idem] of the reversed order, read backwards. *)
Definition int_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (j : InteriorOperator@{u} P) (x : A) :
  cl_fun j (cl_fun j x) ≅[Proset@{u h} P] cl_fun j x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (from (cl_idem@{u h} j x)) (to (cl_idem@{u h} j x)) I I.

Example int_idem_to@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  to (int_idem@{u h} j x) = int_defl j (cl_fun j x) := eq_refl.

(* Under antisymmetry, Riehl's equation itself. *)
Lemma int_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (j : InteriorOperator@{u} P)
  (x : A) : cl_fun j (cl_fun j x) = cl_fun j x.
Proof. exact (AS _ _ (int_defl j (cl_fun j x)) (int_comult j x)). Qed.

(** ** The correspondence *)

Definition interior_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (unflip_mono (cl_fun j)).

(* Interior → comonad: at (Proset P)^op the counit and comultiplication
   families ARE the two fields, by conversion; every law is [I]. *)
Definition interior_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  @Comonad (Proset@{u h} P) (interior_functor j) :=
  @Build_Monad ((Proset@{u h} P)^op) ((interior_functor j)^op)
    (fun x => cl_ext j x) (fun x => cl_mult j x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* The same data as Structure/Thin/Monad.v's [thin_comonad]. *)
Example interior_comonad_extract@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @extract _ _ (interior_comonad@{u h} j) x
    = @extract _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                      (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

Example interior_comonad_duplicate@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (j : InteriorOperator@{u} P) (x : A) :
  @duplicate _ _ (interior_comonad@{u h} j) x
    = @duplicate _ _ (@thin_comonad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
                        (interior_functor@{u h} j) (cl_ext j) (cl_mult j)) x
  := eq_refl.

(* Comonad → interior: the counit and comultiplication are the fields. *)
Definition interior_of_comonad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} : InteriorOperator@{u} P :=
  {| cl_fun  := flip_mono (monotone_of_Functor P P W)
   ; cl_ext  := fun x => @extract _ W H x
   ; cl_mult := fun x => @duplicate _ W H x |}.

Definition comonad_interior_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { W : Proset@{u h} P ⟶ Proset@{u h} P & @Comonad (Proset@{u h} P) W }
    ↔ InteriorOperator@{u} P :=
  (fun p => match p with existT _ W H => interior_of_comonad W (H := H) end,
   fun j => existT (fun W : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Comonad (Proset@{u h} P) W)
              (interior_functor j) (interior_comonad j)).

(* interior → comonad → interior is the identity on the WHOLE record. *)
Example interior_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (j : InteriorOperator@{u} P) :
  interior_of_comonad@{u h} (interior_functor@{u h} j)
    (H := interior_comonad j) = j := eq_refl.

(* comonad → interior → comonad: ≈ of functors, identity components. *)
Definition comonad_round_trip@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_functor (interior_of_comonad W (H := H)) ≈ W :=
  Functor_of_monotone_of_Functor P P W.

Example comonad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  fobj[interior_functor (interior_of_comonad W (H := H))] x = fobj[W] x
  := eq_refl.

Example comonad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x y : A) (f : R x y) :
  fmap[interior_functor (interior_of_comonad W (H := H))] f = fmap[W] f
  := eq_refl.

(* ...and the comonad it rebuilds has W's counit and comultiplication. *)
Example comonad_round_trip_extract@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @extract _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @extract _ W H x := eq_refl.

Example comonad_round_trip_duplicate@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @duplicate _ _ (interior_comonad (interior_of_comonad W (H := H))) x
    = @duplicate _ W H x := eq_refl.

(** ** Riehl's route: a comonad on P is a monad on the reversed order *)

Definition flip_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  Proset@{u h} (flip_PreOrder P) ⟶ Proset@{u h} (flip_PreOrder P) :=
  Functor_of_monotone (flip_PreOrder P) (flip_PreOrder P)
    (flip_mono (monotone_of_Functor P P W)).

(* The monad on the reversed order is Instance/Proset/Monad.v's
   [closure_monad] at the interior operator: its unit is extract and its
   multiplication duplicate. *)
Definition comonad_flip_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  @Monad (Proset@{u h} (flip_PreOrder P)) (flip_functor W) :=
  closure_monad@{u h} (interior_of_comonad W (H := H)).

Example comonad_flip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @ret _ _ (comonad_flip_monad W (H := H)) x = @extract _ W H x
  := eq_refl.

Example comonad_flip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @join _ _ (comonad_flip_monad W (H := H)) x = @duplicate _ W H x
  := eq_refl.

(* It is also Structure/Thin/Monad.v's [thin_monad] on the reversed
   order, on the WHOLE record. *)
Example comonad_flip_monad_is_thin@{u h t} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  comonad_flip_monad W (H := H)
    = @thin_monad@{t u h} (Proset@{u h} (flip_PreOrder P))
        (fun _ _ _ _ => I) (flip_functor W)
        (fun x => @extract _ W H x) (fun x => @duplicate _ W H x)
  := eq_refl.

(* The interior operator of W IS the closure operator of that monad. *)
Example interior_is_flip_closure@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :
  interior_of_comonad W (H := H)
    = closure_of_monad (flip_functor W) (MM := comonad_flip_monad W)
  := eq_refl.

(* The same functor as W^op read through Order.v's [Proset_op_iso]. *)
Example flip_functor_is_op_fobj@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x : A) :
  fobj[flip_functor W] x
    = fobj[Proset_op_to P ◯ W^op ◯ Proset_op_from P] x := eq_refl.

Example flip_functor_is_op_fmap@{u h n | h < n +} {A : Type@{u}}
  {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) (x y : A)
  (f : Basics.flip R x y) :
  fmap[flip_functor W] f
    = fmap[Proset_op_to P ◯ W^op ◯ Proset_op_from P] f := eq_refl.

Lemma flip_functor_is_op@{u h m n | h < n, u <= m, h <= m +}
  {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P) :
  flip_functor W ≈ Proset_op_to P ◯ W^op ◯ Proset_op_from P.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(** ** Coalgebras are the open elements *)

(* A coalgebra of W is an algebra of the reversed-order monad: the two
   records carry the same structure map, and every law is [I]. *)
Definition wcoalgebra_iff_flip_talgebra@{u h} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x
    ↔ @TAlgebra (Proset@{u h} (flip_PreOrder P)) (flip_functor W)
        (comonad_flip_monad W (H := H)) x :=
  (fun c => @Build_TAlgebra (Proset@{u h} (flip_PreOrder P))
              (flip_functor W) (comonad_flip_monad W (H := H)) x
              (@w_coalg _ W H x c) I I,
   fun a => @Build_WCoalgebra (Proset@{u h} P) W H x
              (@t_alg _ _ (comonad_flip_monad W (H := H)) x a) I I).

(* So the coalgebra characterisation is Instance/Proset/Monad.v's
   [talgebra_iff_closed] at the reversed order. *)
Definition wcoalgebra_iff_open@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  iffT@{h p} (@WCoalgebra (Proset@{u h} P) W H x) (R x (W x)) :=
  let (to_flip, of_flip) := wcoalgebra_iff_flip_talgebra@{u h} W (H := H) x in
  let (to_closed, of_closed) :=
    talgebra_iff_closed@{u h p} (flip_functor W)
      (MM := comonad_flip_monad W (H := H)) x in
  (fun c => to_closed (to_flip c), fun h => of_flip (of_closed h)).

Example wcoalgebra_round@{u h p} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) (h : R x (W x)) :
  match wcoalgebra_iff_open@{u h p} W (H := H) x with
  | (to_open, of_open) => to_open (of_open h)
  end = h := eq_refl.

(* The second route: Structure/Thin/Monad.v's [thin_wcoalgebra_iff],
   which is the monad statement at (Proset P)^op.  [Qed]: transparent,
   it carries the sort level of [Thin] in its body only. *)
Lemma wcoalgebra_iff_open_via_thin@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  @WCoalgebra (Proset@{u h} P) W H x ↔ R x (W x).
Proof. exact (@thin_wcoalgebra_iff (Proset@{u h} P) (fun _ _ _ _ => I) W H x).
Qed.

(* "x ≤ Kx ≤ x": open means Kx ≅ x. *)
Definition open_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  R x (W x) ↔ (W x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _
              (@extract _ W H x) h I I,
   fun i => from i).

(* Under antisymmetry a coalgebra is a fixed point: the dual of
   Instance/Proset/Monad.v's [closed_eq]. *)
Lemma open_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (W : Proset@{u h} P ⟶ Proset@{u h} P) {H : @Comonad (Proset@{u h} P) W}
  (x : A) : @WCoalgebra (Proset@{u h} P) W H x → W x = x.
Proof. intro c. exact (AS _ _ (@extract _ W H x) (@w_coalg _ W H x c)). Qed.

(* FixedPoints.v's W-local objects (extract invertible) are the open
   ones. *)
Definition wlocal_iff_open@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} (x : A) :
  sobj (Proset@{u h} P) (WLocal_Subcategory H) x ↔ R x (W x) :=
  (fun Hi => @two_sided_inverse _ _ _ _ Hi,
   fun h => @Build_IsIsomorphism ((Proset@{u h} P)^op) x (W x)
              (@extract _ W H x) h I I).

(* The coreflection onto the open elements: Structure/Thin/Monad.v's
   [thin_coreflective] at the proset. *)
Definition proset_open_coreflective@{u h t s f | h < s, u <= t, h <= t +}
  {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (W : Proset@{u h} P ⟶ Proset@{u h} P)
  {H : @Comonad (Proset@{u h} P) W} :=
  @thin_coreflective@{t u h s f} (Proset@{u h} P) (fun _ _ _ _ => I) W H.

(** ** Seven Sketches SS 1.4.4: both composites of ONE adjunction *)

Definition adj_closure@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  ClosureOperator@{a} PA :=
  closure_of_monad (U ◯ F) (MM := Adjunction_Monad@{b h a h s w} Adj).

(* [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in
   neither its type nor its constraints; it is pinned to h. *)
Definition adj_interior@{a b h s w | h < s +} {A : Type@{a}} {B : Type@{b}}
  {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) :
  InteriorOperator@{b} PB :=
  interior_of_comonad (F ◯ U)
    (H := Adjunction_Comonad@{b h a h s h w} Adj).

Example adj_closure_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (x : A) :
  cl_fun (adj_closure Adj) x = U (F x) := eq_refl.

Example adj_interior_fun@{a b h s w | h < s +} {A : Type@{a}}
  {B : Type@{b}} {RA : relation A} {RB : relation B} {PA : PreOrder RA}
  {PB : PreOrder RB} {F : Proset@{a h} PA ⟶ Proset@{b h} PB}
  {U : Proset@{b h} PB ⟶ Proset@{a h} PA}
  (Adj : @Adjunction@{b h h a h h h h s h w} _ _ F U) (y : B) :
  cl_fun (adj_interior Adj) y = F (U y) := eq_refl.

(* At Galois.v's truncated shift (n - k ⊣ m + k) on (ℕ, ≤). *)
Example shift_closure_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m - k) + k)%nat := eq_refl.

Example shift_interior_fun@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = ((m + k) - k)%nat := eq_refl.

(* The closure is Instance/Proset/Monad.v's [max_closure k]... *)
Lemma shift_closure_is_max@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_closure@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = cl_fun (max_closure@{n} k) m.
Proof. simpl. lia. Qed.

(* ...and the interior is the identity: a degenerate witness. *)
Lemma shift_interior_is_id@{n h s w | h < s +} (k m : nat) :
  cl_fun (adj_interior@{n n h s w} (nat_shift_adjunction@{n n s w h} k)) m
    = m.
Proof. simpl. lia. Qed.

(** ** A non-degenerate interior operator: n ↦ min n k *)

Definition min_mono@{u} (k : nat) :
  @MonotoneFun@{u u} nat (Basics.flip Nat.le) nat (Basics.flip Nat.le) :=
  {| mono_map := fun n => Nat.min n k
   ; mono_pres := fun x y (H : (y <= x)%nat) =>
       Nat.min_le_compat_r y x k H |}.

Lemma min_comult@{} (k n : nat) :
  (Nat.min n k <= Nat.min (Nat.min n k) k)%nat.
Proof. lia. Qed.

Definition min_interior@{u} (k : nat) :
  InteriorOperator@{u} Nat.le_preorder :=
  {| cl_fun  := min_mono k
   ; cl_ext  := fun n => Nat.le_min_l n k
   ; cl_mult := fun n => min_comult k n |}.

(* Its coalgebras (open elements) are exactly the n below k. *)
Lemma min_open_iff@{u h +} (k n : nat) :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} k))
    (interior_comonad@{u h} (min_interior@{u} k)) n ↔ (n <= k)%nat.
Proof.
  destruct (wcoalgebra_iff_open (interior_functor (min_interior k))
              (H := interior_comonad (min_interior k)) n)
    as [to_open of_open].
  split.
  - intro c. pose proof (to_open c) as H. simpl in H. lia.
  - intro H. apply of_open. simpl. lia.
Qed.

Lemma min_three_not_open@{u h} :
  @WCoalgebra (Proset@{u h} Nat.le_preorder)
    (interior_functor@{u h} (min_interior@{u} 2%nat))
    (interior_comonad@{u h} (min_interior@{u} 2%nat)) 3%nat → False.
Proof.
  intro c. destruct (min_open_iff 2%nat 3%nat) as [to_le _].
  pose proof (to_le c). lia.
Qed.
