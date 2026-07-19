Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Operads as one-object multicategories *)

(* nLab: https://ncatlab.org/nlab/show/operad

   An operad is a multicategory with a single object (colour), so that a
   multimorphism is determined by the ARITY of its source list alone.

   BUNDLING.  The one-object condition is recorded as the propositional
   equality [IsOperad M := @mobj M = poly_unit] — [=] on the Type-level
   object data of the multicategory, never on morphisms — bundled as a
   record ([Operad]).  Downstream consumers (operad algebras as
   multifunctors into the endomorphism multicategory of an object, whose
   colour type is [poly_unit] DEFINITIONALLY) only need the underlying
   multicategory, which the projection [operad_multi] exposes.

   THE DERIVED POINT.  Rather than transporting hom-sets along
   [operad_one], every accessor is phrased over the derived point
   [operad_pt O : mobj] (the transport of [ttt] backwards along
   [operad_one]).  Object contractibility [operad_obj_contr] — every
   object equals the point — is derived with no UIP: the transport
   lemma is proved by destructing an equality whose right endpoint is a
   variable.  For an instance whose colour type is [poly_unit]
   definitionally (so [operad_one := eq_refl]), [operad_pt] reduces to
   [ttt] and [ohom n] reduces to [mhom (repeat ttt n) ttt], with no
   transport anywhere.

   ARITY ACCESSORS.  [ohom n := mhom (repeat pt n) pt] is the setoid of
   n-ary operations; [oid] is the unary identity; [ocomp] is the
   single-slot operadic composition [∘ᵢ], obtained from the zipper
   [mcomp] at [Γ1 := repeat pt i], [Γ2 := repeat pt j], recast along the
   transparent [repeat]-arithmetic kit ([repeat_app_t]).  The
   symmetric-group action restricts to self-permutations of
   [repeat pt n]: the witnesses are the Type-valued [tperm] of
   Theory/Multicategory.v (the class's own index; the stdlib
   [Permutation] is recoverable through [tperm_Permutation]).

   THE ROUND TRIP.  Every list of objects of an operad is a [repeat] of
   the point ([all_repeat], by induction from contractibility), so every
   multimorphism [mhom Γ pt] is an [ohom (length Γ)] up to [mcast]; the
   two directions ([to_ohom]/[of_ohom]) compose to the identity up to
   [≈] by the [mcast] groupoid pack ([operad_roundtrip],
   [operad_roundtrip_inv]). *)

(** ** The transport helper and the bundled record *)

(* Transport an inhabitant of [poly_unit] along a Type equality.  Stated
   with the equality oriented [poly_unit = A] so that the contractibility
   lemma below can destruct it (the right endpoint is a variable). *)
Definition unit_transport {A : Type} (e : poly_unit = A) : A :=
  match e in _ = T return T with eq_refl => ttt end.

(* Any type equal to [poly_unit] is contractible onto the transported
   point.  No UIP: [destruct e] abstracts the variable endpoint, and
   [poly_unit] has a single constructor. *)
Lemma unit_transport_contr {A : Type} (e : poly_unit = A) (x : A) :
  x = unit_transport e.
Proof.
  destruct e.
  now destruct x.
Qed.

(* The one-object condition: [=] on the Type-level colour data. *)
Definition IsOperad (M : Multicategory) : Type :=
  @mobj M = poly_unit.

Record Operad : Type := {
  operad_multi : Multicategory;
  operad_one : IsOperad operad_multi
}.

(** ** The derived point and object contractibility *)

(* The unique colour of the operad.  When [operad_one] is [eq_refl]
   (colour type [poly_unit] on the nose), this reduces to [ttt]. *)
Definition operad_pt (O : Operad) : @mobj (operad_multi O) :=
  unit_transport (eq_sym (operad_one O)).

(* Every object of an operad is the point. *)
Lemma operad_obj_contr (O : Operad) (x : @mobj (operad_multi O)) :
  x = operad_pt O.
Proof.
  apply unit_transport_contr.
Qed.

(* Every LIST of objects of an operad is a [repeat] of the point: the
   list-level face of contractibility, and the equality along which the
   round trip below recasts.  [Defined] so the [f_equal2] spine computes
   on list constructors; its leaves ([operad_obj_contr], hence
   [unit_transport_contr]) are opaque, so full reduction stops there —
   no consumer needs more (the casts ride the class's groupoid pack). *)
Definition all_repeat (O : Operad) (Γ : list (@mobj (operad_multi O))) :
  Γ = repeat (operad_pt O) (length Γ).
Proof.
  induction Γ as [|a Γ IH]; simpl.
  - reflexivity.
  - exact (f_equal2 cons (operad_obj_contr O a) IH).
Defined.

(** ** The transparent repeat-arithmetic kit

    The stdlib's [repeat_app] is stated with the concatenation on the
    right and is opaque in some supported versions; the accessors below
    need a proof that COMPUTES on [nat] constructors, so a transparent
    Fixpoint is defined here (the [map_app_t] pattern of
    Theory/Multicategory/Functor.v). *)

Fixpoint repeat_app_t {A : Type} (x : A) (m n : nat) :
  repeat x (m + n) = repeat x m ++ repeat x n :=
  match m with
  | O => eq_refl
  | S m' => f_equal (cons x) (repeat_app_t x m' n)
  end.

(** ** Arity accessors *)

Section OperadAccessors.

Context (O : Operad).

Local Notation MO := (operad_multi O).
Local Notation pt := (operad_pt O).

(* The setoid of n-ary operations. *)
Definition ohom (n : nat) : Type := @mhom MO (repeat pt n) pt.

#[export] Instance ohom_setoid (n : nat) : Setoid (ohom n) :=
  @mhomset MO (repeat pt n) pt.

(* The unary identity operation: [repeat pt 1] is [[pt]] on the nose. *)
Definition oid : ohom 1 := @mid MO pt.

(** *** The round trip

    Every multimorphism of the underlying multicategory whose target is
    the point is an n-ary operation, [n := length Γ], by recasting along
    [all_repeat]; the two directions cancel up to [≈] by the [mcast]
    groupoid pack. *)

Definition to_ohom {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  ohom (length Γ) :=
  @mcast MO _ _ pt (all_repeat O Γ) f.

Definition of_ohom {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  @mhom MO Γ pt :=
  @mcast MO _ _ pt (eq_sym (all_repeat O Γ)) g.

#[export] Instance to_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@to_ohom Γ).
Proof. apply mcast_respects. Qed.

#[export] Instance of_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@of_ohom Γ).
Proof. apply mcast_respects. Qed.

Lemma operad_roundtrip {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  of_ohom (to_ohom f) ≈ f.
Proof. apply mcast_symm_l. Qed.

Lemma operad_roundtrip_inv {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  to_ohom (of_ohom g) ≈ g.
Proof. apply mcast_symm_r. Qed.

(** *** Single-slot operadic composition

    The classical [∘ᵢ]: splice an n-ary operation into the (i+1)-st
    input of an (i + 1 + j)-ary operation, yielding an
    (i + (n + j))-ary operation.  The zipper of Theory/Multicategory.v
    is instantiated at [Γ1 := repeat pt i], [Γ2 := repeat pt j], and
    the boundary lists are renormalised to [repeat] form along the
    transparent arithmetic kit. *)

(* The zipper form of a repeated context: [repeat pt (S j)] is
   [pt :: repeat pt j] on the nose, so [repeat_app_t] already has the
   stated type up to conversion. *)
Definition orep_zip (i j : nat) :
  repeat pt (i + S j) = repeat pt i ++ pt :: repeat pt j :=
  repeat_app_t pt i (S j).

(* Renormalising a three-block spliced context to [repeat] form. *)
Definition orep_splice (i n j : nat) :
  repeat pt i ++ repeat pt n ++ repeat pt j = repeat pt (i + (n + j)) :=
  eq_sym (eq_trans (repeat_app_t pt i (n + j))
                   (f_equal (app (repeat pt i)) (repeat_app_t pt n j))).

Definition ocomp {i j n : nat} (f : ohom (i + S j)) (g : ohom n) :
  ohom (i + (n + j)) :=
  @mcast MO _ _ pt (orep_splice i n j)
    (@mcomp MO (repeat pt i) (repeat pt j) (repeat pt n) pt pt
       (@mcast MO _ _ pt (orep_zip i j) f) g).

#[export] Instance ocomp_respects {i j n : nat} :
  Proper (equiv ==> equiv ==> equiv) (@ocomp i j n).
Proof.
  intros f f' ef g g' eg; unfold ocomp.
  now rewrite ef, eg.
Qed.

(** *** The symmetric-group action on arities

    Self-permutations of the repeated context [repeat pt n] act on
    n-ary operations.  The witnesses are the Type-valued [tperm] of
    Theory/Multicategory.v — the index of the class's own action; the
    stdlib [Permutation (repeat pt n) (repeat pt n)] proposition is
    recoverable through [tperm_Permutation].  The identity law is
    pinned to the canonical [tperm_refl] witness, and functoriality is
    along the [tperm_trans] constructor, exactly as in the class. *)

Definition osym {n : nat} (p : tperm (repeat pt n) (repeat pt n)) :
  ohom n → ohom n :=
  @msym MO _ _ pt p.

#[export] Instance osym_respects {n : nat}
  (p : tperm (repeat pt n) (repeat pt n)) :
  Proper (equiv ==> equiv) (@osym n p).
Proof. apply msym_respects. Qed.

Lemma osym_id {n : nat} (f : ohom n) :
  osym (tperm_refl (repeat pt n)) f ≈ f.
Proof. apply msym_id. Qed.

Lemma osym_compose {n : nat} (p q : tperm (repeat pt n) (repeat pt n))
  (f : ohom n) :
  osym q (osym p f) ≈ osym (tperm_trans p q) f.
Proof. apply msym_compose. Qed.

End OperadAccessors.

