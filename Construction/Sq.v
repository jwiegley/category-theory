Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.DoubleCategory.
Require Import Category.Theory.DoubleCategory.Companion.

Generalizable All Variables.

(** * The double category of commuting squares

    nLab: https://ncatlab.org/nlab/show/double+category (Examples)

    For any category [C], there is a double category [Sq C] whose objects
    are the objects of [C], whose vertical AND horizontal 1-cells are both
    the morphisms of [C], and whose squares

        a --h--> b
        |        |
        u        v
        v        v
        c --k--> d

    are the proofs that the square commutes: [dsq h u v k := k ∘ u ≈ v ∘ h].
    A square is a mere proposition (an inhabitant of the hom-setoid's
    relation), so we equip it with the TRIVIAL setoid identifying all
    inhabitants; every coherence field of [DoubleCategory] then holds
    automatically, and the fields demanding a witness (vertical and
    horizontal pasting, the globular associator and unitors) are exactly
    the associativity and unit laws of [C].

    This instance is the class's reuse audit: it exercises every field of
    [DoubleCategory] in the degenerate proof-irrelevant regime, dually to
    Construction/Cospan/Double.v where squares are genuinely
    proof-relevant. *)

(* The trivial setoid on a type: all inhabitants are identified.  For
   [Sq C] the carrier is always a commuting-square proposition, so this
   is honest proof-irrelevance rather than information loss.  Kept local:
   applied to a data-carrying type it would silently identify everything,
   so it must not leak into the library interface. *)
#[local] Program Definition trivial_setoid (A : Type) : Setoid A := {|
  equiv := fun _ _ => True
|}.

Local Obligation Tactic := simpl; intros; repeat intro; try exact I.

Program Definition Sq (C : Category) : DoubleCategory := {|
  dcat := C;
  dhor := fun a b => a ~{C}~> b;
  dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h;
  dsq_setoid := fun a b c d h u v k => trivial_setoid _;
  dhid := fun a => id[a];
  dhcomp := fun a b c g f => g ∘ f
|}.
Next Obligation.
  (* dsq_coerce : k ∘ u' ≈ v' ∘ h from k ∘ u ≈ v ∘ h along u ≈ u', v ≈ v' *)
  now rewrite <- eu, <- ev.
Qed.
Next Obligation.
  (* dsq_vid : h ∘ id ≈ id ∘ h *)
  cat.
Qed.
Next Obligation.
  (* dsq_vcomp : l ∘ (u' ∘ u) ≈ (v' ∘ v) ∘ h *)
  rewrite comp_assoc, X0, <- comp_assoc, X, comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dsq_hcomp : (k' ∘ k) ∘ u ≈ w ∘ (h' ∘ h) *)
  rewrite <- comp_assoc, X, comp_assoc, X0, <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* dassoc : the globular associator is associativity of C *)
  unshelve eexists.
  { rewrite id_right, id_left.
    symmetry; apply comp_assoc. }
  unshelve eexists.
  { rewrite id_right, id_left.
    apply comp_assoc. }
  split; exact I.
Qed.
Next Obligation.
  (* dunit_left : the globular left unitor is id_left of C *)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.
Next Obligation.
  (* dunit_right : the globular right unitor is id_right of C *)
  unshelve eexists.
  { cat. }
  unshelve eexists.
  { cat. }
  split; exact I.
Qed.

(** ** The coercion/composition interchange mixin holds trivially

    Squares of [Sq C] are propositions under the trivial setoid, so both
    interchange fields of [DoubleCoerceComp] are immediate.  This makes the
    companion/conjoint uniqueness theorems of
    Theory/DoubleCategory/Companion.v available at [Sq C]. *)

Definition Sq_DoubleCoerceComp (C : Category) : DoubleCoerceComp (Sq C).
Proof. construct; exact I. Defined.

(** ** Companions: every vertical morphism is its own companion

    The companion of a vertical morphism [u : a ~> b] is [u] ITSELF viewed
    as a horizontal 1-cell.  The binding squares are the trivially
    commuting squares [u ∘ id ≈ u ∘ id] and [id ∘ u ≈ id ∘ u], and both
    zigzag identities hold automatically since any two squares with the
    same boundary are equal. *)

Program Definition Sq_companion {C : Category} {a b : C}
  (u : a ~{C}~> b) : Companion (D:=Sq C) u := {|
  comp_hor := u
|}.
Next Obligation.
  (* comp_unit : u ∘ id ≈ u ∘ id *)
  reflexivity.
Qed.
Next Obligation.
  (* comp_counit : id ∘ u ≈ id ∘ u *)
  reflexivity.
Qed.

(** ** Conjoints: exactly the isomorphisms

    AUDIT NOTE.  In [Sq C] a conjoint of [u : a ~> b] is a two-sided
    inverse of [u]: unwinding the binding squares at this model,
    [conj_unit] reads [conj_hor ∘ u ≈ id ∘ id] and [conj_counit] reads
    [id ∘ id ≈ u ∘ conj_hor].  A general morphism therefore has no conjoint
    here — in the quintet double category of a 1-category, conjoints are
    right adjoints, and an adjoint between locally discrete hom-categories
    is an inverse.  Accordingly [Sq_conjoint] is delivered at an
    isomorphism (the conjoint of [to u] is [from u]), and the necessity is
    recorded by [Sq_conjoint_iso]: any conjoint of [u] in [Sq C] makes [u]
    invertible.  Conjoints of arbitrary morphisms live instead in the
    transposed model whose horizontal 1-cells are the morphisms of
    [C^op]. *)

Program Definition Sq_conjoint {C : Category} {a b : C}
  (u : a ≅ b) : Conjoint (D:=Sq C) (to u) := {|
  conj_hor := from u
|}.
Next Obligation.
  (* conj_unit : from u ∘ to u ≈ id ∘ id *)
  rewrite iso_from_to; cat.
Qed.
Next Obligation.
  (* conj_counit : id ∘ id ≈ to u ∘ from u *)
  rewrite iso_to_from; cat.
Qed.

(* Necessity: a conjoint of [u] in [Sq C] is a two-sided inverse of [u],
   so only isomorphisms have conjoints in this model. *)
Program Definition Sq_conjoint_iso {C : Category} {a b : C}
  (u : a ~{C}~> b) (P : Conjoint (D:=Sq C) u) : a ≅ b := {|
  to := u;
  from := conj_hor P
|}.
Next Obligation.
  (* iso_to_from : u ∘ conj_hor P ≈ id *)
  pose proof (conj_counit P) as Hc; simpl in Hc.
  rewrite <- Hc; cat.
Qed.
Next Obligation.
  (* iso_from_to : conj_hor P ∘ u ≈ id *)
  pose proof (conj_unit P) as Hu; simpl in Hu.
  rewrite Hu; cat.
Qed.
