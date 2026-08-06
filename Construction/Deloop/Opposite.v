Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** ** The opposite monoid, and delooping against duality *)

(* Riehl, CTiC, Example 1.2.2(iii): the opposite of a delooping is the
   delooping of the opposite monoid.  This is the device by which a RIGHT
   action of M is presented as a LEFT action of M^op, and it is the reason
   the composition-order choice above is a choice rather than a convention:
   the other choice deloops M^op, and for non-commutative M those categories
   differ (Construction/Funny/Comparison.v's [ListMon] is a live example). *)

Program Definition MonObject_op (M : MonObject) : MonObject := {|
  mon_setoid := mon_setoid M;
  mon_unit   := mon_unit;
  mon_op     := fun a b => mon_op b a;

  mon_op_respects := _;
  mon_op_assoc    := fun a b c => mon_op_assoc_sym M c b a;
  mon_op_unit_l   := fun a => mon_op_unit_r a;
  mon_op_unit_r   := fun a => mon_op_unit_l a
|}.
Next Obligation. now intros ?? H1 ?? H2; rewrite H1, H2. Qed.

(* The double opposite agrees with the original on all three DATA fields, by
   [eq_refl].  It is NOT [eq] to it: the two law fields come back as
   [mon_op_assoc_sym] applied twice and as the swapped unit laws, which are
   propositionally but not syntactically the originals, and [MonObject] has no
   proof irrelevance.  So this is weaker than Construction/Opposite.v's
   `C^op^op = C` by reflexivity, and the difference is exactly that the
   category laws there are packaged to be self-inverse while these are not. *)
Example MonObject_op_op_carrier (M : MonObject) :
  carrier (MonObject_op (MonObject_op M)) = carrier M := eq_refl.
Example MonObject_op_op_unit (M : MonObject) :
  @mon_unit (MonObject_op (MonObject_op M)) = @mon_unit M := eq_refl.
Example MonObject_op_op_op (M : MonObject) :
  @mon_op (MonObject_op (MonObject_op M)) = @mon_op M := eq_refl.

(* And the two constructions commute definitionally: (B M)^op and B (M^op)
   have the same objects, the same hom-setoids, the same identity, and the
   same composition, so the comparison functors are identities on both. *)
Program Definition Deloop_op_to (M : MonObject) :
  (Deloop M)^op ⟶ Deloop (MonObject_op M) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Program Definition Deloop_op_from (M : MonObject) :
  Deloop (MonObject_op M) ⟶ (Deloop M)^op := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

(* Riehl Example 1.2.2(iii).  NOTE THE STRENGTH, which the first version of
   this file got wrong: `≅[Cat]` in this library IS equivalence of
   categories, because Cat's hom-setoid identifies naturally isomorphic
   functors (Instance/Cat.v), so the statement below is NOT an isomorphism
   of categories.  Here the stronger statement is available and is given
   immediately after: the two categories agree on objects, homs, hom-setoid,
   identities and composition, so the comparison is an isomorphism in
   StrictCat ([Deloop_op_strict]).  (Correction prompted by the groupoid
   work that consumes this file.) *)
Program Definition Deloop_op (M : MonObject) :
  (Deloop M)^op ≅[Cat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(* Both round trips are the identity functor on the nose, so the witnessing
   natural isomorphism is the identity at the single object and the coherence
   condition collapses under the two unit laws. *)
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.

(* The group case transports too. *)
Definition GrpObject_op (G : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_op (grp_monoid G);
  grp_inv    := grp_inv (g:=G);
  grp_inv_l  := fun a => grp_inv_r (g:=G) a;
  grp_inv_r  := fun a => grp_inv_l (g:=G) a
|}.

(* The strict form.  Both comparison functors are the identity on objects
   and on morphisms, so the object component of StrictCat's hom-setoid is
   [eq_refl], the transports vanish, and what remains is reflexivity of the
   morphism.  This is the genuine "isomorphism of categories" that the
   comment above previously — and wrongly — attached to the [Cat] form. *)
Program Definition Deloop_op_strict (M : MonObject) :
  (Deloop M)^op ≅[StrictCat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(* Both round-trip obligations are discharged by the library's default
   obligation tactic: the comparison functors are the identity on objects
   AND on morphisms, so the two sides are convertible and nothing is left
   to prove. *)
