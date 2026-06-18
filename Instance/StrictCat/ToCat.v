Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * The comparison functor [StrictCat ⟶ Cat] *)

(* Issue #138 observes that [Cat] uses [Functor_Setoid], which identifies
   functors only up to natural isomorphism, whereas the ZFC-style notion of
   equality of functors is the *strict* one used by [StrictCat]
   ([Functor_StrictEq_Setoid]: equal object maps, with morphism maps agreeing
   after transport).  The two notions are not interchangeable — the underlying
   1-category of the 2-category [Cat] genuinely needs the weak hom-equivalence,
   since an isomorphism there is an *equivalence* of categories (this is what
   the Lawvere/comma characterisation of adjunctions in
   [Construction.Comma.Adjunction] relies on).

   What *is* true, and is the content of this file, is that the strict notion
   refines the weak one: strict equality of functors implies natural
   isomorphism.  This gives an identity-on-objects, identity-on-morphisms
   comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat], exhibiting
   [StrictCat] as a strictification of [Cat].  Functors *out of* [StrictCat]
   that do not respect natural isomorphism — e.g. the underlying-graph functor
   [Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv] — therefore cannot
   in general be factored through this comparison functor, which is precisely
   why [StrictCat] is needed. *)

(* An equality of objects induces an isomorphism: transport the identity along
   the equality.  By path induction this is [iso_id] when the proof is
   [eq_refl], so [to] and [from] compute to [id]. *)
Definition iso_of_eq {C : Category} {x y : C} (p : x = y) : x ≅ y :=
  match p in (_ = z) return (x ≅ z) with
  | eq_refl => iso_id
  end.

(* Transporting a morphism along an equality of its codomain is the same as
   post-composing with the induced isomorphism. *)
Lemma transport_cod_to_iso {C : Category} {c a b : C} (p : a = b) (g : c ~> a) :
  transport (fun z => hom c z) p g ≈ to (iso_of_eq p) ∘ g.
Proof. destruct p; simpl; now rewrite id_left. Qed.

(* Dually, transporting along an equality of the domain (via [transport_r]) is
   pre-composition with the induced isomorphism. *)
Lemma transport_r_dom_to_iso {C : Category} {a b d : C} (p : a = b) (g : b ~> d) :
  transport_r (fun z => hom z d) p g ≈ g ∘ to (iso_of_eq p).
Proof. destruct p; unfold transport_r; simpl; now rewrite id_right. Qed.

(* The mathematical core of issue #138: two functors that are strictly equal
   (equal on objects, with morphism maps agreeing after transport) are
   naturally isomorphic.  The natural isomorphism is, objectwise, the identity
   transported along the object equality. *)
Lemma strict_equiv_implies_fun_equiv {C D : Category} (F G : C ⟶ D) :
  @equiv _ Functor_StrictEq_Setoid F G ->
  @equiv _ Functor_Setoid F G.
Proof.
  intros [eq_on_obj coh].
  exists (fun x => iso_of_eq (eq_on_obj x)).
  intros x y f.
  pose proof (coh x y f) as Hc.
  rewrite transport_cod_to_iso in Hc.
  rewrite transport_r_dom_to_iso in Hc.
  rewrite <- comp_assoc.
  rewrite <- Hc.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

(* The comparison functor is the identity on both objects and morphisms; the
   only content is that it sends strict equality to natural isomorphism. *)
Program Definition StrictCat_to_Cat : StrictCat ⟶ Cat := {|
  fobj := fun C => C;
  fmap := fun _ _ F => F
|}.
Next Obligation.
  repeat intro.
  now apply strict_equiv_implies_fun_equiv.
Qed.
