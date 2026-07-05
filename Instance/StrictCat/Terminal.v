Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * 1 is the terminal object of StrictCat *)

(* nLab: https://ncatlab.org/nlab/show/terminal+category

   [Instance.One] shows that the terminal category [_1] is terminal in the
   *weak* category [Cat], where functors are compared up to natural
   isomorphism.  Here we show the stronger fact that [_1] is also terminal in
   [StrictCat], where functors are compared by strict equality
   ([Functor_StrictEq_Setoid]): any two functors [F G : C ⟶ 1] are equal on
   the nose, because both objects and morphisms of [1] are inhabitants of the
   contractible type [poly_unit].  The witness [one] is again the erasure
   functor [Erase].

   This instance is the prerequisite for exhibiting the funny tensor product
   as a *semicartesian* monoidal structure on [StrictCat], whose unit [_1] is
   the terminal object. *)

(* [poly_unit] is contractible: any two inhabitants are equal. *)
Lemma poly_unit_eq (u v : poly_unit) : u = v.
Proof. now destruct u, v. Qed.

(* 1 is the terminal object of StrictCat, witnessed by the unique functor
   [Erase].  Uniqueness is strict: on objects both functors land in the
   contractible [poly_unit], and the transported morphism maps agree because
   the homs of [1] are likewise [poly_unit] under [Morphism_equality]. *)
#[export]
Program Instance StrictCat_Terminal : @Terminal StrictCat := {
  terminal_obj := _1;        (* the terminal category 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 *)
}.
Next Obligation.
  exists (fun c => poly_unit_eq (f c) (g c)).
  intros c c' h; simpl.
  apply poly_unit_eq.
Qed.
