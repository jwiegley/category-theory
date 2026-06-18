Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The terminal category 1 (the point). *)

(* nLab:      https://ncatlab.org/nlab/show/terminal+category
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   1 is the category with a single object and a single (identity) morphism on
   it.  Here the lone object and the lone arrow are both [ttt], the unique
   inhabitant of the universe-polymorphic unit type [poly_unit]; the hom-setoid
   is strict equality, under which that hom is trivially contractible.

   1 is the terminal object of Cat: for every category C there is a unique
   functor `! : C ⟶ 1` ([Erase]), sending every object and morphism to [ttt].
   Dually, functors *out* of 1 pick out objects of the target, so [1, C] ≃ C.
   The dual notion — the initial/empty category 0 — lives in Instance/Zero.v. *)

Program Definition _1@{o h p} : Category@{o h p} := {|
  obj     := poly_unit@{o};            (* the single object *)
  hom     := fun _ _ => poly_unit@{h}; (* the single (identity) arrow *)
  homset  := Morphism_equality@{o h p}; (* hom-setoid is strict equality *)
  id      := fun _ => ttt;             (* identity = the lone arrow *)
  compose := fun _ _ _ _ _ => ttt      (* composition = the lone arrow *)
|}.
Next Obligation.
  now destruct f.
Qed.
Next Obligation.
  now destruct f.
Qed.

Notation "1" := _1 : category_scope.

(* `one[C]` names the unique functor `! : C ⟶ 1` at Cat's Terminal instance. *)
Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.

(* The unique functor `! : C ⟶ 1`, collapsing all of C onto the point. *)
#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 := {
  fobj := fun _ => ttt;      (* every object goes to the lone object *)
  fmap := fun _ _ _ => id    (* every morphism goes to the identity *)
}.

(* 1 is the terminal object of Cat, witnessed by the unique functor [Erase]. *)
#[export]
Program Instance Cat_Terminal : @Terminal Cat := {
  terminal_obj := _1;        (* the terminal category 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 *)
}.
Next Obligation.
  constructive; auto; try exact ttt.
  destruct (fmap[f] f0); auto.
Qed.
