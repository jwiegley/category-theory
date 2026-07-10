Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Zero objects and zero morphisms *)

(* nLab:      https://ncatlab.org/nlab/show/zero+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   A zero object in a category C is an object that is at once initial and
   terminal (nLab; Wikipedia calls it a "null object").  In this setoid-based
   library we do not demand that one chosen object literally play both roles:
   [ZeroObject] packages a terminal structure, an initial structure, and an
   isomorphism [zero_coincide] between the chosen initial object 0 and the
   chosen terminal object 1.  Since initial (resp. terminal) objects are
   unique up to unique isomorphism, this is no loss of generality, and it
   avoids any appeal to equality of objects.

   Every pair of objects x, y then acquires a canonical zero morphism
   x ~> y, obtained by tunnelling through the zero object:

       x ~> 1 ~> 0 ~> y

   first the unique map into 1, then the coincidence isomorphism read
   backwards, then the unique map out of 0.  Zero morphisms absorb
   composition on both sides ([zero_mor_left], [zero_mor_right]), and any
   morphism factoring through the zero object in this way is the zero
   morphism ([zero_mor_unique]). *)

Class ZeroObject (C : Category) := {
  zero_terminal : @Terminal C;
  zero_initial  : @Initial C;

  (* The chosen initial and terminal objects coincide up to isomorphism.
     Stating the coincidence as an iso, rather than as an equality of
     objects, keeps the notion setoid-honest and transportable. *)
  zero_coincide : @initial_obj C zero_initial ≅ @terminal_obj C zero_terminal
}.

(* A convenience name for the zero object itself.  We take the terminal
   side as the representative; [zero_coincide] carries us to the initial
   side whenever needed.  Note: the name [zero] belongs to Initial's
   accessor 0 ~> x, so the object gets the distinct name [zero_obj]. *)
Definition zero_obj {C : Category} `{Z : @ZeroObject C} : C :=
  @terminal_obj C zero_terminal.

(* The zero morphism x ~> y: into 1, across the coincidence iso, out of 0. *)
Definition zero_mor {C : Category} `{Z : @ZeroObject C} {x y : C} : x ~> y :=
  @zero C (@zero_initial C Z) y
    ∘ from (@zero_coincide C Z)
    ∘ @one C (@zero_terminal C Z) x.

(* Postcomposition absorbs: f ∘ 0 ≈ 0.  After reassociation the composite
   f ∘ zero is a morphism out of the initial object, so [zero_comp]
   collapses it to zero, and the zero morphism reassembles. *)
Lemma zero_mor_left {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : y ~> z) :
  f ∘ @zero_mor C Z x y ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite !comp_assoc.
  now rewrite (@zero_comp C (@zero_initial C Z) y z f).
Qed.

(* Precomposition absorbs: 0 ∘ f ≈ 0.  Dually, after reassociation the
   composite one ∘ f is a morphism into the terminal object, so [one_comp]
   collapses it to one. *)
Lemma zero_mor_right {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : x ~> y) :
  @zero_mor C Z y z ∘ f ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite <- !comp_assoc.
  now rewrite (@one_comp C (@zero_terminal C Z) x y f).
Qed.

(* Any morphism factoring through the zero object is the zero morphism:
   the leg into 1 is unique by [one_unique], and the leg out of 0 is
   unique by [zero_unique]. *)
Lemma zero_mor_unique {C : Category} `{Z : @ZeroObject C} {x y : C}
  (g : x ~> @terminal_obj C (@zero_terminal C Z))
  (h : @initial_obj C (@zero_initial C Z) ~> y) :
  (h ∘ from (@zero_coincide C Z)) ∘ g ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite (@one_unique C (@zero_terminal C Z) x g
             (@one C (@zero_terminal C Z) x)).
  rewrite (@zero_unique C (@zero_initial C Z) y h
             (@zero C (@zero_initial C Z) y)).
  reflexivity.
Qed.
