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
   unique up to unique isomorphism -- [initial_unique] and [terminal_unique],
   with [initial_arrow_unique] / [terminal_arrow_unique] supplying the
   "unique" half -- this is no loss of generality, and it avoids any appeal to
   equality of objects.  [zero_object_unique] below is the corresponding
   statement for zero objects themselves.

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

(* Uniqueness of the zero object (Mac Lane, CWM 2nd ed., §I.5, p. 20).

   Two [ZeroObject] structures on C are related by an isomorphism of their
   underlying objects. Because a zero object is simultaneously terminal and
   initial, either half supplies the isomorphism. We take the terminal side as
   the representative, matching the convention used by [zero_mor] above, and
   record the initial-side reading separately; [zero_object_unique_compat]
   below proves the two readings agree. *)
Program Definition zero_object_unique {C : Category} (Z1 Z2 : ZeroObject C) :
  @terminal_obj C (@zero_terminal C Z1) ≅ @terminal_obj C (@zero_terminal C Z2) :=
  terminal_unique (@zero_terminal C Z1) (@zero_terminal C Z2).

(* The same statement read through the chosen initial objects. *)
Program Definition zero_object_unique_initial {C : Category}
      (Z1 Z2 : ZeroObject C) :
  @initial_obj C (@zero_initial C Z1) ≅ @initial_obj C (@zero_initial C Z2) :=
  initial_unique (@zero_initial C Z1) (@zero_initial C Z2).

(* The two readings agree: transporting along [zero_coincide] turns one into
   the other, so the choice of representative above is immaterial.  The square

       0₁ ---- zero_object_unique_initial ----> 0₂
        |                                        |
   zero_coincide Z1                      zero_coincide Z2
        v                                        v
       1₁ ------- zero_object_unique --------> 1₂

   commutes for the cheapest possible reason: both composites are morphisms
   OUT OF the initial object 0₁, and [zero_unique] identifies any two of
   those.  Stating it is still worth the two lines, because it is the one
   claim about zero objects that neither uniqueness lemma above makes -- each
   of them is, on its own, a pure alias for the terminal or initial case. *)
Lemma zero_object_unique_compat {C : Category} (Z1 Z2 : ZeroObject C) :
  to (@zero_coincide C Z2) ∘ to (zero_object_unique_initial Z1 Z2)
    ≈ to (zero_object_unique Z1 Z2) ∘ to (@zero_coincide C Z1).
Proof. apply (@zero_unique C (@zero_initial C Z1)). Qed.

(* An arrow between the underlying objects of two zero objects is unique, so
   the isomorphism above is canonical -- the "up to a UNIQUE isomorphism" half
   of the statement, inherited from the terminal side. *)
Corollary zero_object_arrow_unique {C : Category} (Z1 Z2 : ZeroObject C)
      (f g : @terminal_obj C (@zero_terminal C Z1)
               ~> @terminal_obj C (@zero_terminal C Z2)) : f ≈ g.
Proof. apply (@one_unique C (@zero_terminal C Z2)). Qed.

(* Riehl, CTiC, Exercise 1.6.i.  If there is ANY morphism from a terminal
   object to an initial one, it is an isomorphism, and the two objects are
   then both zero objects.

   The proof is the degenerate case of the usual uniqueness argument.  The
   candidate inverse is the unique arrow `! : 0 ~> 1` supplied by
   terminality of 1 (equivalently `¡`, supplied by initiality of 0 -- they
   agree, being parallel arrows into a terminal object).  One round trip
   `f ∘ ! : 0 ~> 0` is an arrow OUT OF an initial object, so [zero_unique]
   identifies it with the identity; the other, `! ∘ f : 1 ~> 1`, is an
   arrow INTO a terminal object, so [one_unique] does.  Neither direction
   needs the arrow f to be anything in particular -- the hypothesis is
   used only for its existence. *)
Program Definition terminal_initial_arrow_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) :
  @terminal_obj C T ≅ @initial_obj C I := {|
  to   := f;
  from := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(* The same fact as a predicate on the given morphism. *)
Program Definition terminal_initial_arrow_is_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : IsIsomorphism f := {|
  two_sided_inverse := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(* Consequently a zero object can be DERIVED rather than posited.  The
   [zero_coincide] field of [ZeroObject] is data, and until now the only
   in-tree inhabitant (Instance/CMon/Biproduct.v) supplied [iso_id]
   because its two chosen objects were literally the same term.  This
   constructor produces the field from a single morphism 1 ~> 0, which is
   the practical form of the exercise: to know that a category with both
   an initial and a terminal object is pointed, it suffices to connect
   them in the harder direction. *)
Definition ZeroObject_from_arrow {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : ZeroObject C := {|
  zero_terminal := T;
  zero_initial  := I;
  zero_coincide := iso_sym (terminal_initial_arrow_iso T I f)
|}.
