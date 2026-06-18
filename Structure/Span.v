Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Roof.

Generalizable All Variables.

(* A span in C is a diagram of shape `x ← s → y`: two morphisms sharing a
   common domain (the apex, or "roof") s. Equivalently, it is a functor from
   the shape category Roof = (RNeg ← RZero → RPos) into C, so that a span is
   just an element of [Roof ⟶ C]. A span generalizes a morphism: there is no
   longer any asymmetry between source and target.

   nLab:      https://ncatlab.org/nlab/show/span
   Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)

   The apex RZero carries the shared domain, and the two legs out of RZero
   become the morphisms of the span:

                s = RZero
               /         \
            f /           \ g
             v             v
            x = RNeg     y = RPos
*)
Definition Span (C : Category) := Roof ⟶ C.

(* A cospan is the dual notion: a span in the opposite category, i.e. a
   diagram of shape `x → s ← y` (two morphisms sharing a common codomain).
   It is a functor out of the opposite shape category Roof^op.

   nLab:      https://ncatlab.org/nlab/show/cospan
   Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)#Cospans *)
Definition Cospan (C : Category) := Roof^op ⟶ C.

(* [ASpan f g] packages a concrete span `x ← S → y` from its apex S and its
   two legs [f : S ~> x] and [g : S ~> y] as a functor [Roof ⟶ C]. The
   object part sends the apex RZero to S and the feet RNeg, RPos to x, y; the
   morphism part sends the two non-identity Roof arrows ZeroNeg, ZeroPos to
   the legs f and g (all other arrows being identities). *)

Program Definition ASpan {C : Category} {S x y : C} (f : S ~> x) (g : S ~> y) :
  Roof ⟶ C := {|
  fobj := fun z => match z with
    | RNeg  => x          (* left foot  *)
    | RZero => S          (* apex       *)
    | RPos  => y          (* right foot *)
    end;
  fmap := fun z w _ => match z, w with
    | RNeg,  RNeg  => id[x]   (* IdNeg   *)
    | RZero, RNeg  => f       (* left leg  S ~> x  *)
    | RZero, RZero => id[S]   (* IdZero  *)
    | RZero, RPos  => g       (* right leg S ~> y  *)
    | RPos,  RPos  => id[y]   (* IdPos   *)
    | _,      _      => _       (* no other Roof arrows exist *)
    end
|}.
Next Obligation.
  destruct z, w; simpl; intuition idtac; auto with roof_laws.
Defined.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation.
  proper.
  destruct x0, y0; simpl; auto with roof_laws; reflexivity.
Qed.
Next Obligation.
  destruct x0; reflexivity.
Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with roof_laws;
  rewrite ?id_left, ?id_right;
  reflexivity.
Qed.
