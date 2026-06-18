Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The interval category 2 (the "walking arrow"). *)

(* nLab:      https://ncatlab.org/nlab/show/interval+category
   nLab:      https://ncatlab.org/nlab/show/walking+structure (walking morphism)
   Wikipedia: https://en.wikipedia.org/wiki/Posetal_category

   2 is the ordinal {0 < 1} regarded as a (thin / posetal) category: two
   objects 0, 1, their identities, and a single non-identity arrow 0 → 1.
   There is NO arrow 1 → 0.  Here the objects are named TwoX (= 0) and
   TwoY (= 1), and the non-identity arrow is TwoXY : TwoX ~> TwoY.

   2 is the "walking arrow": a functor 2 ⟶ C is exactly a choice of one
   morphism of C (the image of TwoXY), so functors out of 2 classify the
   morphisms of C, and the functor category [2, C] is the arrow category of
   C (objects = arrows of C, morphisms = commutative squares). *)

Inductive TwoObj : Set := TwoX | TwoY.

Inductive TwoHom : TwoObj → TwoObj → Set :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoIdX).
  - exact (f = TwoXY).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = TwoIdY).
Defined.

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(* The category 2 has two objects TwoX, TwoY, their identity morphisms, and
   one non-identity morphism TwoXY : TwoX ~> TwoY from the first to the
   second.  The hom-sets carry strict (Leibniz) equality via
   Morphism_equality, since 2 is thin (at most one arrow between objects). *)

Program Definition _2 : Category := {|
  obj     := TwoObj;
  hom     := TwoHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoX => TwoIdX
    | TwoY => TwoIdY
    end;
  compose := fun x y z (f : TwoHom y z) (g : TwoHom x y) =>
    match x, y, z with
    | TwoX, TwoX, TwoX => TwoIdX
    | TwoY, TwoY, TwoY => TwoIdY
    | TwoX, TwoX, TwoY => TwoXY
    | TwoX, TwoY, TwoY => TwoXY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition; auto with *. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition; auto with *. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.

Require Import Category.Instance.Sets.

(* A functor 2 ⟶ Sets is precisely a morphism of Sets; this one picks out the
   unique map (the empty function) from False to True, sending TwoXY there. *)

Program Definition _2_as_Set : _2 ⟶ Sets := {|
  fobj := fun x =>
    match x with
    | TwoX => {| carrier := False |}
    | TwoY => {| carrier := True |}
    end;
  fmap := fun x y f =>
    match x, y with
    | TwoY, TwoY => _
    | _, _       => _
    end
|}.
Next Obligation.
  construct.
  - repeat intro.
    contradiction.
  - equivalence.
Defined.
Next Obligation.
  construct.
  - repeat intro.
    exact True.
  - equivalence.
Defined.
Next Obligation.
  construct; auto.
Defined.
Next Obligation.
  construct; auto.
  - destruct x, y; simpl in *; auto with two_laws.
  - proper.
    destruct x, y; simpl in *; auto with two_laws.
Qed.
Next Obligation.
  destruct x; simpl in *; auto with two_laws.
  contradiction.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; auto with two_laws.
  contradiction.
Qed.
