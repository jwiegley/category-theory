Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Cartesian monoidal structure on the walking arrow 2.

    The interval category [_2] is thin (posetal): at most one morphism between
    any two objects, with hom-setoids under strict equality [Morphism_equality].
    Regarded as the ordinal {TwoX < TwoY}, it has all finite meets, hence finite
    products, and the top element TwoY is terminal.  Feeding the resulting
    [Cartesian] + [Terminal] data to the cartesian-to-monoidal bridge
    [Cartesian_Monoidal] (tensor := ×, unit := 1) yields the cartesian monoidal
    structure [Two_Monoidal].

    Every coherence law is an equation between parallel morphisms of a thin
    category; [two_thin] below says any two such morphisms coincide, so each
    obligation is discharged uniformly. *)

(* Any two parallel morphisms of [_2] are equal: the category is thin. *)
Lemma two_thin {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof.
  pose proof (TwoHom_inv _ _ f) as Hf.
  pose proof (TwoHom_inv _ _ g) as Hg.
  destruct x, y; simpl in *; try contradiction.
  - now rewrite Hf, Hg.
  - now rewrite Hf, Hg.
  - now rewrite Hf, Hg.
Qed.

(* The binary meet (product object): TwoX is the bottom, TwoY the top. *)
Definition two_meet (x y : TwoObj) : TwoObj :=
  match x with
  | TwoX => TwoX
  | TwoY => y
  end.

(* First projection  meet x y ~> x. *)
Definition two_exl (x y : TwoObj) : TwoHom (two_meet x y) x :=
  match x as x0 return TwoHom (two_meet x0 y) x0 with
  | TwoX => TwoIdX
  | TwoY => match y as y0 return TwoHom (two_meet TwoY y0) TwoY with
            | TwoX => TwoXY
            | TwoY => TwoIdY
            end
  end.

(* Second projection  meet x y ~> y. *)
Definition two_exr (x y : TwoObj) : TwoHom (two_meet x y) y :=
  match x as x0 return TwoHom (two_meet x0 y) y with
  | TwoX => match y as y0 return TwoHom (two_meet TwoX y0) y0 with
            | TwoX => TwoIdX
            | TwoY => TwoXY
            end
  | TwoY => match y as y0 return TwoHom (two_meet TwoY y0) y0 with
            | TwoX => TwoIdX
            | TwoY => TwoIdY
            end
  end.

(* Pairing  x ~> meet y z, given x ~> y and x ~> z. *)
Definition two_fork (x y z : TwoObj)
  (f : TwoHom x y) (g : TwoHom x z) : TwoHom x (two_meet y z).
Proof.
  destruct x.
  - destruct (two_meet y z); [ exact TwoIdX | exact TwoXY ].
  - destruct y.
    + exact (False_rect _ (TwoHom_Y_X_absurd f)).
    + destruct z.
      * exact (False_rect _ (TwoHom_Y_X_absurd g)).
      * exact TwoIdY.
Defined.

(* Binary products on 2 given by meets. *)
Program Instance Two_Cartesian : @Cartesian _2 := {|
  product_obj := two_meet;
  fork := two_fork;
  exl := two_exl;
  exr := two_exr
|}.
Next Obligation.
  split; intros; try split; apply two_thin.
Qed.

(* The unique morphism  x ~> TwoY  into the top object. *)
Definition two_one (x : TwoObj) : TwoHom x TwoY :=
  match x with
  | TwoX => TwoXY
  | TwoY => TwoIdY
  end.

(* TwoY is terminal in 2. *)
Program Instance Two_Terminal : @Terminal _2 := {|
  terminal_obj := TwoY;
  one := two_one
|}.
Next Obligation. apply two_thin. Qed.

(* The cartesian monoidal structure on 2: tensor := meet, unit := TwoY. *)
Definition Two_Monoidal : @Monoidal _2 :=
  @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal.
