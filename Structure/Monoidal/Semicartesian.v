Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section SemicartesianMonoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/semicartesian+monoidal+category
   Wikipedia: no dedicated article; the notion is described under
   https://en.wikipedia.org/wiki/Cartesian_monoidal_category

   A semicartesian (also affine) monoidal category is a monoidal category
   whose unit object I is terminal. Spelled out in this library's notation,
   that is the pair of conditions

       eliminate      : x ~> I             (a map into I for every x),
       unit_terminal  : f ≈ g              (any two x ~> I agree),

   so that I has exactly one map from each object: it is terminal. It is
   strictly weaker than cartesian monoidal, where the tensor is the
   categorical product; here only the discard maps into I are guaranteed,
   not the diagonals (cartesian = semicartesian + coherent diagonals). The
   internal logic is affine logic: weakening (discarding) but not in general
   contraction (copying).

   The terminality of I equips every tensor with projection maps, defined
   exactly as on nLab from a discard on one factor and the matching unitor,

       proj_left  = rho    ∘ (id ⨂ eliminate) : x ⨂ y ~> x,
       proj_right = lambda ∘ (eliminate ⨂ id) : x ⨂ y ~> y. *)

Class SemicartesianMonoidal `{@Monoidal C} := {
  (* the discard / projection-to-unit map, the unique x ~> I *)
  eliminate {x} : x ~> I;

  (* uniqueness of maps into I, i.e. I is terminal (up to ≈) *)
  unit_terminal {x} (f g : x ~> I) : f ≈ g;

  (* left  projection x ⨂ y ~> x: discard y, then the right unitor *)
  proj_left  {x y} : x ⨂ y ~> x := unit_right ∘ id ⨂ eliminate;
  (* right projection x ⨂ y ~> y: discard x, then the left  unitor *)
  proj_right {x y} : x ⨂ y ~> y := unit_left  ∘ eliminate ⨂ id
}.

(* Discarding after any map is discarding: eliminate is natural, since both
   sides are maps A ~> I and I is terminal. *)

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

End SemicartesianMonoidal.

Require Import Category.Structure.Terminal.

(* The two directions below witness that "semicartesian monoidal" and "the
   unit I is terminal" are the same condition, packaged as a Terminal
   structure on I and as a SemicartesianMonoidal structure respectively. Cf.
   Wikipedia, https://en.wikipedia.org/wiki/Cartesian_monoidal_category :
   "in any such category, the terminal object is the monoidal unit." *)

(* Semicartesian monoidal ==> I is a terminal object, with eliminate as the
   unique arrow and unit_terminal as its uniqueness proof. *)

Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
        `{@SemicartesianMonoidal C _} : @Terminal C := {|
  terminal_obj := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

Import EqNotations.

(* Conversely, a monoidal category whose terminal object 1 coincides with the
   unit object I (the hypothesis Heq : 1 = I) is semicartesian monoidal:
   transport the unique arrow `one` along Heq to obtain eliminate, and
   transport one_unique to obtain unit_terminal. *)

Program Definition Terminal_SemicartesianMonoidal `{M : @Monoidal C}
        `{T : @Terminal C} (Heq : 1 = @I C M) :
  @SemicartesianMonoidal C _ := {|
  eliminate := fun x => rew Heq in one;
  unit_terminal := fun x f g =>
    _ (one_unique (rew <- Heq in f) (rew <- Heq in g))
|}.
Next Obligation.
  unfold eq_rect_r, eq_rect, eq_sym in x.
  destruct Heq.
  assumption.
Defined.
