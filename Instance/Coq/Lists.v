Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Coq.
Require Import List.

Generalizable All Variables.

(** * Lists as the initial algebra of the list endofunctor over COQ *)

(* nLab:      https://ncatlab.org/nlab/show/inductive+type
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   The polynomial endofunctor [ListF A X := 1 + A × X] on COQ (Instance/Coq.v)
   has the type [list A] as its initial algebra.  The structure map
   [alg : 1 + A × list A ~> list A] is [nil]/[cons], and initiality is exactly
   the recursion principle of lists: for every [ListF A]-algebra
   [β : 1 + A × Y ~> Y] there is a unique algebra map [list A ~> Y], namely the
   fold (a [foldr]-style catamorphism) determined by [β].  Uniqueness is the
   list induction that any algebra map into [(Y, β)] agrees with the fold.

   This exhibits [list A] as the least fixed point [μ (ListF A)]; by Lambek's
   lemma (Theory/Lambek.v) the structure map is then an isomorphism
   [1 + A × list A ≅ list A].  The whole development stays within pointwise
   equality on COQ hom-sets and ordinary list induction, so it carries no
   axioms (in particular no functional extensionality). *)

(* Keep obligation handling explicit and predictable: the file builds functor
   and F-algebra-hom records whose remaining fields are commuting squares, and
   we want every one surfaced as its own obligation rather than silently
   discharged. *)
#[local] Obligation Tactic := idtac.

(* The list endofunctor [ListF A X = option (A * X) = 1 + A × X]. *)
Program Definition ListF (A : Type) : Coq ⟶ Coq := {|
  fobj := fun X => option (A * X)%type;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None => None
            | Some (a, x) => Some (a, f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality *)
  intros A X Y f g Hfg o.
  destruct o as [[a x]|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros A X o.
  destruct o as [[a x]|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros A X Y Z f g o.
  destruct o as [[a x]|]; reflexivity.
Qed.

(* The structure map of the list algebra: [None] is [nil] and [Some (a, l)] is
   [cons a l].  This is a [ListF A]-algebra on [list A]. *)
Definition alg (A : Type) : ListF A (list A) ~{Coq}~> list A :=
  fun o => match o with
           | None => @nil A
           | Some (a, l) => cons a l
           end.

(* The catamorphism (fold) determined by an algebra [β : 1 + A × Y ~> Y].  This
   is the carrier of the unique algebra map out of [(list A, alg A)]. *)
Fixpoint fold {A Y : Type} (beta : option (A * Y)%type -> Y)
              (l : list A) : Y :=
  match l with
  | nil => beta None
  | cons a l' => beta (Some (a, fold beta l'))
  end.

(* Any [ListF A]-algebra map [h : (list A, alg A) ~> (Y, β)] coincides with the
   fold determined by [β].  This is the uniqueness half of initiality, proven by
   induction on the list using the commuting-square hypothesis [Hh] at the two
   relevant argument shapes. *)
Lemma hom_is_fold {A Y : Type} (beta : option (A * Y)%type -> Y)
      (h : list A -> Y)
      (Hh : forall o, h (alg A o) = beta (fmap[ListF A] h o))
      (l : list A) : h l = fold beta l.
Proof.
  induction l as [|a l' IH].
  - apply (Hh None).
  - simpl.
    rewrite <- IH.
    apply (Hh (Some (a, l'))).
Qed.

(* The unique algebra map from [(list A, alg A)] to an arbitrary algebra [y],
   packaging the fold together with its commuting square. *)
Program Definition list_alg_hom (A : Type) (y : FAlg (ListF A))
  : (list A; alg A) ~{FAlg (ListF A)}~> y :=
  {| falg_hom := fold (`2 y) |}.
Next Obligation.
  (* fold ∘ alg ≈ β ∘ fmap fold, checked shape by shape *)
  intros A y o.
  destruct o as [[a l]|]; reflexivity.
Qed.

(* [list A] together with [alg A] is the initial [ListF A]-algebra: it is the
   terminal object of the opposite of the algebra category. *)
Program Definition list_initial (A : Type) : @Initial (FAlg (ListF A)) := {|
  terminal_obj := (list A; alg A);
  one := fun y => list_alg_hom A y
|}.
Next Obligation.
  (* uniqueness: any two algebra maps out of [(list A, alg A)] agree, since each
     coincides with the fold determined by the target algebra *)
  intros A x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro l; simpl.
  rewrite (hom_is_fold (`2 x) hf Hf l).
  rewrite (hom_is_fold (`2 x) hg Hg l).
  reflexivity.
Qed.
