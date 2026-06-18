Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** * ParE: partial functions with monoidal errors over Coq Types *)

(* nLab:      https://ncatlab.org/nlab/show/exception+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)#The_Either_monad

   [ParE] is the Kleisli category of the *exception* (a.k.a. error) monad
   [T A := E + A] on Coq [Type]s, where the error type [E] carries a [Monoid]
   structure so that errors can be combined. A morphism A ~> B is a total
   function A → E + B, with [inl e] reporting an error [e] and [inr b] a
   successful result [b]. Identity is [inr] (the monad's [return]) and
   composition is Kleisli composition (the monad's [bind]), realized by
   [sum_bind] below: [inl e] short-circuits, propagating the error, while
   [inr b] feeds [b] to the next function.

   The Maybe/partiality monad (see Instance/Coq/Par.v) is the special case
   [E = unit]; here [E] is an arbitrary monoid, so an error carries typed
   information rather than mere undefinedness, and several errors arising "in
   parallel" (e.g. in the cartesian [fork] below) are merged with the monoid
   product [⊗], the empty error being [mempty].

   Crucially, the homset equivalence here is *error irrelevance*: two
   morphisms agree at an input [x] when they return equal [inr] values, or
   when they both return *some* [inl] error (regardless of which). Identifying
   all errors is what makes [bind] (which keeps the first error) and parallel
   error-merging (which uses [⊗]) cohere into a category and a cartesian
   structure. A finer "error compatibility" relation — two errors are
   equivalent when both are parts of a common error — would be desirable, but
   is not provably transitive for this encoding, so it is not used. *)

Section ParE.

Context {E : Type}.
Context `{Monoid E}.

(* Kleisli bind for the exception monad [E + -]: an incoming error [inl x] is
   propagated unchanged, while a value [inr y] is fed to the continuation [f]. *)
Definition sum_bind {A B : Type} (f : A → E + B) (o : E + A) : E + B :=
  match o with
  | Datatypes.inl x => Datatypes.inl x
  | Datatypes.inr y => f y
  end.

Ltac bust x := destruct (x _); subst; auto; try tauto.

Program Definition ParE : Category := {|
  obj     := Type;
  hom     := λ A B, A ~> E + B;
  homset  := λ _ _, {|
    equiv := λ f g, ∀ x,
      match f x, g x return Type with
      | Datatypes.inr x, Datatypes.inr y => x = y
      | Datatypes.inl _, Datatypes.inl _ => True
      | _, _ => False
      end
  |};
  id      := λ _, Datatypes.inr;
  compose := λ _ _ _ f g, sum_bind f ∘ g
|}.
Next Obligation.
  equivalence.
  - bust x.
  - specialize (X x0).
    bust y; bust x.
  - specialize (X x0).
    specialize (X0 x0).
    bust x; bust y.
Qed.
Next Obligation.
  proper.
  unfold sum_bind.
  specialize (X0 x2).
  bust x1; bust y1.
  specialize (X y3).
  bust x0; bust y0.
Qed.
Next Obligation.
  unfold sum_bind.
  bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust h; bust g; bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust h; bust g; bust f.
Qed.

(* The terminal object is the empty type [False]: there is no [inr] value to
   return, so the unique morphism [one] is the always-error map [inl mempty].
   It is unique by error irrelevance, since any two error-valued maps agree. *)
#[export] Program Instance ParE_Terminal : @Terminal ParE := {
  terminal_obj := False;
  one := λ _ _, Datatypes.inl mempty
}.
Next Obligation.
  destruct (f x0), (g x0); try contradiction; auto.
Qed.

(* The categorical product is the product of pointed sets: on the realizations
   [E + x], [E + y] it is their cartesian product with the both-error pair
   merged into the new basepoint, whose underlying non-error set is
   [(x * y) + x + y] (both-defined, left-defined, right-defined). [fork] keeps
   both results when both succeed and merges the two errors with [⊗] when both
   fail; [exl]/[exr] project, falling back to [mempty] when their component is
   absent. This is the product, NOT the smash product (which would collapse the
   wedge to [x * y]). *)
#[export] Program Instance Par_Cartesian : @Cartesian ParE := {
  product_obj := λ x y, (x * y) + x + y;
  fork := λ _ _ _ f g x,
      match f x, g x with
        | Datatypes.inr a, Datatypes.inr b =>
            Datatypes.inr (Datatypes.inl (Datatypes.inl (a, b)))
        | Datatypes.inr a, Datatypes.inl _ =>
            Datatypes.inr (Datatypes.inl (Datatypes.inr a))
        | Datatypes.inl _, Datatypes.inr b =>
            Datatypes.inr (Datatypes.inr b)
        | Datatypes.inl e, Datatypes.inl e' =>
            Datatypes.inl (e ⊗ e')
      end;
  exl  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (a, _)) => Datatypes.inr a
      | Datatypes.inl (Datatypes.inr a) => Datatypes.inr a
      | _ => Datatypes.inl mempty
      end;
  exr  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (_, b)) => Datatypes.inr b
      | Datatypes.inr b => Datatypes.inr b
      | _ => Datatypes.inl mempty
      end;
}.
Next Obligation. proper; congruence. Qed.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  proper.
  specialize (X x2).
  specialize (X0 x2).
  bust x0; bust x1; bust y0; bust y1.
Qed.
Next Obligation.
  unfold sum_bind.
  repeat split; intros.
  - specialize (X x0).
    bust h; bust f; bust g.
  - specialize (X x0).
    bust h; bust f; bust g.
  - destruct X.
    specialize (y0 x0).
    specialize (y1 x0).
    bust h; bust f; bust g;
    destruct s; subst; auto; try tauto;
    destruct s; subst; auto; try tauto;
    destruct p; subst; auto; try tauto.
Qed.

(* nLab:      https://ncatlab.org/nlab/show/smash+product
   Wikipedia: https://en.wikipedia.org/wiki/Smash_product

   [ParE] is not cartesian closed. It is, however, closed for a *different*
   monoidal product: the smash product [x * y] (the cartesian product with the
   whole wedge collapsed to the error), which makes the underlying category of
   pointed objects symmetric monoidal closed. That tensor and its closure are
   not formalized here; this remark only records the structure that exists. *)

(* The initial object is again the empty type [False], but now read as the
   *source*: a morphism out of [False] is given by [False_rect], vacuously. *)
#[export] Program Instance Par_Initial : Initial ParE := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

(* The coproduct is the disjoint sum [sum]: [fork] (the copairing) dispatches
   on the tag, and the injections [exl]/[exr] are total, hence always [inr]. *)
#[export] Program Instance Par_Cocartesian : @Cocartesian ParE := {
  product_obj := sum;
  fork := λ _ _ _ f g x,
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Datatypes.inr (Datatypes.inl p);
  exr  := λ _ _ p, Datatypes.inr (Datatypes.inr p)
}.
Next Obligation.
  proper.
  - specialize (X a).
    bust x0; bust y0.
  - specialize (X0 b).
    bust x1; bust y1.
Qed.
Next Obligation.
  split; intros.
  - split; intros.
    + specialize (X (Datatypes.inl x0)).
      bust h.
    + specialize (X (Datatypes.inr x0)).
      bust h.
  - destruct x0; firstorder.
Qed.

End ParE.
