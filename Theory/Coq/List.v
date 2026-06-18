Require Import Coq.Lists.List.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Maybe.

Generalizable All Variables.

Import ListNotations.
Import MonadNotations.

(** The list type as functor, applicative and monad *)

(* nLab: https://ncatlab.org/nlab/show/list+monad
   nLab: https://ncatlab.org/nlab/show/free+monoid
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   The functional-programming list type [list A] is, categorically, the
   underlying set of the free monoid on A: the coproduct of all finite
   powers of A, with concatenation [app] as multiplication and the empty
   list as unit.  The list monad is the monad induced by the free-monoid /
   forgetful adjunction Set <-> Mon: its unit is the singleton [ret x = [x]]
   and its multiplication is one level of concatenation
   [join = flatten : list (list A) → list A], so that
   [bind x f = flatten (map f x)].  Its Eilenberg-Moore algebras are
   exactly the monoids. *)

#[export]
Instance list_Functor : Functor list := {
  fmap := λ _ _ f, List.map f;
}.

Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint zipWith `(f : a → b → c) (xs : list a) (ys : list b) : list c :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' => f x y :: zipWith f xs' ys'
  end.

(* nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   An applicative functor is a lax monoidal endofunctor (with strength) on
   the cartesian closed category of types, where [pure] is the unit map and
   [ap] is derived from the product map [μ : F x × F y → F (x × y)].

   There are two standard applicative structures on lists.  The one below
   is the positional ZipList structure, where [ap] zips functions against
   arguments via [zipWith id] (i.e. zipWith ($)).  The lawful ZipList
   requires [pure x = repeat x] (an infinite stream) so that
   [pure id <*> v = v]; with [pure x = [x]] the identity law fails because
   the zip truncates to the shorter list.  The lawful, cartesian-product
   structure that agrees with the list monad is [List_Applicative] below. *)
#[export]
Instance list_Applicative : Applicative list := {
  pure := λ _ x, [x];
  ap := λ _ _ f x, zipWith id f x;
}.

(* The [Alternative] instance exposes the underlying free-monoid structure of
   lists: [empty = []] is the monoid unit and [choose = app] is concatenation
   (the monoid multiplication).
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid *)
#[export]
Program Instance list_Alternative : Alternative list := {
  empty := λ _, [];
  choose := List.app;
}.

(* [flatten] is the multiplication (join) of the list monad: it concatenates
   a list-of-lists into a single list by repeated [app], i.e. the monad
   multiplication μ : list (list A) → list A of the free-monoid monad.
   nLab: https://ncatlab.org/nlab/show/list+monad *)
Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

(* [mapM]/[forM] is the applicative traversal of a list (Haskell's
   [traverse]/[mapM]): it threads the effect [m] through the list using the
   lax-monoidal structure of [m], witnessing that [list] is a traversable
   functor.  Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor *)
Fixpoint mapM `{Applicative m} {A B : Type} (f : A → m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition concatMapM `{Applicative m} {A B : Type}
  (f : A → m (list B)) (l : list A) : m (list B) :=
  fmap flatten (mapM f l).

(* nLab: https://ncatlab.org/nlab/show/list+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)#The_list_monad

   The (free-monoid) list monad: unit [ret x = [x]] is the singleton, and
   [bind x f = flatten (map f x)] is map-then-join.  The cartesian-product
   applicative [List_Applicative] below is the one induced by this monad
   (ap fs xs = bind fs (fun f => bind xs (fun x => [f x]))). *)
#[export]
Instance list_Monad : Monad list := {
  ret := λ _ x, [x];
  bind := λ _ _ x f, flatten (map f x)
}.

Definition forM `{Applicative m} {A B : Type} (l : list A) (f : A → m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Applicative m} {A B : Type} (f : A → m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
  end.

Definition forM_ `{Applicative m} {A B : Type} (l : list A) (f : A → m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A B : Type}
  (f : A → B → m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM `{Monad m} {A B : Type}
  (s : A) (l : list B) (f : A → B → m A) : m A := foldM f s l.

Definition foldrM `{Monad m} {A B : Type}
  (f : B → A → m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM `{Monad m} {A B : Type}
  (s : A) (l : list B) (f : B → A → m A) : m A := foldrM f s l.

Fixpoint replicateM_ `{Monad m} (n : nat) (x : m unit) : m unit :=
  match n with
  | O => pure tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM `{Monad m} {A : Type} (P : A → A → m bool)
  (z : A) (l : list A) : m (list A) :=
  match l with
  | nil => pure (cons z nil)
  | cons x xs =>
    b <- P x z ;;
    if (b : bool)
    then cons x <$> insertM P z xs
    else pure (cons z (cons x xs))
  end.

Arguments insertM {m H A} P z l : simpl never.

(* [concat] is the monad multiplication [flatten] under its conventional
   name; [concatMap f = flatten ∘ map f] is exactly Kleisli extension /
   [bind] for the list monad with its arguments flipped.
   nLab: https://ncatlab.org/nlab/show/list+monad *)
Definition concat {A} : list (list A) → list A := flatten.
Definition concatMap {A B} (f : A → list B) : list A → list B :=
  flatten ∘ map f.

Fixpoint lookup `{EqDec a} {b} (dflt : b) (v : list (a * b)) (x : a) : b :=
  match v with
  | nil => dflt
  | cons (k, v) xs =>
    if eq_dec k x
    then v
    else lookup dflt xs x
  end.

Fixpoint maybeLookup `{EqDec a} {b} (v : list (a * b)) (x : a) : Maybe b :=
  match v with
  | (k, v) :: xs =>
    if eq_dec k x
    then Just v
    else maybeLookup xs x
  | _ => Nothing
  end.

Definition listToMaybe `(xs : list a) : Maybe (list a) :=
  match xs with
    | [] => Nothing
    | _  => Just xs
  end.

Definition maybeToList `(mx : Maybe a) : list a :=
  match mx with
  | Just x => [x]
  | Nothing   => []
  end.

Definition olast `(l : list a) : Maybe a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Just x) xs
      end in
  go Nothing l.

Definition oends {a} (l : list a) : Maybe (a + (a * a)) :=
  match l with
  | [] => Nothing
  | x :: xs =>
      match olast xs with
      | Nothing => Just (Datatypes.inl x)
      | Just y => Just (Datatypes.inr (x, y))
      end
  end.

(*
Definition exist_in_cons : forall {A} {a} {l : list A},
  {x : A | List.in x l} → {x : A | List.in x (a :: l)}.
Proof.
  move=> A a l.
  case=> x H.
  exists x.
  rewrite in_cons.
  by apply/orP; right.
Defined.

Definition list_membership {a : eqType} (l : list a) :
  list { x : a | x \in l } :=
  let fix go l :=
      match l with
      | nil => nil
      | cons x xs =>
          exist _ x (mem_head _ xs) :: map exist_in_cons (go xs)
      end in
  go l.
*)

Fixpoint init {a : Type} (x : a) (l : list a) :=
  match l with
    | nil => nil
    | cons y nil => [x]
    | cons y ys => x :: init y ys
  end.

(*
Fixpoint maybe_nth {a} (v : list a) i {struct i} :=
  match v with
  | [] => Nothing
  | x :: s' =>
      match i with
      | 0 => Just x
      | n'.+1 => maybe_nth s' n'
      end
  end.

Fixpoint apply_nth {a} (def : a) (v : list a) i (f : a → a) {struct i} :=
  if v is x :: v'
  then if i is i'.+1
       then x :: apply_nth def v' i' f
       else f x :: v'
  else ncons i def [def].
*)

Definition forFold {A B : Type} (b : B) (v : list A) (f : B → A → B) : B :=
  fold_left f v b.

Definition forFoldr {A B : Type} (b : B) (v : list A) (f : A → B → B) : B :=
  fold_right f b v.

(*
Definition foldl_with_index
  {A B : Type} (f : nat → B → A → B) (b : B) (v : list A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => go n.+1 ys (f n z y)
      end in
  go 0 v b.

Definition foldr_with_index
  {A B : Type} (f : nat → A → B → B) (b : B) (v : list A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => f n y (go n.+1 ys z)
      end in
  go 0 v b.
*)

Definition catMaybes {a} (l : list (Maybe a)) : list a :=
  (fun f => fold_right f [] l) (fun mx rest =>
    match mx with
    | Some x => x :: rest
    | None => rest
    end).

Fixpoint mapAccumL {A X Y : Type} (f : A → X → (A * Y))
  (s : A) (v : list X) : A * list Y :=
  match v with
  | nil => (s, nil)
  | x :: xs =>
    let (s', y) := f s x in
    let (s'', ys) := mapAccumL f s' xs in
    (s'', y :: ys)
  end.

(*
Definition getBy {a} (p : a → bool) (xs : list a) : Maybe a :=
  (fun f => foldl f Nothing xs) (fun acc x =>
    match acc with
    | Just y => Just y
    | Nothing =>
      if p x
      then Just x
      else Nothing
    end).

Definition sumlist : list nat → nat := foldl addn 0.

Definition safe_nth {a} (xs : list a) (n : nat) (H : n < size xs) : a.
Proof.
  elim: xs => [|x xs IHxs] in n H *.
    reflexivity.
  elim: n => [|n IHn] in IHxs H *.
    exact: x.
  simpl in H.
  apply: IHn.
    move=> n0 H0.
    apply: IHxs.
    exact: H0.
  by ordered.
Defined.

Definition safe_hd {a} (xs : list a) : 0 < size xs → a.
Proof. case: xs => //. Defined.

Arguments safe_hd [a] xs H.

Definition safe_last {a} (xs : list a) : 0 < size xs → a.
Proof.
  case: xs => [//|y ys] /= *.
  exact: (last y ys).
Defined.

Arguments safe_last [a] xs H.

Fixpoint span {a} (p : a → bool) (l : list a) : (list a * list a) :=
  match l with
  | nil => (nil, nil)
  | x :: xs =>
    if p x
    then let: (ys,zs) := span p xs in (x::ys,zs)
    else (nil,l)
  end.

Program Fixpoint groupBy {a} (p : a → a → bool) (l : list a)
  {measure (size l)} : list (list a) :=
  match l with
  | [] => nil
  | x :: xs => let: (ys, zs) := span (p x) xs in
               (x :: ys) :: groupBy p zs
  end.
Obligation 1.
  clear groupBy.
  rename Heq_anonymous into Heqe.
  move: ys zs Heqe.
  elim: xs => [|w ws /= IHws] ys zs /=.
    by invert.
  case: (p x w) => /=; last by invert.
  case: (span (p x) ws) => [bs cs] in IHws *.
  invert; subst.
  specialize (IHws bs cs refl_equal).
  move/ltP in IHws.
  apply/ltP.
  exact/leqW.
Qed.

Definition partition {a} (p : a → bool) : list a → list a * list a :=
  foldr (fun x acc =>
           if p x
           then (x :: fst acc, snd acc)
           else (fst acc, x :: snd acc)) ([], []).

Definition map_fst_filter_snd :
  forall (a b : eqType) (i : b) (xs : list (a * b)),
  all (fun x => (x, i) \in xs) [list fst x | x <- xs & snd eq_dec x i].
Proof.
  move=> a b i xs.
  apply/allP => x /mapP[[x1 y1]].
  by rewrite mem_filter => /= /andP [/eqP/=-> pIxs ->].
Qed.

Fixpoint insert {a} (P : a → a → bool) (z : a) (l : list a) : list a :=
  if l is x :: xs
  then if P x z
       then x :: insert P z xs
       else z :: x :: xs
  else [z].
Arguments insert {a} P z l : simpl never.

Fixpoint sortBy {a} (p : a → a → bool) (l : list a) : list a :=
  match l with
  | [] => nil
  | x :: xs => insert p x (sortBy p xs)
  end.

Fixpoint sublist_impl_cons (a : eqType) (x : a) xs s :
  sublist (x :: xs) s → sublist xs s.
Proof.
  elim: s => //= [z zs IHzs].
  case: xs => // [y ys] in IHzs *.
  case: (eq_dec x z).
    case: (eq_dec y z).
      exact: sublist_impl_cons.
    exact.
  case: (eq_dec y z).
    move=> Hsub.
    specialize (IHzs Hsub).
    apply: sublist_impl_cons.
    exact IHzs.
  exact.
Qed.

Fixpoint between_all `(R : rel a) (xs : list a) : bool :=
  if xs is y :: ys
  then all (R y) ys && between_all R ys
  else true.
*)

(* [List_Functor] repeats [list_Functor] above; both define [fmap = map] and
   are therefore definitionally equal.  Being declared last, this instance is
   the one typeclass resolution selects by default. *)
#[export]
Instance List_Functor : Functor list := {
  fmap := map
}.

(* [list_ap] is the cartesian-product application: it applies every function
   in [fs] to every element of [xs], realizing the lax-monoidal product map
   μ : list (A → B) × list A → list B of the standard list applicative.
   nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor *)
Fixpoint list_ap {A B} (fs: list (A → B)) (xs: list A)
  : list B :=
  match fs with
  | f :: fs' => map f xs ++ list_ap fs' xs
  | _ => nil
  end.

(* The lawful, cartesian-product list applicative, induced by [list_Monad]:
   it satisfies the four applicative laws (identity, composition,
   homomorphism, interchange), unlike the ZipList-style [list_Applicative]
   above.  Declared last, it is the instance resolution selects by default. *)
#[export]
Instance List_Applicative : Applicative list := {
  pure := fun _ x => [x];
  ap   := @list_ap
}.

From Coq Require Import Relations ROrderedType.

Require Export Coq.Lists.List.

Import ListNotations.

Fixpoint insert {a} (P : a → a → bool) (z : a) (l : list a) : list a :=
  match l with
  | x :: xs => if P x z
               then x :: insert P z xs
               else z :: x :: xs
  | _ => [z]
  end.
Arguments insert {a} P z l : simpl never.

Fixpoint sortBy {a} (p : a → a → bool) (l : list a) : list a :=
  match l with
  | [] => nil
  | x :: xs => insert p x (sortBy p xs)
  end.
