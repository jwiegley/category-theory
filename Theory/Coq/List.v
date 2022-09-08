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

Fixpoint mapM `{Applicative m} {A B : Type} (f : A → m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

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

Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

Definition concatMapM `{Applicative m} {A B : Type}
  (f : A → m (list B)) (l : list A) : m (list B) :=
  fmap flatten (mapM f l).

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
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else pure (cons z (cons x xs))
  end.

Arguments insertM {m H _ _ A} P z l : simpl never.

Definition concat {A} : list (list A) → list A := flatten.

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

(*
Lemma rcons_nil : forall a us (u : a), rcons us u = [] → False.
Proof. by move=> a us u; case: us => // [|? ?] in u *. Qed.
*)

Definition olast `(l : list a) : Maybe a :=
  let fix go res xs :=
      match xs with
      | nil => res
      | cons x xs => go (Just x) xs
      end in
  go Nothing l.

Lemma olast_last : forall a (u : a) us,
  olast (u :: us) = Just (last us u).
Proof.
  intros a u.
  induction us as [|x xs IHxs]; simpl; trivial.
  generalize dependent u.
  destruct xs as [|y ys]; intros.
  - reflexivity.
  - exact IHxs.
Qed.

Lemma olast_spec : forall a (u : a) us, olast (u :: us) = Nothing → False.
Proof.
  intros a u.
  induction us as [|x xs IHxs]; simpl; intros.
  - discriminate.
  - rewrite olast_last in H.
    rewrite olast_last in IHxs.
    destruct xs as [|y ys]; discriminate.
Qed.

(*
Lemma olast_rcons : forall a (u : a) us, olast (rcons us u) = Just u.
Proof.
  move=> a u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.
*)

Lemma olast_cons : forall a (x y : a) ys,
  olast (x :: y :: ys) = olast (y :: ys).
Proof.
  intros a x y.
  induction ys as [|? xs IHxs]; trivial.
Qed.

(*
Lemma olast_cons_rcons : forall a (z u : a) us,
  olast (z :: rcons us u) = Just u.
Proof.
  move=> a z u.
  elim=> //= [x xs IHxs].
  case: xs => // [|y ys] in IHxs *.
Qed.

Lemma olast_cat : forall a (x : a) xs ys,
  olast (ys ++ x :: xs) = olast (x :: xs).
Proof.
  intros a y xs ys.
  induction xs as [|z zs IHzs].
    rewrite cats1, olast_rcons.
  replace [y, z & zs] with ([y] ++ [z & zs]).
    rewrite catA !IHzs.
  reflexivity.
Qed.
*)

(*
Lemma olast_cat_rcons : forall a (x : a) xs ys,
  olast (ys ++ rcons xs x) = Just x.
Proof.
  move=> a y xs ys.
  elim: xs => /= [|z zs IHzs] in y ys *.
    by rewrite cats1 olast_rcons.
  rewrite olast_cat -cat1s.
  exact: IHzs.
Qed.

Definition oends a (l : list a) : Maybe (a + (a * a)).
Proof.
  case: l => [|x xs].
    exact: Nothing.
  case/lastP: xs => [|ys y].
    exact: Just (inl x).
  exact: Just (inr (x, y)).
Defined.

Lemma oends_spec a (l : list a) :
  match oends l with
  | Just (inr (x, y)) => head x l = x /\ last y l = y
  | Just (inl x)      => head x l = last x l
  | Nothing              => True
  end.
Proof.
  rewrite /oends.
  case: l => // [x xs].
  case/lastP: xs => //= [ys y].
  by rewrite last_rcons.
Qed.

Lemma last_leq : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs <= n → y <= z → last y xs <= n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_trans IHxs _.
Qed.

Lemma last_leq_ltn : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs < n → y <= z → last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma last_ltn : forall (z y : nat) (xs : list nat) (n : nat),
  last z xs < n → y <= z → last y xs < n.
Proof.
  move=> z y.
  elim=> //= [x xs IHxs].
  exact: leq_ltn_trans IHxs _.
Qed.

Lemma list_cons_nonzero : forall {a x} {xs l : list a},
  l = x :: xs → size l > 0.
Proof. by move=> a x xs l ->. Qed.

Definition exist_in_cons : forall {A : eqType} {a} {l : list A},
  {x : A | x \in l} → {x : A | x \in a :: l}.
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

Fixpoint init {a : Type} (x : a) (l : list a) :=
  match l with
    | nil => nil
    | cons y nil => [x]
    | cons y ys => x :: init y ys
  end.

Lemma Forall_head : forall A P (x : A) xs,
  List.Forall P (x :: xs) → P (head x xs).
Proof.
  move=> A P x.
  elim=> /= [|y ys IHys] H.
    by inv H.
  by inv H; inv H3.
Qed.

Lemma Forall_rcons_inv : forall a P (x : a) xs,
  List.Forall P (rcons xs x) → List.Forall P xs /\ P x.
Proof.
  move=> a P x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H2).
  inversion IHys.
  split=> //.
  constructor=> //.
Qed.

Lemma Forall_last : forall A P (x : A) xs,
  List.Forall P (x :: xs) → P (last x xs).
Proof.
  move=> A P x.
  elim/last_ind=> /= [|ys y IHys] H.
    by inv H.
  inv H.
  rewrite last_rcons.
  apply Forall_rcons_inv in H3.
  by inv H3.
Qed.

Lemma Forall_append : forall A (P : A → Prop) xs ys,
   List.Forall P xs /\ List.Forall P ys <-> List.Forall P (xs ++ ys).
Proof.
  move=> A P.
  elim=> [|x xs IHxs] /= ys.
    split.
      by move=> [H1 H2] //=.
    move=> H.
    split=> //.
  split.
    move=> [H1 H2] //=.
    constructor.
      by inversion H1.
    apply/IHxs.
    split=> //.
    by inversion H1.
  move=> H.
  split=> //.
    constructor.
      by inversion H.
    inversion H; subst.
    by move/IHxs: H3 => [? ?].
  inversion H; subst.
  by move/IHxs: H3 => [? ?].
Qed.

Lemma StronglySorted_inv_app : forall a R (l1 l2 : list a),
  StronglySorted R (l1 ++ l2)
    → StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  move=> a R.
  elim=> [|x xs IHxs] /= l2 H.
    split=> //.
    constructor.
  inversion H.
  specialize (IHxs l2 H2).
  inversion IHxs; subst.
  split=> //.
  constructor=> //.
  by move/Forall_append: H3 => [? ?].
Qed.

Lemma StronglySorted_skip : forall a R (y : a) a0 ys,
  StronglySorted R [y, a0 & ys] → StronglySorted R (y :: ys).
Proof.
  move=> a R y a0 ys H.
  elim: ys => [|z zs IHzs] in H *.
    by constructor; constructor.
  constructor.
    by constructor; inv H; inv H2; inv H1.
  by inv H; inv H3.
Qed.

Lemma StronglySorted_cat {A : Type} {xs ys : list A} {R : A → A → Prop}
  `{Transitive _ R} :
  StronglySorted R xs → StronglySorted R ys
    → (match olast xs, ys with
        | Just x, y :: _ => R x y
        | _, _ => True
        end)
    → StronglySorted R (xs ++ ys)%LIST.
Proof.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => //= [xs1 x1] in Hsort1 Hrel *.
  rewrite olast_rcons in Hrel.
  case: ys => [|y1 ys1] in Hsort2 Hrel *.
    by rewrite cats0.
  elim: xs1 => //= [|x2 xs2 IHxs2] in Hsort1 *.
    repeat constructor=> //.
    inv Hsort2.
    have: forall a : A, R y1 a → R x1 a.
      move=> a Ha.
      exact: transitivity Hrel Ha.
    move/List.Forall_impl.
    exact.
  inv Hsort1.
  specialize (IHxs2 H2).
  constructor=> {H2} //.
  apply Forall_append.
  split=> //.
  apply Forall_rcons_inv in H3.
  move: H3 => [_ H3].
  constructor.
    exact: transitivity H3 Hrel.
  move/StronglySorted_inv_app: IHxs2 => [_ IHxs2].
  inv IHxs2.
  have: forall a : A, R y1 a → R x2 a.
    move=> a Ha.
    exact: transitivity (transitivity H3 Hrel) Ha.
  move/List.Forall_impl.
  exact.
Qed.

Lemma StronglySorted_cat_cons
  {A : Type} {x y : A} {xs ys : list A} {R : A → A → Prop} `{Transitive _ R} :
  StronglySorted R (x :: xs) → StronglySorted R (y :: ys)
    → R (last x xs) y
    → StronglySorted R (x :: xs ++ y :: ys).
Proof.
  move=> Hsort1 Hsort2 Hrel.
  case/lastP: xs => /= [|xs1 x1] in Hsort1 Hrel *.
    constructor=> //.
    constructor=> //.
    inv Hsort2.
    have: forall a : A, R y a → R x a.
      move=> a Ha.
      exact: transitivity Hrel Ha.
    move/List.Forall_impl.
    exact.
  rewrite -cat_cons.
  apply: StronglySorted_cat => //.
  rewrite olast_cons_rcons.
  by rewrite last_rcons in Hrel.
Qed.

Lemma StronglySorted_cons_cons : forall a (R : a → a → Prop) x xs y ys,
  StronglySorted R (x :: xs ++ y :: ys) → R x y.
Proof.
  move=> a R x xs y ys H.
  elim: xs => [|z zs IHzs] /= in x y ys H *.
    by inv H; inv H3.
  apply: (IHzs x y ys).
  inv H.
  have H4 := H2.
  rewrite -cat_cons in H4.
  apply StronglySorted_inv_app in H4.
  inv H4.
  inv H2.
  constructor=> //.
  by inv H3.
Qed.

Lemma StronglySorted_rcons_inv : forall a R (x : a) xs,
  StronglySorted R (rcons xs x) → StronglySorted R xs.
Proof.
  move=> a R x.
  elim=> [|y ys IHys] /=.
    by invert.
  invert.
  specialize (IHys H1).
  constructor=> //.
  apply Forall_rcons_inv in H2.
  by inversion H2.
Qed.

Lemma Forall_rcons_rcons : forall a R `{Transitive _ R} (x : a) y z xs,
  List.Forall (R z) (rcons xs x) → R x y
    → List.Forall (R z) (rcons (rcons xs x) y).
Proof.
  move=> a R H x y z.
  elim=> [|w ws IHws] /=.
    constructor.
      by inv H0.
    constructor.
      inv H0.
      exact: transitivity H4 H1.
    by constructor.
  constructor.
    by inv H0.
  apply: IHws => //.
  by inv H0.
Qed.

Lemma Forall_ordered : forall a (R : a → a → Prop) `{Transitive _ R} x y xs,
  R x y → List.Forall (R y) xs → List.Forall (R x) xs.
Proof.
  move=> a R H x y xs H1 H2.
  have: forall a, R y a → R x a.
    move=> z H3.
    exact: transitivity H1 H3.
  move/List.Forall_impl.
  exact.
Qed.

Lemma StronglySorted_rcons_rcons : forall a R `{Transitive _ R} (x : a) y xs,
  StronglySorted R (rcons xs x) → R x y
    → StronglySorted R (rcons (rcons xs x) y).
Proof.
  move=> a R H x y.
  elim=> [|z zs IHzs] /=.
    by repeat constructor.
  constructor.
    inv H0.
   exact: (IHzs H4).
 inv H0.
 exact: Forall_rcons_rcons.
Qed.

Lemma StronglySorted_rcons_rcons_inv : forall a R (x y : a) xs,
  StronglySorted R (rcons (rcons xs x) y) → R x y.
Proof.
  move=> a R x y.
  elim=> [|z zs IHzs] /=.
    invert.
    by inv H2.
  invert.
  exact: IHzs H1.
Qed.

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

Definition forFold {A B : Type} (b : B) (v : list A) (f : B → A → B) : B :=
  foldl f b v.

Definition forFoldr {A B : Type} (b : B) (v : list A) (f : A → B → B) : B :=
  foldr f b v.

Definition foldl_with_index
  {A B : Type} (f : nat → B → A → B) (b : B) (v : list A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => go n.+1 ys (f n z y)
      end in
  go 0 v b.

Example ex_foldl_with_index_1 :
  foldl_with_index (fun n z x => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(2, 3); (1, 2); (0, 1)].
Proof. reflexivity. Qed.

Lemma foldl_cons : forall a (x : a) xs,
  foldl (fun us : list a => cons^~ us) [x] xs
    = foldl (fun us : list a => cons^~ us) [] [x & xs].
Proof. by move=> a x; elim. Qed.

Definition foldr_with_index
  {A B : Type} (f : nat → A → B → B) (b : B) (v : list A) : B :=
  let fix go n xs z :=
      match xs with
        | nil => z
        | y :: ys => f n y (go n.+1 ys z)
      end in
  go 0 v b.

Example ex_foldr_with_index_1 :
  foldr_with_index (fun n x z => (n, x) :: z) nil [1; 2; 3]
  eq_dec   [(0, 1); (1, 2); (2, 3)].
Proof. reflexivity. Qed.

Definition catMaybes {a} (l : list (Maybe a)) : list a :=
  (fun f => foldr f [] l) (fun mx rest =>
    if mx is Just x
    then x :: rest
    else rest).
*)

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

Lemma span_cat {a} (l : list a) : forall p l1 l2,
  (l1, l2) = span p l
    → l = l1 ++ l2 /\ all p l1 /\ (if l2 is x :: _ then ~~ (p x) else True).
Proof.
  move=> p.
  elim: l => /= [|x xs IHxs] l1 l2 Heqe.
    by inv Heqe.
  case E: (p x); rewrite E in Heqe.
    case S: (span p xs) => [l l0] in IHxs Heqe *.
    inv Heqe.
    move: (IHxs l l0 (refl_equal _)) => [? [? ?]].
    split; first by congr (_ :: _).
    split=> //.
    by apply/andP; split=> //.
  inv Heqe.
  split=> //.
  split=> //.
  by apply/negbT.
Qed.

Example span_ex1 :
  span (fun x => x < 10) [1; 5; 10; 15] = ([1; 5], [10; 15]).
Proof. reflexivity. Qed.

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

Example groupBy_ex1 :
  groupBy eq_op [1; 3; 3; 4; 5; 5; 9; 6; 8]
    = [[1]; [3; 3]; [4]; [5; 5]; [9]; [6]; [8]].
Proof. reflexivity. Qed.

Definition partition {a} (p : a → bool) : list a → list a * list a :=
  foldr (fun x acc =>
           if p x
           then (x :: fst acc, snd acc)
           else (fst acc, x :: snd acc)) ([], []).

Lemma partition_all {a} {p q : a → bool} (xs : list a) :
  all p xs → let: (ys, zs) := partition q xs in
              all (fun x => p x && q x) ys &&
              all (fun x => p x && ~~ q x) zs.
Proof.
  move=> H.
  elim: xs => //= [x xs IHxs] in H *.
  case: (partition q xs) => [ys zs] /= in IHxs *.
  move/andP: H => [H1 H2].
  specialize (IHxs H2).
  case E: (q x) => /=.
    by ordered.
  move/negbT in E.
  by ordered.
Qed.

Lemma perm_eq_nil : forall (a : eqType) (xs : list a),
  perm_eq [] xs → xs = [].
Proof.
  move=> a.
  elim=> //= [x xs IHxs].
  rewrite /perm_eq /=.
  move/andP => [H1 H2].
  rewrite eq_refl /= in H1.
  discriminate H1.
Qed.

Lemma all_perm : forall (a : eqType) (xs ys : list a),
  perm_eq xs ys → all^~ xs =1 all^~ ys.
Proof.
  move=> a xs ys H P.
  move/perm_eq_mem in H.
  by rewrite (eq_all_r H).
Qed.

Lemma all_catC {a} (P : pred a) (xs ys : list a) :
  all P (xs ++ ys) = all P (ys ++ xs).
Proof.
  case: xs => /= [|x xs] in ys *.
    by rewrite cats0.
  case: ys => // [|y ys].
    by rewrite cats0.
  by rewrite !all_cat /= andbA andbC.
Qed.

Lemma all_flip : forall A (P : rel A) (_ : symmetric P) x (xs : list A),
  all (P x) xs = all (P ^~ x) xs.
Proof.
  move=> A P H x.
  elim=> //= [y ys IHys].
  by rewrite -IHys H.
Qed.

Lemma all_all_cons : forall a (xs ys : list a) (x : a) (R : rel a),
  all (fun y : a => all (R y) (x :: xs)) ys =
  all (R ^~ x) ys && all (fun y : a => all (R y) xs) ys.
Proof.
  move=> a xs ys x R.
  elim: ys => // [y ys IHys].
  rewrite [all]lock -{1}lock /= -lock IHys /= -!andbA.
  congr (_ && _).
  by rewrite and_swap.
Qed.

Lemma all_all_cat : forall A (P : rel A) (xs ys zs : list A),
  all (fun x => all (P x) (xs ++ ys)) zs
    = all (fun x => all (P x) xs) zs && all (fun x => all (P x) ys) zs.
Proof.
  move=> A P xs ys.
  elim=> //= [z zs IHzs].
  rewrite IHzs all_cat.
  rewrite !andbA.
  congr (_ && _).
  rewrite -!andbA.
  congr (_ && _).
  by rewrite andbC.
Qed.

Lemma all_all_flip : forall A (P : rel A) (_ : symmetric P) (xs ys : list A),
  all (fun x => all (P x) ys) xs = all (fun x => all (P ^~ x) ys) xs.
Proof.
  move=> A P H.
  elim=> //= [z zs IHzs] ys.
  by rewrite -IHzs all_flip.
Qed.

Lemma perm_cat_cons (T : eqType) (x : T) : forall (s1 s2 : list_predType T),
  perm_eql (x :: s1 ++ s2) (s1 ++ x :: s2).
Proof.
  move=> s1 s2.
  apply/perm_eqlP.
  rewrite perm_eq_sym perm_catC cat_cons perm_cons perm_catC.
  exact: perm_eq_refl.
Qed.

Lemma perm_rem_cons (T : eqType) (x : T) : forall (s1 s2 : list_predType T),
  x \in s1 → perm_eql (rem x s1 ++ x :: s2) (s1 ++ s2).
Proof.
  move=> s1 s2 Hin.
  apply/perm_eqlP.
  rewrite perm_catC cat_cons perm_cat_cons perm_catC perm_cat2r perm_eq_sym.
  exact: perm_to_rem.
Qed.

Definition map_fst_filter_snd :
  forall (a b : eqType) (i : b) (xs : list (a * b)),
  all (fun x => (x, i) \in xs) [list fst x | x <- xs & snd eq_dec x i].
Proof.
  move=> a b i xs.
  apply/allP => x /mapP[[x1 y1]].
  by rewrite mem_filter => /= /andP [/eqP/=-> pIxs ->].
Qed.

Lemma has_size : forall (a : eqType) x (xs : list a), x \in xs → 0 < size xs.
Proof. move=> a x; elim=> //. Qed.

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

Example sortBy_ex1 :
  sortBy ltn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof. reflexivity. Qed.

Example sortBy_ex2 :
  sortBy gtn [1; 3; 5; 7; 9; 2; 4; 6; 8] = [9; 8; 7; 6; 5; 4; 3; 2; 1].
Proof. reflexivity. Qed.

Example sortBy_ex3 :
  sortBy (fun x y => false) [1; 3; 5; 7; 9; 2; 4; 6; 8] =
                            [1; 3; 5; 7; 9; 2; 4; 6; 8].
Proof. reflexivity. Qed.

Lemma Forall_insert : forall a (R : a → a → bool) `{Transitive _ R} x xs y,
  R x y → List.Forall (R x) xs → List.Forall (R x) (insert R y xs).
Proof.
  move=> a R H x xs y H1 H2.
  elim: xs => [|z zs IHzs] /= in H1 H2 *.
    rewrite /insert.
    by constructor.
  rewrite /insert /= -/insert.
  case E: (R z y).
    constructor.
      by inv H2.
    apply: IHzs => //.
    by inv H2.
  constructor=> //.
Qed.

Lemma StronglySorted_insert :
  forall a (R : a → a → bool) `{Transitive _ R} x xs,
  StronglySorted R xs → (forall y, ~~ R y x → R x y)
    → StronglySorted R (insert R x xs).
Proof.
  move=> a R H x xs H1 H2.
  elim=> [|y ys IHys] /= in H1 *.
    rewrite /insert.
    by constructor; constructor.
  rewrite /insert /= -/insert.
  case E: (R y x).
    constructor=> //.
    exact: Forall_insert.
  constructor.
    constructor=> //.
    constructor.
    apply/H2.
    by rewrite E.
  move/negbT/H2 in E.
  exact: (@Forall_ordered _ R H x y ys E H1).
Qed.

Lemma StronglySorted_impl_cons : forall a (R : a → a → bool) `{Transitive _ R}
  x y (ys : list a), StronglySorted R (x :: y :: ys) → R x (last y ys).
Proof.
  move=> a R H x y ys Hsort.
  elim: ys => [|z zs IHzs] /= in x y Hsort *.
    by inv Hsort; inv H3.
  apply: IHzs.
  inv Hsort; inv H2; inv H4.
  constructor=> //.
    constructor=> //.
  inv H3; inv H5.
  constructor=> //.
    by transitivity y.
  exact: (Forall_ordered H4).
Qed.

Lemma sortBy_sorted : forall a (R : a → a → bool) `{Transitive _ R} xs,
  (forall x y, ~~ R y x → R x y) → StronglySorted R (sortBy R xs).
Proof.
  move=> a R H xs H1.
  elim: xs => [|x xs IHxs] /=.
    by constructor.
  apply: StronglySorted_insert => //.
  exact: (H1 x).
Qed.

Lemma insert_all : forall a (P : a → bool) (R : a → a → bool) x xs,
  all P (insert R x xs) = P x && all P xs.
Proof.
  move=> a P R x.
  elim=> //= [u us IHus].
  rewrite /insert /= -/insert.
  case: (R u x) => //=.
  by rewrite IHus and_swap.
Qed.

Lemma sortBy_all : forall a (P : a → bool) (R : a → a → bool) xs,
  all P xs = all P (sortBy R xs).
Proof.
  move=> a P R.
  elim=> //= [u us IHus].
  by rewrite IHus insert_all.
Qed.

Lemma perm_cons_swap (T : eqType) (x y : T) : forall (xs : list_predType T),
  perm_eql (x :: y :: xs) (y :: x :: xs).
Proof.
  move=> xs; apply/perm_eqlP.
  rewrite -cat1s perm_catC cat_cons perm_cons perm_catC cat1s.
  exact: perm_eq_refl.
Qed.

Lemma insert_perm (T : eqType) P (x : T) : forall (xs : list_predType T),
  perm_eql (insert P x xs) (x :: xs).
Proof.
  elim=> //= [y ys IHys]; rewrite /insert.
  case: (P y x) => //=; apply/perm_eqlP.
  rewrite perm_eq_sym perm_cons_swap perm_cons perm_eq_sym -/insert.
  exact/perm_eqlP/IHys.
Qed.

Lemma insert_size : forall a P (x : a) xs,
  size (insert P x xs) = (size xs).+1.
Proof.
  move=> a P x xs.
  elim: xs => //= [y ys IHys].
  rewrite /insert /= -/insert.
  case: (P y x) => //=.
  by rewrite IHys.
Qed.

Lemma proj_rem_uniq (a b : eqType) (f : a → b) : forall x xs,
  uniq [list f i | i <- xs] → uniq [list f i | i <- rem x xs].
Proof. by move=> x xs; apply/sublist_uniq/map_sublist/rem_sublist. Qed.

Lemma in_proj : forall (a b : eqType) (x : a) (y : b) (xs : list (a * b)),
  (x \notin [list fst i | i <- xs]) ||
  (y \notin [list snd i | i <- xs]) → (x, y) \notin xs.
Proof.
  move=> a b x y.
  elim=> //= [z zs IHzs] H1.
  move/orP: H1 => [H1|H1];
  rewrite in_cons;
  rewrite in_cons in H1;
  apply/norP;
  move/norP: H1 => [H2 H3];
  (split;
   [ case: z => /= [j k] in H2 *;
     move/eqP in H2;
     apply/eqP;
     move=> Hneg;
     inversion Hneg;
     contradiction
   | apply: IHzs;
     apply/orP ]).
    by left.
  by right.
Qed.

Lemma uniq_proj : forall (a b : eqType) (xs : list (a * b)),
  uniq [list fst i | i <- xs] ->
  uniq [list snd i | i <- xs] → uniq xs.
Proof.
  move=> a b.
  elim=> //= [x xs IHxs] /andP [H1 H2] /andP [H3 H4].
  case: x => /= [j k] in H1 H3 *.
  apply/andP; split; last exact: IHxs.
  apply: in_proj.
  apply/orP; by left.
Qed.

Lemma sublist_in_cons : forall (a : eqType) x y (xs ys : list a),
  sublist (x :: xs) (y :: ys) → x != y → sublist (x :: xs) ys.
Proof.
  move=> a x y xs ys Hsub Hneq.
  elim: ys => /= [|z zs IHzs] in Hsub *.
    case E: (eq_dec x y).
      move/negP: Hneq.
      by rewrite E.
    rewrite E in Hsub.
    inversion Hsub.
  case E: (eq_dec x y).
    move/negP: Hneq.
    by rewrite E.
  rewrite E in Hsub.
  assumption.
Qed.

Lemma sublist_sing : forall (a : eqType) (x : a) xs s,
  sublist (x :: xs) s → sublist [x] s.
Proof.
  move=> a x xs s Hsub.
  elim: s => // [y ys IHys] in Hsub *.
  rewrite sub1list.
  rewrite sub1list in IHys.
  rewrite in_cons.
  apply/orP.
  case E: (eq_dec x y).
    by left.
  right.
  move/negP in E.
  move/negP in E.
  apply: IHys.
  apply: sublist_in_cons.
    exact Hsub.
  exact E.
Qed.

Lemma in_sublist_sing : forall {E : eqType} (s : list E) v (y : E) ys,
  v = y :: ys → sublist v s → y \in s.
Proof.
  move=> E s v y ys ->.
  rewrite -sub1list.
  exact: sublist_sing.
Qed.

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

Lemma sublist_cons_add : forall (a : eqType) (x : a) xs s,
  sublist xs s → sublist xs (x :: s).
Proof.
  move=> a x.
  elim=> // [y ys IHys] s Hsub.
  rewrite /=.
  case: (eq_dec y x).
    apply: sublist_impl_cons.
    exact Hsub.
  exact.
Qed.

Lemma sublist_cons_rem : forall (a : eqType) (x : a) xs s,
  sublist (x :: xs) s → sublist xs (rem x s).
Proof.
  move=> a x xs.
  elim=> //= [y ys IHys].
  rewrite eq_sym.
  case E: (eq_dec y x); first exact.
  move/IHys => Hsub {IHys}.
  exact: sublist_cons_add.
Qed.

Lemma all_xpredT_true : forall a (xs : list a), all xpredT xs.
Proof. by move=> ?; elim. Qed.

Fixpoint between_all `(R : rel a) (xs : list a) : bool :=
  if xs is y :: ys
  then all (R y) ys && between_all R ys
  else true.

Lemma between_all_cat : forall a (xs ys : list a) (R : rel a),
  between_all R (xs ++ ys) =
  [&& between_all R xs
  ,   between_all R ys
  ,   all (fun x => all (R x) ys) xs
  &   all (fun y => all (R ^~ y) xs) ys
  ].
Proof.
  move=> a xs ys R.
  elim: xs => [|x xs IHxs] in ys *.
    by rewrite /= all_xpredT_true Bool.andb_true_r.
  rewrite cat_cons all_all_cons.
  rewrite /= all_cat {}IHxs /=.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite [X in _ = X]andbC.
  rewrite !andbA; f_equal.
  rewrite Bool.andb_diag.
  by rewrite -!andbA and_swap.
Qed.

Lemma between_all_catC {a} (xs ys : list a) (R : rel a) (_ : symmetric R) :
  between_all R (xs ++ ys) = between_all R (ys ++ xs).
Proof.
  elim: xs => /= [|x xs IHxs] in ys *.
    by rewrite cats0.
  rewrite IHxs.
  elim: ys => /= [|y ys IHys].
    by rewrite cats0.
  rewrite -IHys !andbA.
  congr (_ && _).
  rewrite !all_cat -!andbA 2!andbA and_swap.
  congr (_ && _).
  rewrite andbC -!andbA [RHS]and_swap.
  congr (_ && _).
  rewrite [RHS]and_swap.
  congr (_ && _).
  by rewrite H.
Qed.

Lemma allpairs_map :
  forall a b c (f : a → b → c) (xs : list a) (ys : list b),
  [list f x y | x <- xs, y <- ys] =
  flatten [list [list f x y | y <- ys] | x <- xs].
Proof.
  move=> a b c f.
  elim=> //= [x xs IHxs] y.
  congr (_ ++ _).
  exact: IHxs.
Qed. *)

#[export]
Instance List_Functor : Functor list := {
  fmap := map
}.

Fixpoint list_ap {A B} (fs: list (A → B)) (xs: list A)
  : list B :=
  match fs with
  | f :: fs' => map f xs ++ list_ap fs' xs
  | _ => nil
  end.


#[export]
Instance List_Applicative : Applicative list := {
  pure := fun _ x => [x];
  ap   := @list_ap
}.

Require Import
  Coq.Relations.Relations
  Coq.Reals.ROrderedType.

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

Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import FunctionalExtensionality.

Add Parametric Relation {A} : (list A) (@Permutation A)
  reflexivity proved by  (@Permutation_refl A)
  symmetry proved by     (@Permutation_sym A)
  transitivity proved by (@Permutation_trans A)
    as Permutation_parametric.

Add Parametric Morphism {A} : (@insert A)
  with signature
  ((@eq A ==> @eq A ==> @eq bool)
     ==> @eq A
     ==> @Permutation A
     ==> @Permutation A)
  as Permutation_insert_mor.
Proof.
  intros R1 R2 HR x xs ys H.
  generalize dependent R1.
  generalize dependent x.
  induction H; subst;
  unfold insert; simpl; intros; fold @insert.
  - constructor; trivial.
  - rewrite (HR _ _ eq_refl _ _ eq_refl).
    destruct (R2 x x0); simpl.
    + constructor.
      apply IHPermutation; trivial.
    + constructor; constructor.
      exact H.
  - rewrite !(HR _ _ eq_refl _ _ eq_refl).
    destruct (R2 x x0);
    destruct (R2 y x0); simpl.
    + rewrite perm_swap.
      constructor.
      constructor.
      induction l; simpl;
      unfold insert; simpl; intros; fold @insert.
      * constructor; constructor.
      * rewrite (HR _ _ eq_refl _ _ eq_refl).
        destruct (R2 a x0); simpl.
        ** constructor.
           exact IHl.
        ** reflexivity.
    + symmetry.
      rewrite perm_swap.
      constructor.
      rewrite perm_swap.
      reflexivity.
    + rewrite perm_swap.
      constructor.
      rewrite perm_swap.
      reflexivity.
    + constructor.
      rewrite perm_swap.
      reflexivity.
  - rewrite IHPermutation1.
    + apply IHPermutation2.
      intros x0 y0 Heq0 x1 y1 Heq1.
      congruence.
    + exact HR.
Qed.

Add Parametric Morphism {A} : (@Forall A)
  with signature
  ((@eq A ==> @eq Prop)
     ==> @Permutation A
     ==> iff)
  as Permutation_Forall_mor.
Proof.
  intros P1 P2 HP xs ys H.
  split; intros.
  - apply Forall_impl with (P:=P1).
    + intros z H1.
      rewrite (HP z z eq_refl) in H1.
      assumption.
    + induction H; simpl; trivial.
      * constructor.
        ** inversion H0; subst; trivial.
        ** apply IHPermutation.
          inversion H0; trivial.
      * inversion H0; subst.
        inversion H3; subst.
        intuition.
      * intuition.
  - apply List.Forall_impl with (P:=P2).
    + intros z H2.
      rewrite (HP z z eq_refl).
      assumption.
    + induction H; simpl; trivial.
      * constructor.
        ** inversion H0; subst; trivial.
        ** apply IHPermutation.
           inversion H0; trivial.
      * inversion H0; subst.
        inversion H3; subst.
        intuition.
      * intuition.
Qed.

Lemma StronglySorted_impl :
  forall (A : Type) (P Q : A → A → Prop),
    (forall a b : A, P a b → Q a b) ->
      forall l : list A, StronglySorted P l → StronglySorted Q l.
Proof.
  intros.
  induction l; simpl.
  - constructor.
  - constructor.
    + apply IHl.
      inversion H0; assumption.
    + inversion H0; subst.
      apply Forall_impl with (P:=P a).
      * apply H.
      * assumption.
Qed.

Lemma Permutation_insert : forall A (a : A) R xs ys,
  Permutation xs ys → Permutation (insert R a xs) (a :: ys).
Proof.
  intros.
  rewrite H; clear H.
  induction ys; intros; simpl.
  - constructor; trivial.
  - unfold insert.
    destruct (R a0 a) eqn:Heqe;
    fold@insert.
    + rewrite perm_swap.
      constructor.
      exact IHys.
    + reflexivity.
Qed.

Lemma Permutation_sortBy : forall A (a : A) (R : A → A → bool) xs,
  Permutation (sortBy R xs) xs.
Proof.
  induction xs; intros; simpl.
  - constructor.
  - apply Permutation_insert.
    exact IHxs.
Qed.

Lemma Permutation_Forall : forall A (P : A → Prop) (xs ys : list A),
  Permutation xs ys
    → List.Forall P xs
    → List.Forall P ys.
Proof.
  intros.
  rewrite <- H.
  assumption.
Qed.

Lemma Forall_insert : forall a (R : a → a → Prop) (Q : a → a → bool) x xs y,
  Q x y = true
    → (forall a b, R a b <-> Q a b = true)
    → List.Forall (R x) xs
    → List.Forall (R x) (insert Q y xs).
Proof.
  intros.
  apply Permutation_Forall with (xs:=y :: xs).
  - symmetry.
    apply Permutation_insert.
    reflexivity.
  - constructor; trivial.
    apply H0.
    assumption.
Qed.

Lemma Forall_ordered : forall a (R : a → a → Prop) `{Transitive _ R} x y xs,
  R x y → List.Forall (R y) xs → List.Forall (R x) xs.
Proof.
  intros a R H x y xs H1 H2.
  assert (forall a, R y a → R x a).
  - intros z H3.
    transitivity y; trivial.
  - apply List.Forall_impl with (P:=R y);
    intros.
    + apply H0.
      assumption.
    + assumption.
Qed.

Lemma StronglySorted_insert :
  forall a (R : a → a → Prop) (Q : a → a → bool)
         `{Transitive _ R} x xs,
    (forall y, Q y x = false → Q x y = true)
      → (forall a b, R a b <-> Q a b = true)
      → StronglySorted R xs
      → StronglySorted R (insert Q x xs).
Proof.
  intros a R Q H x xs H1 H2 H3.
  generalize dependent x.
  induction xs as [|y ys IHys]; intros; simpl.
  - unfold insert.
    constructor; constructor.
  - unfold insert.
    destruct (Q y x) eqn:E;
    fold @insert.
    + constructor.
      * apply IHys; trivial.
        inversion H3; trivial.
      * apply Forall_insert; trivial.
        inversion H3; trivial.
    + constructor; trivial.
      constructor.
      * apply H2; trivial.
        inversion H3.
        apply H1 in E.
        assumption.
      * apply H1 in E.
        apply H2 in E.
        apply (@Forall_ordered a R H x y ys E).
        inversion H3.
        assumption.
Qed.

Lemma sortBy_sorted : forall a (R : a → a → Prop) (Q : a → a → bool)
                             `{Transitive _ R} xs,
  (forall x y, Q y x = false → Q x y = true)
    → (forall a b, R a b <-> Q a b = true)
    → StronglySorted R (sortBy Q xs).
Proof.
  intros a R Q H xs H1 H2.
  induction xs as [|x xs IHxs]; simpl.
  - constructor.
  - apply StronglySorted_insert; trivial.
    exact (H1 x).
Qed.
