Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Graded monads *)

(* nLab: https://ncatlab.org/nlab/show/graded+monad

   Graded monads (also called parametric monads).  Fix an ordinary monoid
   (E, ε, ·) of "grades" — here a [GradeMonoid], a record over a Coq type with
   the monoid laws stated in propositional equality [=].  An E-graded monad on
   a category C is a family of endofunctors  T : E → (C ⟶ C)  together with a
   unit

     gret : x ~> T ε x

   and a family of graded multiplications

     gjoin : T m (T n x) ~> T (m · n) x

   satisfying the monad laws up to the monoid's associativity and unit
   equations, which are transported along the family by the cast morphisms
   [gcast] below.  Grades typically track a quantitative effect discipline:
   which effects may occur, how many times, at what cost.

   Honest formulation.  The class [GradedMonad] below mirrors Theory/Monad.v
   field-for-field: [gret] and [gjoin] generalize [ret] and [join], and the
   five laws [gfmap_ret], [gjoin_fmap_join], [gjoin_fmap_ret], [gjoin_ret],
   [gjoin_fmap_fmap] generalize the five monad laws, each mediated by a
   [gcast] along the corresponding grade-monoid equation.  At the trivial
   one-element grading every [gcast] reduces to [id] and the five laws are
   literally the five laws of Theory/Monad.v; the bridges [GradedMonad_Monad]
   and [Monad_GradedMonad_const] below make this degeneracy precise in both
   directions, with definitional round-trips ([roundtrip_ret],
   [roundtrip_join]).

   Relation to the monoid picture.  Monad/Monoid.v ([Monoid_Monad]) exhibits
   an ordinary monad as a monoid object in the endofunctor category [C, C]
   under composition.  A graded monad likewise has a delooping reading: it is
   a lax functor from B E — the one-object bicategory whose 1-cells are the
   elements of E, composed by ·, with only identity 2-cells — to the
   one-object bicategory delooping the strict monoidal category
   ([C, C], ◯, Id).  The unique object goes to the unique object, the 1-cell
   m goes to the endofunctor T m, and the lax coherence 2-cells are exactly
   [gret] (unit comparison, Id ⟹ T ε) and [gjoin] (composition comparison,
   T m ◯ T n ⟹ T (m · n)), natural by [gfmap_ret] and [gjoin_fmap_fmap].
   Equivalently: a lax monoidal functor into ([C, C], ◯, Id) from E read as a
   discrete strict monoidal category — objects the grades, tensor ·, unit ε —
   sending the object m to T m.  Bicategories, deloopings and lax monoidal
   functors are outside the scope of this file, so that equivalent reading is
   recorded here as prose only; the record below is the elementary spelling
   of the same data. *)

(* The grade monoid: a plain monoid on a Coq type, with associativity and the
   two unit laws stated in propositional equality [=].

   NOTE on transparency: concrete instances should supply TRANSPARENT
   match-term proofs of the three laws (rather than opaque lemmas from the
   standard library such as [andb_assoc]), so that [gcast] computes to [id]
   on closed grades by mere reduction.  Alternatively, over a grade type with
   decidable equality any closed proof can be rewritten to [eq_refl] via
   [Eqdep_dec.UIP_dec], which by Hedberg's theorem is fully constructive and
   assumes nothing beyond the core theory; the transparent route taken below
   ([Trivial_GradeMonoid], [AndGrade]) avoids that extra step. *)

Record GradeMonoid : Type := {
  grade :> Type;                        (* the underlying type of grades *)
  gunit : grade;                        (* the neutral grade ε *)
  gmul : grade → grade → grade;         (* grade composition m · n *)

  gmul_assoc {a b c : grade} : gmul (gmul a b) c = gmul a (gmul b c);
  gmul_unit_l {a : grade} : gmul gunit a = a;
  gmul_unit_r {a : grade} : gmul a gunit = a
}.

Section Graded.

Context {C : Category}.
Context {E : GradeMonoid}.
Context {T : E → C ⟶ C}.

(* Transport of a graded carrier along an equality of grades.  This is the
   only place where the propositional grade equations touch the morphisms:
   every law of [GradedMonad] is stated up to such a cast.  Defined as a
   direct match so it computes to [id] whenever the proof reduces to
   [eq_refl]. *)

Definition gcast {m n : E} (e : m = n) {x : C} : T m x ~> T n x :=
  match e in _ = k return T m x ~> T k x with
  | eq_refl => id
  end.

Lemma gcast_refl {m : E} {x : C} : @gcast m m eq_refl x ≈ id.
Proof. reflexivity. Qed.

Lemma gcast_trans {m n p : E} (e1 : m = n) (e2 : n = p) {x : C} :
  gcast e2 ∘ @gcast m n e1 x ≈ gcast (eq_trans e1 e2).
Proof. destruct e2, e1; simpl; cat. Qed.

(* [gcast] is natural in the object variable: it commutes with the functorial
   action of the graded carriers. *)
Lemma gcast_natural {m n : E} (e : m = n) {x y : C} (f : x ~> y) :
  gcast e ∘ fmap[T m] f ≈ fmap[T n] f ∘ @gcast m n e x.
Proof. destruct e; simpl; cat. Qed.

(* The E-graded monad, mirroring Theory/Monad.v field-for-field.  [gret] is
   the unit η at the neutral grade, [gjoin] the grade-multiplying μ, and the
   five laws are the five laws of [Monad] with every grade equation
   transported by [gcast].  At the trivial grading every cast is [id] and the
   laws collapse to the ungraded ones (see [GradedMonad_Monad] below). *)

Class GradedMonad := {
  gret {x : C} : x ~> T (gunit E) x;                       (* graded unit η *)
  gjoin {m n : E} {x : C} : T m (T n x) ~> T (gmul E m n) x;   (* graded μ *)

  (* naturality of the unit η: gret ∘ f ≈ fmap f ∘ gret *)
  gfmap_ret {x y : C} (f : x ~> y) :
    gret ∘ f ≈ fmap[T (gunit E)] f ∘ gret;

  (* graded associativity: μ ∘ Tμ ≈ μ ∘ μT, up to gmul_assoc *)
  gjoin_fmap_join {m n p : E} {x : C} :
    gjoin ∘ fmap[T m] (@gjoin n p x)
      ≈ gcast (gmul_assoc E) ∘ @gjoin (gmul E m n) p x ∘ @gjoin m n (T p x);

  (* graded left unit law: μ ∘ Tη ≈ id, up to gmul_unit_r *)
  gjoin_fmap_ret {m : E} {x : C} :
    gjoin ∘ fmap[T m] (@gret x) ≈ gcast (eq_sym (gmul_unit_r E));

  (* graded right unit law: μ ∘ ηT ≈ id, up to gmul_unit_l *)
  gjoin_ret {m : E} {x : C} :
    gjoin ∘ @gret (T m x) ≈ gcast (eq_sym (gmul_unit_l E));

  (* naturality of the multiplication μ *)
  gjoin_fmap_fmap {m n : E} {x y : C} (f : x ~> y) :
    gjoin ∘ fmap[T m] (fmap[T n] f) ≈ fmap[T (gmul E m n)] f ∘ gjoin
}.

End Graded.

Arguments GradedMonad {C} E T.

(* Over a constant family the cast is always the identity, whatever the grade
   equation was: the transport happens in a family that does not move. *)
Lemma gcast_const {C : Category} {E : GradeMonoid} {M : C ⟶ C}
      {m n : E} (e : m = n) {x : C} :
  @gcast C E (fun _ => M) m n e x ≈ id.
Proof. destruct e; reflexivity. Qed.

(** ** The degenerate-grading bridge *)

(* The one-element grade monoid.  All three law proofs are transparent
   match-terms reducing to [eq_refl] on [ttt], so at this grading [gcast]
   is definitionally [id]. *)
Definition Trivial_GradeMonoid : GradeMonoid := {|
  grade := poly_unit;
  gunit := ttt;
  gmul := fun _ _ => ttt;
  gmul_assoc := fun _ _ _ => eq_refl;
  gmul_unit_l := fun a => match a as u return ttt = u with ttt => eq_refl end;
  gmul_unit_r := fun a => match a as u return ttt = u with ttt => eq_refl end
|}.

#[local] Obligation Tactic := idtac.

(* A trivially graded monad is an ordinary monad: every grade proof reduces
   to [eq_refl] definitionally, so every [gcast] reduces to [id], and the
   graded laws are the ungraded ones (the unit laws by direct conversion, the
   associativity law after erasing the identity cast). *)
Program Definition GradedMonad_Monad {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) : @Monad C M := {|
  ret  := fun x => @gret C Trivial_GradeMonoid (fun _ => M) G x;
  join := fun x => @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x
|}.
Next Obligation. (* fmap_ret *)
  intros C M G x y f.
  exact (@gfmap_ret C Trivial_GradeMonoid (fun _ => M) G x y f).
Qed.
Next Obligation. (* join_fmap_join *)
  intros C M G x.
  etransitivity.
  - exact (@gjoin_fmap_join C Trivial_GradeMonoid (fun _ => M) G ttt ttt ttt x).
  - rewrite gcast_const; cat.
Qed.
Next Obligation. (* join_fmap_ret: the cast is definitionally [id] here *)
  intros C M G x.
  exact (@gjoin_fmap_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_ret: the cast is definitionally [id] here *)
  intros C M G x.
  exact (@gjoin_ret C Trivial_GradeMonoid (fun _ => M) G ttt x).
Qed.
Next Obligation. (* join_fmap_fmap *)
  intros C M G x y f.
  exact (@gjoin_fmap_fmap C Trivial_GradeMonoid (fun _ => M) G ttt ttt x y f).
Qed.

(* Conversely, any ordinary monad is E-graded for ANY grade monoid E, as the
   constant family at its endofunctor: all casts are erased by [gcast_const].
   Instantiating E with [Trivial_GradeMonoid] gives the inverse direction of
   the degenerate bridge, so this construction subsumes it. *)
Program Definition Monad_GradedMonad_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (E : GradeMonoid) : @GradedMonad C E (fun _ => M) := {|
  gret  := fun x => @ret C M H x;
  gjoin := fun _ _ x => @join C M H x
|}.
Next Obligation. (* gfmap_ret *)
  intros C M H E x y f.
  exact (@fmap_ret C M H x y f).
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros C M H E m n p x.
  rewrite gcast_const, id_left.
  exact (@join_fmap_join C M H x).
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_fmap_ret C M H x).
Qed.
Next Obligation. (* gjoin_ret *)
  intros C M H E m x.
  rewrite gcast_const.
  exact (@join_ret C M H x).
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros C M H E m n x y f.
  exact (@join_fmap_fmap C M H x y f).
Qed.

(* Round-trips at the trivial grading hold definitionally: passing through
   either bridge leaves the structure maps unchanged. *)

Corollary roundtrip_ret {C : Category} {M : C ⟶ C} (H : @Monad C M) (x : C) :
  @gret C Trivial_GradeMonoid (fun _ => M)
        (Monad_GradedMonad_const H Trivial_GradeMonoid) x ≈ @ret C M H x.
Proof. reflexivity. Qed.

Corollary roundtrip_join {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @join C M (GradedMonad_Monad G) x
    ≈ @gjoin C Trivial_GradeMonoid (fun _ => M) G ttt ttt x.
Proof. reflexivity. Qed.

Corollary roundtrip_ret_trivial {C : Category} {M : C ⟶ C}
  (G : @GradedMonad C Trivial_GradeMonoid (fun _ => M)) (x : C) :
  @ret C M (GradedMonad_Monad G) x
    ≈ @gret C Trivial_GradeMonoid (fun _ => M) G x.
Proof. reflexivity. Qed.

Corollary roundtrip_join_const {C : Category} {M : C ⟶ C}
  (H : @Monad C M) (x : C) :
  @gjoin C Trivial_GradeMonoid (fun _ => M)
         (Monad_GradedMonad_const H Trivial_GradeMonoid) ttt ttt x
    ≈ @join C M H x.
Proof. reflexivity. Qed.

(** ** A nontrivial instance: the bool-graded exception monad over Coq *)

(* The grade monoid (bool, true, andb): grade [true] means "pure so far"
   (no exception can have been raised), grade [false] means an exception may
   have been raised.  A composite computation is pure exactly when both
   stages are, whence [andb].  The law proofs are transparent match-terms so
   that [gcast] reduces on both constructors. *)
Definition AndGrade : GradeMonoid := {|
  grade := bool;
  gunit := true;
  gmul := andb;
  gmul_assoc := fun a b c =>
    match a as a0 return andb (andb a0 b) c = andb a0 (andb b c) with
    | true  => eq_refl
    | false => eq_refl
    end;
  gmul_unit_l := fun a => eq_refl;
  gmul_unit_r := fun a =>
    match a as a0 return andb a0 true = a0 with
    | true  => eq_refl
    | false => eq_refl
    end
|}.

(* The option endofunctor on Coq, defined locally as a categorical functor
   (Theory/Coq covers the programming-style classes instead). *)
Program Definition option_Functor : Coq ⟶ Coq := {|
  fobj := option;
  fmap := fun _ _ f o => option_map f o
|}.
Next Obligation. (* fmap_respects *)
  intros x y f g Hfg [a|]; simpl; [rewrite Hfg|]; reflexivity.
Qed.
Next Obligation. (* fmap_id *)
  intros x [a|]; reflexivity.
Qed.
Next Obligation. (* fmap_comp *)
  intros x y z f g [a|]; reflexivity.
Qed.

(* The graded carrier: at the pure grade the identity functor, at the
   impure grade [option]. *)
Definition ExcT (b : bool) : Coq ⟶ Coq :=
  if b then Id[Coq] else option_Functor.

(* The graded unit lives at grade [true], where the carrier is [Id]. *)
Definition exc_ret (x : Type) : x → ExcT true x := fun a => a.

(* The graded multiplication.  At (true, _) and (false, true) one of the two
   layers is the identity functor and the multiplication is the evident
   reindexing; at (false, false) it is the usual option join. *)
Definition exc_join (b1 b2 : bool) (x : Type) :
  ExcT b1 (ExcT b2 x) → ExcT (andb b1 b2) x :=
  match b1 as a, b2 as b return ExcT a (ExcT b x) → ExcT (andb a b) x with
  | true, _      => fun o => o
  | false, true  => fun o => o
  | false, false => fun o => match o with
                             | Some v => v
                             | None   => None
                             end
  end.

(* The laws are proven by destructing the grades first — after which every
   [gcast] reduces to [id], by transparency of the [AndGrade] proofs — and
   then by pointwise case analysis in Coq's pointwise-equality homsets. *)
Program Definition Exc_GradedMonad : @GradedMonad Coq AndGrade ExcT := {|
  gret  := exc_ret;
  gjoin := exc_join
|}.
Next Obligation. (* gfmap_ret *)
  intros x y f a; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros m n p x; destruct m, n, p; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros m x; destruct m; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros m n x y f; destruct m, n; simpl; intro o;
    repeat (destruct o as [o|]); simpl; reflexivity.
Qed.

(** ** The grade-only writer *)

(* Pure grade tracking with trivial data: for ANY grade monoid W, the
   constant family at the identity functor is W-graded.  All structure maps
   are identities; every law is a [gcast] transport erased by [gcast_const].
   This is the "writer into W" whose entire log lives in the grades. *)
Program Definition GradedWriter (W : GradeMonoid) :
  @GradedMonad Coq W (fun _ => Id[Coq]) := {|
  gret  := fun x (a : x) => a;
  gjoin := fun _ _ x (a : x) => a
|}.
Next Obligation. (* gfmap_ret *)
  intros W x y f; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_join *)
  intros W m n p x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_ret *)
  intros W m x; rewrite gcast_const; reflexivity.
Qed.
Next Obligation. (* gjoin_fmap_fmap *)
  intros W m n x y f; reflexivity.
Qed.
