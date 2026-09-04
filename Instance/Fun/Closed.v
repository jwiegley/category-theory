Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Generalizable All Variables.

(** * Cartesian closure is NOT inherited by functor categories *)

(* Book:      Mac Lane, CWM 2nd ed., §IV.6 "Cartesian Closed Categories",
              Exercise 5, printed p. 98 ([maclane:IV.6:ex5]).  Verbatim:

                  "5. Show that A cartesian closed need not imply A^J
                   cartesian closed."

   Book:      Awodey, Category Theory, §8.7 "Exponentials in categories
              of diagrams", printed pp. 207-208
              (Awodey's unnumbered remark there that the pointwise
              formula does not define an exponential of presheaves;
              the catalog identifier for it is quoted verbatim in
              Test/ProbeFunClosed392.v, which carries it in full).
              Verbatim, with the question-mark-over-equals rendered as
              "=?":

                  "Now suppose we have functors P, Q and we want Q^P.
                   The reader should try to construct the exponential
                   'pointwise',

                       Q^P(C) =? Q(C)^{P(C)}

                   to see that it does not work (it's not functorial)."

   nLab:      https://ncatlab.org/nlab/show/functor+category
   nLab:      https://ncatlab.org/nlab/show/cartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   The issue this file answers describes [Functor_Category_Cartesian]
   (Instance/Fun/Cartesian.v:111) as the only structure lemma for
   functor categories in the tree.  That is stale.  Sweeping the
   declaration heads that put a structure CLASS on a functor category
   as a whole, inherited from the target, returns five, and every one
   of them is POSITIVE and POINTWISE: that one, plus
   [Functor_Category_Terminal] and [Fun_HasIndexedProducts]
   (Instance/Fun/Terminal.v:361 and :519, both landed with #339),
   [Thin_Fun] (Instance/Proset/Closure.v:154) and [Fun_IsGroupoid]
   (Construction/Deloop/Transform.v:781).  Read the criterion, since
   the same sweep also returns constants of a DIFFERENT shape that are
   not counted among the five: subcategories OF a functor category
   ([ReprSubcat], [Models_sub]), structures on particular OBJECTS or
   MORPHISMS of one ([fun_gmonoid], [pare_idem_Idempotent],
   [pare_SplitIdempotent], [two_pick_Monic]), and instantiations of the
   five at a fixed pair ([Two_Sets_Terminal],
   [Two_Sets_HasIndexedProducts], [Deloop_Fun_IsGroupoid] of
   Construction/Deloop/Transform.v:798), and structures on a functor
   category as a whole that are NOT inherited from the target
   ([Compose_Monoidal], Structure/Monoidal/Compose.v:42, which is
   monoidal under COMPOSITION rather than pointwise).

   Exponentials are where that pattern stops, in two distinct senses,
   and this file separates them:

     (i)  the CONCLUSION can be false -- [A] cartesian closed and [J] a
          perfectly ordinary index category (small in the ordinary
          sense, its objects being the naturals, though smallness is
          nowhere formalized in this tree), yet [A^J] carries no
          cartesian closed structure at all; and

     (ii) even when [A^J] IS cartesian closed, its exponential is not
          computed objectwise -- the objectwise VALUE is already the
          wrong object, so no action on that family of values, however
          chosen, can be the exponential.

   WHAT DRIVES BOTH IS ONE LEMMA, and it is elementary.  In any
   cartesian closed category the transposition at the terminal object
   reads

       Hom(P, Q)  ~  Hom(1 x P, Q)  ~  Hom(1, Q^P),

   so morphisms P -> Q are (at least) as few as the points of Q^P.
   Section A gives that as an INJECTION [ccc_point] with an explicit
   injectivity proof; no bijection is claimed, and none is needed.
   Section B specialises the ambient to a functor category [J, A] whose
   INDEX has an initial object j0: the terminal object of [J, A] is the
   constant functor at 1_A ([Functor_Category_Terminal]), whose arrow
   action is the identity, so naturality of a transformation out of it
   at the unique arrow j0 -> j forces

       alpha_j  ~  fmap[E] (zero j) o alpha_{j0},

   and alpha is determined by its component at j0.  Section C composes
   the two into [fun_hom_point], the engine:

       if [J, A] is cartesian closed and J has an initial object j0,
       then Hom_{[J,A]}(P, Q) injects into Hom_A(1_A, (Q^P) j0).

   Sections E and F are the two applications.

   APPLICATION ONE (Mac Lane, Exercise 5).  Take A := skeletal [FinSet],
   which IS cartesian closed ([FinSet_Closed], Instance/FinSet/Closed.v),
   and J := [Omega], the ordinal omega, which HAS an initial object
   ([Omega_Initial], Structure/Limit/Initial.v:679).  In [FinSet] the
   hom-set Hom(1, n) is the maps [Fin.t 1 -> Fin.t n], and two of them
   agree as soon as they agree at [Fin.F1], so that hom-set has at most
   n elements: it is FINITE.  The engine therefore makes every hom-set
   of [Omega, FinSet] finite, as soon as that category is cartesian
   closed.  Section E exhibits a single functor [TwoFun] whose
   endomorphism monoid in [Omega, FinSet] is infinite -- an explicit
   family [Alpha k], k : nat, pairwise distinct -- and concludes
   [fun_not_cartesian_closed].

   THE STRENGTHENING LANDED.  [fun_not_cartesian_closed] quantifies over
   an ARBITRARY [@Cartesian ([Omega, FinSet])], not merely the pointwise
   one, so it is the strict reading of "not cartesian closed".  It costs
   nothing: the engine takes the cartesian structure as a parameter, and
   the only structure it pins is the TERMINAL object, which it supplies
   itself as [Functor_Category_Terminal FinSet_Terminal] rather than
   reading off the given [Cartesian] (that class carries no terminal
   object; see Instance/Fun/Cartesian.v).  So the given product
   structure is genuinely arbitrary throughout.

   APPLICATION TWO (Awodey's objectwise no-go).  Presheaves on the
   walking arrow, [_2^op, Sets].  The initial object of [_2^op] is
   [TwoY], because [TwoY] is terminal in [_2] ([Two_Terminal],
   Instance/Two/Monoidal.v:95); this needs no transport, since
   [Initial C] is NOTATION for [@Terminal (C^op)] and [(C^op)^op] is [C]
   definitionally.  [PresheafP] takes [TwoX] to the terminal setoid and
   [TwoY] to the initial (empty) one -- the representable at [TwoX],
   built directly rather than through Yoneda, whose in-tree statement
   carries a universe restriction this argument does not need.
   [PresheafQ] is constant at a two-element setoid.  Then
   Hom(P, Q) has (at least) TWO elements: the component at [TwoY] is a
   map out of the empty setoid, so it is unique and naturality is
   vacuous, while the component at [TwoX] may be either point of Q.  By
   the engine, (Q^P) TwoY then has two distinct points.  The objectwise
   candidate Q(TwoY)^{P(TwoY)} is the exponential IN [Sets] of a
   two-element setoid by the EMPTY one, and any two of its points are
   equivalent.  Hence [awodey_pointwise_not_exponential].

   BE PRECISE ABOUT WHAT THAT DOES AND DOES NOT SAY.  Awodey's stated
   reason is that the objectwise assignment "is not functorial".  Read
   literally, "there is no contravariant action on this family of sets"
   would be FALSE for the family at hand, which does carry an action --
   though NOT because every family does: over [_2] the family that is a
   singleton at [TwoX] and empty at [TwoY] carries none.  What is proved
   here is different in kind, and stronger in the way that matters: the
   objectwise VALUES are already the wrong objects, so NO action
   whatsoever on them can produce the exponential.  This file does not
   formalize the sentence "it is not functorial"; it formalizes a
   statement that makes the sentence moot.

   THAT SECOND THEOREM IS CONDITIONAL, and the hypothesis is not
   witnessed anywhere in this tree.  It is stated for an arbitrary
   [@Closed ([_2^op, Sets]) CC]; presheaf categories ARE cartesian
   closed mathematically, but nothing in tree proves it -- that is
   issue #718's result -- so the hypothesis is NOT claimed inhabited
   here.  Application one has no such caveat: it is unconditional.

   UNIVERSES, MEASURED.  Both ambient categories elaborate, and the
   measurement was made before any content was written.
   [Omega@{o h p}] is fully polymorphic and [FinSet@{u u0 u1 u2}] has
   hom and proof at one free level, so [Omega, FinSet] carries no [Set]
   beyond [FinSet]'s own [Set < u1].  By contrast [_2@{u u0}] is
   declared [Category@{u Set Set}] -- its homs are the literal [Set] --
   and [Fun] identifies its source and target hom universes, while
   [Sets@{o so} : Category@{so o o}] has its hom universe EQUAL to its
   carrier universe.  So [_2^op, Sets] elaborates only at
   [Sets@{Set _}]: the presheaves of section F take values in setoids
   whose CARRIER lives in [Set].  That attribution is measured, not
   guessed -- replacing [_2^op] by the polymorphic [Omega] leaves
   [Sets]'s carrier universe free ([Omega, Sets] elaborates at
   [Sets@{u u0}] with [u] unconstrained) -- and the pin is [_2]'s, not
   introduced here, and is not claimed unavoidable.  It restricts the
   CONTENT of section F, not merely its presentation: the theorem there
   is about presheaves valued in small setoids.  The three witnesses
   used are all of that size.

   LOCAL LEMMA.  Section D proves a pigeonhole principle for
   [Fin.t]: there is no injective family [nat -> Fin.t N].  It is local
   because the tree has none.  The nearest thing is the [assert] inside
   the proof of [fin_bijection_index] (Instance/FinSet/Skeleton.v:325),
   which runs the same counting argument but is sealed by [Qed] and so
   cannot be reused; the [pigeon] of Instance/Ab/Character/Finite.v:286
   is a different statement, over a setoid with a decider, in a section
   whose context this file does not have.  The ingredients [fin_enum],
   [fin_enum_length], [fin_enum_full], [fin_enum_nodup] and
   [length_of_map] ARE taken from Skeleton.v, and only
   [List.NoDup_incl_length] comes from the standard library -- the same
   lemma Skeleton.v:334 already uses, so the portability across the
   supported Coq/Rocq versions is the one that file already relies on.

   SETOID DISCIPLINE.  Morphism equality is written [~] everywhere
   except where the ambient hom-setoid IS Leibniz equality and the goal
   has already been unfolded to it: [FinSet]'s hom-setoid is
   [fun_setoid], i.e. pointwise [=] on functions [Fin.t m -> Fin.t n],
   and [Omega]'s and [_2]'s are [Morphism_equality], i.e. Leibniz [=] on
   arrows.  Most [=] below are between ELEMENTS -- of [Fin.t n], of
   [nat], of a carrier -- and not between morphisms at all; the ones
   that do relate morphisms are exactly the [FinSet] obligations, whose
   [=] IS that category's [~], and they are flagged in place.

   WHAT IS NOT DELIVERED -- read this as the scope of the file.

     * The POSITIVE companion is NOT here.  Nothing below proves that
       [C] small and [D] cartesian closed and COMPLETE gives [C, D]
       cartesian closed, and no attempt is made at it.

     * The presheaf case of that positive theorem belongs to issue #718,
       whose suggested module is THIS SAME FILE.  Room is deliberately
       left for it: the two negative theorems here scope the positive
       one (they say which hypotheses may not be dropped) rather than
       colliding with it, and section F is stated CONDITIONALLY on
       exactly the cartesian closure #718 would supply.

     * No end formula, limit formula, or any other construction of
       exponentials in a functor category is built.

     * Nothing here says which pairs (J, A) DO give a cartesian closed
       [J, A].  Only one pair is examined.

     * The counterexample of section E uses ONE pair, ([Omega],
       [FinSet]).  No characterisation is claimed, and no other pair is
       tested.  In particular nothing is proved about [Omega] with a
       complete target, or about [FinSet] over a different index.

     * Whether [FinSet] is locally cartesian closed is not touched, and
       neither is the classical statement that [A^2] is cartesian closed
       exactly when [A] is locally cartesian closed.

     * Section B proves an INJECTION and no more.  The reverse map
       (every point of E j0 extends to a transformation) is not built,
       so nothing here is a bijection, and none is needed.

     * That [FinSet] is not COMPLETE is nowhere proved.  What the
       counterexample establishes is that the conclusion of the positive
       theorem can be false when C is small and D is cartesian closed;
       relative to that theorem it follows that completeness of D is
       doing real work, but the incompleteness of this particular D is
       an inference and not a theorem in tree.

     * The count of Hom(P, Q) in section F is a lower bound: TWO
       distinct transformations are exhibited, and nothing proves there
       are no others.  Two is all the argument uses.

     * Nothing below is registered as an [Instance].

     * This file contributes NO lines to [make todo].  The Awodey
       remark is cited by name rather than by its catalog identifier,
       precisely because that identifier contains letters the target
       greps for; the identifier itself is quoted in
       Test/ProbeFunClosed392.v.  That probe does contribute lines to
       the report, as every probe in this tree does. *)

(** ** A: points of an exponential, in any cartesian closed category *)

Section CCCPoints.

Context {C : Category}.
Context {CC : @Cartesian C}.
Context {CT : @Terminal C}.
Context {CL : @Closed C CC}.

(* The transpose of [f o exr : 1 x P ~> Q].  This is the composite

       Hom(P, Q) -> Hom(1 x P, Q) -> Hom(1, Q^P)

   of precomposition with the projection [exr : 1 x P ~> P] and the
   currying isomorphism.  The second map is invertible; the first is
   left-cancellable because [exr] is split epi, its section being the
   pairing of [one] with the identity.  Hence the composite is
   injective. *)
Definition ccc_point {P Q : C} (f : P ~> Q) :
  @terminal_obj C CT ~> @exponent_obj C CC CL P Q :=
  @curry C CC CL _ P Q (f ∘ exr).

(* Distinct morphisms have distinct points.  Uncurrying undoes [curry]
   ([uncurry_curry]), and [exr o (one /\ id) ~ id] ([exr_fork]) cancels
   the projection. *)
Lemma ccc_point_inj {P Q : C} (f g : P ~> Q) :
  ccc_point f ≈ ccc_point g -> f ≈ g.
Proof.
  intro H.
  unfold ccc_point in H.
  assert (Hu : f ∘ (@exr C CC (@terminal_obj C CT) P) ≈ g ∘ exr).
  { rewrite <- (uncurry_curry (f ∘ exr)).
    rewrite <- (uncurry_curry (g ∘ exr)).
    now rewrite H. }
  rewrite <- (id_right f), <- (id_right g).
  rewrite <- (exr_fork (@one C CT P) (id[P])).
  rewrite !comp_assoc.
  now rewrite Hu.
Qed.

End CCCPoints.

(** ** B: a transformation out of the constant functor is determined at
       the initial index *)

Section ConstantPoints.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.

(* [Functor_Category_Terminal AT]'s object is [Constant_Terminal_Functor
   AT], the constant functor at 1_A, so a component of [a] at [j] has
   type [1_A ~> E j] on the nose -- no transport is involved. *)
Definition fun_const_point {E : J ⟶ A}
  (a : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
         ~{[J, A]}~> E) :
  @terminal_obj A AT ~{A}~> E (@initial_obj J JI) :=
  @transform _ _ _ _ a (@initial_obj J JI).

(* The arrow action of the constant functor is the identity, so the
   naturality square at [zero j : 0 ~> j] reads
   [fmap[E] (zero j) o a_0 ~ a_j o id], and the component at [j] is
   forced by the component at [0]. *)
Lemma fun_const_point_inj {E : J ⟶ A}
  (a b : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
           ~{[J, A]}~> E) :
  fun_const_point a ≈ fun_const_point b -> a ≈ b.
Proof.
  intros H j.
  pose proof (@naturality _ _ _ _ a _ _ (@zero J JI j)) as Na.
  pose proof (@naturality _ _ _ _ b _ _ (@zero J JI j)) as Nb.
  simpl in Na, Nb.
  rewrite id_right in Na, Nb.
  rewrite <- Na, <- Nb.
  unfold fun_const_point in H.
  now rewrite H.
Qed.

End ConstantPoints.

(** ** C: the engine *)

Section Engine.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.
Context {CC : @Cartesian ([J, A])}.
Context {CL : @Closed ([J, A]) CC}.

(* Hom_{[J,A]}(P, Q) injects into Hom_A(1_A, (Q^P) 0).  The [Cartesian]
   structure [CC] is arbitrary; the TERMINAL object is supplied here as
   the pointwise one, which is what makes section B applicable. *)
Definition fun_hom_point {P Q : [J, A]} (f : P ~{[J, A]}~> Q) :
  @terminal_obj A AT
    ~{A}~> (@exponent_obj _ CC CL P Q) (@initial_obj J JI) :=
  @fun_const_point J A JI AT (@exponent_obj _ CC CL P Q)
    (@ccc_point ([J, A]) CC (Functor_Category_Terminal AT) CL P Q f).

Lemma fun_hom_point_inj {P Q : [J, A]} (f g : P ~{[J, A]}~> Q) :
  fun_hom_point f ≈ fun_hom_point g -> f ≈ g.
Proof.
  intro H.
  apply (@ccc_point_inj ([J, A]) CC (Functor_Category_Terminal AT) CL).
  apply (@fun_const_point_inj J A JI AT).
  exact H.
Qed.

End Engine.

(** ** D: a local pigeonhole principle for [Fin.t]

    Neither statement below exists in the tree; see the header for what
    was searched and what was reused.  The nearest prior art for
    [nodup_map_inj] is [map_FS_NoDup] (Instance/Matr/Determinant.v:1227),
    which is its instance at [h := Fin.FS]; the general statement is
    absent. *)

Lemma nodup_map_inj {A B : Type} (h : A -> B) (l : list A) :
  (forall x y, h x = h y -> x = y) ->
  List.NoDup l -> List.NoDup (List.map h l).
Proof.
  intros Hinj Hnd.
  induction Hnd as [| a l Hnin Hnd IH]; simpl.
  - constructor.
  - constructor; [ | exact IH ].
    intro Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [b [Hb Hb']].
    apply Hinj in Hb; subst.
    contradiction.
Qed.

(* There is no injective family [nat -> Fin.t N]: restrict it along
   [Fin.to_nat] to get [S N] distinct elements of an [N]-element type. *)
Lemma fin_no_nat_injection {N : nat} (w : nat -> Fin.t N)
  (winj : forall i j, w i = w j -> i = j) : False.
Proof.
  pose (v := fun i : Fin.t (S N) => w (proj1_sig (Fin.to_nat i))).
  assert (vinj : forall i j, v i = v j -> i = j).
  { intros i j Hij; apply Fin.to_nat_inj; now apply winj. }
  assert (Hnd : List.NoDup (List.map v (fin_enum (S N))))
    by (apply nodup_map_inj; [ exact vinj | apply fin_enum_nodup ]).
  assert (Hincl : List.incl (List.map v (fin_enum (S N))) (fin_enum N))
    by (intros x _; apply fin_enum_full).
  pose proof (List.NoDup_incl_length Hnd Hincl) as Hle.
  rewrite length_of_map, !fin_enum_length in Hle.
  exact (Nat.nle_succ_diag_l N Hle).
Qed.

(** ** E: Mac Lane §IV.6 Exercise 5 *)

(* The hypothesis of the exercise, consumed by name so that the theorem
   below is visibly about a cartesian closed TARGET: skeletal [FinSet]
   is cartesian closed, with n^m the canonical (n^m)-element set. *)
Definition FinSet_is_cartesian_closed : @Closed FinSet FinSet_Cartesian :=
  FinSet_Closed.

(* An arrow of [Omega] is a derivation of [le_t n m]; it is the identity
   exactly in the [le_t_n] branch.  [two_map] sends the identity to the
   identity of the two-element set and every genuine step to the
   constant map at [Fin.F1].  Both equalities below are in [FinSet]'s
   hom-setoid [fun_setoid], which is pointwise Leibniz equality of
   functions [Fin.t 2 -> Fin.t 2], and in [Omega]'s [Morphism_equality],
   which is Leibniz equality of arrows -- so [fmap_respects] is
   discharged by substitution. *)
Definition two_map@{h} {n m : nat} (f : le_t@{h} n m) : Fin.t 2 -> Fin.t 2 :=
  match f with
  | le_t_n   => fun i => i
  | le_t_S _ => fun _ => Fin.F1
  end.

(* Functoriality.  Composition in [Omega] is [compose f g = le_t_trans g
   f], and [le_t_trans] recurses on its SECOND argument, so a case split
   on [f] reduces both sides at once.

   THE UNIVERSE BINDERS HERE ARE LOAD-BEARING, and that is measured:
   written without them the same body minimizes to
   [Omega@{_ Set Set} ⟶ FinSet@{...}], pinning [Omega]'s hom and proof
   universes to the literal [Set], and the section below -- where
   [Omega, FinSet] is elaborated once, for the [Cartesian] parameter --
   then declines the resulting object.  Spelling the binders out leaves
   both categories free.  Test/ProbeFunClosed392.v pins the rejection
   against the annotated form as its control. *)
Program Definition TwoFun@{o h p u u0 u1 u2 +}
  : Omega@{o h p} ⟶ FinSet@{u u0 u1 u2} := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

(* The k-th family: the identity at stage [S k], the constant map at
   [Fin.F1] everywhere else. *)
Definition alpha_fam (k n : nat) : Fin.t 2 -> Fin.t 2 :=
  match Nat.eq_dec n (S k) with
  | left  _ => fun i => i
  | right _ => fun _ => Fin.F1
  end.

Lemma alpha_fam_F1 (k n : nat) : alpha_fam k n Fin.F1 = Fin.F1.
Proof. unfold alpha_fam; destruct (Nat.eq_dec n (S k)); reflexivity. Qed.

(* Naturality.  At [le_t_n] the square is an identity; at [le_t_S _]
   both sides reduce to [Fin.F1], because every component of
   [alpha_fam k] preserves [Fin.F1]. *)
Program Definition Alpha@{o h p u u0 u1 u2 +} (k : nat)
  : TwoFun@{o h p u u0 u1 u2} ⟹ TwoFun@{o h p u u0 u1 u2} := {|
  transform := fun n => alpha_fam k n
|}.
Next Obligation.
  destruct f; simpl; [ reflexivity | symmetry; apply alpha_fam_F1 ].
Qed.
Next Obligation.
  destruct f; simpl; [ reflexivity | apply alpha_fam_F1 ].
Qed.

(* The family is injective: [Alpha k] and [Alpha j] already differ at
   stage [S k], applied to the second element of the two-element set. *)
Lemma Alpha_distinct (k j : nat) : Alpha k ≈ Alpha j -> k = j.
Proof.
  intro H.
  destruct (Nat.eq_dec k j) as [Hkj | Hkj]; [ exact Hkj | ].
  exfalso.
  specialize (H (S k) (Fin.FS Fin.F1)).
  simpl in H; unfold alpha_fam in H.
  destruct (Nat.eq_dec (S k) (S k)) as [_ | Hne]; [ | now apply Hne ].
  destruct (Nat.eq_dec (S k) (S j)) as [He | _].
  - apply Hkj; now injection He.
  - discriminate H.
Qed.

(* In [FinSet] every element of the one-element object is [Fin.F1]
   ([fin1_unique]), so a morphism [1 ~> n] is determined by its value
   there.  The [=] is [fun_setoid]'s pointwise Leibniz equality. *)
Lemma finset_point_eq {n : nat}
  (u v : @hom FinSet 1%nat n) : u Fin.F1 = v Fin.F1 -> u ≈ v.
Proof.
  intros H i.
  now rewrite (fin1_unique i).
Qed.

Section MacLaneEx5.

(* An ARBITRARY cartesian structure on the functor category, and an
   arbitrary cartesian closed structure over it. *)
Context (CC : @Cartesian ([Omega, FinSet])).
Context (CL : @Closed ([Omega, FinSet]) CC).

(* The object of [FinSet] -- a natural number -- at which the engine
   lands: the value at stage 0 of the exponential of [TwoFun] by
   itself. *)
Definition exp_card : nat :=
  (@exponent_obj _ CC CL TwoFun TwoFun)
    (@initial_obj Omega Omega_Initial).

(* Each [Alpha k] becomes an element of an [exp_card]-element set. *)
Definition alpha_index (k : nat) : Fin.t exp_card :=
  @fun_hom_point Omega FinSet Omega_Initial FinSet_Terminal CC CL
    TwoFun TwoFun (Alpha k) Fin.F1.

Lemma alpha_index_inj (k j : nat) : alpha_index k = alpha_index j -> k = j.
Proof.
  intro H.
  apply Alpha_distinct.
  apply (@fun_hom_point_inj Omega FinSet Omega_Initial FinSet_Terminal
           CC CL TwoFun TwoFun).
  now apply finset_point_eq.
Qed.

End MacLaneEx5.

(* Mac Lane §IV.6 Exercise 5: [FinSet] is cartesian closed, [Omega] is a
   small category, and the functor category is not cartesian closed --
   under ANY cartesian structure on it, not merely the pointwise one. *)
Theorem fun_not_cartesian_closed
  (CC : @Cartesian ([Omega, FinSet])) :
  @Closed ([Omega, FinSet]) CC -> False.
Proof.
  intro CL.
  exact (fin_no_nat_injection (alpha_index CC CL) (alpha_index_inj CC CL)).
Qed.

(* The hypothesis of the theorem is not vacuous for want of a cartesian
   structure: the pointwise one exists.  What is refuted is the
   existence of a [Closed] structure over it, or over any other. *)
Corollary fun_pointwise_not_cartesian_closed :
  @Closed ([Omega, FinSet])
    (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian) -> False.
Proof. exact (fun_not_cartesian_closed _). Qed.

(** ** F: Awodey §8.7 -- the objectwise formula gives the wrong object *)

(* Presheaves on the walking arrow.  [_2^op]'s initial object is [TwoY],
   which is [Two_Terminal] read in the opposite category: [Initial C] is
   notation for [@Terminal (C^op)] and [(C^op)^op] is [C], so no
   transport is needed and the constant below typechecks by conversion. *)
Definition TwoOpInitial : @Initial (_2^op) := Two_Terminal.

(* [PresheafP] is the representable at [TwoX], built directly.  Its
   value at [TwoX] is the terminal setoid and at [TwoY] the initial
   (empty) one, so that the unique arrow [TwoY ~> TwoX] of [_2^op] acts
   as the empty map. *)
Definition PObj (x : TwoObj) : Sets :=
  match x with
  | TwoX => @terminal_obj Sets Sets_Terminal
  | TwoY => @initial_obj Sets Sets_Initial
  end.

Definition PMap (a b : TwoObj) :
  @hom (_2^op) a b -> (PObj a ~{Sets}~> PObj b).
Proof.
  destruct a, b; intro f.
  - exact id.
  - exact (False_rect _ (TwoHom_Y_X_absurd f)).
  - exact (@zero Sets Sets_Initial _).
  - exact id.
Defined.

(* Any two morphisms out of the empty setoid agree, which discharges
   every case of [fmap_comp] that is not an identity. *)
Program Definition PresheafP : _2^op ⟶ Sets := {|
  fobj := PObj;
  fmap := PMap
|}.
Next Obligation. now destruct x. Qed.
Next Obligation.
  destruct x, y, z; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f)
          | contradiction (TwoHom_Y_X_absurd g) ].
Qed.

(* The two-element setoid, under Leibniz equality on [bool]. *)
Definition two_elt : Sets :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Definition PresheafQ : _2^op ⟶ Sets := Constant_Functor two_elt.

(* A transformation [PresheafP ==> PresheafQ] for each boolean: the
   component at [TwoX] picks a point of [two_elt], the component at
   [TwoY] is the unique map out of the empty setoid, and the single
   naturality square is an equation between maps out of that setoid. *)
Program Definition PQNat (b : bool) : PresheafP ⟹ PresheafQ := {|
  transform := fun x =>
    match x return PObj x ~{Sets}~> two_elt with
    | TwoX => {| morphism := fun _ => b
               ; proper_morphism := fun _ _ _ => reflexivity b |}
    | TwoY => @zero Sets Sets_Initial two_elt
    end
|}.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.

Lemma PQNat_distinct : PQNat true ≈ PQNat false -> False.
Proof.
  intro H.
  exact (Bool.diff_true_false (H TwoX ttt)).
Qed.

Section AwodeyPointwise.

Context (CC : @Cartesian ([_2^op, Sets])).
Context (CL : @Closed ([_2^op, Sets]) CC).

(* The engine at the presheaf category: two distinct points of
   (Q^P) TwoY. *)
Definition pq_point (b : bool) :
  @terminal_obj Sets Sets_Terminal
    ~{Sets}~> (@exponent_obj _ CC CL PresheafP PresheafQ) TwoY :=
  @fun_hom_point (_2^op) Sets TwoOpInitial Sets_Terminal CC CL
    PresheafP PresheafQ (PQNat b).

Lemma pq_point_distinct : pq_point true ≈ pq_point false -> False.
Proof.
  intro H.
  apply PQNat_distinct.
  exact (@fun_hom_point_inj (_2^op) Sets TwoOpInitial Sets_Terminal
           CC CL PresheafP PresheafQ (PQNat true) (PQNat false) H).
Qed.

(* The objectwise candidate Q(TwoY)^{P(TwoY)}: in [Sets], the
   exponential of the two-element setoid by the empty one.  Any two of
   its points are equivalent, because two of its elements are maps out
   of the empty setoid. *)
Definition objectwise_candidate : Sets :=
  @exponent_obj Sets Sets_Cartesian Sets_Closed
    (PresheafP TwoY) (PresheafQ TwoY).

Lemma objectwise_candidate_subsingleton
  (u v : @terminal_obj Sets Sets_Terminal ~{Sets}~> objectwise_candidate) :
  u ≈ v.
Proof. intros x; simpl; intros []. Qed.

(* Awodey's objectwise formula, refuted at the level of OBJECTS: there
   is no isomorphism in [Sets] between the true value of the
   exponential at [TwoY] and the objectwise candidate.  Since the
   argument uses only that the two objects are isomorphic, no
   contravariant action on the objectwise family can repair it. *)
Theorem awodey_pointwise_not_exponential :
  @Isomorphism Sets
    ((@exponent_obj _ CC CL PresheafP PresheafQ) TwoY)
    objectwise_candidate -> False.
Proof.
  intro i.
  apply pq_point_distinct.
  apply (@monic Sets _ _ (to i) (iso_to_monic i)).
  apply objectwise_candidate_subsingleton.
Qed.

End AwodeyPointwise.
