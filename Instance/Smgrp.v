Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Semigroup.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Words and free semigroups: the category Smgrp and the adjunction
      Set ⇀ Smgrp *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.4 "Words and Free Semigroups", printed
         p. 144 (PDF p. 153), the construction before Proposition 1 —
         maclane:VI.4:construction1
   nLab: https://ncatlab.org/nlab/show/semigroup
   nLab: https://ncatlab.org/nlab/show/free+monoid

   WHAT THE BOOK SAYS, read from the page image.  "The free semigroup WX
   on a set X is like the free monoid on X (§ II.7).  It consists of all
   words ⟨x1⟩ … ⟨xn⟩ of positive length n spelled in letters xi ∈ X,
   where we write ⟨x⟩ to distinguish the word ⟨x⟩ in WX from the element
   x ∈ X.  Words are multiplied by juxtaposition, … this multiplication ν
   is associative, so makes FX = ⟨WX, ν⟩ a semigroup, with the set WX the
   disjoint union ∐ Xⁿ, n = 1, 2, ….  If G : Smgrp → Set is the forgetful
   functor from the category of all small semigroups (forget the
   multiplication), then the arrow η_X : X → GFX defined by x ↦ ⟨x⟩ (send
   each x to the one-letter word in x) is universal from X to G.
   Therefore F is a functor, left adjoint to G, and η defines an
   adjunction ⟨F, G, η, ε⟩ : Set ⇀ Smgrp."  The counit "is the unique
   morphism of semi-groups which sends each generator ⟨s⟩ to s.  This
   means that ε_S(⟨s1⟩ … ⟨sn⟩) = s1 … sn (product in S) (1) for all
   si ∈ S: The counit ε removes the 'pointy bracket' ⟨ ⟩."

   THE ENCODING.  [SmgrpSets] is Theory/Algebra/Semigroup.v's [Smgrp] at
   (Sets, ×), Mac Lane's Smgrp of semigroups on setoids, and [Sg_Forget]
   is G.  [Tup A n] is A^(n+1), so that the words [PWord X], the sigma of
   [Tup X], are ∐ Xⁿ for n = 1, 2, … literally, a word (n; t) carrying its
   length; [tup_eq] compares letterwise up to ≈ and is False across
   lengths.  The lists of Instance/Mon/Free.v, the free MONOID on a
   setoid, are not reused (that file came with the free ring of Mac
   Lane's §IV.8 Exercise 2, #400; #296's free monoid is
   Instance/Coq/Monoid/Free.v's, at Coq).  Two reasons separate the
   encodings.  Those lists include the empty word: they are the carrier
   of W₀ = ∐_{n≥0} Xⁿ (#471), not of W, so a semigroup carrier would need
   a nonemptiness encoding over them in any case.  And Proposition 2
   (Instance/Smgrp/Word.v) reads an algebra on W S as one n-ary operation
   on Sⁿ for each n, which a sigma of tuples gives by conversion and lists
   would give only through Tup ↔ list conversions (argued, not built for
   lists).  That file's counit does not compute (its own header measures
   it: the underlying map goes through Theory/Universal/Arrow.v's
   [ump_universal_arrows], closed with [Qed]), but that is how it packages
   its adjunction, from universal arrows, and not a property of lists:
   [Sg_adj] below is built from the hom-set bijection, and so built over a
   list carrier its counit would compute too (argued).  Two shared routes
   were measured and not taken.  Instance/Variety.v's varieties: an
   equation signature for associativity costs
   [functional_extensionality_dep] (Instance/Variety.v records it of
   associativity alone over Instance/Comp.v's [GroupOp], and the #470
   scout measured it of an associativity signature over Instance/
   Variety.v's [MagmaOp]), where this development keeps [Print
   Assumptions] closed.  Lib/NETList.v's nonempty lists: they are
   type-aligned paths in a quiver, their equality decided through
   Equations' [eq_dec] and [rew] casts on the indices, not ∐ Xⁿ.  #471's
   W₀ can reuse [Tup] through a zero-based Tup0 X 0 = unit and
   Tup0 X (S n) = Tup X n (the name Pow is taken, by Structure/Topos.v
   and Instance/Fun/Discrete.v), without changing anything here.  The
   element-level accessors
   ([sg_ob], [sg_mul], [sg_fun], [mk_sg_obj], [mk_sg_hom]) follow
   Instance/Mon/Coproduct.v's mon_* layer.  Names that would shadow
   Instance/Mon/Free.v's ([wapp], [wmap], [Word_Setoid], [WordObj]),
   Construction/FreeMonoidal.v's [Word] or Theory/Multicategory/
   Representable.v's [tfold] are avoided: [PWord], [pwapp], [pwmap],
   [PWord_Setoid], [PWordObj], [tfold1].

   WHAT IS HERE, statement by statement.
     - "words … multiplied by juxtaposition": [pwapp], the juxtaposition
       of tuples [tapp]; [FreeSg_mul] and [FreeSg_mul_literal] at
       [eq_refl].  "This multiplication ν is associative": [pwapp_assoc],
       at ≈; on literal words it holds at [eq_refl] (Test/ProbeWord470.v,
       C6) and at variable words it is refused there (R1), the lengths
       S (S (n + m) + p) and S (n + S (m + p)) being stuck on n.
     - "FX = ⟨WX, ν⟩ a semigroup": [FreeSg X], whose carrier IS the setoid
       of words ([FreeSg_carrier], at [eq_refl]); F on arrows is the
       letterwise map [pwmap] ([FreeSg_map], [Sg_Free]).
     - "η_X … defined by x ↦ ⟨x⟩ … is universal from X to G":
       [sg_insert], and [sg_insert_universal], the unique factorization
       of every h : X → G A as G g ∘ η_X, its factor the fold [sg_extend h]
       at [eq_refl] ([sg_insert_universal_obj]); the fold, w ↦ h(x1) ⋯
       h(xn) bracketed to the left, is [pwfold] over [tfoldl] and
       [tfold1], and a semigroup map out of F X is that fold of its values
       on the letters ([sg_extend_unique], at ≈; at a one-letter word at
       [eq_refl], C17, and at a variable word refused, R5).  "Universal
       from X to G" is Theory/Universal/Arrow.v's notion, and η_X is
       [sg_insert_UA X : UniversalArrow X G], built from
       [sg_insert_universal] by [universal_arrow_from_UMP]; its universal
       object is F X and its arrow η_X as a setoid map, at [eq_refl]
       ([sg_insert_UA_obj], [sg_insert_UA_arrow]).  [Sg_adj] does not go
       through it, so its counit computes (below).
     - "F is a functor, left adjoint to G, and η defines an adjunction":
       [Sg_adj], through Theory/Adjunction.v's hom-set constructor
       [Build_Adjunction'] from the natural bijection [Sg_adj_iso], as
       Instance/SupLat/Free.v builds [SL_adj] (#466), so that the counit
       computes; its unit IS [sg_insert] as a setoid map
       ([Sg_adj_unit], at [eq_refl]).  That readback needs #1347, which
       gave Instance/Sets.v's identity and composite their properness
       fields as terms: compiled against a built tree of master 687ac356,
       before #1347, it is refused ("cannot unify"), and it is the only
       command of this file that is.
     - The counit "sends each generator ⟨s⟩ to s" ([Sg_adj_counit_letter])
       and is (1): ε_S is the fold of the identity, w ↦ s1 ⋯ sn bracketed
       to the left ([Sg_adj_counit]), on a literal word (s1 s2) s3
       ([Sg_adj_counit_literal]), all at [eq_refl]; the right bracketing
       s1 (s2 s3) holds at ≈ (C16) and is refused at [eq_refl] (R4).

   STRENGTHS.  Every [Example] above holds at [eq_refl], and
   Test/ProbeWord470.v restates each one (C3 to C5, C11 to C15, C68 and
   C69).  Seven proofs end [Defined] (counted by token) and all seven are
   load-bearing, measured by closing each alone [Qed] in a scratch copy of
   this file, Instance/Smgrp/Word.v and the probe: [mk_sg_obj] (then
   [FreeSg_carrier] stops), [mk_sg_hom] and [FreeSg_map] ([Sg_Free]),
   [Sg_Free] ([Sg_adj_iso]), [sg_insert_universal]
   ([sg_insert_universal_obj]), [Sg_adj_iso] ([Sg_adj]) and [Sg_adj]
   ([Sg_adj_unit]).  [sg_insert_UA] is a term, and its two readbacks
   reduce through Theory/Universal/Arrow.v's [universal_arrow_from_UMP],
   which ends [Defined].  The twenty-two lemmas end [Qed].  Two of them,
   the auxiliary fold lemmas [tfoldl_tapp] and [tfold1_tapp], state a
   Leibniz equality between elements of a semigroup, proved by induction
   on the first tuple: stronger than ≈, which is all that [pwfold_pwapp],
   rewriting with the second, needs (Instance/Smgrp/Word.v's
   [tfoldl_tmap] and [tfold1_tmap] are the other two; a scan of the
   statements of the three files for [=] finds those four and the
   [eq_refl] readbacks, and no other).  The refusals R1, R4 and R5 stand
   in a copy of the three targets with every [Qed] turned [Defined] and
   [Transparent Obligations] set (the probe's header), so none of them is
   the opacity of these files.

   UNIVERSES, read off [About].  The tuples and words bind @{o}: [Tup],
   [PWord] and [letter] with no constraint, the rest ([tup_eq], [tapp],
   [tmap], [pwapp], [pwmap], their lemmas and the setoid of words) with
   caps of the standard library only (pair and sigma projections,
   [nat_rect], [False_rect]).  Everything over [SmgrpSets] binds
   @{o so} with the one constraint o < so besides caps; [SmgrpSets@{o so}
   : Category@{so o o}] carries exactly the block of
   [Sets_Product_Monoidal@{so o}] (o < so, the strict caps
   o < projections.u0 and o < projections.u1, so <= projections.u0,
   so <= projections.u1, and the caps compose, ID, RelationClasses.Defs,
   eq_ind, eq_ind_r and Logic_lemmas.equality on o) with the three caps
   of the sigma projections added
   (o <= Projections.u0, o <= Projections.u1, so <= Projections.u0).
   [Sg_adj] is [Adjunction@{so o o so o o o o so o so}], the instance of
   Instance/SupLat/Free.v's [SL_adj]: left unpinned, the same term binds
   a third level that occurs in no constraint (measured in a scratch
   file, @{u u0 u1} with u alone free), the phantom level the pin
   removes.  [sg_insert_UA] and its two readbacks bind @{o so} on Rocq
   9.1.1: their [UniversalArrow@{so o so o o so so so so o so}] pins the
   seven levels the class binds beyond its two categories' at the least
   of o and so their constraints allow (left free, the same term binds
   three more, measured in a scratch file: one bounded below by so, one
   by o, and one only from above, by those two), and each block is
   [sg_insert_universal]'s with the three caps of [prod_rect] added.  The
   annotation is extensible, @{o so +}, for Coq 8.19.2 and 8.20.1, where
   Theory/Universal/Arrow.v's [universal_arrow_from_UMP] binds fifteen
   levels to Rocq 9.1.1's eleven (an eleven-level instance of it is
   refused there, "Universe instance length is 11 but should be 15"):
   there the three bind one level more, u, in the body only, with o < u
   and Set < u, a bound and not an equation.  Otherwise no [Set] and no
   equation, on Rocq 9.1.1, Coq 8.19.2 and 8.20.1 alike (compared by
   script; the caps' names differ by version).

   NOT DELIVERED.  The free semigroup on a set as a quotient of lists or
   under Leibniz equality; the free semigroup functor's preservation of
   coproducts; any comparison with Instance/Mon/Free.v's free monoid
   (W₀ and the monoid case are #471's).  The monad W, Propositions 1 and
   2, the Corollary and the comparison functor are
   Instance/Smgrp/Word.v. *)

(* ------------------------------------------------------------------------ *)
(** ** Smgrp, the semigroups in (Sets, ×), and its forgetful functor G *)

Definition SmgrpSets@{o so} : Category@{so o o} :=
  @Smgrp@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}.

Definition Sg_Forget@{o so} : SmgrpSets@{o so} ⟶ Sets@{o so} :=
  @Smgrp_Forget@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}.

(** ** Element-level accessors (after Instance/Mon/Coproduct.v's mon_* ) *)

Definition sg_ob@{o so} (A : SmgrpSets@{o so}) : SetoidObject@{o o} := `1 A.

(* The multiplication ν of A, curried: ν(a, b). *)
Definition sg_mul@{o so} (A : SmgrpSets@{o so}) (a b : sg_ob@{o so} A) :
  sg_ob@{o so} A :=
  @smu Sets@{o so} Sets_Product_Monoidal@{so o} _ (`2 A) (a, b).

Lemma sg_mul_respects@{o so} (A : SmgrpSets@{o so}) :
  Proper (equiv ==> equiv ==> equiv) (sg_mul@{o so} A).
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism (@smu Sets@{o so} Sets_Product_Monoidal@{so o} _
                            (`2 A)) (a, b) (a', b') (Ha, Hb)).
Qed.

#[export] Existing Instance sg_mul_respects.

Lemma sg_mul_assoc@{o so} (A : SmgrpSets@{o so}) (a b c : sg_ob@{o so} A) :
  sg_mul A (sg_mul A a b) c ≈ sg_mul A a (sg_mul A b c).
Proof.
  exact (@smu_assoc Sets@{o so} Sets_Product_Monoidal@{so o} _ (`2 A)
           ((a, b), c)).
Qed.

Definition sg_fun@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) : sg_ob@{o so} A → sg_ob@{o so} B :=
  `1 f.

Lemma sg_fun_respects@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) : Proper (equiv ==> equiv) (sg_fun f).
Proof. exact (proper_morphism (`1 f)). Qed.

#[export] Existing Instance sg_fun_respects.

Lemma sg_fun_mul@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) (a b : sg_ob@{o so} A) :
  sg_fun f (sg_mul A a b) ≈ sg_mul B (sg_fun f a) (sg_fun f b).
Proof.
  exact (@shom_mu Sets@{o so} Sets_Product_Monoidal@{so o} _ _ _ _ _ (`2 f)
           (a, b)).
Qed.

(* A setoid with an associative binary operation respecting ≈ is an object
   of Smgrp: ν(p) := op (fst p) (snd p). *)
Definition mk_sg_obj@{o so} (S : SetoidObject@{o o})
  (op : S → S → S) (opr : Proper (equiv ==> equiv ==> equiv) op)
  (oassoc : ∀ a b c, op (op a b) c ≈ op a (op b c)) : SmgrpSets@{o so}.
Proof.
  unshelve refine
    (S; @Build_Semigroup Sets@{o so} Sets_Product_Monoidal@{so o} S
          {| morphism := fun p => op (fst p) (snd p) |} _).
  - intros [a b] [a' b'] [Ha Hb]. exact (opr _ _ Ha _ _ Hb).
  - intros [[a b] c]. exact (oassoc a b c).
Defined.

(* A function respecting ≈ and the two multiplications is an arrow of
   Smgrp. *)
Definition mk_sg_hom@{o so} {A B : SmgrpSets@{o so}}
  (f : sg_ob@{o so} A → sg_ob@{o so} B)
  (fp : Proper (equiv ==> equiv) f)
  (fm : ∀ a b, f (sg_mul A a b) ≈ sg_mul B (f a) (f b)) :
  A ~{SmgrpSets@{o so}}~> B.
Proof.
  unshelve refine
    (({| morphism := f; proper_morphism := fp |}
        : sg_ob A ~{Sets@{o so}}~> sg_ob B); _).
  constructor.
  intros [a b]. exact (fm a b).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Tuples: [Tup A n] is A^(n+1), a positive power *)

Fixpoint Tup@{o} (A : Type@{o}) (n : nat) : Type@{o} :=
  match n with
  | O => A
  | S n' => prod A (Tup A n')
  end.

(* Letterwise ≈, and False across lengths. *)
Fixpoint tup_eq@{o} {X : SetoidObject@{o o}} (n m : nat) :
  Tup@{o} X n → Tup@{o} X m → Type@{o} :=
  match n as n0, m as m0 return Tup X n0 → Tup X m0 → Type@{o} with
  | O, O => fun a b => a ≈ b
  | S n', S m' => fun t u =>
      prod (fst t ≈ fst u) (tup_eq n' m' (snd t) (snd u))
  | _, _ => fun _ _ => False
  end.

Lemma tup_eq_refl@{o} {X : SetoidObject@{o o}} (n : nat) (t : Tup@{o} X n) :
  tup_eq n n t t.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - split; [ reflexivity | apply IH ].
Qed.

Lemma tup_eq_sym@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq n m t u → tup_eq m n u t.
Proof.
  revert m t u; induction n as [|n IH]; intros [|m] t u H; simpl in *;
    try contradiction.
  - symmetry; exact H.
  - destruct H as [H1 H2].
    split; [ symmetry; exact H1 | apply IH; exact H2 ].
Qed.

Lemma tup_eq_trans@{o} {X : SetoidObject@{o o}} (n m p : nat)
  (t : Tup@{o} X n) (u : Tup@{o} X m) (v : Tup@{o} X p) :
  tup_eq n m t u → tup_eq m p u v → tup_eq n p t v.
Proof.
  revert m p t u v; induction n as [|n IH];
    intros [|m] [|p] t u v H K; simpl in *; try contradiction.
  - transitivity u; assumption.
  - destruct H as [H1 H2], K as [K1 K2]; split.
    + transitivity (fst u); assumption.
    + exact (IH _ _ _ _ _ H2 K2).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Words: Mac Lane's W X = ∐_{n≥1} X^n, as a sigma of tuples *)

Definition PWord@{o} (X : SetoidObject@{o o}) : Type@{o} :=
  sigT (fun n : nat => Tup@{o} X n).

Definition pword_eq@{o} {X : SetoidObject@{o o}} (w v : PWord@{o} X) :
  Type@{o} :=
  tup_eq (projT1 w) (projT1 v) (projT2 w) (projT2 v).

Definition pword_eq_Equivalence@{o} (X : SetoidObject@{o o}) :
  Equivalence@{o o} (@pword_eq@{o} X) :=
  {| Equivalence_Reflexive  := fun w => tup_eq_refl (projT1 w) (projT2 w)
   ; Equivalence_Symmetric  := fun w v =>
       tup_eq_sym _ _ (projT2 w) (projT2 v)
   ; Equivalence_Transitive := fun w v u =>
       tup_eq_trans _ _ _ (projT2 w) (projT2 v) (projT2 u) |}.

Definition PWord_Setoid@{o} (X : SetoidObject@{o o}) : Setoid@{o o} (PWord X) :=
  {| equiv := @pword_eq@{o} X ; setoid_equiv := pword_eq_Equivalence X |}.

#[export] Existing Instance PWord_Setoid.

Definition PWordObj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier := PWord@{o} X ; is_setoid := PWord_Setoid@{o} X |}.

(* The one-letter word ⟨x⟩. *)
Definition letter@{o} {X : SetoidObject@{o o}} (x : X) : PWord@{o} X :=
  existT (fun n => Tup X n) O x.

(* ------------------------------------------------------------------------ *)
(** ** Juxtaposition *)

Fixpoint tapp@{o} {A : Type@{o}} (n m : nat) :
  Tup@{o} A n → Tup@{o} A m → Tup@{o} A (S (n + m)%nat) :=
  match n as n0 return Tup A n0 → Tup A m → Tup A (S (n0 + m)%nat) with
  | O => fun a u => (a, u)
  | S n' => fun t u => (fst t, tapp n' m (snd t) u)
  end.

Definition pwapp@{o} {X : SetoidObject@{o o}} (w v : PWord@{o} X) :
  PWord@{o} X :=
  existT (fun n => Tup X n) (S (projT1 w + projT1 v)%nat)
    (tapp (projT1 w) (projT1 v) (projT2 w) (projT2 v)).

Lemma tapp_respects@{o} {X : SetoidObject@{o o}} (n n' m m' : nat)
  (t : Tup@{o} X n) (t' : Tup@{o} X n') (u : Tup@{o} X m)
  (u' : Tup@{o} X m') :
  tup_eq n n' t t' → tup_eq m m' u u' →
  tup_eq _ _ (tapp n m t u) (tapp n' m' t' u').
Proof.
  intros Ht Hu; revert n' t t' Ht.
  induction n as [|n IH]; intros [|n'] t t' Ht; try contradiction.
  - split; [ exact Ht | exact Hu ].
  - destruct Ht as [H1 H2].
    split; [ exact H1 | exact (IH n' (snd t) (snd t') H2) ].
Qed.

Lemma pwapp_respects@{o} {X : SetoidObject@{o o}} :
  Proper (equiv ==> equiv ==> equiv) (@pwapp@{o} X).
Proof.
  intros w w' Hw v v' Hv.
  exact (tapp_respects _ _ _ _ _ _ _ _ Hw Hv).
Qed.

Lemma tapp_assoc@{o} {X : SetoidObject@{o o}} (n m p : nat)
  (t : Tup@{o} X n) (u : Tup@{o} X m) (v : Tup@{o} X p) :
  tup_eq _ _ (tapp _ p (tapp n m t u) v) (tapp n _ t (tapp m p u v)).
Proof.
  induction n as [|n IH].
  - exact (tup_eq_refl (S (S (m + p)))%nat (t, tapp m p u v)).
  - split; [ reflexivity | exact (IH (snd t)) ].
Qed.

Lemma pwapp_assoc@{o} {X : SetoidObject@{o o}} (w v u : PWord@{o} X) :
  pwapp (pwapp w v) u ≈ pwapp w (pwapp v u).
Proof. exact (tapp_assoc _ _ _ (projT2 w) (projT2 v) (projT2 u)). Qed.

(* ------------------------------------------------------------------------ *)
(** ** The free semigroup F X = ⟨W X, juxtaposition⟩ *)

Definition FreeSg@{o so} (X : SetoidObject@{o o}) : SmgrpSets@{o so} :=
  mk_sg_obj@{o so} (PWordObj X) (@pwapp X) (@pwapp_respects X)
    (@pwapp_assoc X).

Example FreeSg_carrier@{o so} (X : SetoidObject@{o o}) :
  sg_ob (FreeSg@{o so} X) = PWordObj X := eq_refl.

Example FreeSg_mul@{o so} (X : SetoidObject@{o o}) (w v : PWord@{o} X) :
  sg_mul (FreeSg@{o so} X) w v = pwapp w v := eq_refl.

(* Juxtaposition on literal words: (⟨x1⟩⟨x2⟩)(⟨y1⟩) = ⟨x1⟩⟨x2⟩⟨y1⟩. *)
Example FreeSg_mul_literal@{o so} (X : SetoidObject@{o o}) (x1 x2 y1 : X) :
  sg_mul (FreeSg@{o so} X) (existT (fun n => Tup X n) 1%nat (x1, x2))
    (letter y1)
    = existT (fun n => Tup X n) 2%nat (x1, (x2, y1)) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Maps of words, and the free functor F *)

Fixpoint tmap@{o} {A B : Type@{o}} (f : A → B) (n : nat) :
  Tup@{o} A n → Tup@{o} B n :=
  match n as n0 return Tup A n0 → Tup B n0 with
  | O => fun a => f a
  | S n' => fun t => (f (fst t), tmap f n' (snd t))
  end.

Definition pwmap@{o} {X Y : SetoidObject@{o o}} (f : X → Y) (w : PWord@{o} X) :
  PWord@{o} Y :=
  existT (fun n => Tup Y n) (projT1 w) (tmap f (projT1 w) (projT2 w)).

Lemma tmap_respects@{o} {X Y : SetoidObject@{o o}} (f g : X → Y)
  (Hfg : ∀ a b, a ≈ b → f a ≈ g b)
  (n m : nat) (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq n m t u → tup_eq n m (tmap f n t) (tmap g m u).
Proof.
  revert m t u; induction n as [|n IH]; intros [|m] t u H; simpl in *;
    try contradiction.
  - exact (Hfg _ _ H).
  - destruct H as [H1 H2].
    split; [ exact (Hfg _ _ H1) | exact (IH _ _ _ H2) ].
Qed.

Lemma tmap_tapp@{o} {X Y : SetoidObject@{o o}} (f : X → Y)
  (n m : nat) (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq _ _ (tmap f _ (tapp n m t u)) (tapp n m (tmap f n t) (tmap f m u)).
Proof.
  induction n as [|n IH].
  - exact (tup_eq_refl (S m) (f t, tmap f m u)).
  - split; [ reflexivity | exact (IH (snd t)) ].
Qed.

Lemma tmap_id@{o} {X : SetoidObject@{o o}} (n : nat) (t : Tup@{o} X n) :
  tup_eq n n (tmap (fun x => x) n t) t.
Proof.
  induction n as [|n IH].
  - cbn; reflexivity.
  - split; [ reflexivity | exact (IH (snd t)) ].
Qed.

Lemma tmap_comp@{o} {X Y Z : SetoidObject@{o o}} (g : Y → Z) (f : X → Y)
  (n : nat) (t : Tup@{o} X n) :
  tup_eq n n (tmap (fun x => g (f x)) n t) (tmap g n (tmap f n t)).
Proof.
  induction n as [|n IH].
  - cbn; reflexivity.
  - split; [ reflexivity | exact (IH (snd t)) ].
Qed.

Definition FreeSg_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  FreeSg@{o so} X ~{SmgrpSets@{o so}}~> FreeSg@{o so} Y.
Proof.
  unshelve refine
    (@mk_sg_hom@{o so} (FreeSg X) (FreeSg Y) (pwmap f) _ _).
  - intros w v H.
    exact (tmap_respects f f (proper_morphism f) _ _ _ _ H).
  - intros w v.
    exact (tmap_tapp f _ _ (projT2 w) (projT2 v)).
Defined.

Definition Sg_Free@{o so} : Sets@{o so} ⟶ SmgrpSets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} SmgrpSets@{o so} FreeSg@{o so}
       (fun X Y f => FreeSg_map@{o so} f) _ _ _).
  - intros X Y f g H w.
    exact (tmap_respects f g
             (fun a b E => transitivity (proper_morphism f _ _ E) (H b))
             _ _ _ _ (tup_eq_refl _ (projT2 w))).
  - intros X w.
    exact (tmap_id (projT1 w) (projT2 w)).
  - intros X Y Z f g w.
    exact (tmap_comp f g (projT1 w) (projT2 w)).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The insertion of generators η_X x = ⟨x⟩ *)

Definition sg_insert@{o so} (X : SetoidObject@{o o}) :
  X ~{Sets@{o so}}~> fobj[Sg_Forget@{o so}] (FreeSg@{o so} X) :=
  {| morphism := fun x => letter x ; proper_morphism := fun _ _ H => H |}.

(* ------------------------------------------------------------------------ *)
(** ** The fold: the product h(x1) ⋯ h(xn), bracketed to the left *)

(* [tfoldl h acc n t] multiplies acc by h of each letter of t in turn. *)
Fixpoint tfoldl@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (acc : sg_ob@{o so} A) (n : nat) :
  Tup@{o} Y n → sg_ob@{o so} A :=
  match n as n0 return Tup Y n0 → sg_ob A with
  | O => fun y => sg_mul A acc (h y)
  | S n' => fun t => tfoldl h (sg_mul A acc (h (fst t))) n' (snd t)
  end.

(* [tfold1 h n t] = h(t1) ⋯ h(tn), seeded by the first letter. *)
Definition tfold1@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (n : nat) : Tup@{o} Y n → sg_ob@{o so} A :=
  match n as n0 return Tup Y n0 → sg_ob A with
  | O => fun y => h y
  | S n' => fun t => tfoldl h (h (fst t)) n' (snd t)
  end.

Definition pwfold@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (h : X → sg_ob@{o so} A) (w : PWord@{o} X) : sg_ob@{o so} A :=
  tfold1 h (projT1 w) (projT2 w).

Lemma tfoldl_respects@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (h h' : X → sg_ob@{o so} A) (Hh : ∀ a b, a ≈ b → h a ≈ h' b)
  (n m : nat) (acc acc' : sg_ob@{o so} A) (t : Tup@{o} X n)
  (u : Tup@{o} X m) :
  acc ≈ acc' → tup_eq n m t u → tfoldl h acc n t ≈ tfoldl h' acc' m u.
Proof.
  revert m acc acc' t u; induction n as [|n IH];
    intros [|m] acc acc' t u Ha H; simpl in *; try contradiction.
  - apply sg_mul_respects; [ exact Ha | exact (Hh _ _ H) ].
  - destruct H as [H1 H2].
    apply IH; [ apply sg_mul_respects; [ exact Ha | exact (Hh _ _ H1) ]
              | exact H2 ].
Qed.

Lemma tfold1_respects@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (h h' : X → sg_ob@{o so} A) (Hh : ∀ a b, a ≈ b → h a ≈ h' b)
  (n m : nat) (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq n m t u → tfold1 h n t ≈ tfold1 h' m u.
Proof.
  destruct n as [|n], m as [|m]; intro H; simpl in *; try contradiction.
  - exact (Hh _ _ H).
  - destruct H as [H1 H2].
    exact (tfoldl_respects h h' Hh _ _ _ _ _ _ (Hh _ _ H1) H2).
Qed.

Lemma tfoldl_tapp@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (acc : sg_ob@{o so} A) (n m : nat)
  (t : Tup@{o} Y n) (u : Tup@{o} Y m) :
  tfoldl h acc _ (tapp n m t u) = tfoldl h (tfoldl h acc n t) m u.
Proof.
  revert acc; induction n as [|n IH]; intro acc; simpl;
    [ reflexivity | apply IH ].
Qed.

Lemma tfold1_tapp@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (n m : nat) (t : Tup@{o} Y n)
  (u : Tup@{o} Y m) :
  tfold1 h _ (tapp n m t u) = tfoldl h (tfold1 h n t) m u.
Proof.
  destruct n as [|n]; simpl; [ reflexivity | apply tfoldl_tapp ].
Qed.

(* The accumulator factors out: tfoldl h acc t ≈ acc · tfold1 h t. *)
Lemma tfoldl_mul@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (acc : sg_ob@{o so} A) (m : nat)
  (u : Tup@{o} Y m) :
  tfoldl h acc m u ≈ sg_mul A acc (tfold1 h m u).
Proof.
  revert acc; induction m as [|m IH]; intro acc; simpl; [ reflexivity | ].
  rewrite IH.
  rewrite sg_mul_assoc.
  apply sg_mul_respects; [ reflexivity | ].
  destruct m as [|m]; simpl; [ reflexivity | ].
  symmetry. apply IH.
Qed.

Lemma pwfold_pwapp@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (h : X → sg_ob@{o so} A) (w v : PWord@{o} X) :
  pwfold h (pwapp w v) ≈ sg_mul A (pwfold h w) (pwfold h v).
Proof.
  change (tfold1 h _ (tapp _ _ (projT2 w) (projT2 v))
            ≈ sg_mul A (pwfold h w) (pwfold h v)).
  rewrite tfold1_tapp.
  apply tfoldl_mul.
Qed.

(* The extension of h : X → G A along the insertion, w ↦ h(x1) ⋯ h(xn). *)
Definition sg_extend@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (h : X ~{Sets@{o so}}~> fobj[Sg_Forget@{o so}] A) :
  FreeSg@{o so} X ~{SmgrpSets@{o so}}~> A :=
  @mk_sg_hom@{o so} (FreeSg X) A (pwfold h)
    (fun w v H => tfold1_respects h h (proper_morphism h) _ _ _ _ H)
    (fun w v => pwfold_pwapp h w v).

(* The extension is unique: a semigroup map out of F X is the fold of its
   values on the letters. *)
Lemma sg_extend_unique@{o so} {X : SetoidObject@{o o}} {A : SmgrpSets@{o so}}
  (g : FreeSg@{o so} X ~{SmgrpSets@{o so}}~> A) (w : PWord@{o} X) :
  sg_fun g w ≈ pwfold (fun x => sg_fun g (letter x)) w.
Proof.
  destruct w as [n t]; unfold pwfold; cbn [projT1 projT2].
  induction n as [|n IH]; [ reflexivity | ].
  destruct t as [x t'].
  (* ⟨x⟩t' is the product ⟨x⟩ · t', on the nose once the pair is split *)
  change (existT (fun n0 => Tup X n0) (S n) (x, t'))
    with (sg_mul (FreeSg X) (letter x) (existT (fun n0 => Tup X n0) n t')).
  rewrite sg_fun_mul.
  rewrite (IH t').
  symmetry.
  exact (tfoldl_mul (fun x0 => sg_fun g (letter x0))
           (sg_fun g (letter x)) n t').
Qed.

(* η_X is universal from X to G: every h : X → G A factors as G g ∘ η_X
   through exactly one semigroup map g, the extension of h. *)
Definition sg_insert_universal@{o so} (X : SetoidObject@{o o})
  (A : SmgrpSets@{o so}) (h : X ~{Sets@{o so}}~> fobj[Sg_Forget@{o so}] A) :
  ∃! g : FreeSg@{o so} X ~{SmgrpSets@{o so}}~> A,
    h ≈ fmap[Sg_Forget@{o so}] g ∘ sg_insert@{o so} X.
Proof.
  unshelve refine {| unique_obj := sg_extend@{o so} h |}.
  - intro x. reflexivity.
  - intros g Hg w. simpl.
    transitivity (pwfold (fun x => sg_fun g (letter x)) w).
    + apply tfold1_respects; [ | exact (tup_eq_refl _ (projT2 w)) ].
      intros a b E. transitivity (h b).
      * exact (proper_morphism h _ _ E).
      * exact (Hg b).
    + symmetry. exact (sg_extend_unique g w).
Defined.

Example sg_insert_universal_obj@{o so} (X : SetoidObject@{o o})
  (A : SmgrpSets@{o so}) (h : X ~{Sets@{o so}}~> fobj[Sg_Forget@{o so}] A) :
  unique_obj (sg_insert_universal@{o so} X A h) = sg_extend@{o so} h
  := eq_refl.

(* Mac Lane's "η_X ... is universal from X to G" in the tree's own terms:
   Theory/Universal/Arrow.v's [UniversalArrow] from X to G, an initial
   object of the comma category =(X) ↓ G, built from the factorization
   above by [universal_arrow_from_UMP], as Instance/Mon/Free.v and the
   other free-object files build theirs.  The type's levels are pinned at
   o and so; the annotation is extensible because the builder binds more
   levels on Coq 8.19 and 8.20 than on Rocq 9.1 (the header's
   UNIVERSES). *)
Definition sg_insert_UA@{o so +} (X : SetoidObject@{o o}) :
  @UniversalArrow@{so o so o o so so so so o so}
    Sets@{o so} SmgrpSets@{o so} X Sg_Forget@{o so} :=
  @universal_arrow_from_UMP Sets@{o so} SmgrpSets@{o so} X Sg_Forget@{o so}
    (FreeSg@{o so} X) (sg_insert@{o so} X) (sg_insert_universal@{o so} X).

(* Its universal object is F X... *)
Example sg_insert_UA_obj@{o so +} (X : SetoidObject@{o o}) :
  @arrow_obj _ _ _ _ (sg_insert_UA X) = FreeSg@{o so} X := eq_refl.

(* ...and its universal arrow is η_X, x ↦ ⟨x⟩, as a setoid map. *)
Example sg_insert_UA_arrow@{o so +} (X : SetoidObject@{o o}) :
  @arrow _ _ _ _ (sg_insert_UA X) = sg_insert@{o so} X := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The adjunction F ⊣ G, in hom-set form, with a computing counit *)

Definition Sg_adj_iso@{o so} (X : SetoidObject@{o o}) (A : SmgrpSets@{o so}) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
       (@homset SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
       (@homset Sets@{o so} X (fobj[Sg_Forget@{o so}] A))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
          (@homset SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[Sg_Forget@{o so}] A)))
       (@Build_SetoidMorphism
          (@hom SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
          (@homset SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
          (@hom Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
          (fun g => @setoid_morphism_compose@{o o o} _ _ _
                      (fmap[Sg_Forget@{o so}] g) (sg_insert@{o so} X)) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[Sg_Forget@{o so}] A))
          (@hom SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
          (@homset SmgrpSets@{o so} (fobj[Sg_Free@{o so}] X) A)
          (fun h => sg_extend@{o so} h) _) _ _).
  - intros g g' H x. exact (H (letter x)).
  - intros h h' H w.
    exact (tfold1_respects h h'
             (fun a b E => transitivity (proper_morphism h _ _ E) (H b))
             _ _ _ _ (tup_eq_refl _ (projT2 w))).
  - intros h x. reflexivity.
  - intros g w. simpl.
    symmetry.
    exact (sg_extend_unique g w).
Defined.

(* The free semigroup: F ⊣ G, ⟨F, G, η, ε⟩ : Set ⇀ Smgrp. *)
Definition Sg_adj@{o so} :
  @Adjunction@{so o o so o o o o so o so} SmgrpSets@{o so} Sets@{o so}
    Sg_Free@{o so} Sg_Forget@{o so}.
Proof.
  unshelve refine
    (@Build_Adjunction' SmgrpSets@{o so} Sets@{o so}
       Sg_Free@{o so} Sg_Forget@{o so}
       (fun X A => Sg_adj_iso@{o so} X A) _ _).
  - intros X Y A g f x. reflexivity.
  - intros X A B f g x. reflexivity.
Defined.

(* η_X x = ⟨x⟩: the unit of the adjunction IS the insertion. *)
Example Sg_adj_unit@{o so} (X : SetoidObject@{o o}) :
  @unit _ _ _ _ Sg_adj@{o so} X = sg_insert@{o so} X := eq_refl.

(* ε_S sends each generator ⟨s⟩ to s. *)
Example Sg_adj_counit_letter@{o so} (S : SmgrpSets@{o so}) (s : sg_ob S) :
  sg_fun (@counit _ _ _ _ Sg_adj@{o so} S) (letter s) = s := eq_refl.

(* (1): the counit removes the pointy brackets, ε_S(⟨s1⟩⋯⟨sn⟩) = s1⋯sn,
   the product in S bracketed to the left. *)
Example Sg_adj_counit@{o so} (S : SmgrpSets@{o so}) (w : PWord@{o} (sg_ob S)) :
  sg_fun (@counit _ _ _ _ Sg_adj@{o so} S) w = pwfold (fun s => s) w
  := eq_refl.

Example Sg_adj_counit_literal@{o so} (S : SmgrpSets@{o so})
  (s1 s2 s3 : sg_ob@{o so} S) :
  sg_fun (@counit _ _ _ _ Sg_adj@{o so} S)
    (existT (fun n => Tup (sg_ob S) n) 2%nat (s1, (s2, s3)))
  = sg_mul S (sg_mul S s1 s2) s3 := eq_refl.
