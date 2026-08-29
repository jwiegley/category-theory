Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.

Generalizable All Variables.

(** * The free monoid on a SETOID, and its adjunction at Mon(Sets) *)

(* nLab:      https://ncatlab.org/nlab/show/free+monoid
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         GTM 5, Springer 1998, §IV.8, Exercise 2 (maclane:IV.8:ex2) — the
         free ring on a set obtained as a composite of free constructions;
         §II.7 Corollary 2, printed pp. 50-51, for the free monoid itself.

   For a SETOID X — a carrier with a chosen equivalence `≈` — the free
   monoid on X is the setoid of finite words over the carrier of X,
   compared LETTERWISE UP TO `≈`, multiplied by concatenation with the
   empty word as unit.  Its universal property is that the insertion of
   one-letter words is universal among Sets-morphisms from X into the
   underlying setoid of a monoid: every h : X ~> U L extends along the
   insertion to one and only one monoid homomorphism, namely the fold
   that replaces concatenation by the multiplication of L and the empty
   word by its unit.

   Everything is developed at [@Mon Sets Sets_Product_Monoidal], the
   category of internal monoids (Theory/Algebra/Monoid.v) in the
   cartesian monoidal category of setoids, with
   [@Mon_Forget Sets Sets_Product_Monoidal] as the underlying-setoid
   functor U.  A monoid object over that base is exactly an ordinary
   setoid monoid: mu : X ∏ X ~> X, eta : 1 ~> X, and the three laws are
   associativity and the two unit laws with the cartesian associator and
   unitors inserted.  Nothing here needs function extensionality: two
   monoid homomorphisms are identified exactly when they agree at every
   word up to `≈`, which is what word induction proves.

   WHY THIS FILE EXISTS: THE Mon(Coq)/Mon(Sets) MEASUREMENT.  Issue #296
   already delivered a free monoid with its universal property and its
   adjunction — but at a DIFFERENT category.
   Instance/Coq/Monoid/Free.v:126 abbreviates
   [MonCoq := @Mon Coq Coq_Monoidal], and its :323/:326 deliver
   [FreeMonoid : Coq ⟶ MonCoq] and
   [free_monoid_adjunction : FreeMonoid ⊣ UMon] over that base.  The
   monoid-ring leg that #400 wants to compose with runs from the OTHER
   category: Instance/Rng/MonoidRing.v:170 sets
   [MonSets := @Mon Sets Sets_Product_Monoidal] and its :723/:726 give
   [MonoidRingFunctor : MonSets ⟶ Rng] with
   [zmring_adjunction : MonoidRingFunctor ⊣ Rng_Forget_Mon].
   Instance/Roster.v:390 names the same category [Mon_Sets].  So the two
   legs of "Sets → Monoids → Rings" did not compose.

   That gap was re-verified here rather than taken on trust, and the
   coordinating measurement stands, with two refinements worth stating.
   (1) Searching the whole tree for a functor whose CODOMAIN is
   [Mon Sets] returns exactly three, and all three are forgetful:
   [Rig_Forget_Mon] (Theory/Algebra/Rig.v:292),
   [Rng_Forget_Mon] (Instance/Rng/MonoidRing.v:226) and [Grp_MonSets]
   (Instance/Rng/GroupRing.v:155); Instance/Roster.v:397 restates the
   first of them at Roster's own name for the category and adds no
   fourth.  There was no free monoid at [Mon Sets] before this file.
   (2) There is no equivalence between [Coq] and [Sets] in tree — but
   the sharper claim "there is no functor at all between them" would be
   FALSE: Instance/Shapes.v:279 declares
   [Trie_Functor (s : Shape) : Coq ⟶ Sets], which is unrelated to any
   comparison of the two categories, and [Sets_discrete]
   (Instance/Sets/Products.v:394) is an OBJECT-level discrete-setoid
   construction that is nowhere packaged as a functor.  Neither
   transports #296's adjunction, and more to the point transport along
   an arbitrary functor pair would not preserve left-adjointness
   anyway — the free monoid on a SETOID must identify `≈`-equal
   generators, which no discrete-setoid route does.
   That last sentence is an ARGUMENT, not a theorem; what IS proved here
   is the fact it rests on ([free_mon_blur_identifies] against
   [free_mon_two_generators_distinct]).

   Instance/Mon/Coproduct.v:237-242 names this same wall as the reason
   Awodey §3.2 Exercise 5 (M(A) + M(B) ≅ M(A + B) by preservation of
   colimits) went undelivered there: "the only free-monoid adjunction in
   tree is Instance/Coq/Monoid/Free.v's, which is over [Coq], so no such
   adjoint exists at this category to preserve colimits".  This file
   removes exactly that obstruction — there is now a left adjoint of
   [Mon_Forget] at [Mon Sets].  The exercise itself is NOT attempted
   here and nothing is claimed about what else its proof would need.

   THE ELEMENT-LEVEL ACCESSORS ARE REUSED, NOT REWRITTEN, AND THE CHOICE
   IS MEASURED.  Two copies of the element-level reading of [Mon Sets]
   already exist — Instance/Rng/MonoidRing.v:170-220
   ([mcar]/[mop]/[mone]/[mmap]/[mhom]) and Instance/Mon/Coproduct.v:253-346
   ([mon_ob]/[mon_mul]/[mon_one]/[mon_fun]/[mk_mon_obj]/[mk_mon_hom]) —
   and writing a third would have been the wrong move.  The Coproduct.v
   copy is the one imported, for a dependency reason and not a stylistic
   one: MonoidRing.v Requires [Instance.Rng], [Instance.Rng.Algebras],
   [Instance.Rng.Polynomial], [Instance.Rng.Algebras.Associative] and
   [Instance.Mod], so importing it would put the whole ring hierarchy
   behind every consumer of the free monoid — and would invert the
   intended dependency, since the ring-side composite is what will
   consume THIS file.  Coproduct.v Requires only Lib, Category,
   Isomorphism, Morphisms, Monoidal, Cartesian, Cocartesian, Terminal,
   Initial, Monoid, Monoid.Hom and Sets.  No new name for the category
   is introduced here — [MonS] below is a [Local Notation] that does not
   export — so requiring this file alongside MonoidRing.v produces no
   collision with its [MonSets].  A by-product of the import is that
   Coproduct.v's [ListBoolMon] is available as the concrete target for
   the non-vacuity probes, so no new monoid had to be built for them.

   STRENGTHS, MEASURED STRICT-FIRST.  Definitional (shipped as [eq_refl]
   Examples): the carrier, the multiplication, the unit, the underlying
   setoid of the free monoid; the object part of [FreeMonSets]; the
   universal arrow IS the insertion; the unit of the adjunction IS the
   insertion; the fold's value at a literal one-letter word.  Only up to
   `≈`: the counit's action (it is the evaluation of a word in L,
   [free_mon_counit_evaluates]) and the free functor's action on arrows
   ([free_mon_fmap_is_wmap]).  Two strict readings were ATTEMPTED and
   REJECTED, and both are pinned in-file as [Fail] commands with
   positive controls beside them:

     - the counit does not compute.  Its underlying map is
       [unique_obj (ump_universal_arrows ...)], and
       [ump_universal_arrows] (Theory/Universal/Arrow.v:139) is closed
       with [Qed], so nothing reduces through it.  The diagnosis
       DISCRIMINATES: the UNIT of the same adjunction, which routes
       through the transparent [universal_arrow_from_UMP] instead, IS
       [eq_refl] ([free_mon_unit_is_insert]), so opacity of that one
       constant is the cause and not adjunction plumbing in general.

     - [free_mon_extend_insert] is a Leibniz equality but not a
       conversion at a VARIABLE word: [free_mon_extend] is a [Fixpoint]
       and is stuck on a variable.  The control is the same statement at
       a literal one-letter word, where it does hold by [eq_refl] — so
       the obstruction is the stuck recursion, not a mismatch of the two
       sides.  Each step of the induction closes by [reflexivity] with
       no monoid law spent, which is why the theorem is stated at
       Leibniz `=` rather than at `≈`.

   NON-VACUITY.  Two independent routes to the same separation, and the
   difference between them is worth recording.  Unlike
   Instance/Mon/Coproduct.v's [fp_eq] and the other generated
   congruences in this tree, [word_eq] is a STRUCTURAL congruence
   defined by recursion on the two words, so it is open to inversion
   and a negative IS reachable directly: [free_mon_insert_reflects] inverts
   one [we_cons] to recover `≈` of the letters, giving
   [free_mon_two_generators_distinct] in three lines.  The map-out route
   is supplied as well and shares no proof text with it
   ([free_mon_two_generators_distinct_via_probe],
   [free_mon_word2_not_letter]), evaluating in Coproduct.v's
   [ListBoolMon] through the universal property; the fold's value there
   COMPUTES ([two_probe_word2] is [eq_refl]).  The setoid half is the
   point of doing this at [Sets] rather than at [Coq]:
   [free_mon_blur_identifies] exhibits two `≈`-equal but
   Leibniz-distinct generators that the free monoid IDENTIFIES, against
   [free_mon_two_generators_distinct] over the discrete setoid on the
   same carrier, where it does not.

   UNIVERSES.  Read off the constraint blocks, not the binders:
   [FreeMonSetsObject@{u u0}], [FreeMonSets@{u u0 u1 u2 u3}] and
   [free_mon_sets_adjunction@{u u0 u1 u2 u3 u4}] contain NO [Set]
   anywhere — no [Set] universe instance and no constraint mentioning
   it — and the only strict inequality among the two levels that matter
   is [Sets]'s own [o < so] ([Instance/Sets.v:193] declares
   [Sets@{o so} : Category@{so o o}]).  That is guarded rather than
   merely measured: the section [FreeAboveSet] at the end of this file
   declares [Constraint Set < uo] and elaborates all three constants at
   levels strictly above [Set].  So this file introduces no size
   restriction of its own.  Note that the [Set] pin CLAUDE.md records
   for [Rig_Forget_Mon] — and hence for [Rng_Forget_Mon] — is on the
   RING side and is untouched here, but it DOES reach the composite, and
   that was measured rather than guessed: in a scratch file out of tree
   requiring both this module and Instance/Rng/MonoidRing.v, the
   composite [MonoidRingFunctor ◯ FreeMonSets] elaborates, and its
   constraint block reads [Sets@{Set u} ⟶ Rng@{u Set}] with this file's
   own functor instantiated there at [FreeMonSets@{Set u _ _ _}].  So
   the pin is inherited from the ring leg and is not required by
   anything here — but a consumer building the free ring through
   monoids will carry it.  That composite is NOT built in this file and
   nothing here is guarded against the outcome; the measurement is
   reported so that the composite's author does not have to rediscover
   it.

   WHAT IS DELIBERATELY NOT DELIVERED.  No normal form for words beyond
   the list representation itself, hence no decision procedure for
   [word_eq] beyond what a decidable letter setoid would give, and no
   length or degree invariants.  No comparison whatever with
   Instance/Coq/Monoid/Free.v's [FreeMonoid]: the two are NOT related
   here, neither is claimed to determine the other, and no functor
   between the two ambient categories is built (doing so would drag that
   file's own closure — Comma, FAlg, Funny.Comparison, Coq.Lists — into
   this one).  No naturality of the insertion as a [Transform] (#296's
   [insert_Transform] has no counterpart here); no identification of the
   free monoid with the delooping of a free category on a one-vertex
   quiver; no [Foldable]/initial-algebra bridge; no relation to
   Instance/Mon/Coproduct.v's [FreeProd] beyond sharing its accessor
   layer, so in particular the free monoid on a two-element setoid is
   NOT proved to be the free product of two copies of the free monoid on
   one generator.  And no free RING: this file supplies one leg of
   Mac Lane's §IV.8 Exercise 2 and stops there.

   LEDGER.  57 constants, all reported "Closed under the global context"
   by [Print Assumptions] — that is 31 [def] plus 19 [prf] in the [.glob]
   MINUS the three named [Fail] commands, which the [.glob] records as
   [def] although they define nothing, plus [word_eq] with its two
   constructors, its four automatically generated elimination schemes,
   and the three [Program] obligations ([free_mon_insert_obligation_1],
   [Blur_Setoid_obligation_1],
   [free_mon_AUniversalArrow_obligation_1]).  The [.glob] DOES list
   [word_eq] and its two constructors as [ind]/[constr] entries; what it
   does not list are the elimination schemes and the [Program]
   obligations, and the total below excludes [ind]/[constr] anyway, so
   the arithmetic is unaffected.  The [.glob]
   lists.  Three [Fail] commands: two CONVERSION negatives, each with a
   positive control beside it and each stripped once and its message
   read, plus one instrument check confirming that [Fail] reports
   failures in this file at all.  Every constant named inside a [Fail]
   also occurs in a positive command elsewhere in the file, so a rename
   breaks the file loudly rather than turning a negative vacuously
   green.  No separate probe file is shipped.

   DISPLAY HAZARD.  [Print Module] and plain [Check] suppress the
   implicit first argument of the [Sets.morphism] coercion, so
   [free_mon_unit_is_insert] prints as "Sets.morphism a =
   Sets.morphism a", which reads as a tautology and is not one:
   under [Set Printing All] the left side is the adjunction's [unit] and
   the right side is [free_mon_insert X].  The same suppression affects
   [free_mon_fmap_generators]. *)

#[local] Obligation Tactic := idtac.

Local Notation MonS := (@Mon Sets Sets_Product_Monoidal).
Local Notation UMonS := (@Mon_Forget Sets Sets_Product_Monoidal).

(** * Words over a setoid

    The carrier is [list (carrier X)].  Concatenation is spelled out
    rather than taken from [Coq.Lists.List], following the precedent and
    the stated reason of Instance/Mon/Coproduct.v:622-625: importing that
    module brings [list_scope]'s notations into a file whose ambient
    scope is the library's, and the whole of what is needed is five
    lines. *)

Fixpoint wapp {X : SetoidObject} (u v : list (carrier X))
  : list (carrier X) :=
  match u with
  | Datatypes.nil        => v
  | Datatypes.cons a u'  => Datatypes.cons a (wapp u' v)
  end.

Lemma wapp_assoc {X : SetoidObject} (u v w : list (carrier X)) :
  wapp (wapp u v) w = wapp u (wapp v w).
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Lemma wapp_nil_r {X : SetoidObject} (u : list (carrier X)) :
  wapp u Datatypes.nil = u.
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

(* Two words are equivalent when they have the same length and their
   letters are `≈`-equal in order.  This is the pointwise lifting of X's
   own equivalence, and it is [Type]-valued because `≈` in this library
   is a [crelation]: equivalence proofs carry data. *)
Inductive word_eq {X : SetoidObject}
  : list (carrier X) → list (carrier X) → Type :=
  | we_nil : word_eq Datatypes.nil Datatypes.nil
  | we_cons (a b : carrier X) (u v : list (carrier X)) :
      a ≈ b → word_eq u v →
      word_eq (Datatypes.cons a u) (Datatypes.cons b v).

Lemma word_eq_refl {X : SetoidObject} (u : list (carrier X)) :
  word_eq u u.
Proof.
  induction u as [|a u IH].
  - exact we_nil.
  - exact (we_cons a a u u (reflexivity a) IH).
Qed.

Lemma word_eq_sym {X : SetoidObject} (u v : list (carrier X)) :
  word_eq u v → word_eq v u.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH].
  - exact we_nil.
  - exact (we_cons b a v u (symmetry Hab) IH).
Qed.

Lemma word_eq_trans {X : SetoidObject} (u v w : list (carrier X)) :
  word_eq u v → word_eq v w → word_eq u w.
Proof.
  intros H; revert w.
  induction H as [|a b u v Hab Huv IH]; intros w K.
  - exact K.
  - inversion K as [|b' c v' w' Hbc Hvw].
    subst.
    exact (we_cons a c u w' (transitivity Hab Hbc) (IH w' Hvw)).
Qed.

Definition word_eq_Equivalence (X : SetoidObject)
  : Equivalence (@word_eq X) :=
  {| Equivalence_Reflexive  := @word_eq_refl X
   ; Equivalence_Symmetric  := @word_eq_sym X
   ; Equivalence_Transitive := @word_eq_trans X |}.

Definition Word_Setoid (X : SetoidObject) : Setoid (list (carrier X)) :=
  {| equiv := @word_eq X ; setoid_equiv := word_eq_Equivalence X |}.

Definition WordObj (X : SetoidObject) : SetoidObject :=
  {| carrier := list (carrier X) ; is_setoid := Word_Setoid X |}.

Lemma wapp_respects {X : SetoidObject} (u u' v v' : list (carrier X)) :
  word_eq u u' → word_eq v v' → word_eq (wapp u v) (wapp u' v').
Proof.
  intros Hu Hv; induction Hu as [|a b u u' Hab Huu' IH]; simpl.
  - exact Hv.
  - exact (we_cons a b _ _ Hab IH).
Qed.

(** * The free monoid on a setoid

    Mac Lane §II.7 Corollary 2: the finite words over X form a monoid
    under concatenation with the empty word as unit.  Both unit laws and
    associativity are Leibniz equalities of lists, so the three monoid
    obligations are discharged by transporting reflexivity of [word_eq]
    along them. *)

Definition FreeMonSetsObject (X : SetoidObject) : MonS.
Proof.
  unshelve refine
    (mk_mon_obj (WordObj X) Datatypes.nil (@wapp X) _ _ _ _).
  - intros u u' Hu v v' Hv; exact (wapp_respects u u' v v' Hu Hv).
  - intros u v w; rewrite wapp_assoc; exact (word_eq_refl _).
  - intro u; exact (word_eq_refl u).
  - intro u; rewrite wapp_nil_r; exact (word_eq_refl u).
Defined.

(* The four data readings hold on the nose. *)
Example free_mon_carrier (X : SetoidObject) :
  mon_ob (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_forget (X : SetoidObject) :
  UMonS (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_mul_is_wapp (X : SetoidObject)
        (u v : list (carrier X)) :
  mon_mul (FreeMonSetsObject X) u v = wapp u v := eq_refl.

Example free_mon_one_is_nil (X : SetoidObject) :
  mon_one (FreeMonSetsObject X) = @Datatypes.nil (carrier X) := eq_refl.

(** ** The insertion of generators

    A letter goes to the one-letter word.  Respectfulness is one
    application of [we_cons]: this is where the construction differs
    from the [Coq]-based one, and it is the reason `≈`-equal generators
    end up identified. *)

Program Definition free_mon_insert (X : SetoidObject)
  : X ~{Sets}~> UMonS (FreeMonSetsObject X) := {|
  morphism := fun a => Datatypes.cons a Datatypes.nil
|}.
Next Obligation.
  intros X a b Hab.
  exact (we_cons a b Datatypes.nil Datatypes.nil Hab we_nil).
Qed.

(** ** The extension of a map into a monoid: the fold

    The extension of h replaces concatenation by the multiplication of L
    and the empty word by its unit, so it is the right fold of h. *)

Fixpoint free_mon_extend {X : SetoidObject} {L : MonS}
         (h : carrier X → carrier (mon_ob L)) (l : list (carrier X))
  : carrier (mon_ob L) :=
  match l with
  | Datatypes.nil       => mon_one L
  | Datatypes.cons a l' => mon_mul L (h a) (free_mon_extend h l')
  end.

(* The fold respects `≈` on words as soon as h respects `≈` on letters —
   which is exactly the hypothesis a Sets-morphism carries. *)
Lemma free_mon_extend_respects {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
      (u v : list (carrier X)) :
  word_eq u v → free_mon_extend h u ≈ free_mon_extend h v.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH]; simpl.
  - reflexivity.
  - exact (mon_mul_resp L _ _ (hp a b Hab) _ _ IH).
Qed.

(* It carries concatenation to multiplication: induction on the left
   word, using the left unit law at the empty word and associativity at
   a [cons]. *)
Lemma free_mon_extend_wapp {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (u v : list (carrier X)) :
  free_mon_extend h (wapp u v)
    ≈ mon_mul L (free_mon_extend h u) (free_mon_extend h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; exact (mon_one_l L (free_mon_extend h v)).
  - transitivity
      (mon_mul L (h a)
         (mon_mul L (free_mon_extend h u) (free_mon_extend h v))).
    + exact (mon_mul_resp L _ _ (reflexivity (h a)) _ _ IH).
    + symmetry; exact (mon_mul_assoc L (h a) _ _).
Qed.

(* ...and it agrees with h on the generators, by the right unit law. *)
Lemma free_mon_extend_generator {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (a : carrier X) :
  free_mon_extend h (free_mon_insert X a) ≈ h a.
Proof. exact (mon_one_r L (h a)). Qed.

(* Hence it is a monoid homomorphism out of the free monoid.  Its unit
   clause needs no proof at all: the unit of the free monoid IS the
   empty word, on which the fold returns the unit of L by computation. *)
Definition free_mon_hom {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
  : FreeMonSetsObject X ~{MonS}~> L :=
  @mk_mon_hom (FreeMonSetsObject X) L (free_mon_extend h)
    (fun u v Huv => free_mon_extend_respects h hp u v Huv)
    (fun u v => free_mon_extend_wapp h u v)
    (reflexivity (mon_one L)).

(** ** Uniqueness of the extension

    Any monoid homomorphism out of the free monoid that agrees with h on
    the generators IS the fold.  The induction uses both homomorphism
    laws: the unit law at the empty word, the multiplication law at the
    [cons] split [a :: l = (a :: nil) ++ l], which is a Leibniz identity
    here rather than a rewrite. *)

Lemma free_mon_extend_unique {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (g : FreeMonSetsObject X ~{MonS}~> L)
      (Hg : ∀ a : carrier X, mon_fun g (free_mon_insert X a) ≈ h a)
      (l : list (carrier X)) :
  mon_fun g l ≈ free_mon_extend h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (mon_fun_one g).
  - transitivity
      (mon_mul L (mon_fun g (free_mon_insert X a)) (mon_fun g l)).
    + exact (mon_fun_mul g (free_mon_insert X a) l).
    + exact (mon_mul_resp L _ _ (Hg a) _ _ IH).
Qed.

(** ** The universal property

    In the shape [Theory/Universal/Arrow.v]'s
    [universal_arrow_from_UMP] consumes: for every monoid L and every
    h : X ~> U L there is exactly one monoid homomorphism g with
    U g ∘ insert ≈ h.  Uniqueness is up to the ambient `≈`, which in
    Mon(Sets) is pointwise `≈` of the underlying setoid maps. *)

Theorem free_mon_universal (X : Sets) :
  ∀ (L : MonS) (h : X ~{Sets}~> UMonS L),
    ∃! g : FreeMonSetsObject X ~{MonS}~> L,
      h ≈ fmap[UMonS] g ∘ free_mon_insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl.
    symmetry; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; symmetry; exact (Hg b).
Qed.

(* The free monoid packaged as a universal arrow from X to [Mon_Forget].
   By Theory/Universal/Arrow.v this IS an initial object of the comma
   category =(X) ↓ Mon_Forget. *)
Definition free_mon_universal_arrow (X : Sets) : UniversalArrow X UMonS :=
  universal_arrow_from_UMP X UMonS (FreeMonSetsObject X)
                           (free_mon_insert X) (free_mon_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected. *)
Program Definition free_mon_AUniversalArrow (X : Sets)
  : AUniversalArrow X UMonS (FreeMonSetsObject X) := {|
  universal_arrow := free_mon_insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; exact (Hg b).
Qed.

(** ** The free-forgetful adjunction

    Assembled by the generic machinery of Theory/Universal/Arrow.v from
    the family of universal arrows.  This is the constant the
    monoid-ring leg was missing. *)

Definition FreeMonSets : Sets ⟶ MonS :=
  LeftAdjointFunctorFromUniversalArrows UMonS free_mon_universal_arrow.

Definition free_mon_sets_adjunction : FreeMonSets ⊣ UMonS :=
  AdjunctionFromUniversalArrows UMonS free_mon_universal_arrow.

(** * Strengths achieved, and two rejected *)

(* The free functor's object part is the word monoid, definitionally. *)
Example FreeMonSets_obj (X : Sets) :
  FreeMonSets X = FreeMonSetsObject X := eq_refl.

(* The universal arrow is the insertion on the nose:
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. *)
Example free_mon_arrow_is_insert (X : Sets) :
  @arrow _ _ X UMonS (free_mon_universal_arrow X) = free_mon_insert X
  := eq_refl.

(* Hence so is the unit of the adjunction: the transpose of the identity
   is [fmap[U] id ∘ arrow], and [fmap[U] id] is the identity setoid map,
   whose action is [Datatypes.id]. *)
Example free_mon_unit_is_insert (X : Sets) (a : carrier X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction X a
    = free_mon_insert X a := eq_refl.

(* NEGATIVE 1 (conversion).  The counit does NOT compute.  Its
   underlying map is [unique_obj (ump_universal_arrows ...)], and
   [ump_universal_arrows] is closed with [Qed], so nothing reduces
   through it.  Stripping the [Fail] reports
   "cannot unify "mon_fun counit l" and
    "free_mon_extend (λ x, x) l"".
   The control is [free_mon_unit_is_insert] immediately above: the unit
   of the SAME adjunction, which routes through the transparent
   [universal_arrow_from_UMP], does close by [eq_refl].  So the cause is
   the opacity of that one donor, not adjunction plumbing at large. *)
Fail Example free_mon_counit_is_not_strict
  (L : MonS) (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    = free_mon_extend (fun x => x) l := eq_refl.

(* What does hold: the counit evaluates a word in L.  Its defining
   property is the triangle identity [fmap_counit_unit], read at a
   generator; uniqueness of the extension then identifies it with the
   fold of the identity. *)
Lemma free_mon_counit_evaluates (L : MonS)
      (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    ≈ free_mon_extend (fun x => x) l.
Proof.
  apply (free_mon_extend_unique (fun x : carrier (mon_ob L) => x)).
  intro a.
  exact (@fmap_counit_unit _ _ _ _ free_mon_sets_adjunction L a).
Qed.

(** ** The free functor acts on arrows as [map]

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a word
    has to be proved.  It is the letterwise map: the defining
    factorization says generators go to generators, and the uniqueness
    half of the universal property identifies the homomorphism with
    [wmap]. *)

Fixpoint wmap {X Y : SetoidObject} (f : carrier X → carrier Y)
         (l : list (carrier X)) : list (carrier Y) :=
  match l with
  | Datatypes.nil       => Datatypes.nil
  | Datatypes.cons a l' => Datatypes.cons (f a) (wmap f l')
  end.

Lemma free_mon_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
      (a : carrier X) :
  mon_fun (fmap[FreeMonSets] f) (free_mon_insert X a)
    ≈ free_mon_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_mon_universal_arrow X)
              (@arrow _ _ Y UMonS (free_mon_universal_arrow Y) ∘ f)) a).
Qed.

(* NEGATIVE 2 (conversion).  The identification below is a Leibniz
   equality (proved next), but it is NOT a conversion at a VARIABLE
   word: [free_mon_extend] is a [Fixpoint] and is stuck on a variable.
   Stripping the [Fail] reports
   "cannot unify "free_mon_extend (λ a, free_mon_insert Y (f a)) l" and
    "wmap f l"".
   The control is [free_mon_extend_insert_at_letter] just below, which
   is the same statement at a literal one-letter word and DOES close by
   [eq_refl] — so the obstruction is the stuck recursion, not a
   mismatch of the two sides. *)
Fail Example free_mon_extend_insert_is_not_strict
  {X Y : Sets} (f : X ~{Sets}~> Y) (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l := eq_refl.

Example free_mon_extend_insert_at_letter
  {X Y : Sets} (f : X ~{Sets}~> Y) (a : carrier X) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun b => free_mon_insert Y (f b))
    (Datatypes.cons a Datatypes.nil)
    = wmap f (Datatypes.cons a Datatypes.nil) := eq_refl.

(* Each step of the induction closes by [reflexivity] with no monoid law
   spent, which is why this is stated at Leibniz `=`. *)
Lemma free_mon_extend_insert {X Y : Sets} (f : X ~{Sets}~> Y)
      (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l.
Proof.
  induction l as [|a l IH]; simpl in *;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Theorem free_mon_fmap_is_wmap {X Y : Sets} (f : X ~{Sets}~> Y)
        (l : list (carrier X)) :
  mon_fun (fmap[FreeMonSets] f) l ≈ wmap f l.
Proof.
  transitivity (free_mon_extend (L:=FreeMonSetsObject Y)
                  (fun a => free_mon_insert Y (f a)) l).
  - apply (free_mon_extend_unique
             (fun a => free_mon_insert Y (f a)) (fmap[FreeMonSets] f)).
    intro a; exact (free_mon_fmap_generators f a).
  - rewrite free_mon_extend_insert; reflexivity.
Qed.

(** * Non-vacuity

    [word_eq] is a STRUCTURAL congruence, not a generated one, so unlike
    Instance/Mon/Coproduct.v's [fp_eq] it is open to inversion and
    negatives are reachable directly.  Both routes are given below;
    they share no proof text. *)

(* The insertion reflects `≈`: it is injective on generators up to the
   source setoid, for EVERY X, with no hypothesis. *)
Lemma free_mon_insert_reflects {X : SetoidObject} (a b : carrier X) :
  word_eq (Datatypes.cons a Datatypes.nil)
          (Datatypes.cons b Datatypes.nil) → a ≈ b.
Proof. intro H; inversion H; assumption. Qed.

(* Two setoids on ONE carrier, [bool]: the discrete one, and the
   coarsest one, which identifies everything. *)
Definition MonTwoObj : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Program Definition Blur_Setoid : Setoid bool :=
  {| equiv := fun _ _ => True |}.
Next Obligation. constructor; repeat intro; exact Logic.I. Qed.

Definition BlurObj : SetoidObject :=
  {| carrier := bool ; is_setoid := Blur_Setoid |}.

(* Over the discrete setoid the two generators stay apart... *)
Theorem free_mon_two_generators_distinct : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : true = false)
    by exact (free_mon_insert_reflects (X:=MonTwoObj) true false H).
  discriminate K.
Qed.

(* ...and over the coarse setoid on the SAME carrier they are
   identified.  This is what doing the construction at [Sets] rather
   than at [Coq] buys, and it is the fact the header's transport
   argument rests on. *)
Definition free_mon_blur_identifies : @word_eq BlurObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) :=
  @we_cons BlurObj true false Datatypes.nil Datatypes.nil Logic.I
    (@we_nil BlurObj).

(** ** The same separations by mapping out

    The probe sends each letter of the discrete two-element setoid to
    the corresponding one-letter list in Coproduct.v's
    (list bool, ++, nil).  No new monoid is built. *)

Definition two_letter : carrier MonTwoObj → carrier (mon_ob ListBoolMon) :=
  fun x => Datatypes.cons x Datatypes.nil.

Definition two_probe : FreeMonSetsObject MonTwoObj ~{MonS}~> ListBoolMon :=
  free_mon_hom two_letter (fun a b H => f_equal two_letter H).

(* The probe's value at a two-letter word COMPUTES. *)
Example two_probe_word2 :
  mon_fun two_probe
    (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
    = bword2 true false := eq_refl.

Theorem free_mon_two_generators_distinct_via_probe : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe (Datatypes.cons true Datatypes.nil)
                = mon_fun two_probe (Datatypes.cons false Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(* A two-letter word is not equivalent to any one-letter word, so the
   free monoid is not collapsed by length either. *)
Theorem free_mon_word2_not_letter (c : bool) : @word_eq MonTwoObj
  (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
  (Datatypes.cons c Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe
                (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
                = mon_fun two_probe (Datatypes.cons c Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(** * Universe guard

    The three headline constants carry no [Set] pin.  This is not merely
    read off their constraint blocks: the section below declares
    [Set < uo] and elaborates all three at levels strictly above it.
    The two levels are [Sets]'s own carrier and object universes, in
    that order for [FreeMonSetsObject].  The other two are stated by
    ascribing [Sets@{uo uso}] rather than by an explicit instance, for
    the portability reason recorded at the section itself. *)

Section FreeAboveSet.

  Universe uo uso.
  Constraint Set < uo.
  Constraint uo < uso.

  Check FreeMonSetsObject@{uso uo}.
  (* PORTABILITY: the last two are written as ASCRIPTIONS of the SOURCE
     category rather than as explicit universe instances, because the
     number of universes a functor and an adjunction carry here is NOT
     stable across the supported versions -- [FreeMonSets] takes five on
     Rocq 9.1 and six on Coq 8.19/8.20, so a literal [@{uo uso _ _ _}]
     builds on one and fails on the others with "Universe instance
     length is 5 but should be 6".  [Sets] has a stable two-universe
     signature, so ascribing it is version-independent and states the
     same thing.  The guard still discriminates: the same ascription
     shape applied to a [Set]-pinned functor is REJECTED (checked
     against [Rng_Forget_Mon], which cannot take a [Rng] above [Set]). *)
  Check (FreeMonSets : Sets@{uo uso} ⟶ _).
  Check (free_mon_sets_adjunction : @Adjunction _ Sets@{uo uso} _ _).

End FreeAboveSet.

(* Instrument check: [Fail] does report failures in this file. *)
Fail Definition free_mon_instrument_check : False := Logic.I.
