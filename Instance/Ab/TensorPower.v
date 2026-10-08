Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Hypergraph.Spider.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Generalizable All Variables.

(** * ⨁ₙ A^{⊗n}: words modulo multilinearity, and the direct sum of the
      tensor powers *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.4, Exercise 4(a), printed p. 146 (PDF
         p. 155) — maclane:VI.4:ex4
   Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
         p. 205 (PDF p. 225) — riehl:5.5:example7
   nLab: https://ncatlab.org/nlab/show/tensor+algebra
   nLab: https://ncatlab.org/nlab/show/direct+sum
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_algebra

   WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane,
   Exercise 4: "The adjunction ⟨F, G, φ⟩ : Ab ⇀ Rng with G the functor
   "forget the multiplication in a ring" defines a monad T in Ab.  (a)
   Give a direct description of this monad, like that in the text for W,
   with Xⁿ replaced by the n-fold tensor power and coproduct ∐ by the
   (infinite) direct sum of abelian groups."  Riehl, Example 5.5.7(ii):
   "The induced monad on Ab is the free monoid monad TA := ⨁_{n≥0}
   A^{⊗n}".  This file is the abelian-group half of (a), with nothing of
   rings in it: the group ⨁ₙ A^{⊗n} in two readings, and the theorem
   that they are one.  Instance/Rng/FreeMonad/Words.v proves T A
   isomorphic to it and reads η, μ and T f through the isomorphism.

   WORDS MODULO MULTILINEARITY.  [TWAb A] is the formal sums [TWTerm A]
   of words over A (lists of elements) modulo [tw_eq]: the abelian-group
   laws, congruence for + and −, and, in each letter of a word,
   saturation under A's own ≈ ([twe_letter]) and additivity
   ([twe_lin]).  Reflexivity is derived ([tw_refl]), as in
   Instance/Rng/Free.v and Instance/Ab/Tensor.v, so every induction on
   [tw_eq] has ten cases.  [tw_eq] is a [Prop], so the [PropEquiv] field
   an abelian group carries since PR #1320 is the relation's own mirror.
   A function on words that respects each letter and is additive in each
   extends to a homomorphism out of [TWAb A] ([tw_ext], which computes on
   words, [tw_ext_word]): the universal property of the presentation.
   Juxtaposition on the left by a word, [tw_lmul], is here with its laws
   because the injections below are built from it; the ring is Words.v's.
   Its additivity on the right is Instance/CMon/Biproduct.v's middle-four
   interchange [cmon_plus_interchange] at [TWAb], not a local copy.

   THE LITERAL DIRECT SUM.  The n-fold tensor powers are not a new
   construction: they are Structure/Monoidal/Hypergraph/Spider.v's
   [tpower] at Instance/Ab/Monoidal.v's [Ab_Monoidal], written A ^⨂ n,
   with A^{⊗0} the unit [ZAb] (ℤ) and A^{⊗(n+1)} = A ⊗ A^{⊗n},
   Instance/Ab/Tensor.v's [AbTensor], both at [eq_refl]
   ([tpower_ab_zero], [tpower_ab_succ]).  The shared route costs eight
   modules: the imports of this file load 64 [Category] modules with
   Spider.v and 56 without it (Print Libraries, compared by script); a
   local fixpoint would be the same family by [eq_refl] and was not
   written.  [tw_pure w] is a word as the pure tensor a₁ ⊗ (… ⊗ (aₙ ⊗ 1))
   of its length; the injections [tw_iota n : A^{⊗n} → TWAb A] come from
   the tensor's universal property ([tensor_ump]), degree 0 by the
   integer multiples of the empty word ([tw_iota0], through
   Instance/Ab/Monoidal.v's [zsmul]), with ι_{n+1}(a ⊗ x) = ⟨a⟩ · ιₙ x at
   [eq_refl] ([tw_iota_gen]) and every word the image of its pure tensor
   at ≈ ([tw_word_iota]).  The copairing [tw_desc] of a family ιₙ :
   A^{⊗n} → c computes on words ([tw_desc_word]); with [tw_desc_iota]
   (the copairing composed with ιₙ is the n-th map, at ≈) and
   [tw_desc_unique] it gives [TW_is_tensor_coproduct : IsIndexedCoproduct
   (fun n => A ^⨂ n) (TWAb A) tw_iota], Structure/Limit/Coproduct.v's
   class in Ab: Mac Lane's "(infinite) direct sum of the n-fold tensor
   powers", literally.  The copairing respects a letter and is additive
   in it by an induction on the prefix of the word generalized over the
   whole family ([tw_shift], [tw_desc_letter], [tw_desc_lin]), so no
   transport along the length of a word is ever needed.  Read at c := A,
   those two lemmas also say that a family of homomorphisms
   νₙ : A^{⊗n} → A is a function on words respecting each letter and
   additive in each, the form in which Instance/Rng/FreeMonad/System.v
   states Mac Lane's systems.

   STRENGTHS.  Every [Example] holds at [eq_refl], and
   Test/ProbeFreeRing474.v restates each one (C55 to C59).  Stated at ≈:
   [tw_word_iota] and [tw_desc_iota], refused at [eq_refl] at a variable
   (R21, R20) and false at Leibniz = at an explicit instance (C103, C104),
   and the uniqueness [tw_desc_unique], whose hypothesis is at ≈.  Three
   lemmas are Leibniz equalities, stronger than ≈: [tw_lmul_app],
   [tw_lmul_nil] and [tw_desc_lmul] (juxtaposition by one letter shifts
   the family).  Six proofs end [Defined] and eighteen [Qed] (counted by
   token).  Five [Defined]s are load-bearing, measured by closing each
   alone [Qed] in a renamed copy of #474's five files and the probe and
   naming the first command that then stops: [tw_ext] ([tw_ext_word]),
   [tw_iota0] ([tw_word_iota]), [tw_lmul1_bilin] ([tw_iota_gen]),
   [ts_gen_hom] ([tw_desc_letter]) and [tw_desc] ([tw_desc_iota]);
   [TW_is_tensor_coproduct] is [Defined] by the data convention only
   (closed [Qed], nothing stops).

   UNIVERSES, read off [About] (every name, by script).  Every name is
   universe polymorphic, with no [Set] but strict lower bounds and with
   caps of the standard library's global levels only.  Thirty-nine names
   bind three levels (the inductives [TWTerm] and [tw_eq] with their
   constructors bind A's three), six bind four ([tw_Setoid],
   [tw_eq_Equivalence], the eliminators [TWTerm_rect] and [TWTerm_rec],
   [tw_ext_fun] and [tw_ext_respects]), fourteen bind five ([TWAb],
   [tw_lmul1_bilin], [ts_gen_hom], the copairing's nine and the extension's
   two) and [TW_is_tensor_coproduct] six.  Nothing in this file is
   annotated, as in Instance/Ab/Tensor.v: the levels are inferred, and on
   Coq 8.19.2 and 8.20.1 every name binds the same levels as on Rocq 9.1.1
   (FreeMonad.v's header).  One equation, [u0 = u2], in eleven names: the
   nine copairing names of the section [Desc] ([tw_shift] to
   [tw_desc_unique]) and [tw_ext] with [tw_ext_word].  Its cause is
   inherent: those maps run from A's words into c in ONE [Ab], whose
   objects [AbObject@{p p p}] share their carrier level, so A's carrier
   level and c's are identified, while the two object levels stay free.
   [TW_is_tensor_coproduct] itself carries no equation.

   NOT DELIVERED.  A general [HasIndexedCoproducts Ab]: this is the
   coproduct of one family, the tensor powers of one A (the same
   construction over tagged elements would give the general one; not
   attempted).  A normal form for [tw_eq], hence no decision procedure
   and no basis. *)

(* ------------------------------------------------------------------------ *)
(** ** Formal sums of words, modulo multilinearity in each letter *)

Section Words.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

Inductive TWTerm : Type :=
  | tw_word : list L → TWTerm
  | tw_zero : TWTerm
  | tw_plus : TWTerm → TWTerm → TWTerm
  | tw_neg  : TWTerm → TWTerm.

(* The congruence: the abelian-group laws, congruence for the two
   formers, and in each letter of a word saturation under A's own `≈`
   and additivity.  Reflexivity is derived ([tw_refl]). *)
Inductive tw_eq : TWTerm → TWTerm → Prop :=
  | twe_letter (u v : list L) {a b : L} :
      a ≈ b → tw_eq (tw_word (u ++ a :: v)) (tw_word (u ++ b :: v))
  | twe_lin (u v : list L) (a b : L) :
      tw_eq (tw_word (u ++ cmon_plus A a b :: v))
            (tw_plus (tw_word (u ++ a :: v)) (tw_word (u ++ b :: v)))
  | twe_plus {s s' t t'} :
      tw_eq s s' → tw_eq t t' → tw_eq (tw_plus s t) (tw_plus s' t')
  | twe_neg {s s'} : tw_eq s s' → tw_eq (tw_neg s) (tw_neg s')
  | twe_assoc (s t u : TWTerm) :
      tw_eq (tw_plus (tw_plus s t) u) (tw_plus s (tw_plus t u))
  | twe_comm (s t : TWTerm) : tw_eq (tw_plus s t) (tw_plus t s)
  | twe_zero_l (s : TWTerm) : tw_eq (tw_plus tw_zero s) s
  | twe_neg_l (s : TWTerm) : tw_eq (tw_plus (tw_neg s) s) tw_zero
  | twe_sym {s t} : tw_eq s t → tw_eq t s
  | twe_trans {s t u} : tw_eq s t → tw_eq t u → tw_eq s u.

Lemma tw_refl (s : TWTerm) : tw_eq s s.
Proof.
  induction s as [ w | | s IHs t IHt | s IHs ].
  - exact (twe_trans (twe_sym (twe_zero_l (tw_word w)))
                     (twe_zero_l (tw_word w))).
  - exact (twe_trans (twe_sym (twe_zero_l tw_zero)) (twe_zero_l tw_zero)).
  - exact (twe_plus IHs IHt).
  - exact (twe_neg IHs).
Qed.

Lemma tw_eq_Equivalence : Equivalence tw_eq.
Proof.
  constructor.
  - exact tw_refl.
  - exact (fun s t => twe_sym).
  - exact (fun s t u => twe_trans).
Qed.

Definition tw_Setoid : Setoid TWTerm := {|
  equiv := tw_eq;
  setoid_equiv := tw_eq_Equivalence
|}.

Definition TWAb : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := TWTerm; is_setoid := tw_Setoid |};
    cmon_zero := tw_zero;
    cmon_plus := tw_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => twe_plus Hs Ht;
    cmon_plus_assoc := twe_assoc;
    cmon_plus_comm := twe_comm;
    cmon_plus_zero_l := twe_zero_l;
    (* [tw_eq] IS a [Prop]-valued relation, so it is its own [Prop]
       mirror and both implications are the identity. *)
    cmon_prop := @PropEquiv_of_relation _ tw_Setoid tw_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := tw_neg;
  ab_neg_respects := fun _ _ Hs => twe_neg Hs;
  ab_neg_left := twe_neg_l
|}.

Definition tw_eq_of_eq {s t : TWTerm} (e : s = t) : tw_eq s t :=
  match e with eq_refl => tw_refl s end.

(* Juxtaposition on the left by a word, extended additively. *)
Fixpoint tw_lmul (w : list L) (t : TWTerm) : TWTerm :=
  match t with
  | tw_word v => tw_word (w ++ v)
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_lmul w s) (tw_lmul w t)
  | tw_neg s => tw_neg (tw_lmul w s)
  end.

Lemma tw_lmul_app (w v : list L) (t : TWTerm) :
  tw_lmul (w ++ v) t = tw_lmul w (tw_lmul v t).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite app_assoc. reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_lmul_nil (t : TWTerm) : tw_lmul nil t = t.
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl;
    [ reflexivity | reflexivity | rewrite IHs, IHt | rewrite IHs ];
    reflexivity.
Qed.

Lemma tw_lmul_respects_r (w : list L) (t t' : TWTerm) :
  tw_eq t t' → tw_eq (tw_lmul w t) (tw_lmul w t').
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - rewrite !app_assoc. exact (twe_letter (w ++ u) v Hab).
  - rewrite !app_assoc. exact (twe_lin (w ++ u) v a b).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

(* Group-level helpers, read off [TWAb]; the middle-four interchange is
   Instance/CMon/Biproduct.v's [cmon_plus_interchange] at [TWAb]. *)
Lemma tw_neg_plus (a b : TWTerm) :
  tw_eq (tw_neg (tw_plus a b)) (tw_plus (tw_neg a) (tw_neg b)).
Proof. exact (ab_neg_plus TWAb a b). Qed.

Lemma tw_neg_zero : tw_eq (tw_neg tw_zero) tw_zero.
Proof. exact (ab_neg_zero TWAb). Qed.

Lemma tw_zero_zero : tw_eq tw_zero (tw_plus tw_zero tw_zero).
Proof. exact (twe_sym (twe_zero_l tw_zero)). Qed.

(* Juxtaposition on the left respects the letters on the right... *)
Lemma tw_lmul_letter (u v : list L) (a b : L) (H : a ≈ b) (t : TWTerm) :
  tw_eq (tw_lmul (u ++ a :: v) t) (tw_lmul (u ++ b :: v) t).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite <- !app_assoc. simpl. exact (twe_letter u (v ++ x) H).
  - apply tw_refl.
  - exact (twe_plus IHs IHt).
  - exact (twe_neg IHs).
Qed.

(* ...and is additive in each of its letters. *)
Lemma tw_lmul_lin (u v : list L) (a b : L) (t : TWTerm) :
  tw_eq (tw_lmul (u ++ cmon_plus A a b :: v) t)
        (tw_plus (tw_lmul (u ++ a :: v) t) (tw_lmul (u ++ b :: v) t)).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite <- !app_assoc. simpl. exact (twe_lin u (v ++ x) a b).
  - exact tw_zero_zero.
  - refine (twe_trans (twe_plus IHs IHt) _).
    exact (cmon_plus_interchange TWAb _ _ _ _).
  - refine (twe_trans (twe_neg IHs) _). apply tw_neg_plus.
Qed.

End Words.

Arguments tw_word {A} _.
Arguments tw_zero {A}.
Arguments tw_plus {A} _ _.
Arguments tw_neg {A} _.
Arguments tw_lmul {A} _ _.
Arguments tw_refl {A} _.
Arguments twe_sym {A s t} _.
Arguments twe_trans {A s t u} _ _.
Arguments twe_letter {A} u v {a b} _.
Arguments twe_lin {A} u v a b.
Arguments twe_plus {A s s' t t'} _ _.
Arguments twe_neg {A s s'} _.
Arguments twe_assoc {A} s t u.
Arguments twe_comm {A} s t.
Arguments twe_zero_l {A} s.
Arguments twe_neg_l {A} s.
Arguments tw_eq_of_eq {A s t} _.

(* A function on words that respects each letter and is additive in each
   letter extends to a homomorphism out of [TWAb]: the universal
   property of the presentation. *)
Section Extension.

Context (A c : Ab).

Local Notation L := (carrier (cmon_setoid A)).

Context (ν : list L → carrier (cmon_setoid c)).
Context (Hletter : ∀ (u v : list L) (a b : L),
                     a ≈ b → ν (u ++ a :: v) ≈ ν (u ++ b :: v)).
Context (Hlin : ∀ (u v : list L) (a b : L),
                  ν (u ++ cmon_plus A a b :: v)
                    ≈ cmon_plus c (ν (u ++ a :: v)) (ν (u ++ b :: v))).

Fixpoint tw_ext_fun (t : TWTerm A) : carrier (cmon_setoid c) :=
  match t with
  | tw_word w => ν w
  | tw_zero => cmon_zero c
  | tw_plus s t => cmon_plus c (tw_ext_fun s) (tw_ext_fun t)
  | tw_neg s => ab_neg c (tw_ext_fun s)
  end.

Lemma tw_ext_respects (s t : TWTerm A) :
  tw_eq A s t → tw_ext_fun s ≈ tw_ext_fun t.
Proof using Hletter Hlin.
  intro He.
  apply pequiv_to.
  induction He as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                  | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - apply pequiv_from. exact (Hletter u v a b Hab).
  - apply pequiv_from. exact (Hlin u v a b).
  - apply pequiv_from.
    exact (cmon_plus_respects c _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from. exact (ab_neg_respects c _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from. apply cmon_plus_assoc.
  - apply pequiv_from. apply cmon_plus_comm.
  - apply pequiv_from. apply cmon_plus_zero_l.
  - apply pequiv_from. apply ab_neg_left.
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Definition tw_ext : TWAb A ~{Ab}~> c.
Proof using Hletter Hlin.
  unshelve refine (@Build_CMonHom (TWAb A) c
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A)
       (carrier (cmon_setoid c)) (is_setoid (cmon_setoid c)) tw_ext_fun _)
    _ _).
  - intros s t H. exact (tw_ext_respects s t H).
  - reflexivity.
  - intros s t. reflexivity.
Defined.

Example tw_ext_word (w : list L) : cmon_map tw_ext (tw_word w) = ν w
  := eq_refl.

End Extension.

Arguments tw_ext {A} c ν Hletter Hlin.

(* ------------------------------------------------------------------------ *)
(** ** The n-fold tensor powers, and the words as their direct sum *)

(* The tensor powers are Structure/Monoidal/Hypergraph/Spider.v's
   [tpower] at Instance/Ab/Monoidal.v's [Ab_Monoidal]: A^{⊗0} is the unit
   ℤ and A^{⊗(n+1)} is A ⊗ A^{⊗n}, Instance/Ab/Tensor.v's [AbTensor]. *)
Example tpower_ab_zero (A : Ab) : A ^⨂ 0 = ZAb := eq_refl.

Example tpower_ab_succ (A : Ab) (n : nat) :
  A ^⨂ (S n) = AbTensor A (A ^⨂ n) := eq_refl.

Section Coproduct.

Context (A : Ab).

Local Notation L := (carrier (cmon_setoid A)).

(* A word as a pure tensor of its length: ⟨a₁ … aₙ⟩ ↦ a₁ ⊗ (… ⊗ (aₙ ⊗ 1)). *)
Fixpoint tw_pure (w : list L) : carrier (A ^⨂ (length w)) :=
  match w with
  | nil => ZAb_one
  | a :: w' => @ts_gen A (A ^⨂ (length w')) a (tw_pure w')
  end.

(* The injection of degree 0: k ↦ k·⟨⟩. *)
Definition tw_iota0 : ZAb ~{Ab}~> TWAb A.
Proof.
  unshelve refine (@Build_CMonHom ZAb (TWAb A)
    (@Build_SetoidMorphism (carrier ZAb) (is_setoid (cmon_setoid ZAb))
       (TWTerm A) (tw_Setoid A) (fun k => zsmul (TWAb A) k (tw_word nil)) _)
    _ _).
  - intros k k' H. apply ZAb_eq in H. subst. apply tw_refl.
  - exact (zsmul_Z0 (TWAb A) _).
  - intros k k'. exact (zsmul_add (TWAb A) k k' _).
Defined.

(* The bilinear map a, x ↦ ⟨a⟩ · ι x out of A × A^{⊗n}. *)
Definition tw_lmul1_bilin (n : nat) (ι : A ^⨂ n ~{Ab}~> TWAb A) :
  Bilinear A (A ^⨂ n) (TWAb A).
Proof.
  unshelve refine (@Build_Bilinear A (A ^⨂ n) (TWAb A)
                     (fun a x => tw_lmul (a :: nil) (cmon_map ι x)) _ _ _).
  - intros a a' Ha x x' Hx.
    refine (twe_trans (tw_lmul_letter A nil nil a a' Ha _) _).
    exact (tw_lmul_respects_r A _ _ _ (proper_morphism (cmon_map ι) _ _ Hx)).
  - intros a a' x. exact (tw_lmul_lin A nil nil a a' _).
  - intros a x x'.
    exact (tw_lmul_respects_r A _ _ _ (cmon_map_plus ι x x')).
Defined.

(* The injections ιₙ : A^{⊗n} → ⨁, by the tensor's universal property. *)
Fixpoint tw_iota (n : nat) : A ^⨂ n ~{Ab}~> TWAb A :=
  match n with
  | O => tw_iota0
  | S n => tensor_ump (tw_lmul1_bilin n (tw_iota n))
  end.

Example tw_iota_gen (n : nat) (a : L) (x : carrier (A ^⨂ n)) :
  cmon_map (tw_iota (S n)) (ts_gen a x)
    = tw_lmul (a :: nil) (cmon_map (tw_iota n) x) := eq_refl.

(* Every word is the image of its pure tensor. *)
Lemma tw_word_iota (w : list L) :
  tw_eq A (tw_word w) (cmon_map (tw_iota (length w)) (tw_pure w)).
Proof.
  induction w as [ | a w IH ]; simpl.
  - exact (twe_sym (zsmul_one (TWAb A) (tw_word nil))).
  - exact (tw_lmul_respects_r A (a :: nil) _ _ IH).
Qed.

End Coproduct.

Arguments tw_pure {A} w.
Arguments tw_iota {A} n.

(* The copairing of a family ιₙ : A^{⊗n} → c. *)
Section Desc.

Context (A : Ab) (c : Ab).

Local Notation L := (carrier (cmon_setoid A)).

Definition ts_gen_hom (n : nat) (a : L) :
  A ^⨂ n ~{Ab}~> AbTensor A (A ^⨂ n).
Proof.
  unshelve refine (@Build_CMonHom (A ^⨂ n) (AbTensor A (A ^⨂ n))
    (@Build_SetoidMorphism (carrier (A ^⨂ n))
       (is_setoid (cmon_setoid (A ^⨂ n)))
       (tsum A (A ^⨂ n)) (ts_Setoid A (A ^⨂ n)) (@ts_gen A (A ^⨂ n) a) _)
    _ _).
  - intros x y H. exact (te_gen (reflexivity a) H).
  - exact (ts_gen_zero_r a).
  - intros x y. exact (te_bilin_r a x y).
Defined.

(* The family shifted by one letter a: x ↦ ι_{n+1}(a ⊗ x). *)
Definition tw_shift (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (a : L) :
  ∀ n : nat, A ^⨂ n ~{Ab}~> c :=
  fun n => iota (S n) ∘[Ab] ts_gen_hom n a.

Fixpoint tw_desc_fun (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (t : TWTerm A) :
  carrier c :=
  match t with
  | tw_word w => cmon_map (iota (length w)) (tw_pure w)
  | tw_zero => cmon_zero c
  | tw_plus s t => cmon_plus c (tw_desc_fun iota s) (tw_desc_fun iota t)
  | tw_neg s => ab_neg c (tw_desc_fun iota s)
  end.

(* The copairing respects a letter and is additive in it.  The induction
   is on the prefix, generalized over the whole family, so no transport
   along the length of a word is needed. *)
Lemma tw_desc_letter (u : list L) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (v : list L) (a b : L), a ≈ b →
  cmon_map (iota (length (u ++ a :: v))) (tw_pure (u ++ a :: v))
    ≈ cmon_map (iota (length (u ++ b :: v))) (tw_pure (u ++ b :: v)).
Proof.
  induction u as [ | d u IH ]; intros iota v a b H; simpl.
  - apply (proper_morphism (cmon_map (iota (S (length v))))).
    exact (te_gen H (reflexivity _)).
  - exact (IH (tw_shift iota d) v a b H).
Qed.

Lemma tw_desc_lin (u : list L) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (v : list L) (a b : L),
  cmon_map (iota (length (u ++ cmon_plus A a b :: v)))
           (tw_pure (u ++ cmon_plus A a b :: v))
    ≈ cmon_plus c
        (cmon_map (iota (length (u ++ a :: v))) (tw_pure (u ++ a :: v)))
        (cmon_map (iota (length (u ++ b :: v))) (tw_pure (u ++ b :: v))).
Proof.
  induction u as [ | d u IH ]; intros iota v a b; simpl.
  - refine (transitivity (proper_morphism (cmon_map (iota (S (length v))))
                            _ _ (te_bilin_l a b (tw_pure v))) _).
    exact (cmon_map_plus (iota (S (length v))) _ _).
  - exact (IH (tw_shift iota d) v a b).
Qed.

Lemma tw_desc_respects (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (s t : TWTerm A) :
  tw_eq A s t → tw_desc_fun iota s ≈ tw_desc_fun iota t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                  | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - apply pequiv_from. exact (tw_desc_letter u iota v a b Hab).
  - apply pequiv_from. exact (tw_desc_lin u iota v a b).
  - apply pequiv_from.
    exact (cmon_plus_respects c _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from. exact (ab_neg_respects c _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from. apply cmon_plus_assoc.
  - apply pequiv_from. apply cmon_plus_comm.
  - apply pequiv_from. apply cmon_plus_zero_l.
  - apply pequiv_from. apply ab_neg_left.
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Definition tw_desc (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) :
  TWAb A ~{Ab}~> c.
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) c
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (carrier c)
       (is_setoid (cmon_setoid c)) (tw_desc_fun iota) _) _ _).
  - intros s t H. exact (tw_desc_respects iota s t H).
  - reflexivity.
  - intros s t. reflexivity.
Defined.

(* Juxtaposition on the left by one letter shifts the family, LEIBNIZ. *)
Lemma tw_desc_lmul (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (a : L)
  (t : TWTerm A) :
  tw_desc_fun iota (tw_lmul (a :: nil) t) = tw_desc_fun (tw_shift iota a) t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* The copairing composed with ιₙ is the n-th map of the family. *)
Lemma tw_desc_iota (n : nat) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (x : carrier (A ^⨂ n)),
  cmon_map (tw_desc iota) (cmon_map (tw_iota n) x) ≈ cmon_map (iota n) x.
Proof.
  induction n as [ | n IH ]; intros iota x.
  - simpl.
    refine (transitivity (zsmul_hom (tw_desc iota) x (tw_word nil)) _).
    simpl.
    refine (transitivity (symmetry (zsmul_hom (iota O) x ZAb_one)) _).
    apply (proper_morphism (cmon_map (iota O))).
    exact (zsmul_int_one x).
  - refine (tensor_hom_ext (tw_desc iota ∘[Ab] tw_iota (S n)) (iota (S n))
              _ x).
    intros a y. simpl.
    rewrite tw_desc_lmul.
    exact (IH (tw_shift iota a) y).
Qed.

(* ...and it is the only such homomorphism. *)
Lemma tw_desc_unique (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (g : TWAb A ~{Ab}~> c)
  (H : ∀ n : nat, g ∘[Ab] tw_iota n ≈ iota n) (t : TWTerm A) :
  cmon_map g t ≈ tw_desc_fun iota t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - refine (transitivity (proper_morphism (cmon_map g) _ _
                            (tw_word_iota A w)) _).
    exact (H (length w) (tw_pure w)).
  - exact (cmon_map_zero g).
  - refine (transitivity (cmon_map_plus g s t) _).
    exact (cmon_plus_respects c _ _ IHs _ _ IHt).
  - refine (transitivity (ab_map_neg g s) _).
    exact (ab_neg_respects c _ _ IHs).
Qed.

End Desc.

(* Mac Lane's "(infinite) direct sum of the n-fold tensor powers": the
   words are the coproduct in Ab of the A^{⊗n}, with the injections ιₙ. *)
Definition TW_is_tensor_coproduct (A : Ab) :
  @IsIndexedCoproduct Ab nat (fun n => A ^⨂ n) (TWAb A) (@tw_iota A).
Proof.
  apply Build_IsIndexedCoproduct.
  intros c iota.
  unshelve eexists.
  - exact (tw_desc A c iota).
  - intros n x. exact (tw_desc_iota A c n iota x).
  - intros g Hg t. symmetry. exact (tw_desc_unique A c iota g Hg t).
Defined.

(* The copairing computes on words. *)
Example tw_desc_word (A c : Ab) (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (w : list (carrier (cmon_setoid A))) :
  cmon_map (tw_desc A c iota) (tw_word w)
    = cmon_map (iota (length w)) (tw_pure w) := eq_refl.
