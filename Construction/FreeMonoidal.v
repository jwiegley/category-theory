Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Thin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * The free monoidal category on one generator

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §VII.2
    (book pp. 165-168): binary words [maclane:VII.2:def1], the category [W]
    [maclane:VII.2:construction1], and the freeness theorem
    [maclane:VII.2:thm1].
    nLab: https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories

    A monoidal category has a tensor that is associative and unital only UP TO
    coherent isomorphism, so an iterated tensor is not one object but a whole
    family of them, one per bracketing.  Mac Lane's device for studying that
    family is to make the bracketings themselves the objects of a category.  A
    BINARY WORD is a formal parenthesised product built from a single
    placeholder [(-)] and an empty slot [e0]; [W] has the binary words as
    objects and EXACTLY ONE arrow between any two words of the same length.

    That last clause is the whole point.  Because the hom is a proposition, any
    two parallel arrows of [W] are equal, so every diagram in [W] commutes for
    free — and a structure-preserving functor out of [W] must therefore send
    every diagram of bracket-shuffles to a commuting diagram downstream.  [W]
    is the walking (weak, non-symmetric) monoidal category on one object, and
    its universal property is a form of the coherence theorem.

    WHY THE HOM IS A LENGTH EQUATION.  We take [hom v w := wlen v = wlen w]
    and declare the hom-setoid equivalence to be the constantly-true relation,
    exactly as Instance/Proset.v:34-44 does for a preorder.  Two consequences
    are load-bearing:

      - every law of a category, of a bifunctor, and of [Monoidal] — including
        the triangle and the pentagon — is an equation between PARALLEL arrows
        of [W], hence inhabited by [I] : True.  None of them costs a proof.
        This is [W_thin] below, and it is why this file contains no coherence
        argument at all: the coherence content of §VII.2 lives entirely in the
        FREENESS theorem, not in [W] itself.

      - [wlen] must be defined structurally with [+], not with an accumulator.
        Then [wlen (WT WE x)] is convertible with [wlen x] because [0 + n]
        reduces, so the left unitor of [W] is literally [eq_refl].  An
        accumulator-based length would break that conversion and force a cast
        into every unitor.

    SCOPE OF THIS FILE.  It supplies the reusable core: the word datatype, [W],
    and its monoidal structure.  Mac Lane's Theorem 1 — for a monoidal [B] and
    an object [b], a unique structure-preserving functor [W ⟶ B] sending the
    generator to [b] — is developed on top of this and is stated against STRICT
    monoidal functors, which is what Mac Lane's own statement means: his Moncat
    (§VII.1, [maclane:VII.1:construction2]) is "the category of all small
    monoidal categories with strict morphisms as arrows", and his strict
    morphism ([maclane:VII.1:def3]) is required to carry alpha, lambda and rho
    to alpha', lambda' and rho' on the nose.  Uniqueness among merely STRONG
    monoidal functors is false, so the strict reading is not a weakening but
    the only one under which Theorem 1 can hold.

    The word datatype is exported as a standalone [Set] on purpose: §VII.2's
    coherence corollary and the §XI word-functor development both need to
    recurse over the same words. *)

(** ** Binary words *)

(* [maclane:VII.2:def1].  [WE] is the empty word e0, [WI] the single generator
   (-), and [WT] the formal tensor. *)
Inductive Word : Set :=
  | WE : Word
  | WI : Word
  | WT : Word → Word → Word.

(* Structural, with [+] — see the header note on conversion. *)
Fixpoint wlen (w : Word) : nat :=
  match w with
  | WE      => 0
  | WI      => 1
  | WT v u  => wlen v + wlen u
  end.

(* The right-normalised word of each length. *)
Fixpoint nfword (n : nat) : Word :=
  match n with
  | O   => WE
  | S k => WT WI (nfword k)
  end.

Lemma wlen_nfword (n : nat) : wlen (nfword n) = n.
Proof. induction n; simpl; auto. Qed.

(** ** A generic helper: the tensor of two isomorphisms

    Stated over an arbitrary monoidal category because both [W] below and the
    target [B] of the freeness theorem use it.  It duplicates the [iso_bimap]
    of Structure/Monoidal/Drinfeld.v:82 on purpose: importing Drinfeld here
    would drag half-braidings into every consumer of the word datatype, and
    Drinfeld is not edited by this development. *)
Program Definition tensor_iso {C : Category} `{@Monoidal C} {x y z w : C}
  (i : x ≅ y) (j : z ≅ w) : (x ⨂ z) ≅ (y ⨂ w) := {|
  to   := to i ⨂ to j;
  from := from i ⨂ from j
|}.
Next Obligation.
  rewrite <- bimap_comp, !iso_to_from; now rewrite bimap_id_id.
Qed.
Next Obligation.
  rewrite <- bimap_comp, !iso_from_to; now rewrite bimap_id_id.
Qed.

(** ** The category W *)

(* One arrow per pair of equal-length words.  The hom is a proposition and the
   hom-setoid identifies everything parallel, so [W] is thin by construction. *)
Program Definition W : Category := {|
  obj     := Word;
  hom     := fun v w => wlen v = wlen w;
  homset  := fun _ _ => {| Setoid.equiv := fun _ _ => True |};
  id      := fun _ => eq_refl;
  compose := fun _ _ _ f g => eq_trans g f
|}.

(* Every law of [W] — and, below, of its tensor and of [Monoidal] — is an
   equation between parallel arrows, so this single lemma discharges them all. *)
Definition W_thin : Thin W.
Proof. intros x y f g; constructor. Defined.

(* Mac Lane's W is a preorder-groupoid: the arrow backwards always exists. *)
Definition W_iso {v w : Word} (f : v ~{W}~> w) : v ≅[W] w :=
  thin_iso W_thin f (eq_sym f).

(** ** The monoidal structure *)

Program Definition W_tensor : W ∏ W ⟶ W := {|
  fobj := fun p => WT (fst p) (snd p);
  fmap := fun _ _ f => f_equal2 Nat.add (fst f) (snd f)
|}.

(* [unit_left] is [eq_refl] because [0 + n] reduces; [unit_right] and
   [tensor_assoc] are the corresponding [Nat] facts.  Thinness supplies
   uniqueness of each arrow, [Nat] arithmetic supplies its existence. *)
#[export] Program Instance W_Monoidal : @Monoidal W := {|
  I            := WE;
  tensor       := W_tensor;
  (* The endpoints are pinned explicitly: left to inference, [Program] reads
     them off [eq_refl] and then cannot match [x] against [I ⨂ x]. *)
  unit_left    := fun x => @thin_iso W W_thin (WT WE x) x eq_refl eq_refl;
  unit_right   := fun x => @thin_iso W W_thin (WT x WE) x
                             (Nat.add_0_r (wlen x))
                             (eq_sym (Nat.add_0_r (wlen x)));
  tensor_assoc := fun x y z =>
    @thin_iso W W_thin (WT (WT x y) z) (WT x (WT y z))
      (eq_sym (Nat.add_assoc (wlen x) (wlen y) (wlen z)))
      (Nat.add_assoc (wlen x) (wlen y) (wlen z))
|}.

(* Every remaining obligation — the six naturality fields, the triangle and the
   pentagon — is an equation between parallel arrows of [W], so thinness closes
   all of them uniformly.  This is the whole reason the file carries no
   coherence argument. *)
Solve All Obligations with (intros; constructor).

(** ** Acceptance tests

    Everything here computes; the point of stating them is that the
    definitional facts the header claims really are definitional. *)

Example wlen_WE  : wlen WE = 0%nat := eq_refl.
Example wlen_WI  : wlen WI = 1%nat := eq_refl.
Example wlen_mix : wlen (WT (WT WI WE) WI) = 2%nat := eq_refl.

Example nfword_3 : nfword 3 = WT WI (WT WI (WT WI WE)) := eq_refl.

(* The tensor of [W] is the word constructor, on the nose. *)
Example W_tensor_obj (v w : Word) :
  (v ⨂[W_Monoidal] w)%object = WT v w := eq_refl.

(* The unit is the empty word, and the left unitor is [eq_refl] — the
   conversion the header's [wlen] note is about. *)
Example W_unit_is_WE : @I W W_Monoidal = WE := eq_refl.
Example W_unit_left_is_refl (x : Word) :
  to (@unit_left W W_Monoidal x) = eq_refl := eq_refl.

(* Thinness, as it is actually used: ANY two parallel arrows of [W] agree, so
   every diagram of [W] commutes.  This is the property the freeness theorem
   will consume. *)
Example W_thin_concrete (v w : Word) (f g : v ~{W}~> w) : f ≈ g := W_thin v w f g.

(* And the arrows really are the length equations, so [W] is a groupoid. *)
Example W_iso_concrete : WT (WT WI WE) WI ≅[W] WT WI (WT WI WE) :=
  W_iso (v:=WT (WT WI WE) WI) (w:=WT WI (WT WI WE)) eq_refl.
