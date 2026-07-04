Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.

Generalizable All Variables.

(** * Symmetry of the funny tensor product

    [FunnySwap : C □ D ⟶ D □ C] swaps the two coordinates:

      (c, d) ↦ (d, c)        lstep f ↦ rstep f        rstep g ↦ lstep g

    Each step swaps IN PLACE — the word is never reversed.  A word
    (c1, d1) ~> (c2, d2) becomes a word (d1, c1) ~> (d2, c2) with the same
    steps in the same temporal order, each moving the other coordinate;
    reversing the word would flip domain and codomain and is wrong.

    Like every functor out of a funny tensor product, [FunnySwap] is
    packaged through the separately-functorial eliminator [FunnyUP]
    (Construction/Funny.v), so functoriality is inherited from the universal
    property rather than re-proved by word induction.  Since swapping twice
    is the identity on the generating steps, [FunnySwap] is involutive
    ([FunnySwap_invol]) and hence an isomorphism of categories, both in
    [StrictCat] ([Funny_swap]) and — through the comparison functor
    [StrictCat_to_Cat] — in the weak [Cat] ([Funny_swap_cat]).

    [FunnySwap_natural] is the strict naturality square in both variables
    jointly: swapping commutes with [FunnyBimap F G] (Bifunctor.v).  This
    is the braiding underlying the symmetric monoidal structure of [□] on
    [StrictCat] (Instance/StrictCat/Funny.v); per Foltz–Lair–Kelly (1980)
    both monoidal biclosed structures on Cat are symmetric, and this is the
    symmetry of the funny one.

    All coherence statements live in [Functor_StrictEq_Setoid] — the
    hom-setoid of [StrictCat] — because the funny tensor product is not
    invariant under equivalence of categories (see the header of
    Construction/Funny.v). *)

(** ** The action of the swap, as separately functorial data *)

Program Definition FunnySwap_sep {C D : Category} :
  SepFunctorial (E := D □ C) (fun (c : C) (d : D) => (d, c)) := {|
  sf_lmap := fun c c' f d => rstep f;
  sf_rmap := fun c d d' g => lstep g
|}.
Next Obligation.
  proper.
  apply feq_consR; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation. exact (feq_idR fnil). Qed.
Next Obligation. exact (feq_idL fnil). Qed.
Next Obligation. apply feq_sym; apply feq_fuseR. Qed.
Next Obligation. apply feq_sym; apply feq_fuseL. Qed.

Definition FunnySwap {C D : Category} : (C □ D) ⟶ (D □ C) :=
  FunnyUP FunnySwap_sep.

(** ** Computation lemmas

    [ffold] and [fapp] compute, so the action of [FunnySwap] on words is
    definitional, constructor by constructor: the word is mapped step by
    step, in order, with L-steps becoming R-steps and vice versa. *)

Lemma FunnySwap_fnil {C D : Category} {c : C} {d : D} :
  @fmap (C □ D) (D □ C) FunnySwap (c, d) (c, d) fnil = fnil.
Proof. reflexivity. Qed.

Lemma FunnySwap_fconsL {C D : Category} {c1 c2 : C} {d1 : D} {c3 : C} {d3 : D}
  (f : c1 ~{C}~> c2) (t : FunHom c2 d1 c3 d3) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d1) (c3, d3) (fconsL f t)
    = fconsR f (@fmap (C □ D) (D □ C) FunnySwap (c2, d1) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnySwap_fconsR {C D : Category} {c1 : C} {d1 d2 : D} {c3 : C} {d3 : D}
  (g : d1 ~{D}~> d2) (t : FunHom c1 d2 c3 d3) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d1) (c3, d3) (fconsR g t)
    = fconsL g (@fmap (C □ D) (D □ C) FunnySwap (c1, d2) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnySwap_lstep {C D : Category} {c1 c2 : C} {d : D}
  (f : c1 ~{C}~> c2) :
  @fmap (C □ D) (D □ C) FunnySwap (c1, d) (c2, d) (lstep f) = rstep f.
Proof. reflexivity. Qed.

Lemma FunnySwap_rstep {C D : Category} {c : C} {d1 d2 : D}
  (g : d1 ~{D}~> d2) :
  @fmap (C □ D) (D □ C) FunnySwap (c, d1) (c, d2) (rstep g) = lstep g.
Proof. reflexivity. Qed.

(** ** Involutivity

    Swapping twice fixes every generating step on the nose, so the round
    trip is strictly the identity functor.  On an explicit pair the object
    round trip computes to [eq_refl]; [Funny_strict_eq] (StrictEq.v)
    supplies the pair destructuring needed because [prod] has no
    definitional eta at an abstract object. *)

Lemma FunnySwap_invol {C D : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C □ D))
    (@FunnySwap D C ◯ @FunnySwap C D) Id.
Proof.
  apply (Funny_strict_eq (@FunnySwap D C ◯ @FunnySwap C D) Id
           (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

(** ** Strict naturality in both variables

    Both composites send [lstep f] to [rstep (fmap[F] f)] and [rstep g] to
    [lstep (fmap[G] g)] definitionally, and agree definitionally on
    explicit-pair objects. *)

Lemma FunnySwap_natural {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (D' □ C'))
    (@FunnySwap C' D' ◯ FunnyBimap F G) (FunnyBimap G F ◯ @FunnySwap C D).
Proof.
  apply (Funny_strict_eq (@FunnySwap C' D' ◯ FunnyBimap F G)
           (FunnyBimap G F ◯ @FunnySwap C D) (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

(** ** The symmetry isomorphism

    In [StrictCat] the involution makes [FunnySwap] a genuine
    (on-the-nose) isomorphism of categories; pushing it through the
    comparison functor [StrictCat_to_Cat] (Instance/StrictCat/ToCat.v)
    yields the corresponding isomorphism — an equivalence — in the weak
    [Cat]. *)

Definition Funny_swap {C D : Category} : (C □ D) ≅[StrictCat] (D □ C) :=
  @Build_Isomorphism StrictCat (C □ D) (D □ C)
    (@FunnySwap C D) (@FunnySwap D C)
    (@FunnySwap_invol D C) (@FunnySwap_invol C D).

Definition Funny_swap_cat {C D : Category} : (C □ D) ≅[Cat] (D □ C) :=
  fobj_iso StrictCat_to_Cat (C □ D) (D □ C) Funny_swap.
