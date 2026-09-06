Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* [Category.Functor.Opposite] opens [functor_scope], after which a bare
   [C^op] on a CATEGORY parses as [Opposite_Functor C] and is rejected with
   "The term C has type Category while it is expected to have type ?C ⟶ ?D".
   Reopening [category_scope] here restores the reading this file wants.
   Same family as the notation guards of Theory/Universal/Arrow/Dual.v and
   Instance/Rng/Mod.v. *)
Open Scope category_scope.

(* The power-object functor of an elementary topos, and its self-adjointness
   on the right.

   nLab:      https://ncatlab.org/nlab/show/power+object
   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.10,
   book p. 107 (`maclane:IV.10:remark2`), closes the topos section with one
   sentence and no proof:

     "The axioms for a topos have many useful consequences. For exam-
      ples, every topos has all finite colimits."

   The standard route to that sentence is Paré's (1974): the contravariant
   power-object functor P = Ω^(−) : E^op ⟶ E is self-adjoint on the right and
   MONADIC, so E^op is EQUIVALENT to the Eilenberg-Moore category of the induced
   monad and therefore inherits E's finite limits; read in E those are finite
   colimits.  This file is step one and step two of that route: the functor, and
   the self-adjointness.  Monadicity is Structure/Topos/Monadic.v; the colimits
   are Structure/Topos/Colimits.v.  NONE of Mac Lane, Awodey or Seven Sketches
   proves the theorem, and Mac Lane-Moerdijk, the reference Mac Lane and Awodey
   send the reader to, was not available; the argument was reconstructed and
   CHECKED BY COMPILATION.

   THE FUNCTOR IS A PARTIAL APPLICATION AND RAISES NO OBLIGATION.  The
   internal hom [InternalHomFunctor C : C^op ∏ C ⟶ C] of
   Functor/Hom/Internal.v is contravariant in its FIRST argument, which is
   exactly the variance of P, so [Partial_l] at Ω is the whole definition
   and all three functor laws are inherited.  Two nearby constants are NOT
   donors, and both refusals are pinned in Test/ProbeToposColimits405.v:
   [Partial_r] fixes the first argument and varies the second, so it has
   the wrong variance; and [Exp_Functor] of
   Structure/Cartesian/Closed/Adjunction.v is covariant in the base with
   the exponent held fixed (that file's own header calls it "the partial
   application at a fixed exponent"), so its object action is (−)^S and
   not Ω^(−).

   STEP TWO CONSUMES NO SUBOBJECT CLASSIFIER, ONLY THE OBJECT Ω.  The issue
   routes the two-sided transposition through [relations_iso]
   (Structure/Topos.v), i.e. through subobjects of a × b.  That is not needed:
   the bijection E(a, Ω^b) ≅ E(b, Ω^a) is a fact about ANY object in ANY
   cartesian closed category, and the map is already in the tree as [flip]
   (Structure/Cartesian/Closed.v), [flip f := curry (uncurry f ∘ swap)].  What
   was missing is that [flip] is an INVOLUTION: a whole-tree search for an
   involution lemma about that [flip] returned only the list-reversal hypothesis
   [flip_involutive] of Lib/TList.v and Lib/NETList.v and Theory/Morphisms.v's
   [flip_invol] about an [Involutive] endomorphism (a substring sweep adds
   Construction/Free/Groupoid.v's [sflip_involutive], about a different flip),
   none of which is this [flip], and by SHAPE the only statement of the form
   [flip (flip f)] anywhere in the tree is [flip_flip] itself, which supplies it
   in four rewrites.

   THE FOUR NATURALITY FIELDS COLLAPSE TO TWO LEMMAS, and that is why the
   step is cheap.  With S = T = P and both legs of the isomorphism equal
   to [flip], [to_aor_nat_a] and [from_aor_nat_x] are one and the same
   statement ([flip_comp]) and [to_aor_nat_x] and [from_aor_nat_a] are the
   other ([flip_pow_comp]).  The three prior in-tree witnesses of S = T --
   Adjunction/Right.v's [Powerset_AdjointOnTheRight],
   Structure/Monoidal/Dual.v's [dual_self_adjoint_on_the_right] and
   Instance/InnerProduct/Galois.v's [perp_AdjointOnTheRight] -- build
   [aor] the same way, as a record literal whose [to] and [from] are one
   map.

   FIDELITY TO THE ISSUE'S OWN ROUTE is nevertheless recorded, as
   [pow_aor_is_relations]: transporting a morphism a ~> Pow b to the
   subobject of a × b it classifies, reindexing that subobject along
   [swap], and classifying back is [flip].  It holds at ≈ and is refused
   at [eq_refl] -- NOT because either leg of [relations_iso] is stuck
   (both reduce on the nose, and §(E) reads them back by [eq_refl]) but
   because the two sides are [curry] of the untransposed map composed
   with [swap] against [curry] of the characteristic map of a
   doubly-reindexed subobject, and reindexing introduces chosen pullback
   objects.  This is the one place the classifier enters the file, and
   only as a check.

   WHAT IS NOT HERE.  No monad: [pow_monad] would need
   [Adjunction_Induced_Monad] from Monad/Comparison.v, measured at +6
   modules on this file's closure, so it is declared in
   Structure/Topos/Monadic.v where the monadicity machinery is required
   anyway.  No naturality of [pow_aor_is_relations] in a or b.  No claim
   that the unit and the counit differ: they are the same term. *)

Section ToposPower.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

(** ** (A) The power-object functor *)

(* P := Ω^(−), as the partial application of the internal hom at Ω.  Its
   contravariance is [InternalHomFunctor]'s in its first argument. *)
Definition PowF : C^op ⟶ C := Partial_l (InternalHomFunctor C) Ω.

(* Three readbacks, all on the nose. *)
Example powf_obj (a : C) : fobj[PowF] a = Pow a := eq_refl.

Example powf_obj_exponent (a : C) : fobj[PowF] a = exponent_obj a Ω := eq_refl.

Example powf_map {a b : C} (f : b ~{C}~> a) :
  fmap[PowF] f = curry (id ∘ eval ∘ second f) := eq_refl.

(** ** (B) [flip] is an involution, and its two composition laws *)

(* NEW: no involution lemma for the cartesian-closed [flip] existed. *)
Lemma flip_flip {a b : C} (f : a ~> Ω^b) : flip (flip f) ≈ f.
Proof.
  unfold flip.
  rewrite uncurry_curry, <- comp_assoc, swap_invol, id_right.
  apply curry_uncurry.
Qed.

#[local] Program Instance flip_respects {a b : C} :
  Proper (equiv ==> equiv) (@flip C _ _ a Ω b).
Next Obligation. proper. unfold flip. now rewrites. Qed.

(* Naturality in the SOURCE: precomposition downstairs is P-image
   postcomposition upstairs. *)
Lemma flip_comp {a a' b : C} (f : a ~> Ω^b) (g : a' ~> a) :
  flip (f ∘ g) ≈ fmap[PowF] g ∘ flip f.
Proof.
  unfold flip; simpl.
  rewrite uncurry_comp, curry_comp_l, id_left, <- !comp_assoc,
          <- first_second, !comp_assoc, eval_first, uncurry_curry,
          <- !comp_assoc, swap_second.
  reflexivity.
Qed.

(* Naturality in the EXPONENT: P-image precomposition downstairs is
   postcomposition upstairs. *)
Lemma flip_pow_comp {a x x' : C} (p : a ~> Ω^x') (k : x ~> x') :
  flip (fmap[PowF] k ∘ p) ≈ flip p ∘ k.
Proof.
  apply uncurry_inj.
  unfold flip; simpl.
  rewrite uncurry_curry, uncurry_comp, uncurry_curry, uncurry_comp,
          uncurry_curry, id_left, <- (eval_first p), <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  unfork.
Qed.

(** ** (C) Self-adjointness on the right *)

(* [flip] as a morphism of [Sets], used for BOTH legs of the isomorphism. *)
Program Definition flip_mor (a b : C) :
  {| carrier := a ~{C}~> Ω^b ; is_setoid := @homset C a (Ω^b) |}
    ~{Sets}~>
  {| carrier := b ~{C}~> Ω^a ; is_setoid := @homset C b (Ω^a) |} :=
  {| morphism := fun f => flip f |}.
Next Obligation. proper. unfold flip. now rewrites. Qed.

Program Definition pow_aor (a x : C) :
  @Isomorphism Sets
    {| carrier := @hom C a (PowF x); is_setoid := @homset C a (PowF x) |}
    {| carrier := @hom C x (PowF a); is_setoid := @homset C x (PowF a) |} :=
  {| to := flip_mor a x ; from := flip_mor x a |}.
Next Obligation. simpl; apply flip_flip. Qed.
Next Obligation. simpl; apply flip_flip. Qed.

(* Mac Lane §IV.2 definition 2's vocabulary (Adjunction/Right.v): the four
   naturality fields are [flip_comp], [flip_pow_comp], [flip_pow_comp],
   [flip_comp], in that order. *)
Program Definition pow_self_adjoint : AdjointOnTheRight PowF PowF :=
  {| aor := pow_aor |}.
Next Obligation. apply flip_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_comp. Qed.

(* The ordinary adjunction it unpacks to.  In Theory/Adjunction.v's naming
   [Adjunction {C D} (F : D ⟶ C) (U : C ⟶ D)] this reads: the "top"
   category is C^op, the "bottom" is C, the LEFT adjoint is P^op and the
   RIGHT adjoint -- the monadic one -- is P. *)
Definition pow_adjunction :
  @Adjunction (C^op) C (Opposite_Functor PowF) PowF :=
  Adjunction_of_AdjointOnTheRight pow_self_adjoint.

(* The two transposes ARE [flip], on the nose. *)
Example pow_to_adj_is_flip {a x : C} (f : a ~> PowF x) :
  to (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

Example pow_from_adj_is_flip {a x : C} (f : x ~> PowF a) :
  from (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

(* The unit and the counit of a self-adjunction on the right are one and
   the same map, [flip id] -- classically the "singleton of singleton"
   Ω^(Ω^x) map.  Both readbacks are on the nose. *)
Example pow_unit_is_flip_id {x : C} :
  @unit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

Example pow_counit_is_flip_id {x : C} :
  @counit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

(** ** (D) The reduction lemma for precomposition *)

(* P applied to m, precomposed with a transpose, is the transpose of the
   substituted map.  Used at two sites in Structure/Topos/Monadic.v,
   [pow_ex_mono] and [pow_bc]. *)
Lemma pow_precompose {z u x : C} (m : u ~> x) (h : z × x ~> Ω) :
  fmap[PowF] m ∘ curry h ≈ curry (h ∘ second m).
Proof.
  simpl.
  rewrite curry_comp_l, id_left, <- !comp_assoc, <- first_second,
          !comp_assoc, eval_first, uncurry_curry.
  reflexivity.
Qed.

(** ** (E) Fidelity to the issue's [relations_iso] route *)

(* BOTH legs of [relations_iso] reduce on the nose, which the brief for this
   work did not expect: the composite of two [Program]-elaborated setoid
   morphisms still converts to [curry ∘ char_sub] one way and to pulling
   truth back along the untransposed map the other. *)
Example relations_iso_to_is_curry_char {a b : C} (s : SubObj (a × b)) :
  to (relations_iso a b) s = curry (char_sub s) := eq_refl.

Example relations_iso_from_is_reindex {a b : C} (f : a ~> Pow b) :
  from (relations_iso a b) f = sub_reindex (uncurry f) truth_subobject
  := eq_refl.

(* The issue's transposition: read f : a ~> Pow b as a subobject of a × b,
   turn that relation round with [swap], and read it back as b ~> Pow a. *)
Definition pow_relations {a b : C} (f : a ~> Pow b) : b ~> Pow a :=
  to (relations_iso b a) (sub_reindex swap (from (relations_iso a b) f)).

(* It agrees with [flip], hence with [aor], POINTWISE and at ≈.  The proof
   is [char_reindex] followed by the classifier round trip; no naturality
   of either isomorphism is used.  The [eq_refl] form is refused -- the two
   sides are [curry] of the untransposed map composed with [swap] on one
   side and [curry] of a characteristic map of a doubly-reindexed subobject
   on the other, and the reindexing introduces chosen pullback objects.
   Test/ProbeToposColimits405.v pins the refusal with this lemma as its
   control. *)
Lemma pow_aor_is_relations {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f ≈ pow_relations f.
Proof.
  assert (Hl : to (pow_aor a b) f ≈ curry (uncurry f ∘ swap))
    by reflexivity.
  assert (Hr : pow_relations f
                 ≈ curry (char_sub (sub_reindex swap
                     (sub_reindex (uncurry f) truth_subobject))))
    by reflexivity.
  rewrite Hl, Hr.
  apply curry_respects.
  symmetry.
  transitivity (char_sub (sub_reindex (uncurry f) truth_subobject) ∘ swap).
  - apply char_reindex.
  - apply compose_respects; [| reflexivity].
    apply (classifier_char_roundtrip (uncurry f)).
Qed.

End ToposPower.

Arguments PowF {C H}.
