Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(* The free abelian group on one generator separates Ab

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/free+abelian+group

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 127 (PDF p. 136), Definition 4, gives two examples of a
   generating set: the one-point set for sets, and THE INTEGERS for
   abelian groups.  The second is this file's subject.  Awodey, "Category
   Theory" (1st ed., Carnegie Mellon pre-print, September 2005), §7.2,
   printed p. 154 (PDF p. 163), and Riehl, "Category Theory in Context",
   2nd ed., Definition 4.7.7, printed p. 177 (PDF p. 197), are the
   single-object and family forms of the same definition.  The [Sets]
   witness is Instance/Sets/Generator.v and the [Grp] one
   Instance/Grp/Generator.v.

   WHAT IS PROVED, AND WHAT MAC LANE SAID.  Mac Lane's "the integers
   generate Ab" is, up to the standard isomorphism ℤ ≅ F_ab(1), the
   statement proved here: the free abelian group on a ONE-ELEMENT
   generating setoid separates [Ab].  The isomorphism itself is NOT in
   this tree and is not proved here, so the sentence "ℤ separates Ab" is
   not a theorem of this file.  The in-tree integers are
   [ab_int : AbObject] at Instance/Ab/Free.v (one of five names for
   [ring_ab Int_Ring]; Instance/Grp/Generator.v's header lists them with
   the measuring command), and that file's own measured negative
   records the related conversion fact — [FreeAbObject (Ab_Forget ab_int)]
   is not [ab_int] — while explicitly making no claim about isomorphism
   in either direction.  Supplying [FreeAbObject unit_setoid_object ≅
   ab_int] is left undone, and the reason is NOT a missing ℤ-action: the
   tree has [zsmul] (Instance/Ab/Monoidal.v), the ℤ-action on an
   arbitrary abelian group, with its additivity in the scalar
   [zsmul_add] and its compatibility with homomorphisms
   [zsmul_hom].  What is open is the isomorphism itself -- the
   map n ↦ n·(fa_gen ttt) out of [ab_int], the fold out of
   [FreeAbObject] sending the generator to 1, and the two inverse laws by
   induction on [FATerm] -- which is outside this issue's definition of
   done.  (An earlier revision of this paragraph said the tree had only
   the ℕ-scaled [nat_smul], which an audit refuted by reading
   the same file.)  So the honest reading of this file is: Mac Lane's
   example, with his ℤ replaced by the free-on-one-generator object that
   represents the same functor.

   THE PROOF IS ONE [exact], AND THE REASON IS A CONVERSION.  Compare
   Instance/Grp/Generator.v, which needs two [rewrite]s.  The difference
   is the strength at which the two donors state agreement on generators.
   Instance/Ab/Free.v's [free_ab_extend_generators] is an [Example]
   at Leibniz [=] — [cmon_map (free_ab_extend h) (fa_gen x) = h x
   := eq_refl] — because [free_ab_extend] is the fold [fa_eval]
   over the inductive [FATerm] and the generator clause IS the
   equation.  Instance/Grp/Free.v's [free_grp_extend_generators] is
   only at ≈, its extension being [fmap] of a functor whose value on a
   one-letter word comes from a [Qed]-opaque lemma.  Here, therefore, the
   hypothesis instantiated at [free_ab_extend (ab_point x)] and the
   generator [fa_gen ttt] IS the goal after conversion, with no transport
   by properness, and the [exact] closes it.

   NOT DELIVERED.  No claim that this object is the smallest separator of
   [Ab], nor that [Ab] has no other; no generating families of more than
   one object; no joint-faithfulness reading (Structure/Generator.v's
   [JointlyFaithful]), which is the theory half of #447; and no
   isomorphism with [ab_int], as above.  Nothing is said about [CMon],
   whose free objects Instance/Ab/Free.v does not build. *)

(** ** The element of an abelian group as a map out of the singleton *)

(* The constant map at [x], read into [Sets] through [Ab_Forget].  Built
   by [refine] for the same reason as Instance/Grp/Generator.v's
   [grp_point]: under the universe annotation the [Program] form does not
   register the constant before the obligation is met.  It must stay
   TRANSPARENT: closed with [Qed] the separation proof is refused with
   "The term "Hk (free_ab_extend (ab_point x)) (fa_gen ttt)" has type
   "(f ∘ free_ab_extend (ab_point x)) (fa_gen ttt) ≈ …" while it is
   expected to have type "f x ≈ g x"", a CONVERSION refusal. *)
Definition ab_point@{o so+} {A : Ab@{so o}} (x : carrier (cmon_setoid A)) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Ab_Forget A.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation *)

Lemma Ab_free_one_separates@{o so+} :
  @IsSeparator Ab@{so o} (FreeAbObject unit_setoid_object@{o o}).
Proof.
  intros A B f g Hk x.
  exact (Hk (@free_ab_extend unit_setoid_object@{o o} A (ab_point x))
           (@fa_gen unit_setoid_object@{o o} ttt)).
Qed.

(* Mac Lane's second example as a one-object generating family. *)
Definition Ab_Generator@{o so+} : Generator Ab@{so o} :=
  @Generator_of_separator Ab@{so o}
    (FreeAbObject unit_setoid_object@{o o}) Ab_free_one_separates.
