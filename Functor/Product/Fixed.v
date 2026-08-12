Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.Internal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** The fixed-factor product functor H × − and Mac Lane's induced
    transformation "f × id". *)

(* nLab: https://ncatlab.org/nlab/show/natural+transformation
   nLab: https://ncatlab.org/nlab/show/product

   For a fixed object H of a cartesian category C, the assignment
   G ↦ H × G is a functor C ⟶ C: on a morphism g : G ~> G' it acts by
   [second g] : H × G ~> H × G', the identity on the fixed left factor and
   g on the moving right factor.  For a morphism f : H ~> K of fixed
   factors, the family whose component at G is [first f] : H × G ~> K × G
   is natural in G, the naturality square being exactly the interchange
   of [first] and [second].

   A word on the spelling of that component.  Mac Lane writes it
   "f × id".  This tree has no morphism-level × notation; the product of
   two morphisms is [split] (Structure/Cartesian.v:178), which is
   definitionally the action of the product bifunctor,
   [bimap[×(C)] f g] (Functor/Product/Internal.v:37).  So the literal
   in-tree reading of "f × id" is [split f id], and [first f] is that
   only up to ≈ — the identity survives inside the fork until [id_left]
   removes it, which is what [fixed_product_transform_bimap] below
   records.  The components below are [first f] because that is what
   issue #240's "Work to be done" prescribes verbatim ("components
   `first f` and naturality by `first_second`"); [alt_transform] carries
   the [split f id] spelling beside it, and [alt_transform_agrees]
   proves the two equal up to ≈.

   Provenance.  This is the exercise catalogued in this library's issue
   tracker as `maclane:I.4:ex2`, located there at Mac Lane, "Categories
   for the Working Mathematician", 2nd ed. (GTM 5), §I.4, printed p. 18,
   exercise 2, and reported there as posing the case C = Grp.  Both the
   location and the wording of the exercise are taken from that catalogue
   entry; the printed text was NOT consulted while writing this file, and
   nothing here is offered as a quotation from it.  What is machine-
   checked below is the mathematical content, in the generality of an
   arbitrary cartesian category, together with the instantiation at Grp
   that the exercise asks for. *)

(* What is reused, and what is new

   Nearly all the mathematical content of the exercise was already proven
   in this library, as equations about the cartesian combinators.  This
   file supplies the packaging.  The ledger:

   REUSED (nothing below re-derives these):
     - [second_id]     (Structure/Cartesian.v:340)  — the functor's
                        identity law, verbatim.
     - [second_comp]   (Structure/Cartesian.v:346)  — the functor's
                        composition law, verbatim.
     - [first_second]  (Structure/Cartesian.v:386)  — the naturality
                        square, verbatim.  [Transform] carries both
                        orientations as fields
                        (Theory/Natural/Transformation.v:117 and :121),
                        so the two obligations come out as
                        naturality := symmetry (first_second f g) and
                        naturality_sym := first_second f g, in that
                        order.
     - [first_id]      (Structure/Cartesian.v:326)  and
       [first_comp]    (Structure/Cartesian.v:332)  — the functor laws of
                        the mirror [fixed_product_functor_right], and
                        (together with [second_id]) the identity and
                        composition laws of the assignment f ↦ (f × −)
                        into [C, C].
     - [exl_first]     (Structure/Cartesian.v:354)  and [exl_fork]
                        (Structure/Cartesian.v:211) — the two cartesian
                        equations behind [fixed_product_transform_faithful],
                        used there alongside [comp_assoc] and [id_right].
     - [InternalProductFunctor] (Functor/Product/Internal.v:34) — the
                        product bifunctor, compared to this file's
                        functor by [fixed_product_bimap] and to its
                        transformation by [fixed_product_transform_bimap].
     - [Grp_Cartesian] (Instance/Grp.v:677) — binary direct products in
                        Grp.  These were already delivered by the Grp
                        work, so this file does NOT construct them; it
                        was checked before writing that Instance/Grp.v:677
                        is the only definition of that name in the tree
                        (the one other occurrence, Instance/Grp.v:76, is a
                        prose mention in that file's header) and that it
                        is an `#[export] Program Instance`, hence found
                        here by inference.
     - [Z2], [Z2_nontrivial], [Grp_injectivity_is_monic], [Grp_Zero]
                        (Instance/Grp.v) and [sections_are_monic]
                        (Theory/Morphisms.v:179) — the ingredients of the
                        non-vacuity witnesses.

   NEW here: the two packagings the exercise asks for
   ([fixed_product_functor], [fixed_product_transform]); the mirror
   functor − × K ([fixed_product_functor_right]); the [split f id]
   spelling of the same transformation and its agreement with the one
   above ([alt_transform], [alt_transform_agrees]); the currying
   ([fixed_product_curried]); the terminal-free [Cartesian_Binoidal] and
   the comparison against the binoidal composite the tree already
   reaches ([Section BinoidalComparison], including
   [alt_is_inj_left]/[alt_is_inj_right]); the non-degeneracy results
   ([fixed_product_transform_faithful],
   [fixed_product_transform_reflects_id]); and the Grp instantiation
   with its witnesses ([Grp_Z2_zero_not_iso],
   [Grp_fixed_product_transform_not_id],
   [Grp_fixed_product_component_moves],
   [Grp_fixed_product_component_not_monic]). *)

(* On [inj_left] / [inj_right] (Structure/Binoidal.v:49/53)

   These are the one-variable tensoring functors in the binoidal
   vocabulary, and they are the right abstraction for this exercise.
   They are FIELDS of the class [Binoidal], so using them needs a
   [Binoidal] structure in hand — and the tree already reaches one for
   cartesian categories by a two-step composite:

     [Cartesian_Monoidal] (Structure/Monoidal/Cartesian.v:49) makes a
     cartesian category THAT ALSO HAS A TERMINAL OBJECT monoidal, with
     tensor := [InternalProductFunctor] (via [CC_Monoidal],
     Structure/Monoidal/Internal/Product.v:54); and [Monoidal_Binoidal]
     (Structure/Premonoidal/Monoidal.v:124) makes any monoidal category
     binoidal.

   So this file does NOT claim [inj_right] was unavailable, and it does
   not claim to improve on it as a spelling of "f × id".  On that point
   the existing composite is the better match, and the difference runs
   the opposite way to what one might guess.  Since the product of two
   morphisms in this tree is [split] = [bimap[×(C)]] (see the header
   above), and the composite's tensor IS [InternalProductFunctor], the
   composite's morphism maps are the product of morphisms ON THE NOSE:

     fmap[@inj_left  C Cartesian_Monoidal_Binoidal G] f = split f id[G]
     fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g = split id[H] g

   both by [eq_refl].  It is this file's [first f] and [second g] that
   match [split] only up to ≈ — precisely the content of
   [fixed_product_bimap] and [fixed_product_transform_bimap] below.

   [Section BinoidalComparison] states the comparison in that direction:
   [fixed_product_inj_right_obj] shows the object maps of the composite
   and of [fixed_product_functor] are equal by [reflexivity];
   [fixed_product_inj_right_fmap] shows the morphism maps agree up to ≈
   but not on the nose — the composite acts by
   [split id g] = (id ∘ exl) △ (g ∘ exr) whereas [second g] is
   exl △ (g ∘ exr); and [alt_is_inj_left] exhibits, by [reflexivity],
   that the component of [alt_transform] — the [split f id] spelling —
   IS the composite's action on f.  The mirror pair
   [fixed_product_inj_left_obj]/[fixed_product_inj_left_fmap] does the
   same for [inj_left].

   What the existing composite genuinely does not give, and the sole
   reason [Cartesian_Binoidal] is defined below, is the hypothesis
   count.  The composite requires a [Terminal] object to supply the
   monoidal unit, and this library's [Cartesian] class carries no
   terminal object (its fields are product_obj, fork, exl, exr,
   fork_respects, ump_products); the exercise needs none.
   [Cartesian_Binoidal] drops that hypothesis by assembling the
   [Binoidal] structure out of the two functors defined here.  Its two
   corollaries then read those functors back out — see the note at
   [Cartesian_Binoidal_inj_right] for what that does and does not
   establish. *)

(* A note on layering.  This file ends in a Grp section and therefore
   imports Category.Instance.Grp, which is heavier than a Functor/ file
   usually needs.  The exercise is stated for groups and issue #240 asks
   for the instantiation alongside the general result, so the import is
   deliberate — but it is a genuinely new dependency, and the precedent
   for it is thinner than a bare appeal to "Functor/ files already
   import instances" would suggest.  Those precedents (Functor/Hom.v:8-9
   imports Instance/Fun.v and Instance/Sets.v; Functor/Diagonal.v:7,52,76
   imports Instance/Fun.v, Instance/One.v and Instance/Two/Discrete.v)
   are all foundational category instances that much of the tree already
   pulls in.  Instance/Grp.v is 1166 lines, and this is the only file in
   the tree that requires it. *)

Section FixedProduct.

Context {C : Category}.
Context `{CC : @Cartesian C}.

(** ** The functor H × − *)

(* Object map G ↦ H × G, morphism map g ↦ [second g].  The two functor
   laws are [second_id] and [second_comp] with no further argument. *)
Program Definition fixed_product_functor (H : C) : C ⟶ C := {|
  fobj := fun G => H × G;
  fmap := fun _ _ g => second g
|}.
Next Obligation. apply second_id. Qed.
Next Obligation. apply second_comp. Qed.

(* The mirror: fixed factor on the RIGHT, G ↦ G × K, acting by [first].
   It is not part of the exercise; it is here because the [Binoidal]
   structure below needs both one-variable tensorings. *)
Program Definition fixed_product_functor_right (K : C) : C ⟶ C := {|
  fobj := fun G => G × K;
  fmap := fun _ _ g => first g
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(* Both actions are the advertised ones, definitionally.

   On the use of [=] rather than [≈] between morphisms here and in the
   other on-the-nose statements below ([fixed_product_first],
   [Cartesian_Binoidal_inj_right]/[_inj_left], the [_obj] comparisons,
   [alt_is_inj_left]/[alt_is_inj_right]): the whole point of those
   statements is that the two sides are the very same term, which [≈]
   would not say.  The convention is the tree's, recorded at
   [bimap_fmap] (Functor/Bifunctor.v:45, comment at :42-44).  Every
   statement in this file that carries mathematical content — the
   naturality squares, the [bimap] comparisons, the faithfulness
   results, the Grp witnesses — uses [≈]. *)
Corollary fixed_product_fmap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g = second g.
Proof. reflexivity. Qed.

Corollary fixed_product_fmap_right {K x y : C} (g : x ~> y) :
  fmap[fixed_product_functor_right K] g = first g.
Proof. reflexivity. Qed.

(** ** The induced transformation H × − ⟹ K × − *)

(* Components [first f]; naturality is [first_second], whose symmetry
   discharges [naturality] and whose direct form discharges
   [naturality_sym] (that field order is Theory/Natural/Transformation.v
   :117/:121 — the obligations come out in that order, so obligation 1 is
   the symmetric one). *)
Program Definition fixed_product_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun _ => first f
|}.
Next Obligation. symmetry; apply first_second. Qed.
Next Obligation. apply first_second. Qed.

Corollary fixed_product_first {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G = first f.
Proof. reflexivity. Qed.

(** ** Agreement with the product bifunctor *)

(* [InternalProductFunctor] sends (f, g) to (f ∘ exl) △ (g ∘ exr).  Both
   actions above are that bifunctor with one argument held at an
   identity — up to ≈, not up to =, since the identity survives inside
   the fork (as `id ∘ exl` against [second], as `id ∘ exr` against
   [first]) until [id_left] removes it. *)
Theorem fixed_product_bimap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g ≈ bimap[×(C)] (id[H]) g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Theorem fixed_product_transform_bimap {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G ≈ bimap[×(C)] f (id[G]).
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(** ** The same transformation with its component spelled [split f id] *)

(* The literal in-tree reading of Mac Lane's "f × id" (see the header):
   [split f id], which is [bimap[×(C)] f id] definitionally.  Both
   naturality obligations fall to [unfork] with nothing else.  This is
   here so that the comparison against the binoidal composite the tree
   already reaches is a checkable fact rather than a remark — see
   [alt_is_inj_left] in [Section BinoidalComparison]. *)
Program Definition alt_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun G => split f (id[G])
|}.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.

(* The two spellings agree up to ≈, and not more than that: [first f] is
   (f ∘ exl) △ exr while [split f id] is (f ∘ exl) △ (id ∘ exr), and no
   conversion removes that [id ∘ −] — it takes [id_left]. *)
Theorem alt_transform_agrees {H K : C} (f : H ~> K) :
  alt_transform f ≈ fixed_product_transform f.
Proof.
  intro G; simpl.
  symmetry.
  apply (fixed_product_transform_bimap f G).
Qed.

(** ** A terminal-free binoidal structure on any cartesian category *)

(* Assembled from the two functors above.  Kept a [Definition] rather
   than an [Instance], following [Cartesian_Monoidal]
   (Structure/Monoidal/Cartesian.v:49, whose header gives the reason), so
   that it cannot silently capture [Binoidal] resolution elsewhere. *)
Definition Cartesian_Binoidal : @Binoidal C :=
  @Build_Binoidal C
    (fun x y => x × y)
    (fun K => ToAFunctor (fixed_product_functor_right K))
    (fun H => ToAFunctor (fixed_product_functor H)).

(* Reading the two functors back out of the structure just built.  Note
   what this is and is not.  [inj_right x'] is DEFINED as
   [FromAFunctor (right_functor x')] (Structure/Binoidal.v:53), and
   [Cartesian_Binoidal] supplied [right_functor] as
   [ToAFunctor (fixed_product_functor H)]; so these two corollaries are
   instances of [FromAFunctor_ToAFunctor] (Theory/Functor.v:419), which
   holds of every functor whatsoever.  They confirm that the packaging
   round-trips — nothing about products, and nothing specific to this
   exercise, is being established here. *)
Corollary Cartesian_Binoidal_inj_right (H : C) :
  @inj_right C Cartesian_Binoidal H = fixed_product_functor H.
Proof. reflexivity. Qed.

Corollary Cartesian_Binoidal_inj_left (K : C) :
  @inj_left C Cartesian_Binoidal K = fixed_product_functor_right K.
Proof. reflexivity. Qed.

(** ** Non-degeneracy: distinct f give distinct transformations *)

(* The assignment f ↦ (f × −) is injective on hom-setoids.  The proof
   needs no terminal object: probe the component at G := H with the
   diagonal id △ id, which [exl_fork] splits.  So the transformation
   below can never be accidentally trivial — it remembers f exactly. *)
Theorem fixed_product_transform_faithful {H K : C} (f g : H ~> K) :
  fixed_product_transform f ≈ fixed_product_transform g → f ≈ g.
Proof.
  intro Heq.
  assert (Hprobe : ∀ h : H ~> K, h ≈ (exl ∘ first (z:=H) h) ∘ (id △ id)).
  { intro h.
    rewrite exl_first.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    now rewrite id_right. }
  rewrite (Hprobe f), (Hprobe g).
  now rewrite (Heq H).
Qed.

(* Hence the induced transformation is the identity transformation only
   when f itself is an identity: no unlucky choice of f can produce a
   degenerate witness. *)
Corollary fixed_product_transform_reflects_id {H : C} (f : H ~> H) :
  fixed_product_transform f ≈ nat_id → f ≈ id.
Proof.
  intro Heq.
  apply fixed_product_transform_faithful.
  intro G.
  rewrite (Heq G).
  simpl.
  now rewrite first_id, second_id.
Qed.

(** ** Functoriality in the fixed factor *)

Theorem fixed_product_transform_id {H : C} :
  fixed_product_transform (id[H]) ≈ nat_id.
Proof.
  intro G; simpl.
  now rewrite first_id, second_id.
Qed.

Theorem fixed_product_transform_comp {H K L : C} (f : K ~> L) (g : H ~> K) :
  fixed_product_transform (f ∘ g)
    ≈ nat_compose (fixed_product_transform f) (fixed_product_transform g).
Proof.
  intro G; simpl.
  apply first_comp.
Qed.

(* Packaging both: H ↦ (H × −) and f ↦ (f × −) form a functor into the
   functor category — the product bifunctor curried in its first
   argument.  It agrees pointwise up to ≈ with currying
   [InternalProductFunctor] in both halves: on objects (that is, on each
   functor's action on morphisms) by [fixed_product_bimap], and on
   morphisms (that is, on each transformation's components) by
   [fixed_product_transform_bimap].  It is not claimed equal to that
   currying on the nose. *)
Program Definition fixed_product_curried : C ⟶ [C, C] := {|
  fobj := fixed_product_functor;
  fmap := fun _ _ f => fixed_product_transform f
|}.
Next Obligation.
  intros f g Hfg G; simpl.
  now rewrite Hfg.
Qed.
Next Obligation. apply fixed_product_transform_id. Qed.
Next Obligation. apply fixed_product_transform_comp. Qed.

End FixedProduct.

(** ** Comparison with the binoidal structure the tree already reaches *)

(* With a terminal object the tree already composes its way to a
   [Binoidal] structure on a cartesian category, as described in the
   header.  These statements pin down exactly how that composite relates
   to this file's functors: same objects on the nose, same morphism
   action only up to ≈ — and, in [alt_is_inj_left]/[alt_is_inj_right],
   the composite's morphism action IS the product of morphisms, [split],
   on the nose. *)

Section BinoidalComparison.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

Definition Cartesian_Monoidal_Binoidal : @Binoidal C :=
  @Monoidal_Binoidal C (@Cartesian_Monoidal C CC T).

Corollary fixed_product_inj_right_obj (H G : C) :
  (@inj_right C Cartesian_Monoidal_Binoidal H) G = fixed_product_functor H G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_right_fmap (H : C) {x y : C} (g : x ~> y) :
  fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g
    ≈ fmap[fixed_product_functor H] g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Corollary fixed_product_inj_left_obj (K G : C) :
  (@inj_left C Cartesian_Monoidal_Binoidal K) G
    = fixed_product_functor_right K G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_left_fmap (K : C) {x y : C} (g : x ~> y) :
  fmap[@inj_left C Cartesian_Monoidal_Binoidal K] g
    ≈ fmap[fixed_product_functor_right K] g.
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(* The direction the header insists on: on the "f × id" spelling the
   pre-existing composite is exact, not approximate.  The component of
   [alt_transform] at G IS the composite's action on f, by
   [reflexivity]; [alt_transform_agrees] then relates that to this
   file's [first]-valued transformation, up to ≈. *)
Corollary alt_is_inj_left {H K : C} (f : H ~> K) (G : C) :
  transform[alt_transform f] G
    = fmap[@inj_left C Cartesian_Monoidal_Binoidal G] f.
Proof. reflexivity. Qed.

Corollary alt_is_inj_right (H : C) {x y : C} (g : x ~> y) :
  split (id[H]) g = fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g.
Proof. reflexivity. Qed.

End BinoidalComparison.

(** ** The exercise's own setting: C = Grp *)

(* [Grp_Cartesian] (Instance/Grp.v:677) already supplies the binary
   direct products, so the instantiation is a specialization and nothing
   more. *)

Definition Grp_fixed_product (H : Grp) : Grp ⟶ Grp :=
  fixed_product_functor H.

Definition Grp_fixed_product_transform {H K : Grp} (f : H ~{Grp}~> K) :
  Grp_fixed_product H ⟹ Grp_fixed_product K :=
  fixed_product_transform f.

(* The object map is the direct product G ↦ H × G on the nose. *)
Corollary Grp_fixed_product_obj (H G : Grp) :
  Grp_fixed_product H G = Grp_product H G.
Proof. reflexivity. Qed.

(** ** Non-vacuity *)

(* A degenerate witness would show nothing, so the witness is chosen to
   dodge every degeneracy at once.  Take H = K = Z/2 and for f the zero
   homomorphism through the zero object [Grp_Zero], which sends both
   elements of Z/2 to the unit `false`.  Then:

     - f has no left inverse at all ([Grp_Z2_zero_no_left_inverse],
       through [Grp_Z2_zero_not_section] and [Grp_Z2_zero_not_monic]),
       hence is not an isomorphism ([Grp_Z2_zero_not_iso], which is that
       lemma applied to the inverse's left-inverse law);
     - the induced transformation is not the identity transformation
       ([Grp_fixed_product_transform_not_id]).  H = K is what makes that
       statement available at all: [nat_id] inhabits F ⟹ F, so for
       H ≠ K a comparison of the induced transformation with [nat_id]
       does not typecheck (the two sides live in
       Grp_fixed_product H ⟹ Grp_fixed_product K and
       Grp_fixed_product H ⟹ Grp_fixed_product H, which do not unify).
       It is therefore not a claim that would hold for type reasons; it
       is not a claim.  With H = K the two functors are the same term
       and the comparison against [nat_id] is a genuine one;
     - its component at Z/2 genuinely moves an element
       ([Grp_fixed_product_component_moves]) and is not monic
       ([Grp_fixed_product_component_not_monic]), so the transformation
       is not invertible either. *)

Definition Grp_Z2_zero : Z2 ~{Grp}~> Z2 := @zero_mor Grp Grp_Zero Z2 Z2.

(* The zero homomorphism collapses Z/2 onto its unit. *)
Lemma Grp_Z2_zero_const (b : carrier Z2) : grp_map Grp_Z2_zero b ≈ false.
Proof. reflexivity. Qed.

Lemma Grp_Z2_zero_not_injective :
  (∀ a b : carrier Z2, grp_map Grp_Z2_zero a ≈ grp_map Grp_Z2_zero b → a ≈ b)
    → False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  reflexivity.
Qed.

Theorem Grp_Z2_zero_not_monic : Monic Grp_Z2_zero → False.
Proof.
  intro Hm.
  apply Grp_Z2_zero_not_injective.
  destruct (Grp_injectivity_is_monic Grp_Z2_zero) as [_ Hback].
  exact (Hback Hm).
Qed.

(* Not split monic, by [sections_are_monic]. *)
Theorem Grp_Z2_zero_not_section : Section Grp_Z2_zero → False.
Proof.
  intro Hs.
  apply Grp_Z2_zero_not_monic.
  now apply sections_are_monic.
Qed.

(* Hence no left inverse. *)
Theorem Grp_Z2_zero_no_left_inverse (g : Z2 ~{Grp}~> Z2) :
  g ∘ Grp_Z2_zero ≈ id → False.
Proof.
  intro Hg.
  apply Grp_Z2_zero_not_section.
  now refine {| section := g |}.
Qed.

(* And hence not an isomorphism: a two-sided inverse is in particular a
   left inverse.  Stated at the [IsIsomorphism] level (the predicate form
   on a single morphism, Theory/Isomorphism.v:133) so that the prose
   above has a theorem behind it rather than an inference left to the
   reader. *)
Theorem Grp_Z2_zero_not_iso : IsIsomorphism Grp_Z2_zero → False.
Proof.
  intro Hi.
  exact (Grp_Z2_zero_no_left_inverse
           (@two_sided_inverse Grp Z2 Z2 Grp_Z2_zero Hi)
           (@is_left_inverse Grp Z2 Z2 Grp_Z2_zero Hi)).
Qed.

(* The component at Z/2 sends (true, true) to (false, true): it moves the
   fixed factor and leaves the moving factor alone. *)
Example Grp_fixed_product_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (false, true).
Proof. split; reflexivity. Qed.

(* And (true, true) is not (false, true). *)
Lemma Grp_Z2_pair_distinct :
  (@equiv _ (grp_setoid (Grp_product Z2 Z2)) (true, true) (false, true))
    → False.
Proof. intros [Hl _]; discriminate. Qed.

(* Put together: the component really does move (true, true). *)
Theorem Grp_fixed_product_component_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (true, true) → False.
Proof.
  intro Hfix.
  apply Grp_Z2_pair_distinct.
  rewrite <- Hfix.
  exact Grp_fixed_product_moves.
Qed.

Theorem Grp_fixed_product_transform_not_id :
  Grp_fixed_product_transform Grp_Z2_zero ≈ nat_id → False.
Proof.
  intro Heq.
  apply Z2_nontrivial.
  symmetry.
  exact (fixed_product_transform_reflects_id Grp_Z2_zero Heq true).
Qed.

(* The component identifies (true, true) with (false, true), so it is not
   injective, hence not monic, hence not invertible. *)
Theorem Grp_fixed_product_component_not_monic :
  Monic (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) → False.
Proof.
  intro Hm.
  apply Grp_Z2_pair_distinct.
  destruct (Grp_injectivity_is_monic
              (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2))
    as [_ Hback].
  apply (Hback Hm).
  split; reflexivity.
Qed.
