Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(** * Finite products in the category of internal monoids *)

(* Mac Lane, Categories for the Working Mathematician, 2nd ed., Section VII.3,
   Exercise 1.

   For a monoidal category (B, ⨂, I) with finite products, the category
   Mon(B) of internal monoids and monoid homomorphisms again has finite
   products, carried by the product of the underlying objects: the forgetful
   functor Mon(B) ⟶ B sends them to B's own products ON THE NOSE.

   The multiplication put on x × y is

     μ := (μ_X ∘ (exl ⨂ exl)) △ (μ_Y ∘ (exr ⨂ exr))
                                    : (x × y) ⨂ (x × y) ~> x × y

   and the unit is η := η_X △ η_Y : I ~> x × y.  Note that TWO different
   binary operations on objects occur here and must not be confused: ⨂ is the
   monoidal tensor, in which the monoid laws are stated, and × is the
   categorical product, which is what is being built.  No compatibility
   between the two is assumed, and none is needed.

   The terminal monoid is the terminal object 1 of B, with μ and η the unique
   maps into it; every morphism into 1 is then automatically a homomorphism,
   by [one_unique].

   HYPOTHESES, MEASURED RATHER THAN GUESSED.  The binary half needs
   [Cartesian C] ALONE — no [Terminal C], and no interaction between × and ⨂.
   This mirrors [Class Cartesian] itself, which "axiomatizes the binary
   product; the nullary product (the terminal object 1) is supplied separately
   by [Terminal]" (Structure/Cartesian.v:20-22).  The nullary half needs
   [Terminal C] alone and does not mention [Cartesian] at all.  Both halves
   are stated over an ARBITRARY monoidal structure M on C; the cartesian
   monoidal structure [CC_Monoidal] appears only in the final comparison
   section.

   WHAT IS PROVED HERE, IN ORDER

   (1) [Monoid_Product] — the product monoid, over an arbitrary monoidal base.
   (2) [Terminal_Monoid] — the monoid carried by the terminal object.
   (3) [mon_exl_hom], [mon_exr_hom], [mon_fork_hom], [mon_one_hom] — the
       projections, the pairing and the unique map are monoid homomorphisms.
   (4) [Mon_Cartesian] : @Cartesian (Mon C) and [Mon_Terminal] :
       @Terminal (Mon C) — the deliverables.
   (5) [Monoid_of_MonoidObject] / [MonoidObject_of_Monoid] — the passage
       between the two in-tree monoid-object classes, with both round trips,
       and the negative [AbstractBaseProbe] showing it cannot bridge an
       abstract M to [CC_Monoidal].
   (6) [Product_Monoid_as_Monoid] and the comparison with [Product_Monoid]
       (Structure/Monoid.v:179) at the cartesian monoidal base, with the
       strict form of the multiplication comparison refuted and pinned.
   (7) [Mon_Sets_Cartesian] and [Mon_Sets_Terminal] — the concrete
       instantiation at [Mon Sets], with two further negatives showing that
       [Product_Monoid] would NOT have reached it.

   THE TWO CLASSES NAMED "Monoid", AND WHY THE PASSAGE IS NOT THE ROUTE TAKEN

   This tree carries two definitions of an internal monoid:

     Theory/Algebra/Monoid.v   Class Monoid (X : C)
                               fields mu, eta, mu_assoc,
                               mu_unit_left, mu_unit_right
     Structure/Monoid.v:124    Class MonoidObject (mon : C)
                               fields mempty, mappend, mempty_left,
                               mempty_right, mappend_assoc

   They have the same laws with renamed fields in a different order, and
   Structure/Monoid.v:173 additionally declares
   [Definition Monoid := @MonoidObject C CC_Monoidal] — a THIRD spelling,
   which is [MonoidObject] pinned to the cartesian tensor.  A display hazard
   follows, and it is narrower than an earlier draft of this header claimed:
   TWO of the three print alike, not three.  [Check @Monoid] and
   [Check @MonoidObject] both print [∀ C : Category, Monoidal → obj[C] →
   Type] and are indistinguishable by type display; but the [:173] alias
   prints [∀ C : Category, Cartesian → Terminal → obj[C] → Type], which is
   VISIBLY DIFFERENT, and [Check @Product_Monoid] even prints its ARGUMENT
   types qualified.  The claim "type display alone cannot tell the three
   apart" was FALSE and is withdrawn: a single [Check] separates the alias.
   What is true, and is the part that actually bites, is that
   [Product_Monoid] prints its CONCLUSION as [MonoidObject (x × y)] with the
   monoidal instance SUPPRESSED — so the conclusion does not reveal which
   tensor it is at.

   [Mon] (Theory/Algebra/Monoid/Hom.v) is built on the FIRST of these.

   Three routes to this issue's deliverable were available.

     (a) Build the passage [MonoidObject x → Monoid x] and route
         [Product_Monoid] through it.
     (b) Prove the product monoid structure directly on the mu/eta class,
         over an arbitrary monoidal base.
     (c) Re-found [Mon] on [MonoidObject].

   Route (b) is taken.  The reason is not taste: [Product_Monoid] concludes
   [@MonoidObject C CC_Monoidal (x × y)], so its tensor IS the categorical
   product.  Routing through it therefore requires the monoidal structure of
   [Mon] to be [CC_Monoidal], which restricts the theorem from "for every
   monoidal B with finite products" to "for B monoidal via its own products" —
   a restriction relative to both Mac Lane's statement and [Mon]'s own
   signature, which quantifies over an arbitrary [M : @Monoidal C].  The
   passage of route (a) does not repair this: it relates the two classes only
   AT A FIXED monoidal base — it is field renaming and cannot change the
   tensor — and the [Fail Check] in [AbstractBaseProbe] below MEASURES that
   the obvious attempt does not typecheck for a variable M.  Read that as a
   measurement at the current definitions; NO impossibility is proved and none
   is claimed.  The restriction is not hypothetical either, and
   section (7) makes that concrete AT THE TREE'S OWN [Mon Sets]: that category
   is [@Mon Sets Sets_Product_Monoidal] (Instance/Roster.v:390), whose base is
   [Sets]'s hand-built monoidal structure (Instance/Sets.v:288) and NOT
   [@CC_Monoidal Sets _ _] — the two are pinned as not the same term — so
   [Product_Monoid] does not typecheck as a monoid structure there, which is
   also pinned.  Route (c) would edit a file this issue has
   no licence to touch and would break every existing consumer of [Mon].

   The passage of route (a) is nevertheless BUILT here — it is what
   "reconcile the two definitions" asks for — and it is then used for what it
   can actually do: exhibit [Product_Monoid] as the [CC_Monoidal] special case
   of [Monoid_Product] (section 6).  That comparison is an [≈], not an
   [eq_refl], and the residue is diagnosed below.

   STRENGTHS, MEASURED STRICT-FIRST

   - Both round trips of the class passage close by [eq_refl] on the WHOLE
     record ([monoid_round], [monoid_object_round]): both classes are
     declared under [Set Primitive Projections] (Lib/Foundation.v:5), so
     record eta holds and rebuilding the five fields returns the original.
   - The forgetful functor's action on the product object and on the terminal
     object is [eq_refl] ([Mon_Forget_product], [Mon_Forget_terminal]), as are
     the underlying morphisms of the projections, the pairing and the unique
     map ([Mon_Forget_exl], [Mon_Forget_exr], [Mon_Forget_fork],
     [Mon_Forget_one]).  So the forgetful functor's agreement with C's own
     finite products is definitional on DATA — Leibniz equalities, not
     isomorphisms and not [≈].  CREATION in the technical sense of
     Structure/Limit/Creation.v is NOT proved and is not claimed; neither is
     preservation stated at cone level.
   - [Monoid_Product]'s unit agrees with [Product_Monoid]'s at [eq_refl]
     ([Monoid_Product_eta_is_Product_Monoid]); its multiplication agrees only
     at [≈] ([Monoid_Product_mu_is_Product_Monoid]), and the [eq_refl] form is
     REFUTED and pinned ([Fail Example Monoid_Product_mu_not_strict]) against
     [Monoid_Product_mu_is_Product_Monoid] as its control — that [≈] form,
     not the unit Example, is what names [mu] and [mappend].
     DIAGNOSIS: the residue is three
     rewrites, none of which is a proof field or an eta gap — the underlying
     MORPHISMS genuinely differ as terms.  [Product_Monoid] writes the
     multiplication as [split μ_X μ_Y ∘ toggle], a fork composed with a
     morphism, where this file writes the fork of the two composites; one
     [fork_comp] distributes that pairing over [toggle], [fork_inv] reduces to
     the two components, and [exl_fork]/[exr_fork] read the two halves of
     [toggle] back.  All four ARE [Qed] corollaries of
     Structure/Cartesian.v, and the shipped proof also spends [comp_assoc], a
     [Category] law rather than a [Cartesian] corollary — so "three rewrites"
     undercounts, and [fork_inv] is [apply]d rather than rewritten.  An
     earlier draft added "so no unfolding converts one side to the other";
     that is a NON SEQUITUR and is withdrawn — opacity of the LEMMAS used in
     an [≈] proof says nothing about convertibility of the two MORPHISM
     terms.  The terms are non-convertible because one is a fork of
     composites and the other a composite of a fork, an identity holding by
     the product's universal property rather than by computation; it would
     remain non-convertible were [fork_comp] [Defined].
   - Engineering note, RETRACTED in part.  An earlier draft said the
     comparison proof must unfold [bimap] by name because [simpl] does not
     reduce [bimap exl exl] to [split exl exl].  The NECESSITY claim is
     false: [bimap exl exl ≈ split exl exl] closes by bare [reflexivity],
     and the comparison compiles unchanged with [bimap] removed from its
     [unfold] list.  What [simpl] leaves in the goal DISPLAY is untested and
     nothing is claimed about it.

   NEGATIVES.  Four, of two different KINDS kept lexically apart, each
   stripped and its failure kind read off the message.

   - [AbstractBaseProbe] — TYPING.  Stripping the [Fail] reports that
     [Product_Monoid X Y] has type [@MonoidObject C (@CC_Monoidal C _ _)
     (x × y)] where [@MonoidObject C M (x × y)] is wanted.  Control:
     [Product_Monoid_as_Monoid], the same application at M := [CC_Monoidal].
   - [Monoid_Product_mu_not_strict] — CONVERSION.  "cannot unify" between the
     two multiplications.  Control: [Monoid_Product_mu_is_Product_Monoid],
     the [≈] form, which names every constant occurring in the negative.
   - [Sets_Product_Monoidal_is_CC_Monoidal] — CONVERSION.  "cannot unify
     "Sets_Product_Monoidal" and "CC_Monoidal"".  Controls:
     [Mon_Sets_Cartesian] and [Mon_Sets_Terminal], which name all four of
     [Sets_Product_Monoidal], [Sets_Cartesian], [Sets_Terminal] and [Sets].
   - The unnamed [Fail Check] in [SetsWitness] — TYPING, the [Sets] instance
     of the first negative.  Same controls.

   PROBE HYGIENE, recorded because the first version of the first negative was
   a FALSE PASS and only strip-and-read caught it.  Written INSIDE
   [Section MonProduct], where C and M are section VARIABLES rather than
   parameters, [@Monoid_of_MonoidObject C M (x × y) X] passes C into the
   [x] slot: the command failed with "The term "C" has type "Category" while
   it is expected to have type "obj[C]"" — an arity error at an argument
   elaborated before the nominal subject, which says nothing at all about the
   monoidal instance.  The probe is therefore placed AFTER [End MonProduct],
   with its own [Context], where the constant carries all its parameters.

   Rename-simulated over the thirteen constants the four negatives name:
   eleven ([Product_Monoid], [MonoidObject], [CC_Monoidal], [Monoidal], [mu],
   [mappend], [Sets], [Sets_Product_Monoidal], [Sets_Cartesian],
   [Sets_Terminal], [product_obj]) break at a positive command when renamed.
   The other two
   ([Monoid_Product], [Monoid_of_MonoidObject]) are defined in THIS file, so a
   consistent rename is not the threat model; both are consumed by positive
   commands here ([Mon_Cartesian], [monoid_round],
   [Product_Monoid_as_Monoid], [Monoid_Product_mu_is_Product_Monoid]), so
   removing either breaks the build rather than silencing a negative.

   AXIOMS.  All 40 constants of this file — 31 named plus 9 [Program]
   obligations, the latter invisible to a [.glob] sweep and queried by
   fully-qualified name — report "Closed under the global context".  The
   [Instance/Sets] witnesses of section (7) are included in that count and
   add nothing.

   UNIVERSES.  Measured in the constraint blocks AND read off the binders,
   which is the whole point here: several constants below have a block
   containing only BOUNDS while their binder already carries an
   IDENTIFICATION.  Reading either alone gets it wrong.

   - THE BINDER.  Every constant in this file THAT BINDS A [C] is over
     [C : Category@{u u0 u0}] — C's hom and proof universes are IDENTIFIED.
     (The qualifier matters: [Mon_Sets_Cartesian] and [Mon_Sets_Terminal]
     bind no [C] at all, being at a fixed base.)
     That is INHERITED, from THREE donors independently, and the attribution
     is probed rather than assumed: in a section declaring [Constraint uh <
     up] over [C : Category@{uo uh up}], each of [@Monoidal C], [@Cartesian C]
     and [@Terminal C] is rejected with "Cannot enforce up = uh", while
     [x ~> y] and [id[x]] are ACCEPTED at those very levels.  So no one of the
     three is "the" cause, nothing in this file adds to it, and it is not
     claimed unavoidable — all three are declared over an unannotated
     [Context {C : Category}], which is the minimization family this tree
     records elsewhere.
   - THE BLOCKS, part one.  [mon_prod_mu@{u u0}], [mon_prod_eta@{u u0}],
     [mon_prod_assoc_leg@{u u0}], [prod_fork_eta@{u u0}],
     [Terminal_Monoid@{u u0}], [mon_one_hom@{u u0}],
     [Monoid_of_MonoidObject@{u u0}] and [MonoidObject_of_Monoid@{u u0}] carry
     ONLY bounds of C's two levels by the [projections] levels of the setoid
     library.  No further identification, and no [Set] anywhere in the file.
   - THE BLOCKS, part two.  [Monoid_Product@{u u0 u1}], [mon_exl_hom],
     [mon_exr_hom], [mon_fork_hom] and the three comparison constants
     ([Product_Monoid_as_Monoid], [Monoid_Product_eta_is_Product_Monoid],
     [Monoid_Product_mu_is_Product_Monoid]) add [u0 < u1] and three
     [prod_rect] bounds.  TWO SEPARATE CAUSES, and an earlier draft of this
     header attributed both to the first: [fork_inv] (Structure/Cartesian.v)
     concludes a TYPE-valued conjunction which the associativity obligation
     destructs, and THAT accounts for the three [prod_rect] bounds ONLY.  The
     strict [u0 < u1] comes from setoid [rewrite] inside a [Program]
     obligation, isolated by rebuilding this file's own shape twice: a
     [Program Definition] whose obligations are discharged by [apply
     mu_assoc] and siblings elaborates at [@{u u0}], while the identical
     definition with [now rewrite mu_assoc] elaborates at [@{u u0 u1}] with
     [u0 < u1].  Which [Morphisms]/[CMorphisms] constant supplies the level is
     NOT identified here.  Either way it is a strict inequality, not an
     identification.  The six [Mon_Forget_*] Examples are [@{u u0 u1 u2}] with
     [u0 < u2], [u <= u1], [u0 <= u1] and three [prod_rect] bounds, and belong
     to neither list above; [mon_prod_mu_exl]/[_exr],
     [mon_prod_eta_exl]/[_exr], [monoid_round] and [monoid_object_round] are
     [@{u u0}] and belong to part one.
   - THE PACKAGING IS NOT FREE, and an earlier draft of this header wrongly
     said it was.  [Mon_Cartesian@{u u0 u1 u2}] concludes
     [Cartesian@{u2 u0}] and [Mon_Terminal@{u u0 u1 u2}] concludes
     [Terminal@{u2 u0}]: a NEW level [u2] carries the objects of [Mon C],
     bounded below by BOTH of C's levels ([u <= u2] and [u0 <= u2]).  The two
     bounds are MEASURED; the natural attribution — an object of [Mon C] is
     the sigma [{ x : C & Monoid x }], whose second component mentions C's
     homs — is an explanation and is not separately probed.  [u2] is
     identified with NEITHER of C's levels; a bound is not an identification,
     so a consumer loses nothing, but the level is real and is recorded.
   - The comparison section instantiates M := [CC_Monoidal], built from
     [InternalProductFunctor].  Measured, it inherits nothing beyond the
     above: the two comparison constants have the same block shape as
     [Monoid_Product], with no [Set] and no new identification.
   - At [Sets] the new level of the previous bullet costs nothing, and that is
     measured rather than assumed: [Mon_Sets_Cartesian@{u u0}] concludes
     [Cartesian@{u0 u}] — the objects of [Mon Sets] sit at [u0], the SAME
     level as [obj[Sets]], because [Sets@{u u0}]'s own [u < u0] already puts
     its objects above its homs, so the two bounds [u <= u2] and [u0 <= u2]
     are satisfied by [u2 := u0].  Still no [Set] and no identification; the
     extra entries in that block ([Basics.compose], [eq_ind], [ID]) are
     Instance/Sets.v's, not this file's.

   NOT DELIVERED, with reasons.

   - No [Cocartesian (Mon C)].  The coproduct of monoids is NOT carried by the
     coproduct of the underlying objects (it is a free product / tensor
     algebra), so nothing here dualises; Structure/Cocartesian.v's own header
     quotes Mac Lane 1950 on exactly this asymmetry.
   - No exponentials, hence no [Closed (Mon C)]; Structure/Monoid.v's
     [Hom_Monoid] puts a monoid on [y ^ x], which is a different statement and
     is not related here.
   - No infinite or indexed products: this matches [Cartesian], which is
     binary.
   - No monoidal structure on [Mon C], and therefore no claim that [Mon C] is
     cartesian MONOIDAL; that would need [CC_Monoidal] at [Mon C] and is not
     assembled.
   - [Mon_Sets_Cartesian] and [Mon_Sets_Terminal] are plain [Definition]s,
     NOT registered [Instance]s, and no other concrete category is
     instantiated ([CMon], [Grp], [Coq] and the rest are untouched).
     Instance/Roster.v is deliberately not required — its [Mon_Sets] is
     [@Mon Sets Sets_Product_Monoidal] by definition, which is what is written
     out here, and requiring it would pull in that file's closure.
   - The class passage is NOT claimed to be an equivalence of CATEGORIES: no
     category of [MonoidObject]s exists in tree, so there is nothing to
     compare [Mon] with, and only the object-level bijection is proved.
   - Nothing is proved about how [Monoid_Product] interacts with the group
     structure of Structure/Group.v; the group case is owned elsewhere. *)

Section MonProduct.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** ** The product monoid *)

Section Binary.

Context `{CA : @Cartesian C}.

(* Two morphisms into a product are recovered from their two components: the
   eta law for the product, in the form used repeatedly below. *)
Lemma prod_fork_eta {x y z : C} (f : z ~> x × y) :
  (exl ∘ f) △ (exr ∘ f) ≈ f.
Proof. rewrite fork_comp; now rewrite fork_exl_exr, id_left. Qed.

Section Data.

Context {x y : C} (X : Monoid x) (Y : Monoid y).

(* The componentwise multiplication on x × y: project both tensor factors to
   x, multiply there, and likewise on the y side. *)
Definition mon_prod_mu : (x × y) ⨂ (x × y) ~> x × y :=
  (mu[X] ∘ bimap exl exl) △ (mu[Y] ∘ bimap exr exr).

(* The componentwise unit. *)
Definition mon_prod_eta : I ~> x × y := eta[X] △ eta[Y].

Lemma mon_prod_mu_exl : exl ∘ mon_prod_mu ≈ mu[X] ∘ bimap exl exl.
Proof. unfold mon_prod_mu; apply exl_fork. Qed.

Lemma mon_prod_mu_exr : exr ∘ mon_prod_mu ≈ mu[Y] ∘ bimap exr exr.
Proof. unfold mon_prod_mu; apply exr_fork. Qed.

Lemma mon_prod_eta_exl : exl ∘ mon_prod_eta ≈ eta[X].
Proof. unfold mon_prod_eta; apply exl_fork. Qed.

Lemma mon_prod_eta_exr : exr ∘ mon_prod_eta ≈ eta[Y].
Proof. unfold mon_prod_eta; apply exr_fork. Qed.

(* Associativity of [mon_prod_mu], one component at a time.  The hypothesis
   [Hp] says exactly that p commutes with the two multiplications; both
   projections satisfy it, by [mon_prod_mu_exl] and [mon_prod_mu_exr].  The
   two sides are each normalised to a common form ending in
   [(p ⨂ p) ⨂ p]; the associator's naturality is what lets the two
   normalisations meet, and the target monoid's own [mu_assoc] closes it. *)
Lemma mon_prod_assoc_leg {z} (Z : Monoid z) (p : x × y ~> z)
      (Hp : p ∘ mon_prod_mu ≈ mu[Z] ∘ bimap p p) :
  p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
    ≈ p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu ∘ to tensor_assoc).
Proof.
  assert (HL : p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
                 ≈ mu[Z] ∘ bimap mu[Z] id ∘ bimap (bimap p p) p).
  { rewrite comp_assoc, Hp.
    rewrite <- comp_assoc, <- bimap_comp, Hp, id_right.
    rewrite <- comp_assoc, <- bimap_comp.
    now rewrite id_left. }
  assert (HR : p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                      ∘ to tensor_assoc)
                 ≈ mu[Z] ∘ bimap id mu[Z] ∘ to tensor_assoc
                     ∘ bimap (bimap p p) p).
  { rewrite !comp_assoc, Hp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (bimap p p)).
    rewrite <- bimap_comp, Hp, id_right.
    assert (Hb : p ⨂ (mu[Z] ∘ p ⨂ p) ≈ id[z] ⨂ mu[Z] ∘ p ⨂ (p ⨂ p))
      by (rewrite <- bimap_comp; now rewrite id_left).
    rewrite Hb, <- comp_assoc.
    now rewrite to_tensor_assoc_natural. }
  rewrite HL, HR.
  now rewrite mu_assoc.
Qed.

(* The product of two internal monoids.  Declared a plain [Program
   Definition] rather than an [Instance]: registering it would add a
   resolution rule for [Monoid (_ × _)], and [Mon] itself is indexed by this
   class, so leaving the database untouched is the conservative choice (the
   [Hom_Representable] precedent, Functor/Representable.v). *)
Program Definition Monoid_Product : Monoid (x × y) := {|
  mu  := mon_prod_mu;
  eta := mon_prod_eta
|}.
Next Obligation.
  (* associativity *)
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])).
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                               ∘ to tensor_assoc)).
  apply fork_inv; split.
  - apply (mon_prod_assoc_leg X exl mon_prod_mu_exl).
  - apply (mon_prod_assoc_leg Y exr mon_prod_mu_exr).
Qed.
Next Obligation.
  (* left unit *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_right_left eta[X] exl).
  rewrite <- (bimap_id_right_left eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_left, mu_unit_left.
  rewrite <- !to_unit_left_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.
Next Obligation.
  (* right unit *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_left_right eta[X] exl).
  rewrite <- (bimap_id_left_right eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_right, mu_unit_right.
  rewrite <- !to_unit_right_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.

(* The two projections are monoid homomorphisms. *)
Lemma mon_exl_hom : MonoidHom Monoid_Product X exl.
Proof. split; [ apply mon_prod_mu_exl | apply mon_prod_eta_exl ]. Qed.

Lemma mon_exr_hom : MonoidHom Monoid_Product Y exr.
Proof. split; [ apply mon_prod_mu_exr | apply mon_prod_eta_exr ]. Qed.

(* The pairing of two monoid homomorphisms is a monoid homomorphism. *)
Lemma mon_fork_hom {z} {Z : Monoid z} {f : z ~> x} {g : z ~> y} :
  MonoidHom Z X f → MonoidHom Z Y g → MonoidHom Z Monoid_Product (f △ g).
Proof.
  intros F G.
  split; simpl.
  - unfold mon_prod_mu.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exl_fork.
      apply (@hom_mu _ _ _ _ _ _ _ F).
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exr_fork.
      apply (@hom_mu _ _ _ _ _ _ _ G).
  - unfold mon_prod_eta.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + apply (@hom_eta _ _ _ _ _ _ _ F).
    + apply (@hom_eta _ _ _ _ _ _ _ G).
Qed.

End Data.

(** ** Mon(C) is cartesian *)

(* Binary products in Mon(C) from binary products in C.  No terminal object of
   C is used, and no compatibility between × and ⨂. *)
#[export] Program Instance Mon_Cartesian : @Cartesian (Mon C) := {|
  product_obj := fun X Y => (`1 X × `1 Y; Monoid_Product `2 X `2 Y);
  fork := fun _ _ _ f g =>
            (`1 f △ `1 g; mon_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; mon_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; mon_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End Binary.

(** ** The terminal monoid *)

Section Nullary.

Context `{TE : @Terminal C}.

(* The terminal object carries a unique monoid structure: both structure maps
   land in 1, so [one_unique] discharges all three laws.  No [Cartesian] is
   used here. *)
Program Definition Terminal_Monoid : Monoid (1 : C) := {|
  mu  := one;
  eta := one
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(* Every morphism into the terminal object is a monoid homomorphism, both
   preservation conditions being equations between morphisms into 1. *)
Lemma mon_one_hom {x : C} (X : Monoid x) :
  MonoidHom X Terminal_Monoid one.
Proof. split; apply one_unique. Qed.

#[export] Program Instance Mon_Terminal : @Terminal (Mon C) := {|
  terminal_obj := ((1 : C); Terminal_Monoid);
  one := fun X => (one; mon_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End Nullary.

(** ** The forgetful functor agrees with C's finite products, on the nose *)

Section Forget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(* The underlying object of a product monoid IS the product of the underlying
   objects, and likewise for the projections, the pairing and the unique map
   into the terminal monoid: all at Leibniz equality, by [eq_refl].  This is
   preservation on DATA; creation in the sense of Structure/Limit/Creation.v
   is not proved and is not claimed. *)
Example Mon_Forget_product (X Y : Mon C) :
  fobj[Mon_Forget] (X × Y) = fobj[Mon_Forget] X × fobj[Mon_Forget] Y
  := eq_refl.

Example Mon_Forget_terminal :
  fobj[Mon_Forget] (@terminal_obj (Mon C) Mon_Terminal) = (1 : C)
  := eq_refl.

Example Mon_Forget_exl (X Y : Mon C) :
  fmap[Mon_Forget] (@exl (Mon C) Mon_Cartesian X Y) = exl := eq_refl.

Example Mon_Forget_exr (X Y : Mon C) :
  fmap[Mon_Forget] (@exr (Mon C) Mon_Cartesian X Y) = exr := eq_refl.

Example Mon_Forget_fork (X Y Z : Mon C) (f : X ~> Y) (g : X ~> Z) :
  fmap[Mon_Forget] (@fork (Mon C) Mon_Cartesian _ _ _ f g)
    = fmap[Mon_Forget] f △ fmap[Mon_Forget] g := eq_refl.

Example Mon_Forget_one (X : Mon C) :
  fmap[Mon_Forget] (@one (Mon C) Mon_Terminal X) = one := eq_refl.

End Forget.

(** ** Reconciling the two monoid-object classes *)

(* At a FIXED monoidal base the two classes differ only by the names and the
   order of their fields, so the passage is field renaming in both
   directions.  This says nothing about the tensor: it cannot turn an
   abstract M into [CC_Monoidal], which is why it is not the route by which
   [Mon_Cartesian] is obtained. *)

Definition Monoid_of_MonoidObject {x : C} (X : @MonoidObject C M x)
  : Monoid x := {|
  mu           := @mappend _ _ _ X;
  eta          := @mempty _ _ _ X;
  mu_assoc     := @mappend_assoc _ _ _ X;
  mu_unit_left := @mempty_left _ _ _ X;
  mu_unit_right := @mempty_right _ _ _ X
|}.

Definition MonoidObject_of_Monoid {x : C} (X : Monoid x)
  : @MonoidObject C M x := {|
  mempty        := @eta _ _ _ X;
  mappend       := @mu _ _ _ X;
  mempty_left   := @mu_unit_left _ _ _ X;
  mempty_right  := @mu_unit_right _ _ _ X;
  mappend_assoc := @mu_assoc _ _ _ X
|}.

(* Both round trips close on the WHOLE record by [eq_refl]: both classes are
   declared under [Set Primitive Projections] (Lib/Foundation.v:5), so record
   eta identifies a record with the tuple of its own projections. *)
Example monoid_round {x : C} (X : Monoid x) :
  Monoid_of_MonoidObject (MonoidObject_of_Monoid X) = X := eq_refl.

Example monoid_object_round {x : C} (X : @MonoidObject C M x) :
  MonoidObject_of_Monoid (Monoid_of_MonoidObject X) = X := eq_refl.

(* THE DESIGN CLAIM, MACHINE-CHECKED RATHER THAN ARGUED.  The passage above
   cannot carry [Product_Monoid] to an abstract monoidal base: its conclusion
   lives at [CC_Monoidal], and for a variable M there is no conversion between
   the two.  Stripping the [Fail] reports

     The term "Product_Monoid X Y" has type
      "@MonoidObject C (@CC_Monoidal C ?H ?H0) (x × y)"
     while it is expected to have type "@MonoidObject C M (x × y)"

   — a TYPING failure at the monoidal instance itself, not at any argument
   elaborated before it.  The positive control is in the comparison section
   below, where the same application at M := [CC_Monoidal] is accepted. *)

End MonProduct.

Section AbstractBaseProbe.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Fail Check
  (fun (x y : C) (X : @MonoidObject C CC_Monoidal x)
       (Y : @MonoidObject C CC_Monoidal y) =>
     @Monoid_of_MonoidObject C M (x × y) (Product_Monoid X Y)).

End AbstractBaseProbe.

(** ** [Product_Monoid] is the cartesian special case *)

(* Instantiating the monoidal base at [CC_Monoidal] — where the tensor IS the
   categorical product — makes [Monoid_Product] and Structure/Monoid.v's
   [Product_Monoid] two constructions of a monoid on the same object.  They
   agree; the unit on the nose, the multiplication up to [≈]. *)

Section Comparison.

Context {C : Category}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(* [Structure.Monoid.Monoid x] is by definition [@MonoidObject C CC_Monoidal
   x]; the passage above turns it into this file's [Monoid] at the same
   base. *)

Example Monoid_Product_eta_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @eta C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                          (Monoid_of_MonoidObject X)
                          (Monoid_of_MonoidObject Y))
    = @mempty C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

(* [Product_Monoid] read as a [Monoid] in this file's sense.  This is what
   "so that [Product_Monoid] applies" amounts to, and it doubles as the
   positive control for the negative in [AbstractBaseProbe] above: the very
   same application, at M := [CC_Monoidal] instead of a variable M, IS
   accepted. *)
Definition Product_Monoid_as_Monoid {x y : C}
           (X : @MonoidObject C CC_Monoidal x)
           (Y : @MonoidObject C CC_Monoidal y)
  : @Monoid C CC_Monoidal (x × y)
  := @Monoid_of_MonoidObject C CC_Monoidal (x × y) (Product_Monoid X Y).

(* The multiplications are NOT the same term.  Control:
   [Monoid_Product_mu_is_Product_Monoid], immediately below, which names every
   constant occurring in this command. *)
Fail Example Monoid_Product_mu_not_strict
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    = @mappend C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

Lemma Monoid_Product_mu_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    ≈ @mappend C CC_Monoidal _ (Product_Monoid X Y).
Proof.
  simpl.
  unfold mon_prod_mu, bimap, toggle, split; simpl.
  rewrite <- fork_comp.
  apply fork_inv; split; rewrite <- comp_assoc.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.

End Comparison.

(** ** A concrete instantiation, and the design claim made concrete *)

(* [Sets] with the setoid product is a monoidal category (its own hand-built
   [Sets_Product_Monoidal], Instance/Sets.v:288 — NOT [CC_Monoidal]), and it
   is cartesian.  So [Mon Sets] at that base — which is exactly
   Instance/Roster.v:390's [Mon_Sets], by definition there; that file is not
   required here — inherits finite products.

   This is also where the design argument of the header stops being a pointer
   and becomes an in-tree fact: [Product_Monoid] concludes at [CC_Monoidal
   Sets], and the two monoidal structures on [Sets] are NOT the same term, so
   route (a) would not have reached the tree's own [Mon Sets]. *)

Section SetsWitness.

Definition Mon_Sets_Cartesian
  : @Cartesian (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Cartesian Sets Sets_Product_Monoidal Sets_Cartesian.

Definition Mon_Sets_Terminal
  : @Terminal (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Terminal Sets Sets_Product_Monoidal Sets_Terminal.

(* CONVERSION negative: [Sets]'s own monoidal structure is not the cartesian
   monoidal structure built from its products.  Stripping the [Fail] gives
   "cannot unify "Sets_Product_Monoidal" and "CC_Monoidal"".  Controls: the
   two definitions immediately above, which name both [Sets_Product_Monoidal]
   and [Sets_Cartesian] / [Sets_Terminal]. *)
(* Control for the negative below.  Without it, `@CC_Monoidal` applied to
   explicit arguments occurs ONLY inside that `Fail`, so a signature change
   to `CC_Monoidal` would make the command fail for the wrong reason —
   `Illegal application` rather than `cannot unify` — and the guard would go
   vacuously green.  This is the same false-pass mode the section probe
   above records. *)
Check (@CC_Monoidal Sets Sets_Cartesian Sets_Terminal).

Fail Example Sets_Product_Monoidal_is_CC_Monoidal :
  Sets_Product_Monoidal = @CC_Monoidal Sets Sets_Cartesian Sets_Terminal
  := eq_refl.

(* TYPING negative: consequently [Product_Monoid] does not supply a monoid
   for [Mon Sets].  Stripping the [Fail] gives "The term "Product_Monoid X Y"
   has type "@MonoidObject Sets (@CC_Monoidal Sets _ _) (x × y)" while it is
   expected to have type "@MonoidObject Sets Sets_Product_Monoidal (x × y)"".
   Control: [Product_Monoid_as_Monoid] above, the same application where the
   two bases DO agree. *)
Fail Check
  (fun (x y : Sets)
       (X : @MonoidObject Sets CC_Monoidal x)
       (Y : @MonoidObject Sets CC_Monoidal y) =>
     @Monoid_of_MonoidObject Sets Sets_Product_Monoidal
       (@product_obj Sets Sets_Cartesian x y) (Product_Monoid X Y)).

End SetsWitness.

(** * The universe boundary, PINNED

    The UNIVERSES section of this header attributes C's hom = proof
    identification to three donors, measured under a section declaring the
    levels strictly apart.  An earlier revision REPORTED that measurement
    without pinning it anywhere, so nothing in the build would have noticed
    an upstream annotation changing it.  These are that measurement, as
    guarded negatives with their controls.

    Section-local [Universes]/[Constraint] do not leak: a downstream file
    importing this one can still declare its own levels strictly apart. *)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* CONTROLS: a hom and an identity of such a category are formable at
   exactly these levels, so the rejections below are about the donors and
   not about the levels themselves. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).
Check (fun (C : Category@{uo uh up}) (x : C) => id[x]).

(* Controls that the three donor names resolve at unconstrained levels;
   without these a rename would leave the negatives succeeding on a
   reference-not-found error rather than on the universe boundary. *)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.

(* NEGATIVE 1 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

(* NEGATIVE 2 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 3 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

End UniverseDonors.
