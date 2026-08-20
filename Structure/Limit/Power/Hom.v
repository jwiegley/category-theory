Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Coq.Vectors.Fin.

Generalizable All Variables.

Import EqNotations.

(** * The characterizing isomorphisms of a power and a copower *)

(* nLab:      https://ncatlab.org/nlab/show/power
   nLab:      https://ncatlab.org/nlab/show/copower

   Sources are those of Structure/Limit/Power.v, whose header carries the
   full citation block; the two statements this file exists for are

     - Riehl, "Category Theory in Context", 2nd ed., section 3.5, printed
       p. 110 (PDF p. 130), item [riehl:3.5:example4]:
       [C(X, A^I) ≅ C(X, A)^I], natural in [X], given by composing with the
       projections [ev_i]; in Set [A^I] is the ordinary function set and
       [ev_i] is evaluation at [i].
     - the same, printed p. 111 (PDF p. 131), item [riehl:3.5:example8]:
       [C(∐_I A, X) ≅ C(A, X)^I]; in Set the copower is [I × A].
     - Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
       September 2005), section 3.2, unnumbered remark, printed p. 61 (PDF
       p. 70): in Sets a finite set is [1 + 1 + ⋯ + 1].

   NOTHING HERE IS A NEW THEOREM, AND THAT IS THE POINT.

   Structure/Limit/Indexed/Hom.v already proves, for an ARBITRARY family
   [f : A → C], that the comparison map from the representable to
   [c ↦ ∏ₐ C(c, f a)] is invertible exactly when [f] has an indexed product,
   and packages the invertible case as an [Isomorphism] in [[C^op, Sets]]
   natural in the varying object.  A power is that at the CONSTANT family, so
   every isomorphism below is [iprod_hom_iso] or [icoprod_hom_iso] applied,
   supplied by [:=] with no tactic and no obligation.  [power_hom_iso_is_donor]
   and [copower_hom_iso_is_donor] record by [eq_refl] that the derived form is
   the donor's TERM, not merely an isomorphism with the same type; likewise
   for the two comparison maps, the two inverses and the two biconditionals.

   What the constant family buys, beyond the name, is that the RIGHT-HAND
   SIDE becomes a power too -- in [Sets].  [power_hom_functor_is_Sets_power]
   and its dual record, by [eq_refl],

     fobj[power_hom_functor J b] c   =  power J (hom-setoid c b)
     fobj[copower_hom_functor J b] c =  power J (hom-setoid b c)

   with [power] on the right read at [Sets_HasIndexedProducts].  That is what
   turns Riehl's [C(X, A)^I] from a suggestive superscript into the same
   operator applied in another category, and it is why both of her examples
   -- the power one and the copower one -- have a POWER on the right.

   THE POINTWISE FORM IS DERIVED, NOT ASSUMED.  [power_hom_iso_at] evaluates
   the natural isomorphism at an object and lands at the literal shape

     [C(X, A^I) ≅[Sets] C(X, A)^I]

   using nothing but the natural isomorphism's own two laws plus [id_right]:
   the identity transformation's component at [c] is [fmap] of an identity,
   not an identity, so one [id_right] is the whole gap.  Naturality in [X] is
   NOT lost by evaluating -- it stays available in the natural form the
   pointwise one is derived from.

   THE [Sets] IDENTIFICATIONS, AND HOW MUCH OF EACH WAS ALREADY THERE

   Power side: mostly already in tree, and reused rather than reproved.
   Instance/Sets/Products.v:449-486 already builds
   [Sets_exponent_IsIndexedProduct] and [Sets_constant_iprod_exponent] -- the
   function set [X ^ Sets_discrete I] satisfying the constant-family universal
   property, and its isomorphism with [indexed_product (fun _ : I => X)] --
   for Awodey 2.9 exercise 7(b).  [Sets_power_exponent] IS that isomorphism,
   by [:=].  What is added is the power vocabulary and three strict readings
   the donor file does not state: the carrier of [power J X] is literally the
   function type [J → X] ([Sets_power_carrier]), [power_ev] is literally
   evaluation ([Sets_power_ev_computes], [g j] on the nose), and evaluation in
   the exponential agrees with it across the isomorphism
   ([Sets_power_ev_is_exponent_eval], at [≈] -- it is an equation between
   morphisms).

   Copower side: new here.  [Sets_copower_prod] is Riehl's [I · A ≅ I × A],
   with [I] read as the discrete setoid [Sets_discrete I] -- the same reading
   Instance/Sets/Products.v:478 takes for the exponential, and forced by the
   same fact, that the index of [HasIndexedCoproducts] is a bare [Type] while
   a product in [Sets] takes two setoids.  No claim is made about a coarser
   setoid on the index.

   AWODEY'S FINITE DECOMPOSITION IS THE [b := 1] READING AND NOT A SECOND
   CONSTRUCTION.  [Sets_copower_one : J · 1 ≅ Sets_discrete J] is assembled
   from two named maps with a three-tactic isomorphism proof -- built directly
   rather than by composing [Sets_copower_prod] with a right-unit isomorphism
   of the product, which would be longer, not shorter --
   [Sets_copower_fin] is it at [Fin.t n], and
   [Sets_copower_two] -- Awodey's [2 = 1 + 1] -- is
   [Sets_icoprod_bool] at the constant family, so the passage to the BINARY
   coproduct of Instance/Sets/Cocartesian.v costs nothing.  Non-vacuity is
   proved rather than gestured at: [Sets_copower_three_distinct] exhibits
   three pairwise-distinct elements of [Fin.t 3 · 1], so the [n]-fold copower
   of the terminal object is not collapsing.

   AN ENGINEERING FINDING, MEASURED, AND A SECOND SIGHTING OF A KNOWN HAZARD

   Instance/Sets/Products.v:409-424 records that letting instance resolution
   close a [proper_morphism] field can pin a constant's index universe to
   [Set].  That happened again here, at a different construction, and was
   fixed the same way.  Written as a [Program Definition],
   [Sets_copower_one_from] raises NO obligation -- resolution closes the field
   during elaboration, the domain being the discrete setoid [Sets_discrete J]
   whose [≈] is Leibniz [eq] -- and [Set Printing Universes. About ...] then
   prints [Set = u] in its constraint block, an EQUALITY on the index
   universe, so [Sets_copower_one] would have applied only to indices in
   [Set].  Supplying the certificate by hand under [unshelve refine] removes
   it: the constant now carries [u < u0] and no [Set].  This is not left as a
   remembered fact -- Test/ProbePower.v declares the [Program] variant and
   pins its rejection at an index strictly above [Set], against the shipped
   constant at the same index as a control.  The mechanism behind the pinning
   was not investigated further; only the symptom and the fix were measured,
   which is also the scope of the note this repeats.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

   Reproduce with [Set Printing Universes.] and [About]; reading the binder
   alone gets this wrong.  Everything here inherits Structure/Limit/Indexed/
   Hom.v's situation exactly -- nothing below widens or narrows it -- and the
   inheritance was measured constant by constant rather than assumed:

     [power_hom_functor@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}]
     and an index [Type@{u}] with [u <= u1] and [u4 <= u1], so the index
     universe and [C]'s hom universe are each bounded by the target [Sets]'
     carrier universe [u1] and are unrelated to each other -- the same block
     the donor [iprod_hom_functor] carries.  [copower_hom_functor] prints the
     identical block.

     [power_hom_iso@{u u0 u1 u2 u3}] takes [C : Category@{u3 u u}] with the
     index at [Type@{u}]: the index universe IS [C]'s hom universe, an
     IDENTIFICATION and not merely a bound, and [C]'s proof universe is
     dragged along with it.  The donor [iprod_hom_iso] prints exactly the
     same shape, so this is inherited in full.  Structure/Limit/Indexed/Hom.v
     analyses the cause -- a [SetoidObject] is not cumulative here, so the
     [Sets] the comparison lives in has its carrier universe forced EQUAL to
     [C]'s hom universe -- and pins it as a formability negative.
     [copower_hom_iso] and [power_hom_iso_at] print the same shape.

   The [Sets] witnesses below carry only [u < u0] -- index strictly below the
   [Sets] carrier universe -- with no [Set] anywhere; see the finding just
   above for the one place that had to be worked for.

   WHAT IS NOT DELIVERED

   No naturality in the INDEX [J] or in the object [b]: both isomorphisms are
   natural in the varying object only, exactly as their donors are.  No
   [Representable] instance for [power_hom_functor] and no universal-element
   packaging.  No [HasIndexedCoproducts FinSet], so Awodey's decomposition is
   delivered at [Sets] only and nothing is claimed about skeletal [FinSet];
   the issue's own wording allows either.  No cardinality statement: [Fin.t n
   · 1] is shown isomorphic to the discrete setoid on [Fin.t n] and shown to
   have three pairwise-distinct elements at [n = 3], but no counting argument
   is made and Instance/FinSet/Skeleton.v is not invoked.  No comparison of
   the copower with the exponential, and no monoidal or enriched reading of
   either operator.

   STATUS: axiom-free.  All 58 constants -- 51 named plus 7 [Program]
   obligations, enumerated by [Print Module] per the docs/AXIOMS.md
   methodology -- report "Closed under the global context"; the Makefile's
   [print-assumptions] target audits the headline ones.  (Note that [Print
   Module] displays a [Qed]-opaque constant as [Parameter]; running it here
   shows NINE of them -- the seven [Program] obligations, which are opaque
   too, plus the two named lemmas
   [Sets_power_ev_is_exponent_eval] and [Sets_copower_three_distinct] --
   and all nine are ordinary opaque proofs, not axioms, which is what the
   audit above checks.) *)

#[local] Obligation Tactic := idtac.

(** ** The two hom functors, at a constant family *)

(* [c ↦ ∏_J C(c, b)], the right-hand side of Riehl's [C(X, A)^I]. *)
Definition power_hom_functor {C : Category} (J : Type) (b : C) : C^op ⟶ Sets :=
  iprod_hom_functor (fun _ : J => b).

(* [c ↦ ∏_J C(b, c)], the right-hand side of [C(∐_I A, X) ≅ C(A, X)^I]. *)
Definition copower_hom_functor {C : Category} (J : Type) (b : C) : C ⟶ Sets :=
  icoprod_hom_functor (fun _ : J => b).

(* Each right-hand side is itself a power, in [Sets]. *)
Example power_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

Example copower_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[copower_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C b c ; is_setoid := @homset C b c |} := eq_refl.

(** ** The comparison maps: composing with the evaluations, resp. injections *)

Definition power_hom_transform {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  @Transform (C^op) Sets (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_transform C J (fun _ : J => b) p ev.

Definition copower_hom_transform {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  @Transform C Sets (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_transform C J (fun _ : J => b) p inj.

Example power_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) (c : C) (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u := eq_refl.

Example copower_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) (c : C) (u : p ~> c) :
  transform (copower_hom_transform b p inj) c u = fun j : J => u ∘ inj j
  := eq_refl.

(** ** The isomorphisms, derived at the constant family *)

Definition power_hom_inverse {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Transform (C^op) Sets (power_hom_functor J b) (@Curried_CoHom C p) :=
  @iprod_hom_inverse C J (fun _ : J => b) p ev H.

Definition copower_hom_inverse {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Transform C Sets (copower_hom_functor J b) (@Curried_Hom C p) :=
  @icoprod_hom_inverse C J (fun _ : J => b) p inj H.

(* Riehl 3.5.4: [C(X, A^I) ≅ C(X, A)^I], natural in [X]. *)
Definition power_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_iso C J (fun _ : J => b) p ev H.

(* Riehl 3.5.8: [C(I · A, X) ≅ C(A, X)^I], natural in [X]. *)
Definition copower_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_iso C J (fun _ : J => b) p inj H.

(* The converse, and the biconditional: an invertible comparison map is a
   universal property.  Both are the donor's, at the constant family. *)
Definition power_of_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p)
                      (power_hom_functor J b)
                      (power_hom_transform b p ev)) :
  IsPower b p ev :=
  @iprod_of_hom_iso C J (fun _ : J => b) p ev I.

Definition copower_of_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p)
                      (copower_hom_functor J b)
                      (copower_hom_transform b p inj)) :
  IsCopower b p inj :=
  @icoprod_of_hom_iso C J (fun _ : J => b) p inj I.

Definition power_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b)
                 (power_hom_transform b p ev) :=
  @iprod_iff_hom_iso C J (fun _ : J => b) p ev.

Definition copower_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b)
                 (copower_hom_transform b p inj) :=
  @icoprod_iff_hom_iso C J (fun _ : J => b) p inj.

(** ** The derived forms are the donors' TERMS, not merely their types *)

Example power_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  power_hom_functor J b = @iprod_hom_functor C J (fun _ : J => b) := eq_refl.

Example copower_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  copower_hom_functor J b = @icoprod_hom_functor C J (fun _ : J => b)
  := eq_refl.

Example power_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_hom_transform b p ev = @iprod_hom_transform C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_hom_transform b p inj
  = @icoprod_hom_transform C J (fun _ : J => b) p inj := eq_refl.

Example power_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_inverse H = @iprod_hom_inverse C J (fun _ : J => b) p ev H
  := eq_refl.

Example copower_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_inverse H = @icoprod_hom_inverse C J (fun _ : J => b) p inj H
  := eq_refl.

Example power_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_iso H = @iprod_hom_iso C J (fun _ : J => b) p ev H := eq_refl.

Example copower_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_iso H = @icoprod_hom_iso C J (fun _ : J => b) p inj H := eq_refl.

Example power_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_iff_hom_iso b p ev = @iprod_iff_hom_iso C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_iff_hom_iso b p inj = @icoprod_iff_hom_iso C J (fun _ : J => b) p inj
  := eq_refl.

(* And the backward leg still computes to the mediator the [∃!] accessor
   names, so the packaging cannot drift from the universal property. *)
Example power_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  (c : C) (fam : ∀ _ : J, c ~> b) :
  transform (from (power_hom_iso H)) c fam = unique_obj (power_desc H fam)
  := eq_refl.

Example copower_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  (c : C) (fam : ∀ _ : J, b ~> c) :
  transform (from (copower_hom_iso H)) c fam = unique_obj (copower_desc H fam)
  := eq_refl.

(** ** The pointwise form, evaluated at an object

    Riehl states [C(X, A^I) ≅ C(X, A)^I].  Evaluating the natural
    isomorphism above at [X] lands at exactly that shape, the right-hand side
    being a power in [Sets] by [power_hom_functor_is_Sets_power].  The only
    step is a unit law -- [id_right] on the power side, [id_left] on the
    copower side, the orientation flipping with the variance -- because the
    identity transformation's component is [fmap] of an identity. *)

Program Definition power_hom_iso_at {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) (c : C) :
  @Isomorphism Sets {| carrier := @hom C c p ; is_setoid := @homset C c p |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C c b ; is_setoid := @homset C c b |}) := {|
  to   := transform (to (power_hom_iso H)) c;
  from := transform (from (power_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p ev H c fam j.
  pose proof (iso_to_from (power_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_right in Hr.
Qed.
Next Obligation.
  intros C J b p ev H c u.
  pose proof (iso_from_to (power_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_right in Hl.
Qed.

Program Definition copower_hom_iso_at {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) (c : C) :
  @Isomorphism Sets {| carrier := @hom C p c ; is_setoid := @homset C p c |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C b c ; is_setoid := @homset C b c |}) := {|
  to   := transform (to (copower_hom_iso H)) c;
  from := transform (from (copower_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p inj H c fam j.
  pose proof (iso_to_from (copower_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_left in Hr.
Qed.
Next Obligation.
  intros C J b p inj H c u.
  pose proof (iso_from_to (copower_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_left in Hl.
Qed.

(** ** At the chosen (co)power of a category that has all of them *)

Definition class_power_hom_iso {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (power J b))
               (power_hom_functor J b) :=
  power_hom_iso (power_ump J b).

Definition class_copower_hom_iso {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (copower J b))
               (copower_hom_functor J b) :=
  copower_hom_iso (copower_ump J b).

(** ** Riehl 3.5.4 in [Sets]: the power is the function set, [ev_i] is
       evaluation at [i]

    The object-level half was already proved in Instance/Sets/Products.v for
    Awodey 2.9 exercise 7(b), and is reused by [:=] rather than reproved. *)

Definition Sets_power_exponent (J : Type) (X : obj[Sets]) :
  @power Sets Sets_HasIndexedProducts J X ≅[Sets] Sets_pow J X :=
  Sets_constant_iprod_exponent J X.

Example Sets_power_carrier (J : Type) (X : obj[Sets]) :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

Example Sets_power_ev_computes (J : Type) (X : obj[Sets]) (j : J)
  (g : carrier (@power Sets Sets_HasIndexedProducts J X)) :
  @power_ev Sets Sets_HasIndexedProducts J X j g = g j := eq_refl.

Lemma Sets_power_ev_is_exponent_eval (J : Type) (X : obj[Sets]) (j : J) :
  Sets_exponent_eval J X j ∘ to (Sets_power_exponent J X)
    ≈ @power_ev Sets Sets_HasIndexedProducts J X j.
Proof. intros g; reflexivity. Qed.

(** ** Riehl 3.5.8 in [Sets]: the copower is the product with the index *)

Example Sets_copower_carrier (J : Type) (Y : obj[Sets]) :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

Example Sets_copower_inj_computes (J : Type) (Y : obj[Sets]) (j : J)
  (y : carrier Y) :
  @copower_inj Sets Sets_HasIndexedCoproducts J Y j y
  = existT (fun _ : J => carrier Y) j y := eq_refl.

Program Definition Sets_copower_prod_to (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ~{Sets}~> (Sets_discrete J × Y)%object := {|
  morphism := fun p : { _ : J & carrier Y } => (projT1 p, projT2 p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  split; [reflexivity|exact Hxy].
Qed.

Program Definition Sets_copower_prod_from (J : Type) (Y : obj[Sets]) :
  (Sets_discrete J × Y)%object
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J Y := {|
  morphism := fun p : (J * carrier Y)%type =>
                existT (fun _ : J => carrier Y) (fst p) (snd p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [He Hxy]; simpl in *; destruct He; simpl in *.
  exists eq_refl; exact Hxy.
Qed.

Definition Sets_copower_prod (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ≅[Sets] (Sets_discrete J × Y)%object.
Proof.
  refine {| to := Sets_copower_prod_to J Y
          ; from := Sets_copower_prod_from J Y |}.
  - intros [i x]; split; reflexivity.
  - intros [i x]; exists eq_refl; reflexivity.
Defined.

(** ** Awodey 3.2: a finite set is the [n]-fold copower of the terminal object

    This is the [b := 1] reading of [Sets_copower_prod]'s statement and not a
    second construction; it is proved directly because doing so is shorter
    than composing with a right-unit isomorphism of the product. *)

Program Definition Sets_copower_one_to (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object
    ~{Sets}~> Sets_discrete J := {|
  morphism := fun p : { _ : J & poly_unit } => projT1 p
|}.
Next Obligation.
  intros J [i x] [j y] [e Hxy]; simpl in *; destruct e; reflexivity.
Qed.

(* The [proper_morphism] certificate is supplied by hand deliberately: under
   [Program] it is closed by instance resolution instead, and that pins this
   constant's index universe to [Set].  See the header. *)
Definition Sets_copower_one_from (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object.
Proof.
  unshelve refine {| morphism := fun i : J =>
                       existT (fun _ : J => poly_unit) i ttt |}.
  intros i j Hij; destruct Hij; exists eq_refl; reflexivity.
Defined.

Definition Sets_copower_one (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object ≅[Sets] Sets_discrete J.
Proof.
  refine {| to := Sets_copower_one_to J; from := Sets_copower_one_from J |}.
  - intros i; reflexivity.
  - intros [i []]; exists eq_refl; reflexivity.
Defined.

(* The finite case: a set of [n] elements is the [n]-fold copower of [1]. *)
Definition Sets_copower_fin (n : nat) :
  @copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object
    ≅[Sets] Sets_discrete (Fin.t n) :=
  Sets_copower_one (Fin.t n).

(* Awodey's [2 = 1 + 1], through the BINARY coproduct of
   Instance/Sets/Cocartesian.v: the constant-family instance of the
   pre-existing [Sets_icoprod_bool], so the passage costs nothing. *)
Definition Sets_copower_two :
  @copower Sets Sets_HasIndexedCoproducts bool 1%object ≅[Sets] (1 + 1)%object :=
  Sets_icoprod_bool (fun _ : bool => 1%object).

(** ** Non-vacuity: the [n]-fold copower of [1] does not collapse *)

Definition Sets_copower_pt {n : nat} (k : Fin.t n) :
  carrier (@copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object) :=
  existT (fun _ : Fin.t n => poly_unit) k ttt.

Definition fin3_0 : Fin.t 3 := Fin.F1.
Definition fin3_1 : Fin.t 3 := Fin.FS Fin.F1.
Definition fin3_2 : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

Lemma Sets_copower_three_distinct :
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_1) → False) *
  ((Sets_copower_pt fin3_1 ≈ Sets_copower_pt fin3_2) → False) *
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_2) → False).
Proof.
  repeat split; intros [e _]; simpl in e.
  - discriminate.
  - apply Fin.FS_inj in e; discriminate.
  - discriminate.
Qed.
