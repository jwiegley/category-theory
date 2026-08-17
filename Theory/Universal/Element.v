Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Elements.

Generalizable All Variables.

(** * Universal elements *)

(* nLab: https://ncatlab.org/nlab/show/universal+element
   nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   Mac Lane's Definition 2 of §III.1 (CWM 2nd ed., p. 57): if D is a category
   and H : D ⟶ Set a functor, a UNIVERSAL ELEMENT of H is a pair ⟨r, e⟩
   consisting of an object r of D and an element e ∈ H r such that for every
   pair ⟨d, x⟩ with x ∈ H d there is a unique arrow k : r ~> d of D with
   (H k) e = x.

   That is the ELEMENTARY form -- one element, one unique-factorization
   clause, no natural transformation in sight -- and it is the form this file
   takes as primitive ([aue_universal] / [ue_universal] below).  The library
   already carried the same content twice over in less elementary encodings:
   [Functor/Representable.v]'s [Representable] packages a natural isomorphism
   [Hom r,─] ≅ H and its header records, without proving it, that "by the
   Yoneda lemma such a Φ is determined by a single universal element of F(A),
   namely Φ_A(id A)"; and [Structure/UniversalProperty.v]'s
   [representability_by_yoneda] proves exactly that determination, but states
   the universal elements as the ANONYMOUS sigma setoid

       { x : F c & IsIsomorphism (from (Yoneda_Lemma C F c) x) },

   a predicate on x phrased in terms of the invertibility of its Yoneda mate
   rather than in terms of unique factorization.  Neither is a first-class
   [UniversalElement], and neither exhibits Mac Lane's elementary clause.
   This file supplies the class and proves the two encodings equivalent.

   Mac Lane's Remark 3 on the following page (p. 58) then asserts a two-way
   subsumption between universal elements and universal arrows, and it is the
   substance of this file:

     (a) "Since an element x ∈ H d may be described as a function x : * → H d
         from a one-point set *, this definition is a special case of that of
         a universal arrow: ⟨r, e⟩ is universal from * to H."

     (b) "Conversely, the definition of a universal arrow ⟨r, u⟩ from c to
         S : D ⟶ C can be phrased as: ⟨r, u⟩ is a universal element of the
         functor D(c, S−) : D ⟶ Set."

   Both halves are proved below, and then STATED TOGETHER as the single
   biconditional [universal_element_arrow_subsumption], which is the thing the
   tree lacked: the two directions existed nowhere, and a reader had no way to
   see that the two notions are interdefinable rather than merely analogous. *)

(* Where the notion sits, and why it is the elementary one

   Text:  Mac Lane, "Categories for the Working Mathematician", Springer 1998,
          §III.1 (pp. 55-59) and §III.2
   Text:  Riehl, "Category Theory in Context", Dover 2016, §2.4
   Paper: Kan, "Adjoint functors", Trans. Amer. Math. Soc. 87, 1958

   The universal element is the smallest of the universal notions: it
   mentions no comma category, no adjunction, and no natural
   transformation, only an element and a factorization.  Its interest is
   that it is nevertheless EQUIVALENT to the largest of them.  Riehl
   organises §2.4 around this observation, calling a representation of a
   functor and a universal element "the same data", and her Proposition
   2.4.8 makes the sharpest form of the statement: a universal element of
   H is precisely an INITIAL object of the category of elements of H.
   In-tree that reading is already worked out concretely, one functor at
   a time: Instance/Coq/Nat.v's [repr_initial] derives initiality in
   [FAlg NatF] from a representation of the forgetful functor on
   endomaps, and its header explains that [FAlg NatF] is standing in for
   the category of elements.  With the general class in hand that
   argument can be run once instead of per functor, which is what
   Theory/Universal/Element/Elements.v does.

   Historically the elementary form is what the subject started from.
   Kan's 1958 paper introduces adjoints through hom-set bijections, and
   Mac Lane's chapter notes record that the universal-mapping formulation
   predates the functorial one by a decade (see the essay in
   Theory/Universal/Arrow.v).  Mac Lane's own ordering in §III.1 is
   deliberate: universal arrow first, universal element second, remark
   third, the remark being where he tells the reader that nothing new was
   introduced.  This file follows that ordering, and takes the remark
   seriously enough to prove it.

   The setoid discipline changes one word of the definition.  Mac Lane
   writes "(H k) e = x" with equality of elements of a set; here H lands
   in [Sets], whose objects are setoids, so the clause is
   [fmap[H] k e ≈ x] and uniqueness of k is uniqueness up to `≈` -- the
   [Unique] record of Lib/Setoid.v, exactly as [AUniversalArrow] uses it.
   Nothing else moves. *)

(* WHAT IS DELIVERED

   * [AUniversalElement H r] -- the elementary definition with the object
     a PARAMETER, in the idiom of [AUniversalArrow], carrying a [Setoid]
     ([AUniversalElementEquiv]) that compares two universal elements by
     their underlying elements; and [UniversalElement H] -- Mac Lane's
     pair ⟨r, e⟩ with the object a FIELD, in the idiom of [Representable].
     The two passages copy fields, so BOTH round trips close by [eq_refl]
     on the whole record ([aue_of_ue_of_aue], [ue_of_aue_of_ue]) -- record
     eta, primitive projections being on.

   * The mediator calculus and Mac Lane's Proposition 1 for this notion:
     [ue_med] with commutes / unique / id / comp, the canonical
     isomorphism of universal objects, and uniqueness up to a UNIQUE
     isomorphism compatible with the two universal elements
     ([universal_element_unique]).

   * DELIVERABLE 2, and it is an ISOMORPHISM OF SETOIDS IN [Sets], not a
     biconditional and not a pair of mutually inverse maps up to `≈`:
     [universal_element_yoneda] inhabits

         @Isomorphism Sets (AUniversalElement H r) (ue_yoneda_obj)

     where [ue_yoneda_obj] is LITERALLY the anonymous sigma setoid that
     [representability_by_yoneda] takes as its source -- the same
     [exists_setoid] constant, re-registered locally so the two
     elaborate to the same term ([rby_agrees] checks this by ascribing
     [representability_by_yoneda] at the named setoid, which is a
     conversion check and not a proof).
     Composing gives [universal_element_representation], the
     universal-element/representation correspondence as one iso in
     [Sets].  Accessors run both ways: [aue_mate_IsIso] and
     [aue_inverse] out, [AUniversalElement_of_mate] back,
     [universal_element_of_representation] and
     [representation_of_universal_element] at the representation end.

   * A YONEDA-FREE ROUTE TO THE SAME DATA, because deliverable 2's
     statement carries a universe restriction its consumers should not:
     [Yoneda_Lemma], hence [representability_by_yoneda], hence
     [universal_element_representation], is stated over
     [C : Category@{u0 u0 u0}] -- object, hom and proof universes
     IDENTIFIED (measured, and pinned in Test/ProbeUniversalElement.v) --
     so no category whose objects sit strictly above its homs can be
     substituted, and [Instance/Coq/Nat.v]'s [Endos] is such a category.
     [ue_transform], [ue_representation] and [AUniversalElement_of_repr]
     build the same correspondence by hand, with [repr_eval] as the one
     computation; [routes_agree_elem] and [routes_agree_repr] record that
     the two routes carry the same data where both typecheck, and every
     accessor and both [Representable] passages are routed through the
     direct one.  The restriction is the DONOR'S, not one introduced
     here, and nothing here shows it unavoidable.

   * [UniversalElement_of_Representable] and
     [Representable_of_UniversalElement], with the representing object
     kept by [eq_refl] and the universal element identified as Mac Lane's
     Φ_r(id r) ([ue_of_repr_elem]).  [Functor/Representable.v] is
     therefore the SAME notion, not a competing one; its header's
     sentence "by the Yoneda lemma such a Φ is determined by a single
     universal element of F(A), namely Φ_A(id A)" is these two
     definitions.

   * DELIVERABLE 3(a): [AUniversalElement_of_AUniversalArrow] and
     [AUniversalArrow_of_AUniversalElement] between [AUniversalElement H r]
     and [AUniversalArrow SetsOne H r], mediated by the global-elements
     lemma [global_elements_iso : (1 ~> X) ≅ X] in [Sets].

   * DELIVERABLE 3(b): [AUniversalElement_of_hom] and
     [AUniversalArrow_of_hom] between [AUniversalArrow c S a] and
     [AUniversalElement ([Hom c,─] ◯ S) a].  This half is CHEAPER than it
     looks and the file says why: the two records' fields have
     CONVERTIBLE types, because [fmap] of the composite [Hom c,─] ◯ S at
     k is postcomposition with [fmap[S] k].  Both passages are therefore
     [:=] with no tactic, and both round trips are [eq_refl] on the whole
     record.

   * The composite Mac Lane asserts, as ONE theorem:
     [universal_element_arrow_subsumption].

   WHAT IS NOT DELIVERED

   * NO CLAIM THAT THE YONEDA ISO IS A BIJECTION OF TYPES.  It is an
     isomorphism in [Sets], i.e. of SETOIDS, and both setoids compare
     only the underlying element (resp. the first projection).  The full
     record round trip through the Yoneda encoding is NOT [eq_refl] --
     the uniqueness data is rebuilt -- and Test/ProbeUniversalElement.v
     pins that.  What IS [eq_refl] is the element, in both directions.

   * NO DUAL.  A couniversal element -- a universal element of a
     contravariant H : D^op ⟶ Sets, i.e. a TERMINAL object of the
     category of elements -- would be the mirror of
     Theory/Universal/Arrow/Dual.v and is left to the issue that wants
     it.  Note that the presheaf orientation IS the one
     [representability_by_yoneda] is stated in, and this file reaches the
     covariant reading by instantiating it at [D^op] rather than by
     reproving Yoneda; see [ue_mate].

   * NO NOTATION.  [Theory/Universal/Arrow.v]'s `c ⟿ F` is declared
     inside its section and does not survive; there is no exported
     spelling to mirror.

   * NO FUNCTORIALITY.  Nothing here makes [UniversalElement] an
     assignment on functors, and no comparison with
     [Construction/Elements.v]'s [Elements_proj] is stated.

   * The initial-object-of-the-category-of-elements reading (Riehl
     Proposition 2.4.8) is NOT here: it needs [Construction/Elements.v]'s
     [Elements] and [Structure/Initial.v], and lives in the satellite
     Theory/Universal/Element/Elements.v so that consumers of the theory
     do not inherit those.  Non-vacuity likewise lives in
     Theory/Universal/Element/Examples.v, which instantiates the class at
     Instance/Coq/Nat.v's representation and recovers its universal
     element [O] by [eq_refl].  Note what that witness does NOT do: it
     does not re-derive Nat.v's [repr_initial], which lands in
     [FAlg NatF], the comparison [Elements Endos_Forget ≃ FAlg NatF] not
     being in the tree. *)

(* [exists_setoid] (Structure/UniversalProperty.v) is declared there with
   [#[local]], which removes it from the instance database for importers but
   leaves the CONSTANT reachable by name.  Re-registering it here -- locally,
   so this file does not push a first-projection-only setoid on every sigma
   type in the tree -- is what makes [ue_yoneda_obj] below elaborate to the
   very term [representability_by_yoneda] has in its type, rather than to a
   copy with a different [Equivalence] proof that would not be convertible
   with it.  [rby_agrees] records that this worked. *)
#[local] Existing Instance Category.Structure.UniversalProperty.exists_setoid.

(** ** Global elements of a setoid *)

(* Mac Lane's "an element x ∈ H d may be described as a function x : * → H d
   from a one-point set".  [SetsOne] (Construction/Elements.v) is the
   singleton of [Sets_Terminal], the same object the elements-comma category
   =(SetsOne) ↓ K is built over there.

   A NOTE ON UNIVERSES, because it dictates the shape of the three
   definitions below.  A [Sets]-morphism out of the CONCRETE [SetsOne] whose
   [proper_morphism] is left to INSTANCE RESOLUTION -- whether by [Program]'s
   obligation tactic or by writing [reflexive_proper] out by hand -- resolves
   [Reflexive] at [SetsOne] and thereby pins the CARRIER universe of [Sets] to
   [Set], after which [global_element] cannot be applied at [fobj[H] d] for an
   [H] whose [Sets] sits anywhere else, and the whole of 3(a) is unformable.
   Writing the pointwise term [fun a b _ => reflexivity x] avoids the
   resolution and keeps all three fully polymorphic
   ([global_elements_iso@{u u0 u1 u2 u3}], measured).  Hence the record
   literals with that field spelled out, and hence [GlobalElements] is named:
   an anonymous [{| carrier := ... |}] in the [Isomorphism]'s type leaves the
   ambient category of the [to] field unresolved.

   BE PRECISE ABOUT THE CAUSE; an earlier revision of this note was wrong
   twice, and the second error would have misled a reader following it as a
   rule.  It is NOT [Program]: the same definition with a VARIABLE source
   instead of [SetsOne] stays polymorphic under [Program]
   ([∀ {X Y : obj[Sets@{u0 u}]}], measured), and a plain [Definition] with no
   [Program] anywhere is pinned identically once its [proper_morphism] is
   [reflexive_proper _].  And it is NOT that "supplying [proper_morphism]
   explicitly as a term" suffices -- that claim is FALSE, since
   [reflexive_proper (fun _ => x)] is such a term and is pinned; what matters
   is supplying THAT PARTICULAR pointwise term.  Nor is it [Universe
   Minimization ToSet], which changes nothing in either position: the pin
   appears with the flag off (its state from Lib.v) and is byte-identical
   with it on.  [reflexive_proper] itself is innocent, carrying an empty
   constraint set; [Set] is chosen when the [Reflexive] instance is resolved
   for [SetsOne]'s equivalence.  That last step is read off the elaborated
   term rather than separately proved, and is stated as the diagnosis it
   is. *)

Definition global_element {X : Sets} (x : X) : SetsOne ~{Sets}~> X :=
  {| morphism := fun _ => x ; proper_morphism := fun a b _ => reflexivity x |}.

(* The element is recovered on the nose, by conversion. *)
Lemma global_element_at {X : Sets} (x : X) : global_element x ttt = x.
Proof. reflexivity. Qed.

Definition GlobalElements (X : Sets) : Sets :=
  {| carrier := SetsOne ~{Sets}~> X |}.

Definition global_elements_to (X : Sets) : GlobalElements X ~{Sets}~> X :=
  {| morphism := fun f : SetsOne ~{Sets}~> X => f ttt ;
     proper_morphism := fun f g H => H ttt |}.

Definition global_elements_from (X : Sets) : X ~{Sets}~> GlobalElements X :=
  {| morphism := @global_element X ; proper_morphism := fun x y H _ => H |}.

(* Hom(1, X) ≅ X in [Sets]: the global-elements lemma.  One leg is the
   identity on the underlying element by [eq_refl] ([global_element_at]); the
   other needs the singleton's [ttt] to be its only inhabitant, which is the
   [destruct] below. *)
Definition global_elements_iso (X : Sets)
  : @Isomorphism Sets (GlobalElements X) X.
Proof.
  unshelve refine {| to := global_elements_to X; from := global_elements_from X |}.
  - intro x; reflexivity.
  - intros f u; destruct u; reflexivity.
Defined.

Section UniversalElement.

Context {D : Category}.

(** ** The elementary definition *)

(* Mac Lane's clause, with the object r a PARAMETER -- the idiom of
   [AUniversalArrow] (Theory/Universal/Arrow.v), and the shape every
   comparison below needs, since both [representability_by_yoneda] and
   [AUniversalArrow] fix their object.  [d] and [x] are EXPLICIT, unlike
   [AUniversalArrow]'s implicit [{d} {f}]: a deliberate deviation, since
   every use site below supplies both and the implicit form forces the
   [@]-spelling throughout. *)
Class AUniversalElement (H : D ⟶ Sets) (r : D) := {
  aue_elem : H r ;                             (* Mac Lane's e ∈ H r *)
  aue_universal (d : D) (x : H d) :            (* (H k) e ≈ x for a unique k *)
    Unique (fun k : r ~{D}~> d => fmap[H] k aue_elem ≈ x)
}.

(* Two universal elements at the same object are equivalent when their
   underlying elements agree; the factorization data carries nothing
   further.  This mirrors [AUniversalArrowEquiv] exactly. *)
#[export] Program Instance AUniversalElementEquiv (H : D ⟶ Sets) (r : D) :
  Setoid (AUniversalElement H r) :=
  {| equiv := fun X Y => @aue_elem H r X ≈ @aue_elem H r Y |}.

(* Mac Lane's pair ⟨r, e⟩ proper, with the object a FIELD -- the idiom of
   [Representable] (Functor/Representable.v), which bundles [repr_obj] the
   same way.  There is no setoid on this one: comparing two universal
   elements at DIFFERENT objects is not an equation but the isomorphism
   [universal_element_iso] below. *)
Class UniversalElement (H : D ⟶ Sets) := {
  ue_obj : D ;
  ue_elem : H ue_obj ;
  ue_universal (d : D) (x : H d) :
    Unique (fun k : ue_obj ~{D}~> d => fmap[H] k ue_elem ≈ x)
}.

(* The two encodings pass into one another by copying fields. *)
Definition AUniversalElement_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : AUniversalElement H (@ue_obj H U) :=
  {| aue_elem := @ue_elem H U ; aue_universal := @ue_universal H U |}.

Definition UniversalElement_of_AUniversalElement {H : D ⟶ Sets} {r : D}
  (U : AUniversalElement H r) : UniversalElement H :=
  {| ue_obj := r ; ue_elem := @aue_elem H r U ;
     ue_universal := @aue_universal H r U |}.

(* Both round trips are [eq_refl] ON THE WHOLE RECORD -- not merely on the
   element -- because the fields are copied verbatim and primitive
   projections give record eta.  Contrast the Yoneda passage below, where
   only the element survives. *)
Corollary aue_of_ue_of_aue {H : D ⟶ Sets} {r : D} (U : AUniversalElement H r) :
  AUniversalElement_of_UniversalElement (UniversalElement_of_AUniversalElement U)
    = U.
Proof. reflexivity. Qed.

Corollary ue_of_aue_of_ue {H : D ⟶ Sets} (U : UniversalElement H) :
  UniversalElement_of_AUniversalElement (AUniversalElement_of_UniversalElement U)
    = U.
Proof. reflexivity. Qed.

(** ** The Yoneda mate *)

(* The natural transformation [Hom r,─] ⟹ H determined by an element x of
   H r: its component at d carries k : r ~> d to (H k) x.  It is supplied by
   INSTANTIATING the presheaf Yoneda lemma at D^op rather than by using
   [Covariant_Yoneda_Lemma], for one reason: [representability_by_yoneda]
   below is stated with [Yoneda_Lemma C F c], and deliverable 2 composes with
   it, so the mate must be that term.  The instantiation is free --
   (D^op)^op IS D and [Curried_CoHom (D^op) r] IS [Curried_Hom D r], both by
   conversion (Construction/Opposite.v, Functor/Hom.v:146) -- so no [op]
   appears in the type. *)
Definition ue_mate (H : D ⟶ Sets) (r : D) (x : H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  from (Yoneda_Lemma (D^op) H r) x.

(* Its action, by conversion: this is the [(H k) e] of Mac Lane's clause. *)
Lemma ue_mate_at (H : D ⟶ Sets) (r : D) (x : H r) (d : D) (k : r ~{D}~> d) :
  transform (ue_mate H r x) d k = fmap[H] k x.
Proof. reflexivity. Qed.

(* The covariant Yoneda lemma gives the same mate -- but only up to `≈`, not
   by [eq_refl].  The two instances are separate [Program Instance]s whose
   naturality obligations are distinct opaque constants, so the two
   transformations are distinct TERMS with convertible actions;
   Test/ProbeUniversalElement.v pins the negative side.  Nothing below uses
   this lemma; it is here so that a reader reaching for the covariant lemma
   knows what is and is not available. *)
Lemma ue_mate_covariant (H : D ⟶ Sets) (r : D) (x : H r) :
  from (Covariant_Yoneda_Lemma D H r) x ≈ ue_mate H r x.
Proof. intros d k; reflexivity. Qed.

Section MateIso.

Context (H : D ⟶ Sets).
Context (r : D).

(* From a universal element, the inverse of its mate: the component at d
   sends x to the unique k factoring it.  Respectfulness and both naturality
   squares are uniqueness arguments, and nothing else. *)
Program Definition aue_inverse (U : AUniversalElement H r)
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  {| transform := fun d => {| morphism := fun x => unique_obj (aue_universal d x) |} |}.
Next Obligation.
  proper.
  symmetry.
  apply (uniqueness (aue_universal d y)).
  transitivity x; [ apply (unique_property (aue_universal d x)) | exact X ].
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.
Next Obligation.
  simpl; intros.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.

(* ... hence the mate of a universal element is invertible.  The two inverse
   laws are [unique_property] and [uniqueness] respectively; the [fmap_id]
   and [id_left] residues are the identity of the functor category
   [D, Sets] unfolding. *)
Program Definition aue_mate_IsIso (U : AUniversalElement H r)
  : IsIsomorphism (ue_mate H r (@aue_elem H r U)) :=
  {| two_sided_inverse := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity (unique_obj (aue_universal x (fmap[H] x0 (@aue_elem H r U)))).
  - reflexivity.
  - transitivity x0.
    + apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
    + symmetry; apply id_left.
Qed.

Definition ue_unmate (x : H r) (I : IsIsomorphism (ue_mate H r x))
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  @two_sided_inverse _ _ _ (ue_mate H r x) I.

(* ... and conversely, an invertible mate IS a universal element: the
   factorization is the inverse's component, its property is one inverse law
   and its uniqueness the other. *)
Program Definition AUniversalElement_of_mate (x : H r)
  (I : IsIsomorphism (ue_mate H r x)) : AUniversalElement H r :=
  {| aue_elem := x ;
     aue_universal := fun d y =>
       {| unique_obj := transform (ue_unmate x I) d y |} |}.
Next Obligation.
  transitivity (fmap[H] id{D} y).
  - exact (@is_right_inverse _ _ _ (ue_mate H r x) I d y).
  - exact (@fmap_id _ _ H d y).
Qed.
Next Obligation.
  transitivity (transform (ue_unmate x I) d (fmap[H] v x)).
  - apply proper_morphism; symmetry; exact X.
  - transitivity (id{D} ∘ v).
    + exact (@is_left_inverse _ _ _ (ue_mate H r x) I d v).
    + apply id_left.
Qed.

(** ** The representation, built directly *)

(* [ue_mate] is the Yoneda mate and is what deliverable 2 must be stated
   against; but it inherits a UNIVERSE CONSTRAINT from its donor that a
   consumer should not have to pay.  [Yoneda_Lemma], and hence
   [representability_by_yoneda], is stated over `C : Category@{u0 u0 u0}` --
   object, hom and proof universes all IDENTIFIED (measured, not assumed) --
   so neither can be instantiated at a category whose objects sit strictly
   above its homs.  [Instance/Coq/Nat.v]'s [Endos] is exactly such a
   category, so the entire Yoneda route is unavailable there.

   The same transformation built by hand is not so constrained: its component
   at d carries k to (H k) e, which is the action of [ue_mate] BY CONVERSION
   ([ue_mate_is_transform] below records it), but the term mentions no
   Yoneda lemma.  Everything the accessors need is therefore routed through
   these three definitions, and only [universal_element_yoneda] and
   [universal_element_representation] -- the deliverable-2 statements
   proper -- carry the constraint.  Theory/Universal/Element/Examples.v is
   the payoff: it instantiates at [Endos], which the Yoneda route cannot
   reach. *)

Program Definition ue_transform (U : AUniversalElement H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  {| transform := fun d =>
       {| morphism := fun k => fmap[H] k (@aue_elem H r U) |} |}.
Next Obligation.
  proper.
  exact (@fmap_respects _ _ H _ _ x y X (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.

(* The Yoneda mate IS this transformation, pointwise by [reflexivity] -- but
   NOT as a term: the two records carry different naturality proofs.  This is
   the same seam as [ue_mate_covariant]. *)
Lemma ue_mate_is_transform (U : AUniversalElement H r) :
  ue_mate H r (@aue_elem H r U) ≈ ue_transform U.
Proof. intros d k; reflexivity. Qed.

Program Definition ue_representation (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H :=
  {| to := ue_transform U ; from := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
  - symmetry; apply id_left.
Qed.

(* ... and back, without Yoneda: the factorization is the inverse's
   component.  The Yoneda computation Mac Lane invokes -- that Φ sends an
   arrow to the image of the universal element under it -- is run here as the
   naturality of [to Phi] evaluated at the identity, which is
   Instance/Coq/Nat.v's [repr_eval] generalized off its one functor. *)
Lemma repr_eval (Phi : @Curried_Hom D r ≅[[D, Sets]] H) {d : D}
      (k : r ~{D}~> d) :
  fmap[H] k (transform (to Phi) r id{D}) ≈ transform (to Phi) d k.
Proof.
  transitivity (transform (to Phi) d (k ∘ id{D})).
  - exact (naturality (to Phi) r d k id{D}).
  - apply proper_morphism, id_right.
Qed.

Program Definition AUniversalElement_of_repr
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r :=
  {| aue_elem := transform (to Phi) r id{D} ;
     aue_universal := fun d x =>
       {| unique_obj := transform (from Phi) d x |} |}.
Next Obligation.
  transitivity (transform (to Phi) d (transform (from Phi) d x)).
  - apply repr_eval.
  - transitivity (fmap[H] id{D} x).
    + exact (iso_to_from Phi d x).
    + exact (@fmap_id _ _ H d x).
Qed.
Next Obligation.
  transitivity (transform (from Phi) d (transform (to Phi) d v)).
  - apply proper_morphism.
    transitivity (fmap[H] v (transform (to Phi) r id{D})).
    + symmetry; exact X.
    + apply repr_eval.
  - transitivity (id{D} ∘ v).
    + exact (iso_from_to Phi d v).
    + apply id_left.
Qed.

(** ** Deliverable 2: the two encodings, as an isomorphism of setoids *)

(* The anonymous sigma setoid [representability_by_yoneda] uses, named. *)
Definition ue_yoneda_obj : SetoidObject :=
  {| carrier := { x : H r & IsIsomorphism (ue_mate H r x) } |}.

(* ... and the check that naming it changed nothing: [representability_by_yoneda]
   at D^op has EXACTLY this setoid as its source, [exists_setoid] instance
   included.  [Defined]-free: the ascription is the whole content. *)
Definition rby_agrees : @Isomorphism Sets ue_yoneda_obj
  (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := representability_by_yoneda (D^op) H r.

Program Definition ue_to_yoneda
  : Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r)
      ~{Sets}~> ue_yoneda_obj :=
  {| morphism := fun U => (@aue_elem H r U; aue_mate_IsIso U) |}.

Program Definition ue_of_yoneda
  : ue_yoneda_obj ~{Sets}~>
      Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r) :=
  {| morphism := fun p => AUniversalElement_of_mate (`1 p) (`2 p) |}.

(* THE STATEMENT, and it is an isomorphism in [Sets] -- of SETOIDS.  Not a
   biconditional (which would forget the maps), and not merely a pair of
   mutually inverse maps up to `≈` (which would forget respectfulness).  The
   two setoids compare only the underlying element and the first projection
   respectively, so what the two round-trip laws say is that the ELEMENT
   survives both passages; that they say it by [eq_refl] rather than by a
   proof is recorded immediately below. *)
Program Definition universal_element_yoneda
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      ue_yoneda_obj :=
  {| to := ue_to_yoneda ; from := ue_of_yoneda |}.

Corollary ue_yoneda_round_elem (x : H r) (I : IsIsomorphism (ue_mate H r x)) :
  `1 (ue_to_yoneda (ue_of_yoneda (x; I))) = x.
Proof. reflexivity. Qed.

Corollary ue_yoneda_round_ue (U : AUniversalElement H r) :
  @aue_elem H r (ue_of_yoneda (ue_to_yoneda U)) = @aue_elem H r U.
Proof. reflexivity. Qed.

(* Composing with [representability_by_yoneda]: a universal element of H at r
   is the same data as a representation of H by r.  This is the theorem
   [Functor/Representable.v]'s header states in prose ("by the Yoneda lemma
   such a Φ is determined by a single universal element") and that
   [Structure/UniversalProperty.v] proved only for the anonymous encoding. *)
Definition universal_element_representation
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := iso_compose (representability_by_yoneda (D^op) H r) universal_element_yoneda.

Definition representation_of_universal_element (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H
  := to universal_element_representation U.

Definition universal_element_of_representation
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r
  := from universal_element_representation Phi.

(* The universal element read off a representation is Mac Lane's Φ_r(id r) --
   the image of the identity -- by conversion, for every H, r and Φ.

   BUT DO NOT READ THIS AS THE GENERAL FORM OF Instance/Coq/Nat.v's
   [nat_universal_element].  It is not, and the reason is this file's own
   headline finding read back on itself: [universal_element_of_representation]
   goes through the Yoneda route, so this lemma inherits the donor's universe
   identification -- [About] reports the constraint [u = u0] -- and it is
   therefore NOT instantiable at [Endos], which is the only category
   Nat.v's check lives in.  The statement that does generalize
   [nat_universal_element], and the one Theory/Universal/Element/Examples.v
   actually uses, is [ue_of_repr_elem] below, stated over the DIRECT route
   with the object universe free of the hom universe.  So this lemma is a
   second instance of the restriction rather than an escape from it. *)
Lemma universal_element_of_representation_at
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = transform (to Phi) r id{D}.
Proof. reflexivity. Qed.

(* THE TWO ROUTES AGREE.  The Yoneda-composed accessors and the direct ones
   are not the same TERMS -- the Yoneda route goes through
   [representability_by_yoneda]'s [Defined] proof -- but they carry the same
   data: the same universal element, by [eq_refl], and representations that
   agree pointwise.  So nothing is lost by taking the direct route
   downstream, which is what [UniversalElement_of_Representable] does. *)
Corollary routes_agree_elem (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = @aue_elem H r (AUniversalElement_of_repr Phi).
Proof. reflexivity. Qed.

Corollary routes_agree_repr (U : AUniversalElement H r) :
  to (representation_of_universal_element U) ≈ to (ue_representation U).
Proof. intros d k; reflexivity. Qed.

End MateIso.

(** ** The bundled form and [Representable] *)

(* [Functor/Representable.v]'s [Representable] bundles exactly [ue_obj] plus
   the natural isomorphism, so it is the SAME notion as [UniversalElement],
   not a competing one -- and the two pass into one another through
   [universal_element_representation] with the representing object kept on the
   nose.  That file's header says "by the Yoneda lemma such a Φ is determined
   by a single universal element of F(A), namely Φ_A(id A)" and cites
   Structure/UniversalProperty.v for it; the citation was to the anonymous
   encoding, and these two definitions are the statement in the form the
   sentence promises.

   Both are routed through the DIRECT constructions, not through
   [universal_element_representation], so that they inherit no universe
   constraint from [Yoneda_Lemma] and remain usable at categories whose
   objects sit strictly above their homs.  [routes_agree_elem] and
   [routes_agree_repr] record that the choice costs nothing. *)

Definition UniversalElement_of_Representable {H : D ⟶ Sets}
  (R : Representable H) : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_repr H (@repr_obj _ _ R) (@represented _ _ R)).

Definition Representable_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : Representable H :=
  {| repr_obj := @ue_obj H U ;
     represented := ue_representation H (@ue_obj H U)
                      (AUniversalElement_of_UniversalElement U) |}.

Corollary ue_of_repr_obj {H : D ⟶ Sets} (R : Representable H) :
  @ue_obj H (UniversalElement_of_Representable R) = @repr_obj _ _ R.
Proof. reflexivity. Qed.

Corollary repr_of_ue_obj {H : D ⟶ Sets} (U : UniversalElement H) :
  @repr_obj _ _ (Representable_of_UniversalElement U) = @ue_obj H U.
Proof. reflexivity. Qed.

(* Mac Lane's Φ_r(id r), for the bundled form. *)
Corollary ue_of_repr_elem {H : D ⟶ Sets} (R : Representable H) :
  @ue_elem H (UniversalElement_of_Representable R)
    = transform (to (@represented _ _ R)) (@repr_obj _ _ R) id{D}.
Proof. reflexivity. Qed.

(** ** Uniqueness up to a unique isomorphism *)

(* Mac Lane's Proposition 1 of §III.1 for this notion, mirroring
   [auniversal_arrow_unique] (Theory/Universal/Arrow.v) clause for clause.
   The predicate cutting the isomorphism down is compatibility with the two
   universal elements, [fmap[H] (to i) e₁ ≈ e₂]; without it the statement
   would be false for the same reason it is false for universal arrows (the
   universal object can have automorphisms). *)

Section UniversalElementUnique.

Context {H : D ⟶ Sets}.

Definition ue_med {a b : D} (U1 : AUniversalElement H a)
           (U2 : AUniversalElement H b) : a ~{D}~> b :=
  unique_obj (@aue_universal H a U1 b (@aue_elem H b U2)).

Lemma ue_med_commutes {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) :
  fmap[H] (ue_med U1 U2) (@aue_elem H a U1) ≈ @aue_elem H b U2.
Proof.
  exact (unique_property (@aue_universal H a U1 b (@aue_elem H b U2))).
Qed.

Lemma ue_med_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (g : a ~{D}~> b) :
  fmap[H] g (@aue_elem H a U1) ≈ @aue_elem H b U2 → ue_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness (@aue_universal H a U1 b (@aue_elem H b U2)) g Hg).
Qed.

Lemma ue_med_id {a : D} (U1 : AUniversalElement H a) : ue_med U1 U1 ≈ id.
Proof.
  apply ue_med_unique.
  exact (@fmap_id _ _ H a (@aue_elem H a U1)).
Qed.

Lemma ue_med_comp {a b e : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (U3 : AUniversalElement H e) :
  ue_med U2 U3 ∘ ue_med U1 U2 ≈ ue_med U1 U3.
Proof.
  symmetry.
  apply ue_med_unique.
  transitivity (fmap[H] (ue_med U2 U3) (fmap[H] (ue_med U1 U2) (@aue_elem H a U1))).
  - exact (@fmap_comp _ _ H _ _ _ (ue_med U2 U3) (ue_med U1 U2) (@aue_elem H a U1)).
  - transitivity (fmap[H] (ue_med U2 U3) (@aue_elem H b U2)).
    + apply proper_morphism, ue_med_commutes.
    + apply ue_med_commutes.
Qed.

Program Definition universal_element_iso {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) : a ≅ b := {|
  to   := ue_med U1 U2;
  from := ue_med U2 U1
|}.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.

Lemma universal_element_iso_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (v : a ≅ b) :
  fmap[H] (to v) (@aue_elem H a U1) ≈ @aue_elem H b U2 →
  universal_element_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply ue_med_unique.
Qed.

Program Definition universal_element_unique {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) :
  Unique (fun i : a ≅ b =>
            fmap[H] (to i) (@aue_elem H a U1) ≈ @aue_elem H b U2) := {|
  unique_obj      := universal_element_iso U1 U2;
  unique_property := ue_med_commutes U1 U2
|}.
Next Obligation. exact (universal_element_iso_unique U1 U2 v X). Qed.

End UniversalElementUnique.

(** ** Deliverable 3(a): universal elements are universal arrows from 1 *)

(* Mac Lane's Remark 3, first half.  The passage is not definitional: an
   [AUniversalArrow SetsOne H r] quantifies over MAPS f : 1 ~> H d and states
   its clause as an equation of maps, while an [AUniversalElement H r]
   quantifies over ELEMENTS x : H d and states it as an equation of elements.
   The two are interchanged by [global_element] and evaluation at [ttt], and
   the single [destruct] on [poly_unit] in each direction is the whole
   difference. *)

Section OnePoint.

Context (H : D ⟶ Sets).
Context (r : D).

Definition AUniversalElement_of_AUniversalArrow
  (U : AUniversalArrow SetsOne H r) : AUniversalElement H r.
Proof.
  unshelve econstructor.
  - exact (@universal_arrow _ _ SetsOne H r U ttt).
  - intros d x.
    unshelve eexists
      (unique_obj (@universal_arrow_universal _ _ SetsOne H r U d
                     (@global_element (fobj[H] d) x))).
    + exact (unique_property
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x)) ttt).
    + intros v Hv.
      apply (uniqueness
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x))).
      intros []; exact Hv.
Defined.

Definition AUniversalArrow_of_AUniversalElement
  (U : AUniversalElement H r) : AUniversalArrow SetsOne H r.
Proof.
  unshelve econstructor.
  - exact (@global_element (fobj[H] r) (@aue_elem H r U)).
  - intros d f.
    unshelve eexists (unique_obj (aue_universal d (f ttt))).
    + intros []; exact (unique_property (aue_universal d (f ttt))).
    + intros v Hv.
      apply (uniqueness (aue_universal d (f ttt))).
      exact (Hv ttt).
Defined.

(* Both passages keep the datum on the nose. *)
Corollary aue_of_aua_elem (U : AUniversalArrow SetsOne H r) :
  @aue_elem H r (AUniversalElement_of_AUniversalArrow U)
    = @universal_arrow _ _ SetsOne H r U ttt.
Proof. reflexivity. Qed.

Corollary aua_of_aue_arrow (U : AUniversalElement H r) :
  @universal_arrow _ _ SetsOne H r (AUniversalArrow_of_AUniversalElement U)
    = @global_element (fobj[H] r) (@aue_elem H r U).
Proof. reflexivity. Qed.

(* ... and so the element survives the element-side round trip by [eq_refl],
   while the arrow survives the arrow-side one only up to `≈` -- rebuilding a
   map out of the singleton from its value at [ttt] is [global_elements_iso]'s
   non-definitional leg, and it lands here. *)
Corollary aue_aua_round (U : AUniversalElement H r) :
  @aue_elem H r
    (AUniversalElement_of_AUniversalArrow (AUniversalArrow_of_AUniversalElement U))
    = @aue_elem H r U.
Proof. reflexivity. Qed.

Corollary aua_aue_round (U : AUniversalArrow SetsOne H r) :
  @universal_arrow _ _ SetsOne H r
    (AUniversalArrow_of_AUniversalElement (AUniversalElement_of_AUniversalArrow U))
    ≈ @universal_arrow _ _ SetsOne H r U.
Proof. intros []; reflexivity. Qed.

End OnePoint.

End UniversalElement.

(** ** Deliverable 3(b): universal arrows are universal elements of D(c, S−) *)

(* Mac Lane's Remark 3, second half, and it is CHEAPER than the first.
   [fobj[Curried_Hom C] c] is the covariant hom-functor [Hom c,─], whose
   [fmap] at h is postcomposition with h; so the composite
   [Hom c,─] ◯ S : D ⟶ Sets is Mac Lane's D(c, S−), its elements at d are the
   morphisms c ~> S d, and

       fmap[[Hom c,─] ◯ S] k u   IS   fmap[S] k ∘ u

   BY CONVERSION.  Hence [AUniversalElement ([Hom c,─] ◯ S) a] and
   [AUniversalArrow c S a] have field types that are convertible one for one,
   the two passages below are [:=] with no tactic, and -- record eta being
   available under primitive projections -- both round trips are [eq_refl] on
   the WHOLE record, not merely on the arrow. *)

Section HomFunctor.

Context {C : Category}.
Context {D : Category}.
Context (S : D ⟶ C).
Context (c : C).

(* Mac Lane's D(c, S−). *)
Definition HomAfter : D ⟶ Sets := @Compose D C Sets (fobj[@Curried_Hom C] c) S.

(* The two clauses ARE the same clause. *)
Lemma hom_after_fmap (d d' : D) (k : d ~{D}~> d') (u : c ~{C}~> S d) :
  fmap[HomAfter] k u = fmap[S] k ∘ u.
Proof. reflexivity. Qed.

(* [@Build_...] rather than the `{| ... |}` literal: for a Class, the literal
   sends the elaborator looking for an instance of the head, and here it
   guesses [?H] before [HomAfter] is available to fix it. *)
Definition AUniversalElement_of_hom {a : D} (U : AUniversalArrow c S a)
  : AUniversalElement HomAfter a :=
  @Build_AUniversalElement D HomAfter a
    (@universal_arrow C D c S a U)
    (fun d x => @universal_arrow_universal C D c S a U d x).

Definition AUniversalArrow_of_hom {a : D} (U : AUniversalElement HomAfter a)
  : AUniversalArrow c S a :=
  @Build_AUniversalArrow C D c S a
    (@aue_elem D HomAfter a U)
    (fun d f => @aue_universal D HomAfter a U d f).

Corollary aue_of_hom_round {a : D} (U : AUniversalElement HomAfter a) :
  AUniversalElement_of_hom (AUniversalArrow_of_hom U) = U.
Proof. reflexivity. Qed.

Corollary aua_of_hom_round {a : D} (U : AUniversalArrow c S a) :
  AUniversalArrow_of_hom (AUniversalElement_of_hom U) = U.
Proof. reflexivity. Qed.

End HomFunctor.

(** ** The subsumption Mac Lane asserts, as one theorem *)

(* Remark 3 in full.  The tree carried neither half; stating them together is
   the point, because what Mac Lane claims is that the two notions are
   INTERDEFINABLE, and that claim is visible only when both directions sit in
   one statement.  Each component is a pair of maps, not a bijection: 3(a) is
   a bijection up to the round trips recorded above, and 3(b) is one on the
   nose. *)
Theorem universal_element_arrow_subsumption
  {C : Category} {D : Category} (S : D ⟶ C) (c : C) (H : D ⟶ Sets) (r : D) :
  (* (a) a universal element of H is a universal arrow from the one-point
         setoid to H, and conversely *)
  ((AUniversalArrow SetsOne H r → AUniversalElement H r) *
   (AUniversalElement H r → AUniversalArrow SetsOne H r))
  *
  (* (b) a universal arrow from c to S is a universal element of D(c, S−),
         and conversely *)
  ((AUniversalArrow c S r → AUniversalElement (HomAfter S c) r) *
   (AUniversalElement (HomAfter S c) r → AUniversalArrow c S r)).
Proof.
  split; split.
  - exact (AUniversalElement_of_AUniversalArrow H r).
  - exact (AUniversalArrow_of_AUniversalElement H r).
  - exact (@AUniversalElement_of_hom C D S c r).
  - exact (@AUniversalArrow_of_hom C D S c r).
Defined.

(* The two halves compose, and the composite is not vacuous: starting from a
   universal arrow ⟨a, u⟩ from c to S, reading it as a universal element of
   D(c, S−) by (b) and then back out as a universal arrow from the SINGLETON
   to that functor by (a) returns the same underlying morphism, up to the
   evaluation [global_element] performs.  This is the round trip that only
   exists once both halves are present. *)
Corollary subsumption_composite {C D : Category} (S : D ⟶ C) (c : C) (a : D)
  (U : AUniversalArrow c S a) :
  (@universal_arrow _ _ SetsOne (HomAfter S c) a
     (AUniversalArrow_of_AUniversalElement (HomAfter S c) a
        (AUniversalElement_of_hom S c U)) ttt : c ~{C}~> fobj[S] a)
  = @universal_arrow C D c S a U.
Proof. reflexivity. Qed.
