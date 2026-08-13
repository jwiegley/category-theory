Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** The category of elements of a Sets-valued functor, and its projection. *)

(* nLab: https://ncatlab.org/nlab/show/category+of+elements
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_elements

   BOOK LOCATIONS. Recorded from the statement of issue #345: Mac Lane,
   "Categories for the Working Mathematician", III.7; Riehl, "Category
   Theory in Context", 2.4 (Definitions 2.4.1 and 2.4.2, Exercise
   2.4.ii); Awodey, "Category Theory", 8.6. Those texts were not
   consulted while writing this file. The locations are given so a
   reader can look the construction up; nothing beyond the locations is
   reproduced here, and no claim is made about the wording or numbering
   at those places.

   THE CONSTRUCTION. For K : D ⟶ Sets, an object of [Elements K] is a
   pair (d, x) with d an object of D and x an element of the setoid K d;
   a morphism (d, x) ~> (d', y) is a morphism f : d ~> d' of D that
   carries x to y, that is, [fmap[K] f x ≈ y]. The projection
   [Elements_proj] sends (d, x) to d and a morphism to its underlying
   D-morphism.

   SETOID PRESENTATION. Two different `≈` occur below and neither is
   Leibniz equality. In the hom condition [fmap[K] f x ≈ y] the `≈` is
   the equivalence of the target setoid K d': every object of Sets is a
   carrier packaged with a Setoid (Instance/Sets.v:118-121), and every
   morphism of Sets is a carrier function together with a proof that it
   respects `≈` (Instance/Sets.v:126-130). In the hom-setoid of
   [Elements] the `≈` is D's own hom equivalence. The books state the
   hom condition with an equality of elements; this file states it with
   `≈`, which is the setoid reading issue #345 asks for.

   HOM-SETOID, AND WHAT IT BUYS. [Elements] compares two morphisms by
   their underlying D-morphisms alone; the carried condition takes no
   part in the comparison. That is the encoding already in use at
   Construction/Slice.v:124-126 (sigma object, sigma hom, hom-setoid on
   the first component) and, componentwise, at Construction/Comma.v:135-
   136. One consequence is recorded here because consumers rely on it:
   faithfulness of [Elements_proj] is DEFINITIONAL rather than a theorem
   with content. The identity function typechecks as the injectivity
   proof, which [Elements_proj_faithful_definitional] exhibits, and the
   [Faithful] instance (Theory/Functor.v:342) is then discharged with
   nothing left to prove. Fullness does not hold in general and is not
   claimed: a D-morphism must carry the element to be a morphism here.

   ROUTE TAKEN. The definition below is direct: objects are literally
   the pairs. The comma presentation is related to it by a proved
   comparison instead of being taken as the definition. Two other routes
   are present in the tree and are deliberately not used.

   (1) The comma route. With the constant functor =(c) : 1 ⟶ Sets of
   Functor/Diagonal.v:55, taken at the singleton of Instance/Sets.v:253
   ([Sets_Terminal]), the comma category of Construction/Comma.v:127 has
   the same content. Its objects are triples ((ttt, d); h) in which h is
   a setoid map out of the singleton, so an element is presented as a map
   rather than as an inhabitant, and every morphism carries a contentless
   component in the terminal category 1 (the FIRST component of the
   underlying pair, in Comma.v's encoding). Taking that
   as the definition would in addition turn the comparison this file is
   asked for into a definitional identity. It is therefore introduced
   below as [ElementsComma] and compared, following the precedent of
   Construction/Slice.v:140 ([Comma_Slice]) and
   Instance/Cones/Comma.v:73 ([Cones_Comma]).

   (2) The Grothendieck route. The background essay at
   Construction/Grothendieck.v:107-110 says that restricting the fibres
   of an indexed category to sets viewed as discrete categories recovers
   the category of elements el(F). That sentence is background prose,
   not a construction, and this file does not obtain [Elements] from it.
   The obstruction sits at the coherence level. [DiscreteCat]
   (Instance/Discrete.v:37-43) has [hom := fun x y => x = y] with
   [Morphism_equality] as its hom-setoid, so a fibre [DiscreteCat (K d)]
   carries strict equality of elements. The fibre functors themselves can
   be formed from the underlying carrier maps, but the coherence cells an
   [IndexedCat] asks for would then have to be Leibniz equalities of
   elements, whereas K's functor laws supply equivalences in the fibre
   setoid. The direct route below has no such requirement.

   THE COMMA COMPARISON, STATED EXACTLY. [Elements_Comma] is an
   isomorphism in Cat, [Elements K ≅[Cat] ElementsComma]. Cat's
   hom-setoid is natural isomorphism of functors (Instance/Cat.v), so an
   isomorphism in Cat is an equivalence of categories; no statement is
   made in StrictCat, and none is intended. What is delivered concretely
   is the functor pair [Elements_to_Comma] and [Elements_from_Comma]
   together with the two natural isomorphisms. The round trip
   [Elements_from_Comma ◯ Elements_to_Comma] is the identity on objects
   and on morphisms, and its natural isomorphism has identity components.
   The other round trip is not the identity: it replaces a setoid map h
   out of the singleton by the constant map at [h ttt], and those two
   records agree pointwise up to `≈` without being the same term.
   Compatibility with the projections is recorded separately as
   [Elements_proj_comma_iso], a natural isomorphism in [[Elements K, D]]
   between [comma_proj2 ◯ Elements_to_Comma] and [Elements_proj] whose
   components are identities; the two functors agree on objects and on
   morphisms, and only the packaged proof fields differ.

   ORIENTATION, AND THE PRESHEAF READING. [Elements] as defined is the
   covariant construction: for K : D ⟶ Sets it lies over D. For a
   presheaf P : C^op ⟶ Sets the books use the other arrow orientation, in
   which a morphism (c, x) ~> (c', x') is f : c ~> c' with
   [fmap[P] f x' ≈ x]. That is [PElements P] below, the opposite
   (Construction/Opposite.v:106) of the covariant construction on C^op,
   and [PElements_hom] is a definitional check -- it holds by
   [reflexivity] -- that the hom type is exactly the one just displayed.
   The orientation is chosen so that the projection stays covariant:
   [PElements_proj] lands in C, with [fmap] the first projection and no
   transport, which typechecks because the opposite of the opposite of C
   is C (Construction/Opposite.v:126, [op_invol]).

   WORKING WITH Sets HOM EQUATIONS. [fmap_id], [fmap_comp] and
   [fmap_respects] for a functor into Sets are equations in a Sets
   hom-setoid, hence pointwise families indexed by elements
   (Instance/Sets.v:139-141). Setoid rewriting with them underneath an
   application does not apply, and [apply fmap_id] does not unify with an
   element-level goal. The three element-level readings are packaged once
   as [elements_id_cond], [elements_comp_cond] and
   [elements_respects_cond]; the first two carry every proof below
   ([elements_respects_cond] is used by none of them -- it is exported for
   consumers), and consumers should reuse all three rather than rewrite
   the functor laws in place. Note also that [=(1)] does not elaborate inside a functor type,
   because there [1] is read as the terminal category; write
   [=(1%object)], or use the named [SetsOne] below.

   NOT IN THIS FILE. The remaining items of issue #345 are listed so
   their absence is not read as an oversight. The contravariant analogue
   of the comma comparison, [PElements P ≅[Cat] (=(1) ↓ P)^op], is not
   proved here: it asks for a transport of an isomorphism in Cat along
   opposites, which no in-tree lemma supplies yet. The description of
   [lim F] as the sections of the projection needs limits of Sets-valued
   diagrams, which the tree does not have, and its section condition is a
   strict equation of functors whereas `≈` in Cat is natural
   isomorphism. The characterization of the elements category as a
   pullback in Cat waits on pullbacks in Cat (issue #337) and on the
   category of pointed sets (issue #261). The identification of [colim F]
   with the connected components of the elements category waits on issues
   #352 and #355. The discrete-opfibration predicate is owned by issues
   #809 and #948; what this file supplies is the chosen lift
   [Elements_lift] over a base morphism, the definitional check
   [Elements_lift_over] that the projection returns that base morphism,
   and faithfulness, which together are the uniqueness reading in the
   form the setoid presentation permits. *)

Section Elements.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* The functor laws of K, read at an element. A Sets hom equation is a
   pointwise family, so it must be instantiated at the element before it
   can be used as an ordinary equivalence. *)

Lemma elements_id_cond {d : D} (x : K d) : fmap[K] id x ≈ x.
Proof. exact (@fmap_id _ _ K _ x). Qed.

Lemma elements_comp_cond {c d e : D} {x : K c} {y : K d} {z : K e}
      (u : d ~> e) (v : c ~> d) :
  fmap[K] v x ≈ y → fmap[K] u y ≈ z → fmap[K] (u ∘ v) x ≈ z.
Proof.
  intros Hv Hu.
  transitivity (fmap[K] u (fmap[K] v x)).
  - exact (@fmap_comp _ _ K _ _ _ u v x).
  - now rewrite Hv.
Qed.

Lemma elements_respects_cond {c d : D} {x : K c} (f g : c ~> d) :
  f ≈ g → fmap[K] f x ≈ fmap[K] g x.
Proof. intro Hfg; exact (@fmap_respects _ _ K _ _ f g Hfg x). Qed.

(* Objects are the pairs (d, x) with x an element of the setoid K d;
   morphisms are the D-morphisms that carry the element. The hom-setoid
   looks only at the underlying D-morphism, so the carried condition is
   not compared. *)

Program Definition Elements : Category := {|
  obj := ∃ d : D, K d;
  hom := fun x y => ∃ f : `1 x ~{D}~> `1 y, fmap[K] f (`2 x) ≈ `2 y;
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. apply elements_id_cond. Qed.
Next Obligation. eapply elements_comp_cond; eassumption. Qed.

(* The projection, taking (d, x) to d and a morphism to its first
   component. *)

Program Definition Elements_proj : Elements ⟶ D := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Instance Elements_proj_Faithful : Faithful Elements_proj.

(* Faithfulness is definitional under the hom-setoid chosen above: the
   injectivity statement is the identity implication, and this witness
   records that fact for readers of the instance. *)

Definition Elements_proj_faithful_definitional
  {x y : Elements} (f g : x ~{Elements}~> y) :
  fmap[Elements_proj] f ≈ fmap[Elements_proj] g → f ≈ g :=
  fun H => H.

(* The chosen lift of a base morphism at an element, and the definitional
   check that the projection returns that base morphism. *)

Program Definition Elements_lift {d d' : D} (x : K d) (f : d ~> d') :
  ((d; x) : Elements) ~{Elements}~> (d'; fmap[K] f x) := (f; _).

Lemma Elements_lift_over {d d' : D} (x : K d) (f : d ~> d') :
  fmap[Elements_proj] (Elements_lift x f) ≈ f.
Proof. reflexivity. Qed.

(* The comma presentation. [SetsOne] is the singleton of Sets_Terminal,
   and [=(SetsOne)] is the constant functor 1 ⟶ Sets at it. *)

Definition SetsOne : Sets := @terminal_obj Sets Sets_Terminal.

Definition ElementsComma : Category := =(SetsOne) ↓ K.

Program Definition Elements_to_Comma : Elements ⟶ ElementsComma := {|
  fobj := fun x => ((ttt, `1 x); {| morphism := fun _ => `2 x |});
  fmap := fun _ _ f => ((ttt, `1 f); _)
|}.

Program Definition Elements_from_Comma : ElementsComma ⟶ Elements := {|
  fobj := fun x => (snd `1 x; `2 x ttt);
  fmap := fun _ _ f => (snd `1 f; _)
|}.

(* An isomorphism in Cat, hence an equivalence of categories: `≈` between
   functors is natural isomorphism. [Elements_from_Comma] after
   [Elements_to_Comma] is the identity on objects and on morphisms -- up to
   eta: the equation holds after destructing the object (both projections
   agree by bare reflexivity), not by reflexivity at a variable -- and its
   natural isomorphism has identity components; the other round trip
   replaces a setoid map h by the constant map at h ttt, which agrees with
   h pointwise up to `≈` and not as a term. *)

Theorem Elements_Comma : Elements ≅[Cat] ElementsComma.
Proof.
  isomorphism; simpl; intros.
  - apply Elements_to_Comma.
  - apply Elements_from_Comma.
  - constructive.
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity |
                        simpl; rewrite id_right, id_left; reflexivity]).
  - constructive.
    + exists id; abstract (apply elements_id_cond).
    + exists id; abstract (apply elements_id_cond).
    + abstract cat.
    + abstract cat.
    + abstract (simpl; rewrite id_right, id_left; reflexivity).
Qed.

End Elements.

(* Instances declared inside a section are not registered once the section
   closes; re-register so downstream files can resolve
   [Faithful (Elements_proj K)] by typeclass search rather than by name. *)
#[export] Existing Instance Elements_proj_Faithful.

(* [Category.Functor.Opposite] is not imported because nothing here needs
   it.  (An earlier draft claimed importing it would shadow the category
   [^op] notation and break the presheaf section; that was tested and is
   FALSE -- the two notations live in different scopes, category_scope and
   functor_scope, and coexist.  The import is omitted purely as unused.) *)

Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.

Section Elements_Comma_Projection.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* Compatibility of the comma comparison with the projections to D. The
   two functors agree on objects and on morphisms; only their packaged
   proof fields differ, so the statement is a natural isomorphism with
   identity components and not an equation of functors. *)

Program Definition Elements_proj_comma_iso :
  comma_proj2 ◯ Elements_to_Comma K ≅[[Elements K, D]] Elements_proj K := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

End Elements_Comma_Projection.

Section Presheaf_Elements.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* The contravariant (presheaf) orientation: the opposite of the covariant
   construction taken on C^op. Objects are still the pairs (c, x) with x
   an element of P c. *)

Definition PElements : Category := (Elements P)^op.

(* A definitional check, closed by [reflexivity]: the hom type is the one
   the presheaf orientation asks for, with the element condition running
   backwards. *)

Lemma PElements_hom (x y : PElements) :
  (x ~{PElements}~> y) = (∃ f : `1 x ~{C}~> `1 y, fmap[P] f (`2 y) ≈ `2 x).
Proof. reflexivity. Qed.

(* The projection stays covariant: it lands in C, with no transport,
   because the opposite of the opposite of C is C. *)

Program Definition PElements_proj : PElements ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

End Presheaf_Elements.
