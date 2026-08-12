Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Ens_V, the category of sets belonging to a set V *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
         §I.2 "Categories", printed p. 11 (PDF p. 21)
   nLab: https://ncatlab.org/nlab/show/category+of+sets
   nLab: https://ncatlab.org/nlab/show/full+subcategory
   nLab: https://ncatlab.org/nlab/show/type+universe

   Mac Lane's construction, as this repo's catalog summarizes it: for any set
   V of sets, Ens_V is
   the category with objects all sets X in V and arrows all functions
   f : X → Y with the usual composition; "Ens" then denotes any one of these
   categories. The point is the word ALL — the arrows carry no side condition
   whatever, so Ens_V is the FULL subcategory of the category of sets spanned by
   the members of V. What V buys is size: by choosing V one gets a category
   whose objects form a set rather than a proper class.

   Rendered type-theoretically, "a set V of sets" is a type of codes together
   with a decoding of each code into a type — a universe à la Tarski in the
   nLab's terminology, as opposed to a universe à la Russell where the codes
   *are* the types. So this file is parameterized by

       V  : Type          the codes, i.e. the members of Mac Lane's V
       El : V → Type      the decoding, i.e. "the set named by this code"

   and builds the category

       objects: the codes x : V
        arrows: x ~> y  :=  El x → El y      (ALL functions, no side condition)
     hom-setoid: f ≈ g  :=  ∀ a : El x, f a = g a
      identity: the identity function
   composition: ordinary function composition

   [EnsV_Sets] is the same construction over Instance/Sets.v instead: [El]
   decodes into [SetoidObject], an arrow is a setoid map, and two arrows are
   identified when they agree pointwise up to the codomain's own `≈`. Both are
   instances of one section, [Spanned], which spans a full subcategory of an
   arbitrary ambient category C along a family El : V → C. *)

(* How this file sits in the library, and what "recovers Coq" is measured to mean

   nLab: https://ncatlab.org/nlab/show/Grothendieck+universe
   Book: Mac Lane, CWM 2nd ed., §I.2, printed p. 11 (PDF p. 21)

   Three neighbours, and what distinguishes each.

   Instance/Ens.v is NOT this construction, despite the name. Its [Ens] has for
   objects the dependent pairs [∃ T : Type, Ensemble T] and for arrows the
   whole-carrier functions f : TA → TB satisfying ∀ x, x ∈ A ↔ f x ∈ B — that
   is, A = f⁻¹(B), membership preservation AND reflection. Its own header says
   so outright: "This file does NOT build that classical category directly."
   [EnsT], in the same file, is that idea with one carrier type fixed. (Those
   two are cited by name rather than by line, since the pointer comment this
   file's arrival adds to Instance/Ens.v moves them.) They are subobject-flavoured
   categories whose arrows are constrained; Mac Lane's Ens_V constrains nothing.
   Both files are kept, and neither construction subsumes the other.

   Instance/Coq.v:120 ([Coq]) and Instance/Sets.v:188 ([Sets]) are the
   "everything at one universe level" categories: objects are all of [Type@{o}],
   respectively all setoids at level o, and arrows are all functions,
   respectively all setoid maps. They are Ens_V with the bound fixed at a
   universe rather than at an arbitrary family — which is the set-theorist's
   Grothendieck universe (a transitive set closed under the usual operations,
   per the nLab) doing the job Mac Lane assigns to V. What this file adds is the
   arbitrary family: V may be any type at all, with no closure conditions, so a
   two-object Ens_V is as available as a universe-sized one.

   The relationship to [Coq] is measured, not asserted. At the tautological
   family (V := the objects of [Coq], El := the identity) the two categories
   are DEFINITIONALLY EQUAL: [EnsV_recovers_Coq] below is proved by [eq_refl],
   which is a conversion check on the whole [Category] record, subsuming
   agreement of every field — objects, homs, hom-setoids together with their
   [Equivalence] proofs, identity, composition, and all four laws. This is
   strictly stronger than an isomorphism in Cat. (It is not stronger than
   field-wise agreement: with definitional eta the two are equivalent.)

   The mechanism deserves a precise account, because an earlier draft got it
   wrong. For the two INSTANCE equalities below, eta is not what does the
   work: [Coq] and [Sets] are transparent constants whose bodies are literal
   records, so the check is constructor-against-constructor by delta, iota
   and beta alone. Where primitive-projection eta (Lib.v's [Primitive
   Projections]; the let-in fields [uhom], [dom], [cod] do not obstruct it on
   Rocq 9.1) becomes load-bearing is the GENERAL statement, where the ambient
   category is a variable and no delta is available:
   [Spanned_recovers_ambient] proves [@Spanned C (@obj C) (λ x, x) = C] for
   every C by the same one-line [eq_refl], and the two instance equalities
   are its corollaries. The same holds one universe over for [Sets]
   ([EnsV_Sets_recovers_Sets]). What is
   claimed is exactly what [eq_refl] checks: convertibility of the two
   [Category] values. Nothing is claimed about the two definitions' proof terms
   being syntactically the same, and the recovery is not vacuous — a family
   other than the identity is rejected by the same conversion check.

   On smallness. Mac Lane calls Ens_V a category of sets *within* a set
   precisely because its objects form a set. The corresponding in-tree fact is
   [EnsV_obj_is_V]: the object type of [EnsV El] is [V] on the nose, with no
   universe inflation and no packaging. So the size of Ens_V is exactly the size
   the caller chooses for V — [bool], a finite type, [nat], or the whole of
   [Type@{o}] — and [EnsV_two] below is a two-object witness that the small case
   is genuinely inhabited rather than vacuous. This is a remark about the shape
   of the definition, not a theorem: the library carries no internal notion of
   smallness or size, so "small" here means only "the codes are a type the
   caller picked", and nothing about cardinality is being claimed. *)

(** ** The full subcategory of C spanned by a family *)

(* nLab: https://ncatlab.org/nlab/show/full+subcategory

   Given any category C and any family El : V → C of its objects, [Spanned] has
   V for objects and, between codes x and y, exactly the C-morphisms
   El x ~> El y. Every field is the corresponding field of C read along El, so
   every law is C's law and nothing is reproved. El is not required to be
   injective: distinct codes may decode to the same object of C, in which case
   [Spanned] carries two copies of it. This is the general shape; Mac Lane's
   Ens_V is the case C = [Coq], and its setoid counterpart the case C = [Sets].

   The section is self-contained and does not mention [Coq] or [Sets]; should
   another development want it, it moves to Construction/ unchanged. *)

Section Spanned.

Context {C : Category}.
Context {V : Type}.
Context (El : V → C).

Definition Spanned : Category := {|
  obj     := V;                                    (* objects are the codes *)
  hom     := λ x y, El x ~> El y;                  (* ALL C-arrows between decodings *)
  homset  := λ x y, @homset C (El x) (El y);       (* C's hom-setoid, unchanged *)
  id      := λ x, @id C (El x);                    (* C's identity *)
  compose := λ x y z f g, @compose C (El x) (El y) (El z) f g;  (* C's composition *)

  compose_respects := λ x y z, @compose_respects C (El x) (El y) (El z);

  id_left  := λ x y, @id_left  C (El x) (El y);
  id_right := λ x y, @id_right C (El x) (El y);

  comp_assoc     := λ x y z w, @comp_assoc     C (El x) (El y) (El z) (El w);
  comp_assoc_sym := λ x y z w, @comp_assoc_sym C (El x) (El y) (El z) (El w)
|}.

(* The inclusion into the ambient category: decode on objects, and the identity
   on morphisms, since a [Spanned] morphism already IS a C-morphism. *)
Program Definition Spanned_Incl : Spanned ⟶ C := {|
  fobj := El;
  fmap := λ _ _ f, f
|}.

(* It is full — the chosen preimage of a C-morphism is that morphism — which is
   the formal content of "spanned by El" being a FULL subcategory. *)
#[export] Program Instance Spanned_Incl_Full : Full Spanned_Incl := {|
  prefmap := λ _ _ g, g
|}.

(* And faithful, since the hom-map is the identity function. Note that it is
   injective on objects only when El is; fullness and faithfulness are hom-level
   statements and hold for every family. *)
#[export] Program Instance Spanned_Incl_Faithful : Faithful Spanned_Incl := {|
  fmap_inj := λ _ _ _ _ H, H
|}.

End Spanned.

(** ** Ens_V over [Coq]: objects are codes, arrows are all functions *)

(* Mac Lane's Ens_V. The decoding lands in bare types, so an arrow is an
   arbitrary function and morphism equivalence is pointwise Leibniz equality,
   exactly as in Instance/Coq.v:120. *)
Definition EnsV {V : Type} (El : V → Type) : Category := @Spanned Coq V El.

(* The inclusion Ens_V ⟶ Set, full and faithful by the section above. *)
Definition EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  @Spanned_Incl Coq V El.

(* Statement fidelity, checked by conversion rather than argued.

   Objects are the members of V on the nose. *)
Definition EnsV_obj_is_V {V : Type} (El : V → Type) : @obj (EnsV El) = V := eq_refl.

(* Arrows from x to y are ALL functions El x → El y: the right-hand side is the
   bare function type, carrying no membership condition and no other side
   condition. This is the clause the issue's reviewer note singles out. *)
Definition EnsV_hom_is_all_functions {V : Type} (El : V → Type) (x y : V) :
  @hom (EnsV El) x y = (El x → El y) := eq_refl.

(* Two arrows are identified exactly when they agree pointwise. *)
Definition EnsV_equiv_is_pointwise {V : Type} (El : V → Type) (x y : V)
           (f g : @hom (EnsV El) x y) :
  (f ≈ g) = (∀ a : El x, f a = g a) := eq_refl.

(* Identity and composition are "the usual" ones, in Mac Lane's phrase. *)
Definition EnsV_id_is_identity {V : Type} (El : V → Type) (x : V) (a : El x) :
  @id (EnsV El) x a = a := eq_refl.

Definition EnsV_compose_is_usual {V : Type} (El : V → Type) (x y z : V)
           (f : @hom (EnsV El) y z) (g : @hom (EnsV El) x y) (a : El x) :
  (f ∘ g) a = f (g a) := eq_refl.

(** ** Ens_V over [Sets]: the setoid-flavoured variant *)

(* The same construction with the decoding landing in setoids. An arrow is a
   setoid map (a function together with its respectfulness certificate) and two
   arrows agree when they are pointwise `≈`-equal, exactly as in
   Instance/Sets.v:188. This variant is the one to use when Ens_V must serve as
   the codomain of a hom-functor or otherwise interact with the library's
   setoid-enriched machinery; the [Coq]-flavoured one above is the literal
   reading of Mac Lane, where a set is a bare type and equality of elements is
   Leibniz equality. *)
Definition EnsV_Sets {V : Type} (El : V → SetoidObject) : Category :=
  @Spanned Sets V El.

Definition EnsV_Sets_Incl {V : Type} (El : V → SetoidObject) : EnsV_Sets El ⟶ Sets :=
  @Spanned_Incl Sets V El.

Definition EnsV_Sets_obj_is_V {V : Type} (El : V → SetoidObject) :
  @obj (EnsV_Sets El) = V := eq_refl.

(* Arrows are ALL setoid maps between the decodings — again no side condition
   beyond the respectfulness that being a morphism of [Sets] already means. *)
Definition EnsV_Sets_hom_is_all_setoid_maps {V : Type} (El : V → SetoidObject)
           (x y : V) :
  @hom (EnsV_Sets El) x y = SetoidMorphism (El x) (El y) := eq_refl.

Definition EnsV_Sets_equiv_is_pointwise {V : Type} (El : V → SetoidObject)
           (x y : V) (f g : @hom (EnsV_Sets El) x y) :
  (f ≈ g) = (∀ a : El x, f a ≈ g a) := eq_refl.

(** ** The tautological family recovers the ambient category *)

(* At V := the objects of [Coq] and El := the identity family, [EnsV] IS [Coq]:
   the two [Category] records are convertible, so [eq_refl] typechecks. Every
   field agrees definitionally — including the hom-setoids with their
   [Equivalence] proofs and all four category laws — because [Spanned] never
   builds a field, it only reads one off the ambient category.

   The measured strength is therefore definitional equality of the two
   categories, which is strictly stronger than an isomorphism in Cat and
   equivalent (under eta) to field-wise agreement: any statement whatever about
   [Coq] transports to [EnsV (λ T : Type, T)] by conversion alone. *)
(* The general form, for ANY ambient category: spanning C by its own objects
   along the identity family gives back C on the nose.  This is the statement
   for which definitional eta on [Category] is genuinely load-bearing -- C is
   a variable here, so no delta unfolding is available and the conversion
   must go record-against-eta-expansion.  The two named recoveries below are
   its instances (each also checkable by delta alone, their ambients being
   transparent constants). *)
Definition Spanned_recovers_ambient {C : Category} :
  @Spanned C (@obj C) (λ x, x) = C := eq_refl.

Definition EnsV_recovers_Coq : EnsV (λ T : Type, T) = Coq := eq_refl.

(* The same one universe over, for the setoid-flavoured variant and [Sets]. *)
Definition EnsV_Sets_recovers_Sets :
  EnsV_Sets (λ X : SetoidObject, X) = Sets := eq_refl.

(** ** A small Ens_V *)

(* Mac Lane's V is a SET of sets, and the interesting case is the one his
   notation is for: V small. Here is the two-member case, V = {1, 2}, a category
   with exactly two objects whose homs are honest function types. Its object
   type is [bool] and nothing has been enlarged, which is the whole content of
   the smallness remark in the header. *)
Definition EnsV_two_family (b : bool) : Type := if b then unit else bool.

Definition EnsV_two : Category := EnsV EnsV_two_family.

Definition EnsV_two_obj : @obj EnsV_two = bool := eq_refl.

(* The arrows from the one-element member to the two-element member are all
   functions unit → bool, and back again all functions bool → unit. *)
Definition EnsV_two_hom_up : @hom EnsV_two true false = (unit → bool) := eq_refl.

Definition EnsV_two_hom_down : @hom EnsV_two false true = (bool → unit) := eq_refl.
