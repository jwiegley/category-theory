Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Limits in a preorder are greatest lower bounds *)

(* nLab: https://ncatlab.org/nlab/show/preorder
   nLab: https://ncatlab.org/nlab/show/thin+category
   nLab: https://ncatlab.org/nlab/show/join
   Wikipedia: https://en.wikipedia.org/wiki/Infimum_and_supremum

   Regard a preorder [(A, R)] as the thin category [Proset P] of
   Instance/Proset.v, in which [x ~> y] is the relation [R x y] itself.
   Under that dictionary the categorical universal constructions become
   the order-theoretic ones:

     - a product   x × y   is a greatest lower bound (a meet) of x and y;
     - a terminal object   1   is a greatest element (a top);
     - a limit of a diagram is a greatest lower bound of the family of
       its objects, whatever the shape of the diagram;

   and dually coproducts are least upper bounds (joins), the initial
   object is a least element, and colimits are least upper bounds.

   CITATIONS ARE LOCATIONS ONLY.  The passages below are cited for where
   the statement is found, not paraphrased from a consulted copy; none of
   these sources was read while preparing this file, and no sentence here
   is offered as their wording. Mac Lane, "Categories for the Working
   Mathematician", 2nd ed., V.2; Awodey, "Category Theory", 2nd ed., 2.6
   and the example in 3.2; Riehl, "Category Theory in Context", 1.2, 3.1
   and 3.6; Fong and Spivak, "An Invitation to Applied Category Theory
   (Seven Sketches in Compositionality)", 3.5.1 and 6.2.

   WHAT CARRIES CONTENT, AND WHAT DEGENERATES.  [Proset P] is thin: its
   hom-setoid equivalence is the constant relation [True], by the
   construction in Instance/Proset.v ([proset_equiv_is_True] below states
   this literally and proves it by [eq_refl]). Consequently every
   requirement that is an EQUATION between parallel morphisms holds by
   [Logic.I] and constrains nothing:

     - the [Proper] obligation [fork_respects] of Structure/Cartesian.v;
     - both halves of [ump_products] there;
     - the [cone_coherence] field of Structure/Cone.v, for every shape of
       diagram — this is why the identification below holds at an
       arbitrary index category and not merely at a discrete one;
     - the commutation clause and the [uniqueness] clause of the [∃!]
       in [ump_limits] / [ump_limit] of Structure/Limit.v;
     - [one_unique] of Structure/Terminal.v.

   What carries the mathematics is exactly the DATA:

     - the apex object [m] ([product_obj], [terminal_obj], the cone
       vertex) — the candidate bound;
     - the leg family ([exl], [exr], [vertex_map], [iprod_proj]) — the
       lower-bound clause of [IsGLB];
     - the mediating arrow ([fork], the [unique_obj] of the [∃!]) — the
       greatest clause of [IsGLB].

   So "limit = greatest lower bound" is an identification of data, with
   the proof obligations on both sides degenerate. Following the same
   discipline, this file does not leave that observation unguarded:
   [nat_glb_not_4] refutes an [IsGLB] claim over a concrete preorder, and
   [discrete_two_no_initial] and [discrete_two_no_cartesian] exhibit a
   preorder that has neither a least element nor binary meets. The
   predicates are therefore not uniformly inhabited, and the theorems
   above are not statements about an empty distinction.

   COORDINATION WITH ADJACENT WORK.  Two neighbouring developments touch
   the same vocabulary, and this file is written to stay clear of both.
   (i) A Galois-connection development for a preorder (issue #380)
   introduces a [Thin] predicate with [proset_thin] and companion lemmas
   in a separate Instance/Proset/ module. This file deliberately
   introduces no such predicate and does not require that module:
   wherever thinness is needed it is used concretely, as the fact that
   the hom-setoid of [Proset P] is the constant-[True] setoid.
   (ii) Order-theoretic vocabulary proper — meet- and join-semilattices,
   lattices, Heyting and Boolean algebras — is claimed by a separate
   Structure/Lattice.v effort (issues #340, #389, #1003). This file
   therefore defines no [Meet], [Join], [Lattice] or [BooleanAlgebra]
   class and creates no such module: [IsGLB] and [IsLUB] below are
   family-level PREDICATES over a bare [PreOrder], not an algebraic
   structure, and the four constructors [Proset_Cartesian],
   [Proset_Cocartesian], [Proset_Terminal] and [Proset_Initial] are
   exactly the interface such a class would later consume. *)

(** ** Bounds over a preorder *)

(* [R] is kept explicit in the bound predicates: it does not occur in the
   types of [d] or [m], so an implicit binder would be unresolvable at
   the use sites. Families are indexed by an arbitrary [Type]; the
   library carries no subset machinery, so "every subset has an
   infimum" is modelled throughout as "every [Type]-indexed family has
   a greatest lower bound". *)

(* [m] is a lower bound of the family [d]. *)
Definition IsLowerBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  ∀ i : Ix, R m (d i).

(* [m] is a greatest lower bound (an infimum, a meet) of [d]: a lower
   bound that every other lower bound precedes. *)
Definition IsGLB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  IsLowerBound R d m * (∀ n : A, IsLowerBound R d n → R n m).

(* The reversed preorder. Upper bounds and least upper bounds are the
   lower bounds and greatest lower bounds of it — definitionally, so
   that every dual statement below is the original one read at
   [op_rel R] and no dual proof is written twice. *)
Definition op_rel {A : Type} (R : relation A) : relation A :=
  fun x y => R y x.

Definition op_PreOrder {A : Type} {R : relation A} (P : PreOrder R) :
  PreOrder (op_rel R) :=
  {| PreOrder_Reflexive := fun x => @PreOrder_Reflexive A R P x;
     PreOrder_Transitive :=
       fun x y z Hxy Hyz => @PreOrder_Transitive A R P z y x Hyz Hxy |}.

Definition IsUpperBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsLowerBound (op_rel R) d m.

Definition IsLUB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsGLB (op_rel R) d m.

(* Uniqueness of an infimum, and of a supremum. Without antisymmetry the
   sharpest available conclusion is mutual precedence, which is exactly
   isomorphism of the two apexes in [Proset P]; over a poset
   (Instance/Poset.v, where [Poset P] is [Proset P] with an
   antisymmetry constraint) it upgrades to equality by antisymmetry.

   The supremum statement is obtained by reading the infimum statement
   at the reversed preorder, since [IsLUB R] is by definition
   [IsGLB (op_rel R)]: [lub_unique] below is literally [glb_unique]
   applied to [op_rel R], with no second argument. That is the
   duality-respecting formulation, in which the dual proof establishes
   the dual result rather than a fresh proof being written. *)
Definition glb_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsGLB R d m) (G' : IsGLB R d m') :
  R m m' * R m' m :=
  (snd G' m (fst G), snd G m' (fst G')).

Definition lub_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsLUB R d m) (G' : IsLUB R d m') :
  R m' m * R m m' :=
  glb_unique (op_rel R) d m m' G G'.

(* The binary family, used to read a two-element meet as a product. *)
Definition pair_family {A : Type} (x y : A) : bool → A :=
  fun b => if b then x else y.

(* The empty family, used to read a greatest element as the nullary
   meet. A greatest element is exactly a greatest lower bound of it,
   matching the fact that the terminal object is the limit of the empty
   diagram; the least/supremum form is the same statement at the
   reversed preorder, with no second proof. *)
Definition empty_family {A : Type} : False → A := fun e => match e with end.

Lemma greatest_iff_empty_glb {A : Type} (R : relation A) (top : A) :
  (∀ x, R x top) ↔ IsGLB R (@empty_family A) top.
Proof.
  split.
  - intro Htop; split; [ intros [] | intros n _; exact (Htop n) ].
  - intros [_ Hg] x; exact (Hg x (fun e => match e with end)).
Qed.

Definition least_iff_empty_lub {A : Type} (R : relation A) (bot : A) :
  (∀ x, R bot x) ↔ IsLUB R (@empty_family A) bot :=
  greatest_iff_empty_glb (op_rel R) bot.

(* Completeness of the order, in the form the bicompleteness statement
   consumes below. *)
Definition HasAllMeets {A : Type} (R : relation A) : Type :=
  ∀ (Ix : Type) (d : Ix → A), { m : A & IsGLB R d m }.

Definition HasAllJoins {A : Type} (R : relation A) : Type :=
  HasAllMeets (op_rel R).

Section Proset_Limits.

Context {A : Type} {R : relation A} (P : PreOrder R).

(** ** Thinness, stated concretely *)

(* Every equivalence of parallel morphisms in [Proset P] is the
   proposition [True], by construction of the hom-setoid in
   Instance/Proset.v. This is the one fact about thinness this file
   uses, and it holds by [eq_refl]. No [Thin] predicate is introduced;
   see the coordination note in the header. *)
Lemma proset_equiv_is_True (x y : A) (f g : x ~{Proset P}~> y) :
  (f ≈ g) = True.
Proof. reflexivity. Qed.

(** ** Binary products are meets *)

(* Structure ⇒ order: the chosen product object of a cartesian structure
   on [Proset P] is a greatest lower bound of its two factors. The two
   projections ARE the lower-bound clause and [fork] IS the greatest
   clause; each bullet below is a projection of the class, not a
   proof step. *)
Lemma cartesian_product_IsGLB (CP : @Cartesian (Proset P)) (x y : A) :
  IsGLB R (pair_family x y) (@product_obj (Proset P) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl (Proset P) CP x y).
    + exact (@exr (Proset P) CP x y).
  - intros n Hn.
    exact (@fork (Proset P) CP n x y (Hn true) (Hn false)).
Qed.

(* Order ⇒ structure: a choice of binary meets equips [Proset P] with a
   cartesian structure. Both law fields are equations between parallel
   morphisms of a thin category, so the global obligation tactic
   discharges them and the whole mathematical content is the data
   supplied here. *)
Program Definition Proset_Cartesian
  (glb : A → A → A)
  (glb_l : ∀ x y, R (glb x y) x)
  (glb_r : ∀ x y, R (glb x y) y)
  (glb_greatest : ∀ n x y, R n x → R n y → R n (glb x y)) :
  @Cartesian (Proset P) := {|
  product_obj := glb;
  fork := fun x y z f g => glb_greatest x y z f g;
  exl := fun x y => glb_l x y;
  exr := fun x y => glb_r x y
|}.

(* Dually, a choice of binary joins equips [Proset P] with a cocartesian
   structure. Recall from Structure/Cocartesian.v that [Cocartesian C]
   is notation for [@Cartesian (C^op)] — there is no separate class — so
   the fields below are read in the opposite category and the
   "projections" run [x ~> lub x y]. *)
Program Definition Proset_Cocartesian
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  @Cocartesian (Proset P) := {|
  product_obj := lub;
  fork := fun x y z f g => lub_least x y z f g;
  exl := fun x y => lub_l x y;
  exr := fun x y => lub_r x y
|}.

(* The dual of [cartesian_product_IsGLB]: a chosen coproduct is a join. *)
Lemma cocartesian_coproduct_IsLUB (CP : @Cocartesian (Proset P)) (x y : A) :
  IsLUB R (pair_family x y) (@product_obj ((Proset P)^op) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl ((Proset P)^op) CP x y).
    + exact (@exr ((Proset P)^op) CP x y).
  - intros n Hn.
    exact (@fork ((Proset P)^op) CP n x y (Hn true) (Hn false)).
Qed.

(** ** Terminal is greatest, initial is least *)

Program Definition Proset_Terminal (top : A) (Htop : ∀ x, R x top) :
  @Terminal (Proset P) := {| terminal_obj := top; one := Htop |}.

Definition terminal_is_greatest (T : @Terminal (Proset P)) :
  ∀ x, R x (@terminal_obj (Proset P) T) := fun x => @one (Proset P) T x.

(* [Initial C] is notation for [@Terminal (C^op)] (Structure/Initial.v),
   so the record is built with the field names [terminal_obj] and [one],
   whose op-reading gives [R bot x]. *)
Program Definition Proset_Initial (bot : A) (Hbot : ∀ x, R bot x) :
  @Initial (Proset P) := {| terminal_obj := bot; one := Hbot |}.

Definition initial_is_least (Iobj : @Initial (Proset P)) :
  ∀ x, R (@terminal_obj ((Proset P)^op) Iobj) x :=
  fun x => @one ((Proset P)^op) Iobj x.

(* The nullary case of the identification is [greatest_iff_empty_glb]
   above, stated over the bare preorder. *)

(** ** Cones over a thin category *)

(* A cone over ANY diagram valued in [Proset P] is nothing but a lower
   bound of the diagram's objects: the leg family is the lower-bound
   clause, and the coherence condition [fmap[F] f ∘ ψ x ≈ ψ y] is an
   equation in a thin category, hence [Logic.I]. This is the single
   observation that makes the identification below independent of the
   shape [J]. *)
Definition proset_cone {J : Category} (F : J ⟶ Proset P) (n : A)
  (Hn : IsLowerBound R (fobj[F]) n) : Cone F.
Proof.
  unshelve econstructor.
  - exact n.                             (* apex: the candidate bound *)
  - unshelve econstructor.
    + exact Hn.                          (* legs: the lower-bound clause *)
    + intros x y f; exact Logic.I.       (* coherence: degenerate, thin *)
Defined.

(* The same statement in the opposite category, used for the colimit
   half. Note that [(Proset P)^op] is NOT [Proset (op_PreOrder P)] by
   definitional unfolding — the two categories have distinct
   Program-generated law fields — so the dual construction is carried
   out directly rather than by re-instantiating [Proset] at the
   reversed relation. Its hom-setoid is nonetheless the same
   constant-[True] setoid, so the coherence condition degenerates in
   exactly the same way. *)
Definition proset_op_cone {J : Category} (G : J ⟶ (Proset P)^op) (n : A)
  (Hn : ∀ j : J, R (G j) n) : Cone G.
Proof.
  unshelve econstructor.
  - exact n.
  - unshelve econstructor.
    + exact Hn.
    + intros x y f; exact Logic.I.
Defined.

(** ** The identification, at an arbitrary diagram shape *)

(* An object is a limit of [F] exactly when it is a greatest lower bound
   of the family of objects of [F]. Both directions are the data
   transposition described in the header: legs against lower-bound
   clause, mediating arrow against greatest clause. *)

Definition Proset_IsALimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsGLB R (fobj[F]) m) : IsALimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isalimit_IsGLB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsALimit F c) : IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_cone F n Hn))).
Defined.

Theorem proset_limit_iff_glb {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsALimit F c ↔ IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (isalimit_IsGLB F c).
  - exact (Proset_IsALimit F c).
Defined.

(* The unpinned form, for callers holding the [Limit] class. *)
Program Definition Proset_Limit_general {J : Category} (F : J ⟶ Proset P)
  (m : A) (H : IsGLB R (fobj[F]) m) : Limit F := {|
  limit_cone := proset_cone F m (fst H)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
  - intro x; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

Definition limit_general_IsGLB {J : Category} (F : J ⟶ Proset P)
  (L : Limit F) : IsGLB R (fobj[F]) (vertex_obj[L]) :=
  isalimit_IsGLB F _ (limit_is_alimit L).

(* Dually: an object is a colimit of [F] exactly when it is a least
   upper bound of the family of objects of [F]. [IsAColimit F c] is
   [IsALimit (F^op) c] (Structure/Limit/Preservation.v), whose legs run
   [F j ~> c] in [Proset P], that is [R (F j) c]. *)

Definition Proset_IsAColimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsLUB R (fobj[F]) m) : IsAColimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isacolimit_IsLUB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsAColimit F c) : IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_op_cone (F^op) n Hn))).
Defined.

Theorem proset_colimit_iff_lub {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsAColimit F c ↔ IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (isacolimit_IsLUB F c).
  - exact (Proset_IsAColimit F c).
Defined.

(** ** The discrete case: indexed products are indexed meets *)

(* A family [d : Ix → A] is a functor out of the discrete category on
   [Ix] via [DiscreteCat_Functor], and Structure/Limit/Product.v reads a
   limit of that diagram as an indexed product. This is the special case
   [J := DiscreteCat Ix] of the theorems above, kept as a separate
   interface because that is the form indexed consumers want; nothing
   new is proved. *)

Program Definition Proset_Limit {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset P) d) :=
  Proset_Limit_general (DiscreteCat_Functor (C:=Proset P) d) m H.

Definition limit_IsGLB {Ix : Type} (d : Ix → A)
  (L : Limit (DiscreteCat_Functor (C:=Proset P) d)) :
  IsGLB R d (iprod (C:=Proset P) d L).
Proof.
  split.
  - intro i; exact (iprod_proj (C:=Proset P) d L i).
  - intros n Hn.
    exact (unique_obj (iprod_ump (C:=Proset P) d L n Hn)).
Defined.

(* The elementary indexed-product reading, for callers that prefer the
   [IsIndexedProduct] record of Structure/Limit/Product.v to the [Limit]
   class. *)
Definition Proset_IsIndexedProduct {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  IsIndexedProduct (C:=Proset P) d m (fst H).
Proof.
  constructor; intros c pi.
  unshelve econstructor.
  - exact (snd H c pi).
  - intro a; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

(** ** Bicompleteness *)

(* The complete-lattice form of the identification: the thin category of
   a preorder is complete exactly when the preorder has all
   [Type]-indexed infima. [Complete] here is the library's own
   unrestricted predicate (Structure/Complete.v), quantifying over every
   diagram category with no smallness side condition, so this is
   completeness at the library's universe discipline rather than
   small-completeness.

   Both halves are stated: [proset_Complete_iff_all_meets] for infima and
   [proset_Cocomplete_iff_all_joins] for suprema, the latter over
   [Cocomplete (Proset P)] itself rather than [Complete] at the reversed
   preorder (the two readings are not definitionally equal).  That the two
   HYPOTHESES are not independent — all infima already yield all suprema, a
   supremum being the infimum of the family of upper bounds — is the
   standard complete-lattice redundancy; it is treated separately (issue
   #684) and is not re-proved here. *)
Theorem proset_Complete_iff_all_meets :
  @Complete (Proset P) ↔ HasAllMeets R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                          (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (limit_general_IsGLB
             (@DiscreteCat_Functor Ix (Proset P) d)
             (HC (DiscreteCat Ix) (@DiscreteCat_Functor Ix (Proset P) d))).
  - intros HM D F.
    exact (Proset_Limit_general F
             (projT1 (HM (obj[D]) (fun j : D => F j)))
             (projT2 (HM (obj[D]) (fun j : D => F j)))).
Defined.

(** ** Pushouts from joins *)

(* Since a colimit of any diagram is the join of its objects, pushouts
   exist in [Proset P] as soon as binary joins do: the apex of the
   pushout of a span is the join of its two feet, and the span itself
   contributes nothing, its commutation condition being an equation in a
   thin category. *)
Program Definition Proset_HasPushouts
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  HasPushouts (Proset P) := {| pushout := fun x y z f g => _ |}.
Next Obligation.
  unshelve econstructor.
  - exact (lub y z).
  - exact (lub_l y z).
  - exact (lub_r y z).
  - exact Logic.I.
  - intros q i1 i2 Hc.
    unshelve econstructor.
    + exact (lub_least q y z i1 i2).
    + split; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

(* Conversely, any pushout apex in [Proset P] is a join of the two feet
   of the span. *)
Lemma proset_pushout_IsLUB {x y z : A}
  (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  IsLUB R (pair_family y z) (pushout_apex Q).
Proof.
  split.
  - intros [|].
    + exact (pushout_in1 Q).
    + exact (pushout_in2 Q).
  - intros n Hn.
    exact (unique_obj (pushout_ump Q n (Hn true) (Hn false) Logic.I)).
Qed.

(* The join half, PROVED rather than left to duality-by-remark: an earlier
   revision stated only the meet side under a "bicompleteness" heading; the
   verifier of that revision assembled this biconditional from the file's
   own pieces, and it is landed here so the heading is earned.  Note the
   conclusion is [Cocomplete (Proset P)] itself, not
   [Complete (Proset (op_PreOrder P))] -- the two are NOT definitionally
   equal (checked by a rejected [eq_refl] probe). *)
Theorem proset_Cocomplete_iff_all_joins : @Cocomplete (Proset P) ↔ HasAllJoins R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                        (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (isacolimit_IsLUB (@DiscreteCat_Functor Ix (Proset P) d) _
             (limit_is_alimit (HC (DiscreteCat Ix)
                                 (@DiscreteCat_Functor Ix (Proset P) d)))).
  - intros HJ D F.
    unshelve econstructor.
    + exact (proset_op_cone (F^op)
               (projT1 (HJ (obj[D]) (fun j : D => F j)))
               (fst (projT2 (HJ (obj[D]) (fun j : D => F j))))).
    + intro N.
      unshelve econstructor.
      * exact (snd (projT2 (HJ (obj[D]) (fun j : D => F j))) _
                 (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
      * intro x; exact Logic.I.
      * intros v Hv; exact Logic.I.
Defined.

(* Hence the pushout of any span coincides with the coproduct of its two
   feet: both are joins of the same pair, and two joins of one family
   precede each other. In [Proset P] mutual precedence is exactly
   isomorphism of the two objects. *)
Definition pushout_is_coproduct_of_feet (CP : @Cocartesian (Proset P))
  {x y z : A} (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  R (@product_obj ((Proset P)^op) CP y z) (pushout_apex Q)
  * R (pushout_apex Q) (@product_obj ((Proset P)^op) CP y z) :=
  lub_unique R (pair_family y z) (pushout_apex Q)
    (@product_obj ((Proset P)^op) CP y z)
    (proset_pushout_IsLUB f g Q)
    (cocartesian_coproduct_IsLUB CP y z).

End Proset_Limits.

(* The dual indexed statement is this development applied to the
   reversed preorder: [IsLUB R d m] is by definition [IsGLB (op_rel R)
   d m], so a least upper bound of the original preorder is a limiting
   cone in [Proset (op_PreOrder P)]. *)
Definition Proset_LUB_Limit {A : Type} {R : relation A} (P : PreOrder R)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset (op_PreOrder P)) d) :=
  Proset_Limit (op_PreOrder P) d m H.

(* Named for what it concludes: [Complete] at the REVERSED preorder.  The
   genuine cocompleteness corollary follows from the biconditional above. *)
Definition Proset_op_Complete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Complete (Proset (op_PreOrder P)) :=
  snd (proset_Complete_iff_all_meets (op_PreOrder P)) H.

Definition Proset_Cocomplete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Cocomplete (Proset P) :=
  snd (proset_Cocomplete_iff_all_joins P) H.

(** ** Equivalence-invariance of completeness *)

(* Theory/Equivalence/Limit.v transports an individual limit along an
   equivalence ([equivalence_creates_limits]) but does not record that
   the completeness PREDICATE is invariant. The two lemmas below supply
   that, by running the transport at the quasi-inverse, which is itself
   an equivalence (Theory/Equivalence.v, [EquivalenceOfCategories_sym]).

   PLACEMENT.  These are general statements about categories, not about
   prosets, and Theory/Equivalence/Limit.v would be their natural home;
   they are kept here because that file does not currently depend on
   Structure/Complete.v and adding the dependency to a shared Theory/
   module is a change with a wider blast radius than this issue needs.
   Moving them later is a pure relocation.

   The intended order-theoretic corollary — a preorder is bicomplete
   exactly when its skeletal poset is — is NOT stated, because the
   library has no skeleton construction for a preorder (the quotient by
   mutual precedence, together with the equivalence between a preorder
   and that quotient). Once such a construction exists the corollary is
   an immediate instance of the two lemmas below; until then it is
   deliberately left unclaimed. *)

Section Complete_Invariance.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

Definition Complete_equivalence_invariant (HC : @Complete C) : @Complete D :=
  fun J H =>
    @equivalence_creates_limits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

Definition Cocomplete_equivalence_invariant (HC : @Cocomplete C) :
  @Cocomplete D :=
  fun J H =>
    @equivalence_creates_colimits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

End Complete_Invariance.

(** ** The two existing thin witnesses, read through the identification *)

(* [Instance/Props.v]'s [Props] and [Instance/Two.v]'s [_2] are thin, but
   neither is [Proset P] for any [P]: each is its own [Program
   Definition], and [_2] carries the strict-equality hom-setoid
   [Morphism_equality] rather than the constant-[True] one. The general
   theorems above therefore do not apply to them directly.

   What does apply, to EVERY category, is the identification read at the
   hom-inhabitation preorder [hom_le]: the chosen product of a cartesian
   structure is a greatest lower bound of its factors for the relation
   "there exists a morphism". Recording the two existing binary
   witnesses through that bridge is the honest sense in which they are
   instances of the general statement rather than freestanding facts —
   instances of the CHARACTERIZATION, not of the [Proset]
   construction. *)

(* Theory/Category.v already records that a category has an underlying
   preorder of objects, as the exported instance [hom_preorder :
   PreOrder (@hom C)]. That one cannot be reused here: [IsGLB] is stated
   over a [relation], which is [Prop]-valued, whereas [@hom C] is
   [Type]-valued. [hom_le] is therefore its propositional truncation,
   and [hom_le_preorder] below is the corresponding [PreOrder] — named
   apart from [hom_preorder] deliberately, so that this file shadows no
   existing instance. *)
Definition hom_le (C : Category) (x y : C) : Prop := inhabited (x ~{C}~> y).

Program Definition hom_le_preorder (C : Category) : PreOrder (hom_le C) :=
  Build_PreOrder _ _ _.
Next Obligation. intro x; exact (inhabits id). Qed.
Next Obligation. intros x y z [f] [g]; exact (inhabits (g ∘ f)). Qed.

Definition cartesian_is_glb (C : Category) (CP : @Cartesian C) (x y : C) :
  IsGLB (hom_le C) (pair_family x y) (@product_obj C CP x y).
Proof.
  split.
  - intros [|].
    + exact (inhabits (@exl C CP x y)).
    + exact (inhabits (@exr C CP x y)).
  - intros n Hn.
    destruct (Hn true) as [f]; destruct (Hn false) as [g].
    exact (inhabits (@fork C CP n x y f g)).
Defined.

Definition cocartesian_is_lub (C : Category) (CP : @Cocartesian C) (x y : C) :
  IsLUB (hom_le C) (pair_family x y) (@product_obj (C^op) CP x y) :=
  cartesian_is_glb (C^op) CP x y.

(* The two existing binary witnesses, recorded through that bridge:
   conjunction is the meet of two propositions, disjunction their join,
   and [Instance/Two/Monoidal.v]'s [two_meet] is the meet of the
   two-element order. *)
Definition props_product_is_glb (p q : Prop) :=
  cartesian_is_glb Props Props_Cartesian p q.

Definition props_coproduct_is_lub (p q : Prop) :=
  cocartesian_is_lub Props Props_Cocartesian p q.

Definition two_product_is_glb (x y : TwoObj) :=
  cartesian_is_glb _2 Two_Cartesian x y.

(** ** A concrete witness: the natural numbers under [<=] *)

(* [Instance/Proset.v]'s [LessThanEqualTo_Category] is the thin category
   of [(nat, <=)]. The name is also defined in Instance/Poset.v, over
   [Poset] rather than [Proset]; it is written qualified here so the
   intended one is unambiguous. *)
Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(* [Nat.min] is the binary meet for [<=], so it produces a genuine
   cartesian structure on that thin category. *)
Definition Nat_Cartesian : @Cartesian Nat_Proset :=
  Proset_Cartesian Nat.le_preorder Nat.min
    Nat.le_min_l Nat.le_min_r
    (fun n x y Hx Hy => Nat.min_glb x y n Hx Hy).

Definition nat_meet (x y : nat) : nat :=
  @product_obj Nat_Proset Nat_Cartesian x y.

(* The identification computes: the categorical product of 3 and 5 in
   this thin category is the number 3, by reduction alone. (Object
   positions parse in [object_scope], where a bare numeral has no
   interpretation, hence the [%nat] annotation.) *)
Example nat_product_3_5 : nat_meet 3 5 = 3%nat := eq_refl.

Definition nat_product_IsGLB (x y : nat) :
  IsGLB le (pair_family x y) (@product_obj Nat_Proset Nat_Cartesian x y) :=
  cartesian_product_IsGLB Nat.le_preorder Nat_Cartesian x y.

(* Non-vacuity, in the sense described in the header: [IsGLB] is a
   refutable predicate, so the theorems above are not statements about a
   uniformly inhabited type. 4 is not a lower bound of {3, 5}. *)
Lemma nat_glb_not_4 : IsGLB le (pair_family 3%nat 5%nat) 4%nat → False.
Proof.
  intros [Hlb _].
  pose proof (Hlb true) as H4.
  apply Nat.nle_succ_diag_l with (n:=3%nat).
  exact H4.
Qed.

(* Zero is least, hence initial. The natural numbers have no greatest
   element, so this thin category has an initial object but no terminal
   one — a reminder that the identification transports the ORDER facts,
   it does not manufacture them.  The negative half is PROVED below
   ([Nat_no_Terminal]), not asserted. *)
Definition Nat_Initial : @Initial Nat_Proset :=
  Proset_Initial Nat.le_preorder 0%nat Nat.le_0_l.

(* Registered as an instance, which is what the Seven Sketches §6.2.1
   checkbox asks for; usable by typeclass search as well as by name. *)
#[export] Existing Instance Nat_Initial.

(* A terminal object of this thin category would be an upper bound of
   every natural, in particular of its own successor. *)
Theorem Nat_no_Terminal : @Terminal Nat_Proset → False.
Proof.
  intros T.
  pose proof (@one Nat_Proset T (S (@terminal_obj Nat_Proset T))) as H.
  simpl in H.
  exact (Nat.nle_succ_diag_l _ H).
Qed.

Definition nat_indexed_limit (x y : nat) :
  Limit (DiscreteCat_Functor (C:=Nat_Proset) (pair_family x y)) :=
  Proset_Limit Nat.le_preorder (pair_family x y) (Nat.min x y)
    (nat_product_IsGLB x y).

(** ** A preorder with no least element, and no binary meets *)

(* The two-element discrete order: [bool] under equality. It is a
   preorder, so the constructions above apply to it, and it has neither
   a bottom nor binary meets. Both facts are stated in the refutation
   form, which is what makes the corresponding positive statements
   informative.

   Two other in-tree candidates were available and are deliberately not
   used: Instance/Two/Discrete.v's [Two_Discrete] is a hand-built
   category rather than a [Proset], so it would not witness a statement
   about preorders without a bridge; and packaging
   Construction/Enriched/Two.v's [two_bot] as an initial object of [_2]
   belongs to a separate effort on joins in the two-element order
   (issue #756), which owns those names. *)
Definition bool_eq_preorder : PreOrder (@eq bool) :=
  Build_PreOrder (@eq bool) (@eq_Reflexive bool) (@eq_Transitive bool).

Lemma discrete_two_no_initial :
  @Initial (Proset bool_eq_preorder) → False.
Proof.
  intro Iobj.
  pose proof (initial_is_least bool_eq_preorder Iobj true) as Ht.
  pose proof (initial_is_least bool_eq_preorder Iobj false) as Hf.
  rewrite Ht in Hf; discriminate.
Qed.

Lemma discrete_two_no_cartesian :
  @Cartesian (Proset bool_eq_preorder) → False.
Proof.
  intro CP.
  assert (Hl : @product_obj (Proset bool_eq_preorder) CP true false = true)
    by exact (@exl (Proset bool_eq_preorder) CP true false).
  assert (Hr : @product_obj (Proset bool_eq_preorder) CP true false = false)
    by exact (@exr (Proset bool_eq_preorder) CP true false).
  rewrite Hl in Hr; discriminate.
Qed.
