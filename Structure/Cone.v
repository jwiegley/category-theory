Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/cone
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   A cone over a diagram F : J ⟶ C is an apex object c : C together with a
   family of legs ψx : c ~> F x, one for each object x of J, that is natural
   in x: for every f : x ~> y in J we have F(f) ∘ ψx ≈ ψy. The apex sits
   "above" the diagram with arrows pointing down into each F x, compatibly
   with all of the diagram's morphisms. The terminal cone over F (the cone
   through which every other cone factors uniquely) is the limit of F.

   [ACone] fixes the apex [c] and records just the leg family and its
   coherence; [Cone] below bundles the apex together with such an [ACone].
   A cocone over F is dually a cone over F^op (see [Cocone]). *)

Class ACone@{u0 u1 u2 u3 u4 u5} {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}} (c : obj[C]) (F : J ⟶ C) := {
    (* The leg (component) at x: a morphism from the apex c into F x. *)
    vertex_map (x : J) : c ~{C}~> F x;
    (* Naturality of the legs: pushing the leg at x along F f lands on the
       leg at y, i.e. F(f) ∘ ψx ≈ ψy, so every diagram triangle commutes. *)
    cone_coherence {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ vertex_map x ≈ vertex_map y
  }.

(* Two cones with the same apex are identified when their legs agree
   pointwise (up to ≈); the coherence proof is irrelevant to this equivalence. *)
#[export]
  Program Instance AConeEquiv@{u0 u1 u2 u3 u4 u5 +}
  {J: Category@{u0 u1 u2}} {C: Category@{u3 u4 u5}}
  c (F : C ⟶ J) : Setoid (ACone c F) :=
  {| equiv := fun cone1 cone2 =>
                forall j, @vertex_map _ _ _ _ cone1 j ≈ @vertex_map _ _ _ _ cone2 j |}.
Next Obligation.
  equivalence.
  specialize X with j. specialize X0 with j.
  exact (Equivalence_Transitive _ _ _ X X0).
Qed.

(* A [Cone] over F packages an apex with a leg family over that apex,
   matching the nLab/Wikipedia definition of a cone as an apex object
   together with its commuting legs. *)
Class Cone@{u0 u1 u2 u3 u4 u5}
  {J : Category@{u0 u1 u2}}
  {C : Category@{u3 u4 u5}}
  (F : J ⟶ C) := {
  vertex_obj : C;                  (* the apex (vertex) object *)
  coneFrom : ACone vertex_obj F    (* the legs over that apex, with coherence *)
}.

Coercion vertex_obj : Cone >-> obj.
#[export] Existing Instance coneFrom.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ L ]" := (@vertex_map _ _ _ _ (@coneFrom _ _ _ L) _)
  (at level 9, format "vertex_map[ L ]") : category_scope.

Notation "Cone[ N ] F" := (ACone N F)(* . { ψ : Cone F | vertex_obj[ψ] = N } *)
  (at level 9, format "Cone[ N ] F") : category_scope.

(* A cocone over F is the dual notion: a cone over the opposite diagram
   F^op, whose legs run F x ~> apex (see nLab: cocone). *)
Definition Cocone `(F : J ⟶ C) := Cone (F^op).

(* The presheaf of cones over F: each object c is sent to the setoid of
   cones with apex c, and a morphism f : c' ~> c in C (i.e. c ~> c' in C^op)
   precomposes every leg with f, reindexing a c-cone to a c'-cone. Its
   representing object, when one exists, is the limit of F. *)
#[export]
Instance ConePresheaf@{u0 u1 u2 u3 u4 u5 +}
   {J : Category@{u0 u1 u2}} {C : Category@{u3 u4 u5}} (F : @Functor J C) :
   @Functor C^op Sets.
Proof.
  unshelve eapply Build_Functor.
  - change obj[C^op] with obj[C].
    exact (fun c => {| carrier := Cone[c]F ; is_setoid := AConeEquiv _ _ |}).
  - change obj[C^op] with obj[C] in *; intros c c'.
    intro f; simpl in f.
    unshelve eapply Build_SetoidMorphism.
    + simpl; intro λ1. unshelve eapply Build_ACone.
      * exact (fun x => compose (@vertex_map _ _ _ _ λ1 x) f).
      * abstract(simpl; intros x y g; now rewrite comp_assoc, (cone_coherence g)).
    + abstract(simpl; intros a b t j; specialize t with j; cbn;
      rewrite t; reflexivity).
  - abstract(proper).
  - abstract(intro x; cbn; intros y j; now apply id_right).
  - abstract(cbn; intros; now apply comp_assoc).
Defined.
