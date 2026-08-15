(** * Monoid and group actions as functor categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.4, printed pp. 41–42 (PDF 51–52) —
              maclane:II.4:construction2, maclane:II.4:ex5
   nLab:      https://ncatlab.org/nlab/show/action
   nLab:      https://ncatlab.org/nlab/show/G-set

   Mac Lane's construction 2: a functor from a delooped monoid into
   Sets is exactly an action of M on a set, and a natural
   transformation between two such functors is exactly a single
   EQUIVARIANT map — its one component, at the one object.  This file
   packages the correspondence at category strength: the category
   [MSet M] of M-actions with equivariant maps, and the equivalence
   [MSet_Fun_equiv : [Deloop M, Sets] ≅[Cat] MSet M].  Exercise 5
   specializes to a group acting on finite sets: every finite-set
   value of a functor on a delooped GROUP is acted on by
   permutations, since group elements are invertible arrows and
   functors preserve isomorphisms — the permutation-representation
   reading.

     - [Equivariant]: a setoid morphism between the carriers
       commuting with the actions, with the componentwise setoid
     - [MSet M]: the category of M-actions and equivariant maps
     - [MSet_to]/[MSet_from]: the two comparison functors, riding
       Construction/Deloop/Functors.v's [action_of_functor] and
       [functor_of_action] (cited, not rebuilt)
     - [MSet_Fun_equiv]: the equivalence [Deloop M, Sets] ≅ [MSet M]
       in Cat, and [MSet_hom_iso], the hom-setoid isomorphism
       stating literally that a natural transformation IS one
       equivariant map
     - [perm_of_group_element]/[FinPermRep]/
       [perm_rep_acts_by_bijections]: Exercise 5 — for a group G,
       each g acts on the finite-set value of any
       F : Deloop G ⟶ FinSet as an isomorphism of FinSet (a
       permutation), and representations correspond to functors
       along the spine, invertibility being automatic rather than
       part of the data

   Design:

   1. THE OBJECT-LEVEL DICTIONARY IS ALREADY IN THE TREE, AND IS NOT
      REBUILT.  Construction/Deloop/Functors.v has [MSetoidAction],
      [action_of_functor], [functor_of_action], the object-level
      round trips ([action_round] is pointwise reflexivity;
      [action_functor_round] is the [Functor_Setoid] witness), the
      spine correspondence [functor_of_hom_monoid]/
      [hom_monoid_of_functor] with its round trips, and
      [action_automorphism] with its definitional readings — all
      consumed below, none re-proved.  What this file adds is the
      MORPHISM level — equivariant maps as a category — and the
      equivalence at [Cat] strength.  The one thing rebuilt is the
      functor-side round-trip ISOMORPHISM, with a transparent
      component family ([MSet_round_iso]): the in-tree lemma is
      opaque (Qed) and the equivalence needs to compute with the
      components — the same transparent-witness discipline as
      Construction/Arrow/Functor.v's [fs_refl].

   2. NATURALITY AT THE ONE OBJECT IS EQUIVARIANCE.  A transformation
      η between functors on [Deloop M] has one component, and its
      naturality square at g : ttt ~> ttt says precisely that this
      component commutes with the two actions.  [MSet_to]'s morphism
      action reads this off; [MSet_from] materializes an equivariant
      map as the constant transformation family, naturality being
      equivariance again.

   3. EXERCISE 5 RIDES INVERTIBILITY, AND ITS SCOPE IS THIS.
      [perm_of_group_element] is Construction/Deloop/Functors.v's
      [action_automorphism] read at the FinSet target — a functor
      carries the group inverse to the inverse permutation — and
      [FinPermRep] identifies representations with functors at the
      OBJECT level along the spine (mirroring [MatrixRep]), with
      invertibility a theorem rather than data
      ([perm_rep_acts_by_bijections]).  A FinSet hom is a function
      on positions (Instance/FinSet.v), so an isomorphism is
      literally a permutation; Instance/FinSet/Classifier.v holds
      the injectivity/surjectivity characterizations, cited not
      imported.  What is NOT built: a separate CATEGORY of
      permutation representations with an equivalence
      [Deloop G, FinSet] ≃ PermRep (the morphism-level story at
      FinSet would repeat the [MSet] development at a second
      target), and no finiteness hypothesis on the GROUP is
      rendered — [GrpObject] carries none, so every statement here
      holds for all groups, strictly more than the exercise's
      "finite group" asks.

   4. THE GROUP-WITH-OPERATORS ASIDE.  Mac Lane's remark that
      functors [Deloop M ⟶ Grp] are groups with operator monoid M
      (and similarly for other targets) is the same dictionary at a
      different target; there is no in-tree category of groups at
      the needed generality to instantiate it, so it remains this
      prose note, per the issue's own scoping. *)

(** ** Equivariant maps *)

(* A morphism of M-actions: a setoid morphism between the carriers
   commuting with the actions. *)
Record Equivariant {M : MonObject} (A B : MSetoidAction M) := {
  equiv_map :> act_setoid A ~{Sets}~> act_setoid B;
  equivar : ∀ (g : carrier M) x,
    equiv_map (act A g x) ≈ act B g (equiv_map x)
}.

Arguments equiv_map {M A B} _.
Arguments equivar {M A B} _ _ _.

(** ** The category of M-actions *)

Program Definition MSet (M : MonObject) : Category := {|
  obj := MSetoidAction M;
  hom := fun A B => Equivariant A B;
  homset := fun A B =>
    {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |};
  id := fun A =>
    {| equiv_map := {| morphism := fun x => x |} |};
  compose := fun A B C f g =>
    {| equiv_map := {| morphism := fun x => equiv_map f (equiv_map g x) |} |}
|}.
Next Obligation.
  intros M A B; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x; transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; reflexivity.
Qed.
Next Obligation.
  intros M A B C f g x y Hxy.
  apply (proper_morphism (equiv_map f)).
  apply (proper_morphism (equiv_map g)).
  exact Hxy.
Qed.
Next Obligation.
  intros M A B C f g gr x; simpl.
  rewrite (equivar g gr x).
  apply (equivar f).
Qed.
Next Obligation.
  intros M A B C f f' Hf g g' Hg x; simpl.
  rewrite (Hg x).
  exact (Hf (equiv_map g' x)).
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.

(** ** The comparison functors *)

(* Reading an action and its equivariant maps off a functor: the
   morphism action takes a transformation to its single component,
   whose naturality at g IS equivariance. *)
Program Definition MSet_to (M : MonObject) :
  [Deloop M, Sets] ⟶ MSet M := {|
  fobj := fun F => action_of_functor F;
  fmap := fun F G η =>
    {| equiv_map := transform[η] ttt |}
|}.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F x; simpl; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F G H η θ x; simpl; reflexivity.
Qed.

(* Materializing an equivariant map as the constant transformation
   family; naturality is equivariance. *)
Program Definition MSet_from (M : MonObject) :
  MSet M ⟶ [Deloop M, Sets] := {|
  fobj := fun A => functor_of_action A;
  fmap := fun A B h =>
    {| transform := fun _ => equiv_map h |}
|}.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M A [] x; simpl.
  now rewrite (act_unit A x).
Qed.
Next Obligation.
  intros M A B C f g [] x; simpl; reflexivity.
Qed.

(** ** The equivalence *)

(* The functor-side round trip, with a transparent component family
   (the in-tree [action_functor_round] is opaque). *)
Program Definition MSet_round_iso {M : MonObject} (F : Deloop M ⟶ Sets) :
  @Isomorphism ([Deloop M, Sets])
    (functor_of_action (action_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return (functor_of_action (action_of_functor F) x ~{Sets}~> F x)
    with ttt => {| morphism := fun p => p |} end |};
  from := {| transform := fun x =>
    match x return (F x ~{Sets}~> functor_of_action (action_of_functor F) x)
    with ttt => {| morphism := fun p => p |} end |}
|}.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.

(* The action-side round trip: the two actions coincide pointwise
   ([action_round] is reflexivity), so the identity map is
   equivariant in both directions. *)
Program Definition MSet_action_round_iso {M : MonObject}
        (A : MSetoidAction M) :
  @Isomorphism (MSet M) (action_of_functor (functor_of_action A)) A := {|
  to   := {| equiv_map := {| morphism := fun x => x |} |};
  from := {| equiv_map := {| morphism := fun x => x |} |}
|}.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.

(* Mac Lane's construction 2 at category strength: the functor
   category over a delooped monoid IS the category of M-actions, an
   isomorphism in Cat and hence (by Cat's convention) an equivalence
   of categories. *)
Program Definition MSet_Fun_equiv (M : MonObject) :
  [Deloop M, Sets] ≅[Cat] MSet M := {|
  to   := MSet_to M;
  from := MSet_from M
|}.
Next Obligation.
  (* MSet_to ∘ MSet_from ≈ Id: the action round trip is pointwise
     reflexivity *)
  intros M.
  exists (fun A => MSet_action_round_iso A).
  intros A B h x; simpl; reflexivity.
Qed.
Next Obligation.
  (* MSet_from ∘ MSet_to ≈ Id: the transparent functor-side round trip *)
  intros M.
  exists (fun F => MSet_round_iso F).
  intros F G η [] x; simpl.
  reflexivity.
Qed.

(** ** The transformation setoid IS the equivariant-map setoid *)

(* Issue item 2's "unwind", stated literally as a hom-setoid
   isomorphism in Sets, following the same-directory precedents
   [One_hom_iso] and [Discrete_hom_iso]: a natural transformation
   between functors on the delooping is exactly one equivariant
   map. *)
Program Definition MSet_hom_iso {M : MonObject}
        (F G : Deloop M ⟶ Sets) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid (Deloop M) Sets F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := Equivariant (action_of_functor F) (action_of_functor G);
     is_setoid :=
       {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |} |} := {|
  to   := {| morphism := fun η => {| equiv_map := transform[η] ttt |} |};
  from := {| morphism := fun h =>
    {| transform := fun o =>
         match o return (fobj[F] o ~{Sets}~> fobj[G] o) with
         | ttt => equiv_map h
         end |} |}
|}.
Next Obligation.
  intros M F G; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x;
    transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M F G h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F G η [] x; simpl; reflexivity.
Qed.

(** ** Exercise 5: groups act on finite sets by permutations *)

(* Each group element acts on the finite-set value as an isomorphism
   of FinSet — a permutation.  The isomorphism is Construction/
   Deloop/Functors.v's [action_automorphism] read at the FinSet
   target (the donor is general in the target category and carries
   the definitional readings [action_automorphism_to]/[_from]);
   nothing is re-proved here. *)
Definition perm_of_group_element {G : GrpObject}
        (F : Deloop G ⟶ FinSet) (g : carrier G) :
  @Isomorphism FinSet (F ttt) (F ttt) :=
  action_automorphism F g.

(* The identification with permutation representations, at the object
   level and along the spine correspondence: a permutation
   representation is a dimension with a homomorphism into the
   endomorphism monoid of that object of FinSet — mirroring
   [MatrixRep] — and the passage to and from functors is the spine,
   with the round trips already in the tree.  Invertibility is NOT
   part of the data: over a group it is automatic
   ([perm_rep_acts_by_bijections]). *)
Definition FinPermRep (M : MonObject) : Type :=
  { n : nat & MonHom M (hom_monoid FinSet n) }.

Definition functor_of_perm_rep {M : MonObject} (ρ : FinPermRep M) :
  Deloop M ⟶ FinSet :=
  functor_of_hom_monoid (C := FinSet) (`1 ρ) (`2 ρ).

Definition perm_rep_of_functor {M : MonObject} (F : Deloop M ⟶ FinSet) :
  FinPermRep M :=
  existT (fun n : nat => MonHom M (hom_monoid FinSet n))
    (F ttt : nat) (hom_monoid_of_functor (C := FinSet) F).

(* Over a group, every representation acts by bijections: each element
   goes to an isomorphism of FinSet. *)
Definition perm_rep_acts_by_bijections {G : GrpObject}
        (ρ : FinPermRep G) (g : carrier G) :
  @Isomorphism FinSet (`1 ρ) (`1 ρ) :=
  perm_of_group_element (functor_of_perm_rep ρ) g.
