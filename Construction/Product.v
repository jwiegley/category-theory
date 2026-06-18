Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The product of two categories. *)

(* nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   The product category C ∏ D has as objects the pairs (c, d) with c : C and
   d : D, and as morphisms (c, d) ~> (c', d') the pairs (f, g) of a morphism
   f : c ~> c' in C and a morphism g : d ~> d' in D. Identity and composition
   are componentwise: id := (id, id) and (f, g) ∘ (f', g') := (f ∘ f', g ∘ g').
   Equivalence of morphisms is the componentwise conjunction of ≈ in C and ≈
   in D, and the unit and associativity laws hold componentwise because they
   hold in each factor.

   This is the cartesian product in Cat, the category of categories: the
   projection functors Fst and Snd (π₁, π₂ below) exhibit C ∏ D as the
   categorical product of C and D, so a functor E ⟶ C ∏ D is the same as a
   pair of functors E ⟶ C and E ⟶ D. This is the product *of categories*, and
   is distinct from a product *object* inside a single category, formed via a
   universal cone in Structure/Cartesian.v.

   All of the methods are spelled out here to ease simplification. *)

Definition Product (C D : Category) : Category := {|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g);

  compose_respects := fun x y z f g fg h i hi =>
    (compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun x y f =>
    (@id_left C (fst x) (fst y) (fst f),
     @id_left D (snd x) (snd y) (snd f));
  id_right := fun x y f =>
    (@id_right C (fst x) (fst y) (fst f),
     @id_right D (snd x) (snd y) (snd f));

  comp_assoc := fun x y z w f g h =>
    (@comp_assoc C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun x y z w f g h =>
    (@comp_assoc_sym C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h))
|}.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

(* First projection functor π₁ : C ∏ D ⟶ C, taking (c, d) to c on objects and
   (f, g) to f on morphisms. *)
#[export]
Program Instance Fst {C D : Category} : C ∏ D ⟶ C := {
  fobj := fst;                          (* (c, d) ↦ c *)
  fmap := fun _ _ => fst                (* (f, g) ↦ f *)
}.

(* Second projection functor π₂ : C ∏ D ⟶ D, taking (c, d) to d on objects and
   (f, g) to g on morphisms. *)
#[export]
Program Instance Snd {C D : Category} : C ∏ D ⟶ D := {
  fobj := snd;                          (* (c, d) ↦ d *)
  fmap := fun _ _ => snd                (* (f, g) ↦ g *)
}.

(* The symmetry functor C ∏ D ⟶ D ∏ C exchanging the two factors, witnessing
   that the product of categories is commutative up to isomorphism. *)
Program Definition Swap
        {C : Category} {D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);      (* (c, d) ↦ (d, c) *)
  fmap := fun _ _ f => (snd f, fst f);  (* (f, g) ↦ (g, f) *)
|}.

Corollary fst_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.

Require Import Category.Construction.Opposite.

(* The opposite of a product is the product of the opposites, on the nose:
   both Opposite and Product act componentwise, so the two categories are
   definitionally equal (hence the proof by reflexivity, using =). *)
Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
