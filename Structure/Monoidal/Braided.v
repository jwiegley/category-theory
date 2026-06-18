Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section BraidedMonoidal.

Context {C : Category}.

(** Braided monoidal category. *)

(* nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

   A braided monoidal category is a monoidal category equipped with a natural
   isomorphism, the braiding,

       beta : x ⊗ y ≅ y ⊗ x              ([braid]),

   that is compatible with the associator (alpha = [tensor_assoc]) by way of
   two hexagon identities. Writing the equations in this library's notation
   (composition reads right to left), they are

       alpha ∘ beta ∘ alpha
         = (id ⨂ beta) ∘ alpha ∘ (beta ⨂ id)
                                          ([hexagon_identity]),

       alpha⁻¹ ∘ beta ∘ alpha⁻¹
         = (beta ⨂ id) ∘ alpha⁻¹ ∘ (id ⨂ beta)
                                          ([hexagon_identity_sym]),

   where on the upper path the middle [braid] is the braiding of one object
   past a whole tensor product (B_{x, y⊗z} and B_{x⊗y, z} respectively). The
   first hexagon braids x past y ⊗ z; the second braids x ⊗ y past z, and uses
   the inverse associator throughout. Both follow the nLab orientation; the
   coherence consequence on triple tensors is the Yang-Baxter equation proved
   below. Adding the further axiom beta ∘ beta = id yields a symmetric
   monoidal category (see Structure/Monoidal/Symmetric.v).

   Only the braiding's naturality is asked for: the two hexagons are equations
   between fixed composites and so need no separate respectfulness. *)

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  (* The braiding beta : x ⊗ y ≅ y ⊗ x, natural in both arguments. *)
  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  (* First hexagon: braiding x past the tensor product y ⊗ z. *)
  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  (* Second hexagon: braiding the tensor product x ⊗ y past z. *)
  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

Coercion braided_is_monoidal : BraidedMonoidal >-> Monoidal.

Context `{BraidedMonoidal}.

(* The hexagons imply the Yang-Baxter equation on a triple tensor product:
   the two ways of fully reversing a ⊗ b ⊗ c by adjacent braidings agree. *)
Theorem Yang_Baxter_equation {a b c : C} :
  braid ⨂ id[a] ∘ tensor_assoc⁻¹
    ∘ id[b] ⨂ braid ∘ tensor_assoc
    ∘ braid ⨂ id[c] ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ id[c] ⨂ braid
        ∘ tensor_assoc ∘ braid ⨂ id[b]
        ∘ tensor_assoc⁻¹ ∘ id[a] ⨂ braid.
Proof.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite iso_to_from, id_right.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite (@comp_assoc _ _ _ _ _ _ tensor_assoc⁻¹).
  rewrite iso_to_from, id_left.
  spose (braid_natural a _ id _ _ (@braid _ b c)) as X.
  rewrite bimap_id_id in X.
  rewrite id_right in X.
  rewrite X.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

End BraidedMonoidal.
