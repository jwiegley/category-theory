Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Monoidal.Product.
Require Import Category.Structure.Monoidal.Cartesian.

Generalizable All Variables.

(** The product of strong functors is strong *)

(* nLab: https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   If F, G : C ⟶ C are strong (each carries a left tensorial strength
   strength[x,y] : x ⨂ F y ~> F (x ⨂ y), see Functor/Strong.v), then their
   componentwise product F ∏⟶ G : C ∏ C ⟶ C ∏ C is strong for the product
   monoidal structure on C ∏ C (Structure/Monoidal/Product.v), where the
   tensor and unit act factorwise. The strength of F ∏⟶ G at a pair of objects
   is built componentwise from the two given strengths,

     strength[(x₁,x₂),(y₁,y₂)] = (strength[F]_{x₁,y₁}, strength[G]_{x₂,y₂}),

   and naturality together with both coherence laws (unit law w.r.t. λ and
   associativity law w.r.t. α) hold in C ∏ C because equivalence there is the
   componentwise conjunction, so each obligation splits into the F-part and the
   G-part and is discharged factorwise. This needs only that C be monoidal; the
   cartesian structure is not used. ProductFunctor_Strong_proj1/proj2 are the
   converse projections, recovering a strength on each factor from a strength on
   F ∏⟶ G by fixing the other coordinate at the unit I. *)

Section ProductFunctorStrong.

Context `{@Monoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Program Definition ProductFunctor_Strong
  `{!StrongFunctor F} `{!StrongFunctor G} : StrongFunctor (F ∏⟶ G) := {|
  strength := fun _ _ => (strength[F], strength[G]);  (* componentwise strength *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation. split; apply strength_natural. Qed.   (* naturality, each factor *)
Next Obligation. split; apply strength_id_left. Qed.   (* unit law, each factor *)
Next Obligation. split; apply strength_assoc. Qed.     (* assoc law, each factor *)

(* Recover a strength on the first factor F from one on F ∏⟶ G: fix the second
   coordinate at the unit I and project the first component. The unit and assoc
   laws follow by transporting the product strength's naturality along the unit
   isomorphism I ≅ I ⨂ I before invoking the corresponding product law. *)
Program Definition ProductFunctor_Strong_proj1 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor F := fun P => {|
  strength := fun x y => fst (@strength _ _ _ P (x, I) (y, I));  (* fst at y₂ = I *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (fst (@strength_natural _ _ _ P (x, I) (y, I) (g, id)
                                (z, I) (w, I) (h, id))).
Defined.
Next Obligation.
  exact (fst (@strength_id_left _ _ _ P (x, I))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (fst (@strength_natural _ _ _ P
                     (x, I) (x, I) (id[x], id[I])
                     (y ⨂ z, I)%object (y ⨂ z, I ⨂ I)%object
                     (id[y ⨂ z], from X0))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (fst (@strength_natural _ _ _ P
                     (x ⨂ y, I)%object (x ⨂ y, I ⨂ I)%object
                     (id[x ⨂ y], from X0)
                     (z, I) (z, I) (id[z], id[I]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (fst (@strength_assoc _ _ _ P (x, I) (y, I) (z, I))).
Qed.

(* Dual of proj1: recover a strength on the second factor G by fixing the first
   coordinate at the unit I and projecting the second component. *)
Program Definition ProductFunctor_Strong_proj2 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor G := fun P => {|
  strength := fun x y => snd (@strength _ _ _ P (I, x) (I, y));  (* snd at x₁ = I *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (snd (@strength_natural _ _ _ P (I, x) (I, y) (id, g)
                                (I, z) (I, w) (id, h))).
Defined.
Next Obligation.
  exact (snd (@strength_id_left _ _ _ P (I, x))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x) (I, x) (id[I], id[x])
                     (I, y ⨂ z)%object (I ⨂ I, y ⨂ z)%object
                     (from X0, id[y ⨂ z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x ⨂ y)%object (I ⨂ I, x ⨂ y)%object
                     (from X0, id[x ⨂ y])
                     (I, z) (I, z) (id[I], id[z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (snd (@strength_assoc _ _ _ P (I, x) (I, y) (I, z))).
Qed.

End ProductFunctorStrong.
