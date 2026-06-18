Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.UniversalProperty.

Local Hint Extern 5 (hom ?z ?x) => apply (@exl' _ x _ z (ltac:(typeclasses eauto))) : cat.
Local Hint Extern 5 (hom ?z ?y) => apply (@exr' _ _ y z (ltac:(typeclasses eauto))) : cat.
Local Hint Extern 5 (Proper _ _ ) => progress(repeat(intro)) : cat.

#[local] Hint Rewrite @exl_fork : categories.
#[local] Hint Rewrite @exr_fork : categories.

(** * The cartesian product as a universal property *)

(* nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/universal+property
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   A product x × y of two objects is characterized by the universal mapping
   property of its projections, equivalently by the natural isomorphism

       Hom(z, x × y) ≅ Hom(z, x) × Hom(z, y)    (natural in z)

   i.e. x × y represents the presheaf z ↦ Hom(z, x) × Hom(z, y).  This is the
   product as a representing object / a limit of the discrete two-object
   diagram (the terminal object being the empty product).

   [CartesianProductIsUniversalProperty] instantiates the generic
   "universal property ⟺ representability" packaging from
   [Structure.UniversalProperty] for this case.  The predicate is
   [IsCartesianProduct x y z] (Structure/Cartesian.v): z carries projections
   [exl'], [exr'] and a pairing [fork'] satisfying the universal mapping
   property [ump_product].  Working in C^op makes the ambient covariant
   hom-functor [Hom z,─] of [IsUniversalProperty] unfold to the presheaf
   Hom_C(─, z), so the representing functor is the product of presheaves

       repr_functor := [Hom ─ , x ] × [Hom ─ , y ]  =  Hom_C(─, x) × Hom_C(─, y)

   ([Hom ─ , a ] = Curried_CoHom is the contravariant hom Hom_C(─, a);
   the binary × on presheaves is the pointwise product from
   Instance/Fun/Cartesian.v).  The per-z isomorphism in [Sets] then identifies
   proofs of [IsCartesianProduct x y z] with natural isomorphisms
   Hom_C(─, z) ≅ Hom_C(─, x) × Hom_C(─, y), which is exactly the bijection
   above.  Specializing the generic uniqueness result then recovers the usual
   fact that the product is unique up to a unique isomorphism. *)

Section CartesianProduct.
  Context (C : Category).
  Context (x y : C).
  Proposition CartesianProductIsUniversalProperty :
    IsUniversalProperty C^op (fun z => IsCartesianProduct x y z)
                            (fun z => CartesianProductStructuresEquiv x y z).
  Proof.
    unshelve econstructor; [ exact ([Hom ─ , x ] × [Hom ─ , y ]) |].
    intro z; unshelve econstructor.
    - simpl. unshelve econstructor.
      + intro H. unshelve econstructor.
        * simpl. unshelve eapply Build_Transform'.
          -- intro a. simpl. unshelve econstructor.
             ++ auto with cat.
             ++ abstract(auto with cat).
          -- abstract(simpl; auto with cat).
        * simpl. unshelve eapply Build_Transform'.
          -- intro a. unshelve econstructor.
             ++ simpl. intros [? ?]. now apply fork'.
             ++ abstract(repeat(intro); destruct x0, y0, X; simpl in *;
                now apply fork'_respects).
          -- abstract(simpl; intros w s f [a b]; simpl; apply ump_product; split;
                      [ now rewrite comp_assoc, exl'_fork |
                        now rewrite comp_assoc, exr'_fork]).
        * abstract(simpl; intros w [f g]; split;
                   [ rewrite exl'_fork | rewrite exr'_fork];
                    now autorewrite with categories ).
        * abstract(simpl; intros; rewrite id_right; symmetry;
                   apply ump_product; split; reflexivity).
      + abstract(simpl; intros F G [eq1 eq2]; apply to_equiv_implies_iso_equiv;
                 simpl; intros; split; apply compose_respects; auto with cat).
    - simpl. unshelve econstructor.
      + intro X.
        destruct X as [[X_to_transform X_to_naturality ?]
                         [X_from_transform X_from_naturality ?]
                         X_tofromid X_fromtoid ]. simpl in *.
        simpl in X_to_transform, X_from_transform.
        clear naturality_sym naturality_sym0.
        unshelve econstructor.
        * intros a f g.
          exact (X_from_transform a (f, g)).
        * exact (fst (X_to_transform z id{C})).
        * exact (snd (X_to_transform z id{C})).
        * abstract(intros a ? ? ? ? ? ?;
          apply (proper_morphism (X_from_transform a));
                   split; auto).
        * simpl in *. intros; split.
          -- abstract(
             intro heq; split; specialize X_to_naturality with _ _ h (id{C});
               destruct X_to_naturality as [fst' snd'];
               [ now rewrite fst', id_left, heq,
                 (fst (X_tofromid _ _)), id_right |
                 now rewrite snd', id_left, heq,
                 (snd (X_tofromid _ _)), id_right ]).
          -- abstract(intros [l r]; now rewrite <- l, <- r, <- X_from_naturality,
               X_fromtoid, 2 id_left).
      + abstract(
          intros [Ftrans Fnat ?] [Gtrans Gnat ?] [eqto eqfrom]; simpl in *; apply (eqto _ _)).
    - abstract(simpl; intros [[iso_to_transform iso_to_nat ?]
                       [iso_from_transform iso_from_nat ?]
                       tofrom_id fromto_id]; simpl in *;
               apply to_equiv_implies_iso_equiv; simpl;
               intros c f; assert (j:= (iso_to_nat z c f id{C}));
               set (m := f) at 2 4; split;
               rewrite <- (id_left m); [ exact (fst j) | exact (snd j)]).
    - abstract(simpl; intro a; split; now rewrite id_right).
  Defined.
End CartesianProduct.
