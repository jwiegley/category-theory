Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(** * Split coequalizers are absolute *)

(* nLab:      https://ncatlab.org/nlab/show/split+coequalizer
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   A split coequalizer of a parallel pair f, g : x ~> y is a coforking map
   e : y ~> q (law 1: e ∘ f ≈ e ∘ g) equipped with a section s : q ~> y of
   e (law 2: e ∘ s ≈ id) and a section t : y ~> x of f (law 3: f ∘ t ≈ id)
   such that the idempotent s ∘ e on y is computed by the pair through t
   (law 4: g ∘ t ≈ s ∘ e).

   The four equations force e to be a coequalizer of f and g
   ([split_coequalizer_is_coequalizer]): a coforking map h : y ~> z
   descends through e as h ∘ s, since

       (h ∘ s) ∘ e ≈ h ∘ (g ∘ t) ≈ (h ∘ f) ∘ t ≈ h,

   and law 2 pins the descent down uniquely.

   Because the definition is purely equational — no quantification over
   the ambient category — every functor carries split coequalizers to
   split coequalizers ([functor_preserves_split]), hence to coequalizers
   ([split_coequalizer_preserved]).  Colimits preserved by all functors in
   this way are called *absolute* (Paré, "On absolute colimits", 1971;
   nLab: absolute colimit), and split coequalizers are the archetypal
   example.  They are the engine of Beck's monadicity theorem, where the
   canonical presentation of an algebra by free algebras is a split
   coequalizer after applying the forgetful functor. *)

(* The equational data: a cofork e over the pair, a section s splitting e,
   and a section t of f mediating between s ∘ e and the pair. *)
Record SplitCoequalizer {C : Category} {x y : C} (f g : x ~> y) := {
  scoeq_obj : C;

  scoeq_e : y ~> scoeq_obj;   (* the coequalizing map *)
  scoeq_s : scoeq_obj ~> y;   (* section of e *)
  scoeq_t : y ~> x;           (* section of f *)

  scoeq_law1 : scoeq_e ∘ f ≈ scoeq_e ∘ g;       (* e coforks the pair *)
  scoeq_law2 : scoeq_e ∘ scoeq_s ≈ id;          (* s splits e *)
  scoeq_law3 : f ∘ scoeq_t ≈ id;                (* t splits f *)
  scoeq_law4 : g ∘ scoeq_t ≈ scoeq_s ∘ scoeq_e  (* g ∘ t computes s ∘ e *)
}.

Arguments scoeq_obj  {_ _ _ _ _} _.
Arguments scoeq_e    {_ _ _ _ _} _.
Arguments scoeq_s    {_ _ _ _ _} _.
Arguments scoeq_t    {_ _ _ _ _} _.
Arguments scoeq_law1 {_ _ _ _ _} _.
Arguments scoeq_law2 {_ _ _ _ _} _.
Arguments scoeq_law3 {_ _ _ _ _} _.
Arguments scoeq_law4 {_ _ _ _ _} _.

(** ** A split coequalizer is a coequalizer *)

(* Descent through a split coequalizer: a coforking map h descends as
   h ∘ s, and the splitting of e makes this the only possibility. *)
Lemma split_coeq_desc {C : Category} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : scoeq_obj S ~> z, u ∘ scoeq_e S ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (h ∘ scoeq_s S).
  - (* (h ∘ s) ∘ e ≈ h: trade s ∘ e for g ∘ t (law 4), g for f under h
       (the cofork hypothesis), then cancel t against f (law 3) *)
    rewrite <- comp_assoc.
    rewrite <- (scoeq_law4 S).
    rewrite comp_assoc.
    rewrite <- Hh.
    rewrite <- comp_assoc.
    rewrite (scoeq_law3 S).
    apply id_right.
  - (* uniqueness: any v with v ∘ e ≈ h is v ∘ (e ∘ s) ≈ h ∘ s by law 2 *)
    intros v Hv.
    rewrite <- Hv.
    rewrite <- comp_assoc.
    rewrite (scoeq_law2 S).
    apply id_right.
Qed.

(* The elementary coequalizer carried by a split coequalizer. *)
Theorem split_coequalizer_is_coequalizer {C : Category} {x y : C}
  (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S).
Proof.
  exact {| cofork    := scoeq_law1 S
         ; coeq_desc := fun z h Hh => split_coeq_desc S h Hh |}.
Defined.

(** ** Absoluteness: every functor preserves split coequalizers *)

(* Push each datum through fmap; each law follows from the corresponding
   law in the source by functoriality.  The proof ends with [Defined] so
   that the transported data ([F (scoeq_obj S)], [fmap (scoeq_e S)], ...)
   remain visible to conversion in the corollary below. *)
Theorem functor_preserves_split {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  SplitCoequalizer f g → SplitCoequalizer (fmap[F] f) (fmap[F] g).
Proof.
  intros S.
  unshelve refine
    {| scoeq_obj := F (scoeq_obj S)
     ; scoeq_e   := fmap[F] (scoeq_e S)
     ; scoeq_s   := fmap[F] (scoeq_s S)
     ; scoeq_t   := fmap[F] (scoeq_t S) |}.
  - (* law 1 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law1 S).
  - (* law 2 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law2 S).
    apply fmap_id.
  - (* law 3 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law3 S).
    apply fmap_id.
  - (* law 4 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law4 S).
Defined.

(* The headline: the coequalizer of a split pair is preserved, in the
   elementary [IsCoequalizer] sense, by an arbitrary functor. *)
Corollary split_coequalizer_preserved {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer (fmap[F] f) (fmap[F] g)
    (F (scoeq_obj S)) (fmap[F] (scoeq_e S)).
Proof.
  exact (split_coequalizer_is_coequalizer
           (fmap[F] f) (fmap[F] g) (functor_preserves_split F f g S)).
Defined.
