Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The hom-functor Hom(-,-) : C^op ∏ C ⟶ Sets. *)

(* nLab: https://ncatlab.org/nlab/show/hom-functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor

   For a (locally small) category C, the hom-functor sends a pair of objects
   (a, b) to the hom-set hom[C] a b, regarded as a setoid object of Sets. On a
   morphism of C^op ∏ C — that is, a pair (f, g) with f : a' ~{C}~> a (an arrow
   a ~{C^op}~> a') and g : b ~{C}~> b' — it sends an arrow q : a ~> b to the
   composite g ∘ q ∘ f : a' ~> b', i.e. pre-compose with f and post-compose
   with g. The bifunctor is therefore contravariant in its first argument and
   covariant in its second; equivalently it is the identity profunctor on C.

   Fixing one argument yields the two partial hom-functors: the covariant
   Hom(a, -) : C ⟶ Sets (acting by post-composition) and the contravariant
   Hom(-, b) : C^op ⟶ Sets (acting by pre-composition). The curried form
   Curried_Hom : C^op ⟶ [C, Sets] packages the covariant family, and as a
   full and faithful embedding it is the Yoneda embedding (Yoneda_Full and
   Yoneda_Faithful below); this is the basis of representability, developed in
   Functor/Representable.v. Since hom-sets here are setoids, Hom lands in Sets,
   the category of setoids. *)

(* Bifunctors can be curried:

  C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) → E --> C → D → E

  Where ~~~ should be read as "Morally equivalent to".

  Note: We do not need to define Bifunctors as a separate class, since they
  can be derived from functors mapping to a category of functors. So in the
  following two definitions, [P] is effectively our bifunctor.

  The trick to [bimap] is that both the [Functor] instances we need (for
  [fmap] and [fmap1]), and the [Natural] instance, can be found in the
  category of functors we're mapping to by applying [P]. *)

Program Definition Hom `(C : Category) : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom C (fst p) (snd p)
                    ; is_setoid := @homset (C) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C^op ∏ C}~> y) =>
            (* g ↦ snd f ∘ g ∘ fst f: post-compose with the C-component
               (covariant in the second argument), pre-compose with the
               C^op-component (contravariant in the first). *)
            {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite !comp_assoc. Qed.

Program Definition Curried_Hom `(C : Category) : C^op ⟶ [C, Sets] := {|
  fobj := fun x => {|
    fobj := fun y => {| carrier := @hom C x y
                      ; is_setoid := @homset C x y |};
    fmap := fun y z (f : y ~{C}~> z) =>
              {| morphism := fun (g : x ~{C}~> y) =>
                               (f ∘ g) : x ~{C}~> z |}
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  unfold op.
  apply comp_assoc.
Qed.

Coercion Curried_Hom : Category >-> Functor.

Notation "[Hom A , ─]" := (@Curried_Hom _ A) : functor_scope.

(* Faithfulness of the Yoneda embedding: if f and g (arrows of C^op) induce
   the same natural transformation [Hom _,─] ⟹ [Hom _,─], then evaluating that
   transformation at the identity already forces f ≈ g. *)
#[export] Instance Yoneda_Faithful (C : Category) : Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same_nat_iso.
  simpl in same_nat_iso.
  specialize same_nat_iso with c id. now rewrite 2 id_left in same_nat_iso.
Qed.

(* Fullness of the Yoneda embedding: every natural transformation between hom-
   functors arises from a morphism, recovered as its component at the identity
   (the [prefmap] field, fun c d f => f c id). *)
#[export] Instance Yoneda_Full (C : Category) : Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

(* The fully-faithful Yoneda bijection on hom-sets: full + faithful means
   fmap[Curried_Hom C] is, in Sets, an isomorphism between (d ~> c) = (c ~{C^op}~> d)
   and the natural transformations [Hom c,─] ⟹ [Hom d,─] (here fobj[C] is the
   coercion of C through Curried_Hom). *)
Corollary Yoneda_Embedding' (C: Category) (c d : C) :
  @IsIsomorphism Sets {| carrier := hom d c |}
                 {| carrier := hom (fobj[C] c) (fobj[C] d) |}
                 {| morphism := @fmap _ _ (Curried_Hom C) c d;
                            proper_morphism := fmap_respects _ _ |}.
Proof.
  apply bijective_is_iso.
  - abstract(assert (H := Yoneda_Faithful C); constructor;
             intros x y eq; apply H; exact eq).
  - constructor. simpl.
    intro A; exists (@prefmap _ _ _ (Yoneda_Full C) _ _ A ).
    abstract(intros x f; unfold op;
             assert (M := @fmap_sur _ _ _ (Yoneda_Full C));
             specialize M with _ _ A; simpl in M;
             unfold op in M; apply M).
Defined.

(* The opposite hom-functor Hom_C^op(-,-) : C ∏ C^op ⟶ Sets, presented two
   ways. CoHom_Alt is Hom on C^op precomposed with the factor-swap Swap; on the
   pair (a, b) both forms give the set hom[C^op] a b = hom[C] b a, so they are
   the same bifunctor (covariant in the first argument, contravariant in the
   second). *)
Program Definition CoHom_Alt `(C : Category) : C ∏ C^op ⟶ Sets :=
  Hom C ◯ Swap.

Program Definition CoHom `(C : Category) : C ∏ C^op ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom (C^op) (fst p) (snd p)
                    ; is_setoid := @homset (C^op) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C ∏ C^op}~> y) =>
    {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite <- ! comp_assoc. Qed.

(* The curried contravariant hom-functor: Curried_CoHom C c = [Hom ─,c] is the
   presheaf Hom(-, c) : C^op ⟶ Sets, obtained as the covariant Curried_Hom on
   C^op. This is the contravariant Yoneda embedding C ⟶ [C^op, Sets] used to
   present presheaves. *)
Definition Curried_CoHom `(C : Category) : C ⟶ [C^op, Sets] :=
  Curried_Hom C^op.

Notation "[Hom ─ , A ]" := (@Curried_CoHom _ A) : functor_scope.
