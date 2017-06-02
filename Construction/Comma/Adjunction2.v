Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Hom.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Comma.Adjunction.Lib.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section AdjunctionComma.

Context {C : Category}.
Context {D : Category}.
Context {G : C ⟶ D}.
Context {F : D ⟶ C}.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
   : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
   1x → k in B ↓ p that is universal from i to k."

   Lawvere's own statement of the theorem, from his thesis (page 40):

   "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
   is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
   and a map φ : B ~> Af in B such that for every object A′ ∈ |A| and every
   map x : B ~> A′f in B, there exists a unique map y : A ~> A′ in A such that
   x = φ(yf) in B."

   Repeating this using the names and syntax of this module:

   "∀ (G : C ⟶ D) (F : D ⟶ C), F ⊣ G ↔
      ∀ a : D, ∃ (b : C) (phi : a ~{D}~> G b),
        ∀ (b' : C) (psi : a ~{D}~> G b'),
          ∃! y : b ~{C}~> b',
            psi ≈ fmap[G] y ∘ phi" *)

Program Definition Adjunction_to_Comma (A : F ⊣ G) :
  @fibered_equivalence _ _ F G := {|
  fiber_iso := Comma_F_Id_Id_G_Iso A
|}.

Context (E : @fibered_equivalence _ _ F G).

Local Obligation Tactic := simpl; intros.

Program Instance comma_projF_iso (f : (F ↓ Id)) :
  `1 f ≅ `1 (to (fiber_iso E) f) := `1 (projF E) f.

(*
Program Instance comma_projF_iso_respects a b (f g : F a ~> b) :
  f ≈ g ->
  (a, b) ≅[D ∏ C] `1 (to (fiber_iso E) ((a, b); f)) ->
  (a, b) ≅[D ∏ C] `1 (to (fiber_iso E) ((a, b); g)).
Next Obligation.
  destruct H0; simpl in *.
  exact (fst (to H0), snd (to H0)).
Qed.
*)

Program Instance comma_projG_iso (f : (Id ↓ G)) :
  `1 f ≅ `1 (from (fiber_iso E) f) := `1 (projG E) f.

Definition comma_to a b (f : F a ~> b) : a ~> G b :=
  let g := ((a, b); f) in
  fmap[G] (snd (comma_projF_iso g)⁻¹)
    ∘ `2 (to (fiber_iso E) g)
    ∘ fst (to (comma_projF_iso g)).

Definition comma_from a b (f : a ~> G b) : F a ~> b :=
  let g := ((a, b); f) in
  snd (comma_projG_iso g)⁻¹
    ∘ `2 (from (fiber_iso E) g)
    ∘ fmap[F] (fst (to (comma_projG_iso g))).

Program Instance comma_to_respects a b :
  Proper (equiv ==> equiv) (comma_to a b).
Next Obligation.
  proper.
(*
  unfold comma_to.
  Notation "f ∘[ X ] g" :=
    (@compose _%category _%object X%object _%object f%morphism g%morphism)
    (at level 40, format "'[v' f '/'   ∘[  X  ] '//' g ']'") : morphism_scope.
  simpl.

  pose (snd (to (comma_projF_iso ((a, b); y)))
            ∘ y ∘ fmap[F] (fst (from (comma_projF_iso ((a, b); y))))) as g.
  given (hh : { f : (a ~{ D }~> fst `1 (to (fiber_iso E) ((a, b); y))) *
                    (b ~{ C }~> snd `1 (to (fiber_iso E) ((a, b); y)))
              & g ∘ fmap[F] (fst f) ≈ snd f ∘ x }).
    exists (fst (to (comma_projF_iso ((a, b); y))),
            snd (to (comma_projF_iso ((a, b); y)))).
    abstract (
      unfold g; simpl;
      rewrite <- !comp_assoc;
      rewrite <- !fmap_comp;
      srewrite (fst (iso_from_to (comma_projF_iso ((a, b); y))));
      rewrite fmap_id, id_right;
      rewrite X;
      reflexivity).
  destruct (`2 (projF E) ((a, b); x)
             ((fst `1 (to (fiber_iso E) ((a, b); y)),
               snd `1 (to (fiber_iso E) ((a, b); y))); g) hh).
  simpl in e, e0.
  unfold comma_projF_iso in *.
  rewrite e; clear e.
  comp_right.

  (* pose proof (`2 (@fmap _ _ (to (fiber_iso E)) *)
  (*                       ((a, b); x) *)
  (*                       ((fst `1 (to (fiber_iso E) ((a, b); y)), *)
  (*                         snd `1 (to (fiber_iso E) ((a, b); y))); g) hh)). *)
  (* simpl in X0. *)

  pose (snd (to (comma_projF_iso ((a, b); y)))
            ∘ y ∘ fmap[F] (fst (from (comma_projF_iso ((a, b); y))))) as h.
  given (ii : { f : (fst `1 (to (fiber_iso E) ((a, b); y)) ~{ D }~> a) *
                    (snd `1 (to (fiber_iso E) ((a, b); y)) ~{ C }~> b)
              & x ∘ fmap[F] (fst f) ≈ snd f ∘ h }).
    exists (fst (from (comma_projF_iso ((a, b); y))),
            snd (from (comma_projF_iso ((a, b); y)))).
    abstract (
      unfold h; simpl;
      rewrite !comp_assoc;
      srewrite (snd (iso_from_to (comma_projF_iso ((a, b); y))));
      rewrite id_left;
      rewrites.
      reflexivity).
  destruct (`2 (projF E) ((fst `1 (to (fiber_iso E) ((a, b); y)),
                           snd `1 (to (fiber_iso E) ((a, b); y))); h)
             ((a, b); x) ii).
  simpl in e, e1.
  unfold comma_projF_iso in *.
  rewrites.
  rewrite !fmap_comp.
  comp_left.

  pose proof (`2 (@fmap _ _ (to (fiber_iso E))
                        ((fst `1 (to (fiber_iso E) ((a, b); y)),
                          snd `1 (to (fiber_iso E) ((a, b); y))); h)
                        ((a, b); x) ii)).
  simpl in X.


  given (jj : { f : (a ~{ D }~> a) * (b ~{ C }~> b)
              & x ∘ fmap[F] (fst f) ≈ snd f ∘ y }).
    exists (id, id); abstract cat.
  pose proof (`2 (@fmap _ _ (to (fiber_iso E)) ((a, b); y) ((a, b); x) jj)).
  simpl in X1.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
*)

(*
  remember (fmap[G] (snd _ ∘ snd _)) as H.
  enough (H ≈ fmap[G] (snd `1 (@fmap _ _ (to (fiber_iso E))
                                     ((a, b); y) ((a, b); x) jj))).
    rewrites.
    rewrites.
    rewrite <- (id_right (`2 (to (fiber_iso E) ((a, b); x)))).
    comp_left.

  rewrites.
  apply fmap_respects.
  rewrite <- (id_left (snd _)).
  pose proof (snd (iso_to_from (comma_projF_iso ((a, b); x)))).
  unfold comma_projF_iso in X1; simpl in X1.
  rewrites.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (snd _) (snd _) (snd _)).
  rewrites.
  unfold jj.
*)
Admitted.

Program Instance comma_from_respects a b :
  Proper (equiv ==> equiv) (comma_from a b).
Next Obligation.
Admitted.

Theorem comma_to_from a b f : comma_to a b (comma_from a b f) ≈ f.
Proof.
Admitted.

Theorem comma_from_to a b f : comma_from a b (comma_to a b f) ≈ f.
Proof.
Admitted.

Program Definition comma_iso a b : F a ~> b ≊ a ~> G b := {|
  to   := {| morphism := comma_to   a b |};
  from := {| morphism := comma_from a b |}
|}.
Next Obligation. apply comma_to_from. Qed.
Next Obligation. apply comma_from_to. Qed.

Theorem comma_to_natural_dom a b c (f : F a ~> b) (g : c ~> a) :
  comma_to _ _ f ∘ g ≈ comma_to _ _ (f ∘ fmap[F] g).
Proof.
  unfold comma_to, comma_projF_iso.
  given (hh : { f0 : (c ~{ D }~> a) * (b ~{ C }~> b)
              & f ∘ fmap[F] (fst f0) ≈ snd f0 ∘ (f ∘ fmap[F] g) }).
    exists (g, id); abstract cat.
  destruct (`2 (projF E) ((c, b); f ∘ fmap[F] g) ((a, b); f) hh);
  simpl in e, e0; rewrite e at 1; clear e.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (fst _)).
  srewrite (fst (iso_to_from (comma_projF_iso ((a, b); f)))).
  rewrite id_left.
  comp_right.
  pose proof (`2 (@fmap _ _ (to (fiber_iso E))
                        ((c, b); f ∘ fmap[F] g) ((a, b); f) hh)).
  simpl in X.
  rewrite <- comp_assoc.
  rewrites.
  comp_right.
  rewrite <- fmap_comp.
  apply fmap_respects.
  symmetry.
  rewrite <- (id_left (snd _)).
  rewrites.
  comp_left.
  rewrite <- (id_right (snd _)) at 2.
  comp_left.
  sapply (snd (iso_to_from (comma_projF_iso ((c, b); f ∘ fmap[F] g)))).
Qed.

Theorem comma_to_natural_cod a b c (h : b ~{C}~> c) (f : F a ~> b) :
  fmap[G] h ∘ comma_to _ _ f ≈ comma_to _ _ (h ∘ f).
Proof.
  unfold comma_to, comma_projF_iso.
  given (hh : { f0 : (a ~{ D }~> a) * (b ~{ C }~> c)
              & h ∘ f ∘ fmap[F] (fst f0) ≈ snd f0 ∘ f }).
    exists (id, h); abstract cat.
  destruct (`2 (projF E) ((a, b); f) ((a, c); h ∘ f) hh);
  simpl in e, e0; rewrite e0 at 1; clear e0.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (snd _)).
  srewrite (snd (iso_to_from (comma_projF_iso ((a, b); f)))).
  rewrite id_right.
  rewrite fmap_comp.
  comp_left.
  pose proof (`2 (@fmap _ _ (to (fiber_iso E))
                        ((a, b); f) ((a, c); h ∘ f) hh)).
  simpl in X.
  rewrite comp_assoc.
  rewrites.
  comp_left.
  symmetry.
  rewrite <- (id_right (fst _)).
  rewrites.
  comp_right.
  rewrite <- (id_left (fst `1 _)) at 2.
  comp_right.
  sapply (fst (iso_to_from (comma_projF_iso ((a, c); h ∘ f)))).
Qed.

Theorem comma_to_natural a b c d (h : b ~{C}~> c) (f : F a ~> b) (g : d ~> a) :
  fmap[G] h ∘ comma_to _ _ f ∘ g ≈ comma_to _ _ (h ∘ f ∘ fmap[F] g).
Proof.
  rewrite <- comp_assoc.
  rewrite comma_to_natural_dom.
  rewrite comma_to_natural_cod.
  rewrite comp_assoc.
  reflexivity.
Qed.

Theorem comma_from_natural_dom a b c (f : a ~> G b) (g : c ~> a) :
  comma_from _ _ f ∘ fmap[F] g ≈ comma_from _ _ (f ∘ g).
Proof.
Admitted.

Theorem comma_from_natural_cod a b c (h : b ~{C}~> c) (f : a ~> G b) :
  h ∘ comma_from _ _ f ≈ comma_from _ _ (fmap[G] h ∘ f).
Proof.
Admitted.

Theorem comma_from_natural a b c d (h : b ~{C}~> c) (f : a ~> G b) (g : d ~> a) :
  h ∘ comma_from _ _ f ∘ fmap[F] g ≈ comma_from _ _ (fmap[G] h ∘ f ∘ g).
Proof.
  rewrite <- comp_assoc.
  rewrite comma_from_natural_dom.
  rewrite comma_from_natural_cod.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition Adjunction_from_Comma : Adjunction_Hom F G := {|
  hom_adj :=
    {| to   := {| transform := fun X =>
         {| morphism := @comma_to _ _ |} |}
     ; from := {| transform := fun X =>
         {| morphism := @comma_from _ _ |} |} |}
|}.
Next Obligation. apply comma_to_natural. Qed.
Next Obligation. symmetry; apply comma_to_natural. Qed.
Next Obligation. apply comma_from_natural. Qed.
Next Obligation. symmetry; apply comma_from_natural. Qed.
Next Obligation. cat; apply (iso_to_from (comma_iso _ _) _). Qed.
Next Obligation. cat; apply (iso_from_to (comma_iso _ _) _). Qed.

End AdjunctionComma.
