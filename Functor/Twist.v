Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Twisting a functor by a family of isomorphisms *)

(* nLab: https://ncatlab.org/nlab/show/functor
   nLab: https://ncatlab.org/nlab/show/natural+isomorphism

   Given a functor [F : C ⟶ C] and a family of isomorphisms
   [α x : x ≅ F x] -- one for each object, with NO naturality assumed --
   the assignment

       x ↦ x,      f ↦ (α y)⁻¹ ∘ fmap[F] f ∘ α x

   is again an endofunctor of C, [Twist F α].  Functoriality needs nothing
   from α beyond invertibility: the identity law is [fmap_id] followed by
   [iso_from_to], and the composition law is [fmap_comp] with the inner
   [α y ∘ (α y)⁻¹] cancelled by [iso_to_from].

   The point of the construction is that its OBJECT FUNCTION IS THE
   IDENTITY, [fun x => x], on the nose, while its arrow function need not
   be the identity.  It is therefore the standard machine for producing
   two functors that agree on objects and differ on morphisms -- the
   question Mac Lane raises in "Categories for the Working Mathematician",
   2nd ed. (GTM 5), Section I.3 ("Functors"), where the reader is asked to
   find two different functors [Grp ⟶ Grp] whose object function is the
   identity, so that a functor is seen not to be determined by its action
   on objects.

   WHEN THE TWIST COLLAPSES.  [Twist_natural_strict_id] proves that if α
   IS natural -- [α y ∘ f ≈ fmap[F] f ∘ α x] for every f -- then
   [Twist F α] is strictly equal to [Id], because naturality lets the two
   copies of α annihilate across f.  [Twist_strict_id_natural] is the
   converse under uniqueness of identity proofs on the objects of C, so
   for a category whose objects have decidable equality the twist differs
   from the identity EXACTLY when α is not natural.  That is what makes
   Mac Lane's exercise awkward in a proof assistant: every natural family
   produces nothing new, and the families one can write uniformly in the
   object tend to be natural.  Instance/Grp/TwoFunctors.v works two such
   candidates out in full, and both do collapse.

   STRICT VERSUS WEAK EQUALITY OF FUNCTORS.  The library has two
   equivalences on [C ⟶ D].  [Functor_Setoid] (Theory/Functor.v:148),
   which is the hom-setoid of [Cat] (Instance/Cat.v:145), identifies two
   functors as soon as they are naturally isomorphic.
   [Functor_StrictEq_Setoid] (Theory/Functor.v:508), the hom-setoid of
   [StrictCat] (Instance/StrictCat.v:59), asks instead for a propositional
   equality of the object maps together with agreement of the arrow maps
   after transport along it; it refines the weak one
   ([strict_equiv_implies_fun_equiv], Instance/StrictCat/ToCat.v:57, and
   Test/Issue138.v:109 pins both hom-setoids).

   The twist sits exactly on that seam.  [Twist_Id_weak_equiv] shows that
   for F = Id the twisted functor is ALWAYS identified with [Id] by the
   weak setoid -- α itself is the witnessing natural isomorphism, and its
   coherence condition holds by construction rather than by an argument.
   So a separation of [Twist Id α] from [Id] can only be a separation in
   the strict setoid, and that is the sense in which Mac Lane's exercise
   has to be read here. *)

Section Twist.

Context {C : Category}.
Context (F : C ⟶ C).
Context (α : ∀ x : C, x ≅ F x).

#[local] Obligation Tactic := idtac.

(* The twisted functor.  Note [fobj := fun x => x]: the object function is
   the identity function itself, not merely a function isomorphic to it. *)
Program Definition Twist : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y f => (α y)⁻¹ ∘ fmap[F] f ∘ α x
|}.
Next Obligation.
  intros x y f g Hfg.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite (comp_assoc (α y)).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* The object function is the identity, by computation.  The [=] is on
   OBJECTS, which is where this library does use propositional equality --
   it is what [Functor_StrictEq_Setoid] compares; morphisms are compared
   with ≈ everywhere. *)
Lemma Twist_fobj (x : C) : fobj[Twist] x = x.
Proof. reflexivity. Qed.

(* If α is natural, the twist is strictly equal to the identity functor:
   the object equalities are all [eq_refl], and the arrow condition is
   α cancelling itself across f. *)
Theorem Twist_natural_strict_id
  (nat : ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C).
Proof.
  exists (fun _ => eq_refl).
  intros x y f.
  (* Both transports are along [eq_refl], hence the identity, so the
     coherence condition reduces by conversion to the arrow maps agreeing. *)
  change ((α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f).
  rewrite <- comp_assoc.
  rewrite <- nat.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(* The converse, given uniqueness of identity proofs on the objects of C.
   The hypothesis is needed because the strict setoid allows an ARBITRARY
   proof of [x = x] as the object component; without [uip] a nontrivial
   loop could in principle scramble the transports. *)
Theorem Twist_strict_id_natural
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  (H : @equiv _ Functor_StrictEq_Setoid Twist (@Id C)) :
  ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x.
Proof.
  destruct H as [eq_on_obj coherent].
  intros x y f.
  pose proof (coherent x y f) as Hc.
  rewrite (uip x (eq_on_obj x)), (uip y (eq_on_obj y)) in Hc.
  (* with both object equalities [eq_refl] the transports vanish *)
  assert (Hred : (α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f) by exact Hc.
  assert (Hpost : α y ∘ ((α y)⁻¹ ∘ fmap[F] f ∘ α x) ≈ α y ∘ f)
    by (apply compose_respects; [ reflexivity | exact Hred ]).
  rewrite <- Hpost.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* The distinctness criterion in the form it is used: a SINGLE morphism at
   which α is not natural separates the twist from the identity in
   the strict functor setoid. *)
Corollary Twist_not_strict_id
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  {x y : C} {f : x ~> y}
  (Hnat : α y ∘ f ≈ fmap[F] f ∘ α x → False) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C) → False.
Proof.
  intro H.
  exact (Hnat (Twist_strict_id_natural uip H x y f)).
Qed.

End Twist.

Arguments Twist {C} F α.

(* Uniqueness of identity proofs from decidable equality of objects
   (Hedberg's argument, via the stdlib's axiom-free [UIP_dec]); this is
   how the [uip] hypothesis above is discharged for the concrete
   categories used as witnesses. *)
Definition uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x <> y}) (x : A) (p : x = x) : p = eq_refl :=
  UIP_dec dec p eq_refl.

Section TwistId.

Context {C : Category}.
Context (α : ∀ x : C, x ≅ x).

(* The twist of the IDENTITY functor is always naturally isomorphic to the
   identity functor -- α is the natural isomorphism, and the coherence
   condition of [Functor_Setoid] is literally the definition of the
   twisted arrow map.  Hence the weak setoid, which is the hom-setoid of
   [Cat], never separates this pair, however far α is from being natural. *)
Theorem Twist_Id_weak_equiv :
  @equiv _ Functor_Setoid (Twist (@Id C) α) (@Id C).
Proof.
  exists α.
  intros x y f; simpl.
  reflexivity.
Qed.

End TwistId.
