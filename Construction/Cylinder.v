(** * The cylinder C ∏ 2 and the universal natural transformation *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.3, printed p. 39 (PDF 49), display (6), and §II.4
              Exercise 8, printed p. 42 (PDF 52) —
              maclane:II.3:construction5, maclane:II.4:ex8
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
              Example 7.16, printed p. 171 (PDF pp. 180–181) —
              awodey:7.7:example16
   Book:      Riehl, "Category Theory in Context" (Dover, 2016), §1.5,
              Lemma 1.5.1 (printed p. 31) and Exercise 1.5.i (printed
              p. 38) — riehl:1.5:lem1, riehl:1.5:exi
   nLab:      https://ncatlab.org/nlab/show/natural+transformation

   The cylinder on a category C is the product C ∏ 2 with the walking
   arrow: two copies of C joined by connecting arrows, a directed
   homotopy cylinder.  It carries a transformation μ between the two
   inclusion functors that is UNIVERSAL: every natural transformation
   τ : S ⟹ T between functors out of C is obtained from μ by a
   functor on the cylinder, uniquely so among functors restricting to
   S and T on the two ends AND carrying μ to τ (the third condition
   is load-bearing: functors merely restricting to two constants are
   the arrows between them).  This is Mac Lane's construction 5
   (display (6) of §II.3), Riehl's Lemma 1.5.1 with Exercise 1.5.i
   its deferred proof, and — under the exponential transpose of Cat —
   Awodey's "transcendental deduction" of the arrows of a functor
   category, connecting to the arrow-category encoding of Exercise
   II.4.8.

     - [Cyl_incl0]/[Cyl_incl1]: the two inclusions C ⟶ C ∏ 2, as
       named functors, with [Cyl_restrict0]/[Cyl_restrict1] the
       restriction-along-them operations (so the bijection reads
       "restricts to S and T", per Riehl's phrasing)
     - [Cyl_mu]: the universal transformation μ : Cyl_incl0 ⟹
       Cyl_incl1, component (id[c], the walking arrow)
     - [Cyl_functor τ]: the classifying functor of τ on the cylinder,
       with [Cyl_restrict0_eq]/[Cyl_restrict1_eq] (it restricts to S
       and T, with definitional components) and [Cyl_functor_mu] (it
       carries μ to τ)
     - [Cyl_functor_unique]: any functor restricting to S and T and
       carrying μ to τ (through the chosen restriction isomorphisms)
       is ≈ [Cyl_functor τ]
     - [cylinder_universal]: the universal property bundled as a
       unique existence statement
     - [Cyl_extract]/[Cyl_functor_Cyl_extract]: the inverse leg of
       Riehl's bijection — every functor on the cylinder IS the
       classifier of the transformation it carries (its whiskering
       of μ), closing the correspondence in both directions
     - [cylinder_arrow_agree] (in Construction/Cylinder/Arrow.v —
       see note 4): the exponential transpose carries the cylinder
       encoding to the arrow-category encoding

   Design:

   1. THE CLASSIFYING FUNCTOR IS A DEPENDENT MATCH ON THE WALKING
      ARROW.  [Cyl_functor τ] sends (c, TwoX) to S c and (c, TwoY) to
      T c, and a morphism (f, g) by cases on g: the two identity ends
      act by S and T, and the crossing arrow acts by the composite
      τ ∘ S f — equal to T f ∘ τ by naturality, which is exactly what
      makes the functor laws close (the mixed composition case IS the
      naturality square).

   2. THE WHISKER CONDITION IS STATED THROUGH THE RESTRICTION
      ISOMORPHISMS.  For the chosen [Cyl_functor τ] the restrictions
      are definitional and [Cyl_functor_mu] reads literally; for an
      arbitrary competitor F' the condition must be transported
      along the given [Functor_Setoid] witnesses σ0, σ1, in the same
      intertwining form Construction/Arrow/Functor.v uses for its
      triple setoid: to (σ1 c) ∘ F'(μ c) ≈ τ c ∘ to (σ0 c).  The
      hom-equivalence is written with an explicit [@equiv]/[@homset]
      to fix the intended hom-setoid in the statement itself.

   3. UNIQUENESS DERIVES THE CROSSING CASE FROM THE ENDS.  A
      competitor agrees with [Cyl_functor τ] on the ends by σ0/σ1's
      own conjugate naturality; on the crossing morphisms it is
      forced because (f, TwoXY) factors as μ c' ∘ (f, TwoIdX) in the
      cylinder, so the whisker condition plus the σ0-naturality
      determine it.  No condition beyond the three stated is needed.

   4. THE EXERCISE-8 / AWODEY COMPARISON LIVES ONE FILE OVER.
      Relating this encoding to functors into the arrow category
      goes through [Cat_Closed]'s exponential transpose at exponent
      [_2]; the composite there measures at [Category@{Set Set Set}]
      — object universe included — so it cannot be applied above
      [Set].  This file is free of any Set-level pin — the cylinder
      itself never mentions [Fun] — so the comparison is quarantined
      in Construction/Cylinder/Arrow.v, keeping the universal
      property here at the library's general levels (with only the
      ambient h = p constraint every [Functor] statement carries;
      verified by instantiation strictly above [Set]). *)

(** ** The two inclusions and the universal transformation *)

Program Definition Cyl_incl0 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoX);
  fmap := fun _ _ f => (f, TwoIdX)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

Program Definition Cyl_incl1 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoY);
  fmap := fun _ _ f => (f, TwoIdY)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

(* Restriction along the inclusions: the two ends of a functor on the
   cylinder. *)
Definition Cyl_restrict0 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl0.
Definition Cyl_restrict1 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl1.

(* The universal natural transformation: at each c, the connecting
   arrow of the cylinder. *)
Program Definition Cyl_mu {C : Category} :
  @Cyl_incl0 C ⟹ @Cyl_incl1 C := {|
  transform := fun c => (id[c], TwoXY)
|}.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.

(** ** The classifying functor of a transformation *)

Program Definition Cyl_functor {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : C ∏ _2 ⟶ B := {|
  fobj := fun p => match snd p with
                   | TwoX => S (fst p)
                   | TwoY => T (fst p)
                   end;
  fmap := fun p q fg =>
    match snd fg in TwoHom t t'
      return (match t with TwoX => S (fst p) | TwoY => T (fst p) end
                ~{B}~>
              match t' with TwoX => S (fst q) | TwoY => T (fst q) end)
    with
    | TwoIdX => fmap[S] (fst fg)
    | TwoIdY => fmap[T] (fst fg)
    | TwoXY  => τ (fst q) ∘ fmap[S] (fst fg)
    end
|}.
Next Obligation.
  intros C B S T τ [c t] [c' t'] [f g] [f' g'] [Hf Hg]; simpl in *.
  subst g'.
  destruct g; simpl; now rewrite Hf.
Qed.
Next Obligation.
  intros C B S T τ [c t]; simpl.
  destruct t; simpl; apply fmap_id.
Qed.
Next Obligation.
  (* destruct the walking-arrow OBJECTS first, so _2's composition — a
     match on objects — reduces before the homs are inverted *)
  intros C B S T τ [c t] [c' t'] [c'' t''] [f g] [f' g']; simpl in *.
  destruct t, t', t'';
  try contradiction (TwoHom_Y_X_absurd g);
  try contradiction (TwoHom_Y_X_absurd g');
  pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g;
  pose proof (TwoHom_inv _ _ g') as Hg'; simpl in Hg'; subst g'; simpl.
  - apply fmap_comp.
  - (* crossing after an X-endomorphism *)
    rewrite fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
  - (* Y-endomorphism after the crossing: the naturality square *)
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite <- (naturality[τ]).
    rewrite <- !comp_assoc.
    reflexivity.
  - apply fmap_comp.
Qed.

(** ** The three defining properties *)

(* Restricting the classifying functor to either end recovers the given
   functor, with definitional components. *)
Program Definition Cyl_restrict0_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict0 (Cyl_functor τ) ≈ S :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

Program Definition Cyl_restrict1_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict1 (Cyl_functor τ) ≈ T :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

(* The classifying functor carries the universal transformation to the
   given one. *)
Lemma Cyl_functor_mu {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ c : C, fmap[Cyl_functor τ] (Cyl_mu c) ≈ τ c.
Proof.
  intro c; simpl; cat.
Qed.

(** ** Uniqueness *)

(* Any functor on the cylinder restricting to S and T and carrying μ to
   τ — through the chosen restriction isomorphisms, in the intertwining
   form — is equivalent to the classifying functor. *)
Theorem Cyl_functor_unique {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T)
        (F' : C ∏ _2 ⟶ B)
        (σ0 : Cyl_restrict0 F' ≈ S) (σ1 : Cyl_restrict1 F' ≈ T)
        (Hμ : ∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1 c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0 c))) :
  F' ≈ Cyl_functor τ.
Proof.
  unshelve eexists.
  - intros [c t]; destruct t; simpl.
    + exact (`1 σ0 c).
    + exact (`1 σ1 c).
  - intros [c t] [c' t'] [f g]; simpl.
    destruct t, t';
    try contradiction (TwoHom_Y_X_absurd g);
    pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g; simpl.
    + exact (`2 σ0 c c' f).
    + (* the crossing case: factor (f, TwoXY) ≈ μ c' ∘ (f, TwoIdX) *)
      assert (Hfact : fmap[F'] ((f, TwoXY) : (c, TwoX) ~{C ∏ _2}~> (c', TwoY))
                        ≈ fmap[F'] (Cyl_mu c')
                            ∘ fmap[F'] ((f, TwoIdX) :
                                (c, TwoX) ~{C ∏ _2}~> (c', TwoX))). {
        rewrite <- fmap_comp.
        apply fmap_respects; split; simpl; cat.
      }
      rewrite Hfact.
      (* express F'(μ c') via Hμ and F'(f, TwoIdX) via σ0's naturality *)
      assert (Hmu : fmap[F'] (Cyl_mu c')
                      ≈ from (`1 σ1 c') ∘ (τ c' ∘ to (`1 σ0 c'))). {
        rewrite <- (Hμ c').
        rewrite comp_assoc.
        rewrite iso_from_to, id_left.
        reflexivity.
      }
      rewrite Hmu.
      rewrite (`2 σ0 c c' f); simpl.
      rewrite !comp_assoc.
      rewrite <- (comp_assoc _ (to (`1 σ0 c'))).
      rewrite iso_to_from, id_right.
      reflexivity.
    + exact (`2 σ1 c c' f).
Qed.

(* The universal property, bundled: τ is classified by a functor on the
   cylinder restricting to S and T and carrying μ to τ, uniquely up to
   the ambient functor equivalence. *)
Theorem cylinder_universal {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  { F : C ∏ _2 ⟶ B
  & { σ0 : Cyl_restrict0 F ≈ S
    & { σ1 : Cyl_restrict1 F ≈ T
      & (∀ c, @equiv _ (@homset B (F (c, TwoX)) (T c))
            (to (`1 σ1 c) ∘ fmap[F] (Cyl_mu c))
            (τ c ∘ to (`1 σ0 c)))
        * (∀ F' (σ0' : Cyl_restrict0 F' ≈ S) (σ1' : Cyl_restrict1 F' ≈ T),
             (∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1' c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0' c))) →
             F' ≈ F) } } }.
Proof.
  exists (Cyl_functor τ), (Cyl_restrict0_eq τ), (Cyl_restrict1_eq τ); split.
  - intro c; simpl; cat.
  - intros F' σ0' σ1' Hμ'.
    exact (Cyl_functor_unique τ F' σ0' σ1' Hμ').
Qed.

(** ** The inverse leg: every cylinder functor classifies its own
       transformation *)

(* Reading the transformation off a functor on the cylinder: whisker
   the universal transformation.  Its component at c is
   [fmap[F] (Cyl_mu c)]. *)
Definition Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  Cyl_restrict0 F ⟹ Cyl_restrict1 F :=
  F ⊳ @Cyl_mu C.

(* The round trip: F is the classifier of the transformation it
   carries, through transparent reflexivity witnesses (Construction/
   Arrow/Functor.v's [fs_refl]).  With [cylinder_universal] this
   closes Riehl's bijection in both directions. *)
Theorem Cyl_functor_Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  F ≈ Cyl_functor (Cyl_extract F).
Proof.
  apply (Cyl_functor_unique (Cyl_extract F) F (fs_refl _) (fs_refl _)).
  intro c; simpl; cat.
Qed.
