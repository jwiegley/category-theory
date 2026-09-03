Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Functors between slice categories induced by a base morphism. *)

(* nLab: https://ncatlab.org/nlab/show/base+change
   nLab: https://ncatlab.org/nlab/show/dependent+sum
   nLab: https://ncatlab.org/nlab/show/over+category
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)
   Book:      Mac Lane, "Categories for the Working Mathematician",
              2nd ed., Springer GTM 5, 1998, SS IV.5, printed p. 97,
              Exercise 3 (catalog id maclane:IV.5:ex3)

   Mac Lane's Exercise 3 reads, verbatim from the printed page:

     "For C a category with pullbacks, each arrow f : a→a' defines a
      functor (C↓f) = f_*: (C↓a)→(C↓a') which carries each object
      x→a of (C↓a) to the composite x→a→a'.  Show that f_* has a
      right adjoint f* with f*(x'→a') = y→a, where y is the vertex
      of the pullback of a→a'←x'."

   A NOTE ON HIS NOTATION, since it collides with this file's.  He
   writes f_* for POST-COMPOSITION, where this file and the nLab
   write f_! or Σ_f -- that is [Bang_Functor] below -- while his f*
   is this file's [Star_Functor].  So his displayed conclusion, that
   f_* has a right adjoint f*, IS [Base_Functor_Adjunction] with the
   names translated, and his "y is the vertex of the pullback" is
   [Pull].

   A morphism f : a ~> b in C induces two functors between the slice
   categories C ̸ a and C ̸ b:

   - Bang_Functor f : C ̸ a ⟶ C ̸ b is the dependent sum Σ_f (also
     written f_!, "lower shriek"), defined by post-composition with f:
     it sends an object (o; h) with h : o ~> a to (o; f ∘ h), an object
     over b.  This needs no extra structure on C.

   - Star_Functor f : C ̸ a ⟶ C ̸ c is the base change (pullback)
     functor f*, defined by pulling back along f: given f : c ~> a, it
     sends an object (o; h) with h : o ~> a to (Pull h f;
     pullback_snd h f), the fiber product o ×_a c equipped with its
     projection to c.  This requires that the relevant pullbacks exist
     in C, which is assumed below as the Hypothesis [pullbacks].

   The theorem of this file is that the two are adjoint, dependent sum
   on the LEFT and base change on the RIGHT: for a single f : a ~> b,
   [Base_Functor_Adjunction] inhabits

       Bang_Functor f ⊣ Star_Functor f,   i.e.   Σ_f ⊣ f*

   with the class of Theory/Adjunction.v, so the left adjoint is the
   functor C ̸ a ⟶ C ̸ b and the right adjoint is the functor
   C ̸ b ⟶ C ̸ a obtained by instantiating [Star_Functor] at the same
   f (its declared shape `(f : c ~> a) : C ̸ a ⟶ C ̸ c reads, at our
   f : a ~> b, as C ̸ b ⟶ C ̸ a).  The orientation matters, and the
   opposite reading Star_Functor f ⊣ Bang_Functor f -- which an earlier
   commented sketch in this file proposed -- is NOT ill formed: both
   functors have the shapes the class wants once the roles are swapped,
   so it is a well typed statement that is simply not true in general.
   Test/ProbeBaseChange387.v measures both halves of that: it records
   the reversed statement as formable, and [reversed_orientation_refuted]
   there compiles a counterexample over Sets along the unique morphism
   ∅ ~> 1, where the unit such an adjunction would supply is a map from
   the singleton into a setoid with uninhabited carrier -- the pullback
   object, whose carrier is a sub-setoid of 1 × ∅.

   The hom-set bijection is the universal property of the chosen
   pullback, read twice.  For x = (o; h) over a and y = (p; k) over b, a
   slice morphism Σ_f x ~> y is a C-morphism g : o ~> p with
   k ∘ g ≈ f ∘ h, and that equation is precisely the square condition of
   the competing cone ⟨g, h⟩ over the pullback square of k along f; the
   mediator it produces is the transposed morphism x ~> f* y, its
   [pullback_snd] leg equation being the slice condition over a.
   Conversely a morphism into the pullback is turned back by
   post-composing with [pullback_fst].  Because the slice hom-setoid of
   Construction/Slice.v compares only the underlying C-morphism, both
   round trips, both respectfulness obligations and both naturality
   clauses are equations in C alone, and each is one appeal to the
   uniqueness half of the universal property.

   Unit and counit are named.  [bang_star_unit] at (o; h) is the
   comparison of o into the pullback of f ∘ h along f -- the mediator of
   the cone ⟨id, h⟩, whose square condition is (f ∘ h) ∘ id ≈ f ∘ h.
   [bang_star_counit] at (p; k) is the pullback projection
   [pullback_fst k f], whose slice condition k ∘ fst ≈ f ∘ snd IS
   [pullback_commutes] verbatim, with no proof of its own.  Read their
   identification with the class's η and ε at the strength measured, not
   the one hoped for: the class's counit IS this projection composed
   with a residual [id], on the nose ([bang_star_counit_strict]), and
   the class's unit IS [base_to_mor] of the slice identity, on the nose
   ([bang_star_unit_strict]), while against [bang_star_unit_mor] and
   [bang_star_counit_mor] themselves only ≈ holds.  On the unit side
   that is not the residual [id] but the PROOF argument: both sides are
   mediators of the same cone ⟨id, h⟩, and [ump_pullbacks] takes the
   square condition as an argument on which the mediator depends, so
   feeding it the slice identity's own witness and feeding it
   [id_right (f ∘ h)] give two mediators related by [uniqueness] and not
   by conversion.

   What is NOT built here.  When C is locally cartesian closed, f*
   itself has a further right adjoint Π_f (the dependent product),
   giving the string Σ_f ⊣ f* ⊣ Π_f.  Π_f is not constructed, and the
   reason is measured rather than guessed: no class of local cartesian
   closure is declared anywhere in this tree (the phrase occurs only in
   prose, in Structure/Pullback.v, Construction/Slice.v and
   Instance/Sets.v), and Structure/Cartesian/Closed.v's [Closed] is a
   structure on C over a [Cartesian C], while no [Cartesian] instance
   for a slice category is declared either -- so the dependent product
   would have to be built from scratch.  That is left for a later
   effort, and nothing below depends on it.  Also not delivered: no
   Beck-Chevalley condition, no comparison of this adjunction with the
   codomain fibration of Construction/Displayed/Codomain.v, no
   monad or comonad from the adjunction, and no statement about when the
   unit or counit is an isomorphism. *)

Section SliceFunctors.

Context `{C : Category}.

#[local] Set Transparent Obligations.

(* Dependent sum Σ_f (= f_!): post-compose the structure morphism with f. *)
Program Definition Bang_Functor `(f : a ~> b) : @Slice C a ⟶ @Slice C b := {|
  fobj := λ '(o; h), (o; f ∘ h);
  fmap := λ x y f, (_; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  now rewrite X.
Qed.

(* Postfix notation for Σ_f, mirroring the standard f_! ("lower shriek"). *)
Notation "f !" := (Bang_Functor f) (at level 90) : category_scope.

(* C has all binary pullbacks; this is what makes base change f* below total. *)
Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g.

(* Base change f*: pull the structure morphism back along f, taking the
   resulting projection onto c as the new structure morphism over c. *)
Program Definition Star_Functor `(f : c ~> a) :
  @Slice C a ⟶ @Slice C c := {|
  fobj := λ '(_; h),
            let pull : Pullback h f := pullbacks h f in
            (Pull h f pull; pullback_snd h f pull);
  fmap := λ '(a; x) '(b; y) '(g; H),
            let ypb : Pullback y f := pullbacks y f in
            let xpb : Pullback x f := pullbacks x f in
            let uniq :=
                  ump_pullbacks
                    _ _ ypb _
                    (g ∘ pullback_fst x f xpb)
                    (pullback_snd x f xpb)
                    ltac:(rewrite comp_assoc, H;
                          exact (pullback_commutes x f xpb)) in
            (unique_obj uniq; snd (unique_property uniq))
|}.
Next Obligation.
  proper; simpl in *.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  intuition eauto.
  now rewrites.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  now cat.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  repeat (destruct (ump_pullbacks1 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  split.
  - rewrite comp_assoc.
    rewrite a1.
    now comp_left.
  - rewrite comp_assoc.
    now rewrite b0.
Qed.

(** ** The base change adjunction Σ_f ⊣ f* *)

Section BaseChange.

Context `(f : a ~> b).

(* The universal property of the chosen pullback of k along f, read at
   the competing cone that a slice morphism Σ_f (o; h) ~> (p; k)
   supplies: its two legs are the morphism itself and h, and the square
   condition IS that morphism's slice condition. *)
Definition base_ump {o p : C} (h : o ~> a) (k : p ~> b)
      (g : o ~> p) (Hg : k ∘ g ≈ f ∘ h) :
  ∃! u : o ~> Pull k f (pullbacks k f),
      pullback_fst k f (pullbacks k f) ∘ u ≈ g ∧
      pullback_snd k f (pullbacks k f) ∘ u ≈ h :=
  ump_pullbacks k f (pullbacks k f) o g h Hg.

(* The arrow action of f* is itself a pullback mediator; its underlying
   C-morphism is named here so that its two leg equations can be stated
   with the pullback objects already in reduced form. *)
Definition star_fmap_mor {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  Pull k1 f (pullbacks k1 f) ~> Pull k2 f (pullbacks k2 f) :=
  `1 (fmap[Star_Functor f] g).

Lemma star_fmap_fst {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_fst k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ `1 g ∘ pullback_fst k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (fst (unique_property U))
  end.
Qed.

Lemma star_fmap_snd {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_snd k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ pullback_snd k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (snd (unique_property U))
  end.
Qed.

(* The forward transpose, on underlying C-morphisms. *)
Definition base_to_mor {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  o ~> Pull k f (pullbacks k f) :=
  unique_obj (base_ump h k (`1 g) (`2 g)).

Lemma base_to_fst {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_fst k f (pullbacks k f) ∘ base_to_mor g ≈ `1 g.
Proof. exact (fst (unique_property (base_ump h k (`1 g) (`2 g)))). Qed.

Lemma base_to_snd {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_snd k f (pullbacks k f) ∘ base_to_mor g ≈ h.
Proof. exact (snd (unique_property (base_ump h k (`1 g) (`2 g)))). Defined.

(* Every competitor satisfying the two leg equations IS the transpose.
   This single lemma discharges respectfulness, one round trip and both
   naturality clauses. *)
Lemma base_to_mor_unique {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k))
      (u : o ~> Pull k f (pullbacks k f)) :
  pullback_fst k f (pullbacks k f) ∘ u ≈ `1 g →
  pullback_snd k f (pullbacks k f) ∘ u ≈ h →
  base_to_mor g ≈ u.
Proof.
  intros H1 H2.
  exact (uniqueness (base_ump h k (`1 g) (`2 g)) u (H1, H2)).
Qed.

Definition base_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  (o; h) ~{@Slice C a}~> Star_Functor f (p; k) :=
  (base_to_mor g; base_to_snd g).

(* The backward transpose: post-compose with the pullback projection.
   Its slice condition over b is [pullback_commutes] followed by the
   argument's own slice condition over a. *)
Lemma base_from_ok {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  k ∘ (pullback_fst k f (pullbacks k f) ∘ `1 u) ≈ f ∘ h.
Proof.
  pose proof (`2 u) as Hu; simpl in Hu.
  rewrite comp_assoc.
  rewrite (pullback_commutes k f (pullbacks k f)).
  rewrite <- comp_assoc.
  now rewrite Hu.
Defined.

Definition base_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  (o; f ∘ h) ~{@Slice C b}~> (p; k) :=
  (pullback_fst k f (pullbacks k f) ∘ `1 u; base_from_ok u).

Lemma base_to_respects {o p : C} {h : o ~> a} {k : p ~> b}
      (g1 g2 : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 g1 ≈ `1 g2 → base_to_mor g1 ≈ base_to_mor g2.
Proof.
  intro Hg.
  apply base_to_mor_unique.
  - rewrite base_to_fst.
    now symmetry.
  - apply base_to_snd.
Qed.

(* Round trip: the transpose of a morphism into the pullback recovers
   it, by uniqueness of the mediator. *)
Lemma base_to_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  base_to_mor (base_from u) ≈ `1 u.
Proof.
  apply base_to_mor_unique.
  - reflexivity.
  - exact (`2 u).
Qed.

(* The other round trip is the FIRST leg equation of the mediator, with
   no further argument. *)
Lemma base_from_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 (base_from (base_to g)) ≈ `1 g.
Proof. exact (base_to_fst g). Qed.

Program Definition base_adj_to (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    ~{Sets}~>
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  morphism := @base_to o p h k
|}.
Next Obligation. proper; now apply base_to_respects. Qed.

Program Definition base_adj_from (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |}
    ~{Sets}~>
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |} := {|
  morphism := @base_from o p h k
|}.

Program Definition base_adj_at (o p : C) (h : o ~> a) (k : p ~> b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
     ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  to   := base_adj_to o p h k;
  from := base_adj_from o p h k
|}.
Next Obligation. apply base_to_from. Qed.
Next Obligation. apply base_from_to. Qed.

Definition base_adj (x : @Slice C a) (y : @Slice C b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f x ~{@Slice C b}~> y
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f x) y |}
    {| carrier   := x ~{@Slice C a}~> Star_Functor f y
     ; is_setoid := @homset (@Slice C a) x (Star_Functor f y) |}.
Proof.
  destruct x as [o h], y as [p k].
  exact (base_adj_at o p h k).
Defined.

(* The two leg equations the [to_adj_nat_r] clause needs, stated at
   arguments whose slice types are already in pullback form, so that the
   rewriting below has the shape it expects. *)
Lemma base_nat_r_fst {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_fst k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u)
    ≈ `1 g ∘ `1 u.
Proof.
  rewrite comp_assoc, star_fmap_fst, <- comp_assoc, base_to_fst.
  reflexivity.
Qed.

Lemma base_nat_r_snd {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_snd k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u) ≈ h.
Proof.
  rewrite comp_assoc, star_fmap_snd.
  apply base_to_snd.
Qed.

(** The base change adjunction: dependent sum is left adjoint to
    pullback along the same morphism. *)
Definition Base_Functor_Adjunction : Bang_Functor f ⊣ Star_Functor f.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C b) (@Slice C a)
                     (Bang_Functor f) (Star_Functor f) base_adj).
  - intros [ox hx] [oy hy] [p k] g u; simpl.
    apply base_to_mor_unique.
    + rewrite comp_assoc, base_to_fst.
      reflexivity.
    + rewrite comp_assoc, base_to_snd.
      exact (`2 u).
  - intros [o h] [p1 k1] [p2 k2] g u.
    change (@base_to_mor o p2 h k2 (g ∘ u)
              ≈ star_fmap_mor g ∘ @base_to_mor o p1 h k1 u).
    apply base_to_mor_unique.
    + apply (base_nat_r_fst g u).
    + apply (base_nat_r_snd g u).
Defined.

(** ** Unit and counit *)

(* The unit at (o; h) is the comparison of o into the pullback of f ∘ h
   along f: the mediator of the cone ⟨id, h⟩, whose square condition is
   (f ∘ h) ∘ id ≈ f ∘ h. *)
Definition bang_star_unit_mor (o : C) (h : o ~> a) :
  o ~> Pull (f ∘ h) f (pullbacks (f ∘ h) f) :=
  unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))).

Definition bang_star_unit (o : C) (h : o ~> a) :
  (o; h) ~{@Slice C a}~> Star_Functor f (Bang_Functor f (o; h)) :=
  (bang_star_unit_mor o h;
   snd (unique_property (base_ump h (f ∘ h) id (id_right (f ∘ h))))).

(* The counit at (p; k) is the pullback projection itself; its slice
   condition k ∘ fst ≈ f ∘ snd IS [pullback_commutes]. *)
Definition bang_star_counit_mor (p : C) (k : p ~> b) :
  Pull k f (pullbacks k f) ~> p := pullback_fst k f (pullbacks k f).

Definition bang_star_counit (p : C) (k : p ~> b) :
  Bang_Functor f (Star_Functor f (p; k)) ~{@Slice C b}~> (p; k) :=
  (bang_star_counit_mor p k; pullback_commutes k f (pullbacks k f)).

(** *** How the named unit and counit relate to the class *)

(* The class's unit at (o; h) IS the forward transpose of the identity,
   on the nose. *)
Example bang_star_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = base_to_mor (id[Bang_Functor f (o; h)]) := eq_refl.

(* The residue is exhibited rather than described: both sides are the
   mediator of the cone whose legs are [id] and [h], and they differ in
   nothing but the proof of that cone's square condition. *)
Example bang_star_unit_residue (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = unique_obj (base_ump h (f ∘ h) id
                  (`2 (id[Bang_Functor f (o; h)]))) := eq_refl.

Example bang_star_unit_mor_residue (o : C) (h : o ~> a) :
  bang_star_unit_mor o h
  = unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))) := eq_refl.

(* Against [bang_star_unit_mor] the identification holds up to ≈ and not
   on the nose: both are mediators of the SAME cone ⟨id, h⟩, but the
   mediator is produced from a proof of the square condition and the two
   sides feed it different proofs -- the slice identity's own commuting
   witness on the class side, [id_right (f ∘ h)] on the named side. *)
Lemma bang_star_unit_is_mediator (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
    ≈ bang_star_unit_mor o h.
Proof.
  symmetry.
  apply (uniqueness (base_ump h (f ∘ h) id (id_right (f ∘ h)))).
  split.
  - apply (base_to_fst (id[Bang_Functor f (o; h)])).
  - apply (base_to_snd (id[Bang_Functor f (o; h)])).
Qed.

Lemma bang_star_unit_is_unit (o : C) (h : o ~> a) :
  @unit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (o; h)
    ≈ bang_star_unit o h.
Proof. exact (bang_star_unit_is_mediator o h). Qed.

(* The class's counit at (p; k) is the pullback projection with one
   residual identity, which is exactly what ε := ⌈id⌉ produces. *)
Example bang_star_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
  = bang_star_counit_mor p k ∘ id := eq_refl.

Lemma bang_star_counit_is_fst (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
    ≈ bang_star_counit_mor p k.
Proof. apply id_right. Qed.

Lemma bang_star_counit_is_counit (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (p; k)
    ≈ bang_star_counit p k.
Proof. exact (bang_star_counit_is_fst p k). Qed.

End BaseChange.

End SliceFunctors.
