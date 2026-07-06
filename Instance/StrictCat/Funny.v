Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Construction.Funny.Swap.
Require Import Category.Construction.Funny.Associator.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

(** * The funny tensor product as a symmetric monoidal structure on StrictCat

    This file assembles the funny tensor product [□] (Construction/Funny.v)
    into a tensor bifunctor [FunnyTensor : StrictCat ∏ StrictCat ⟶ StrictCat]
    and the instances

      [@Monoidal StrictCat], [@BraidedMonoidal StrictCat],
      [@SymmetricMonoidal StrictCat], [@SemicartesianMonoidal StrictCat _]

    with tensor [□] and unit the terminal category [1].

    A load-bearing caveat: there is NO such tensor on the weak [Cat]
    (Instance/Cat.v), whose hom-setoid [Functor_Setoid] identifies functors
    up to natural isomorphism.  The funny tensor product is not invariant
    under equivalence of categories: with I the "walking isomorphism"
    chaotic groupoid on two objects, [Functor_Setoid] identifies [Id[I]]
    with the constant functor at a point (they are naturally isomorphic by
    chaotic naturality), yet [1 □ 1 ≅ 1] while [I □ I] is equivalent to the
    group ℤ — the interchange loop
    [(fapp (rstep u) (lstep u))⁻¹ ∘ (fapp (lstep u) (rstep u))]
    at (a, a) is free ([fapp t u] is "t then u", Construction/Funny.v).
    Hence [fmap_respects] of a would-be
    [tensor : Cat ∏ Cat ⟶ Cat] is FALSE, and the obstruction persists with one
    argument fixed ([− □ I] is already non-Proper).  The tensor therefore
    lives on [StrictCat] (Instance/StrictCat.v), whose hom-setoid
    [Functor_StrictEq_Setoid] compares functors strictly — the same shape of
    problem as the issue #138 discussion recorded in Instance/StrictCat.v.

    Per Foltz–Lair–Kelly ("Algebraic categories with few monoidal biclosed
    structures or none", JPAA 17(2) (1980) 171-177), up to isomorphism there
    are exactly two monoidal biclosed structures on Cat, and both are
    symmetric: the cartesian one and this funny one.  The braiding is
    [FunnySwap] (Construction/Funny/Swap.v), and the unit [1] is terminal in
    StrictCat (Instance/StrictCat/Terminal.v), making the structure
    semicartesian.

    Proof method: every coherence law is a strict equality of two functors
    out of an iterated funny tensor product, so it reduces via the master
    lemma [Funny_strict_eq]/[Funny_strict_eq_word]
    (Construction/Funny/StrictEq.v) to transported agreement on the
    generating steps.  For the nested domains ((x □ y) □ z etc.) the master
    lemma is applied ITERATIVELY: a generator of the outer level is
    [lstep w]/[rstep w] with w a whole inner word, and
    [fmap[F ◯ FunnyL d] w ≡ fmap[F] (lstep w)] holds definitionally, so
    agreement on outer left generators is again a strict-equality-of-functors
    problem one level down.  At the leaves all coherence routes send each
    generating step to the SAME nested generator on the nose — except in the
    triangle, where the unitors produce [id ∘ f]-shaped payloads and the
    congruence [feq]'s identity-removal and payload-congruence rules fire. *)

#[local] Obligation Tactic := idtac.

(** ** The tensor bifunctor *)

Program Definition FunnyTensor : (StrictCat ∏ StrictCat) ⟶ StrictCat := {|
  fobj := fun p => (fst p □ snd p)%category;
  fmap := fun _ _ FG => FunnyBimap (fst FG) (snd FG)
|}.
Next Obligation.
  (* fmap_respects: componentwise strict equality is preserved. *)
  intros p q F G E.
  exact (FunnyBimap_respects (fst F) (fst G) (fst E) (snd F) (snd G) (snd E)).
Qed.
Next Obligation.
  (* fmap_id *)
  intros p.
  exact (@FunnyBimap_id (fst p) (snd p)).
Qed.
Next Obligation.
  (* fmap_comp *)
  intros p q r f g.
  exact (FunnyBimap_comp (fst f) (fst g) (snd f) (snd g)).
Qed.

(** ** The triangle identity

    [bimap unit_right id ≈ bimap id unit_left ∘ tensor_assoc] on
    [(x □ 1) □ y].  Unlike the pentagon and the hexagons, the two routes do
    NOT agree definitionally on generators: the unitors fold away the
    [1]-steps into [id ∘ id]-composites, so the leaves genuinely exercise
    the congruence [feq] (payload congruence + identity removal). *)

Lemma Funny_triangle_word {x y : Category} (d : y)
  {a : x} {u : _1} {a' : x} {u' : _1} (w : FunHom a u a' u') :
  @fmap (x □ _1) (x □ y)
    (FunnyBimap Funny_unit_right_to Id[y] ◯ @FunnyL (x □ _1) y d)
    (a, u) (a', u') w
  ≈ @fmap (x □ _1) (x □ y)
    ((FunnyBimap Id[x] Funny_unit_left_to ◯ @FunnyAssocTo x _1 y)
       ◯ @FunnyL (x □ _1) y d)
    (a, u) (a', u') w.
Proof.
  apply (Funny_strict_eq_word
           (FunnyBimap Funny_unit_right_to Id[y] ◯ @FunnyL (x □ _1) y d)
           ((FunnyBimap Id[x] Funny_unit_left_to ◯ @FunnyAssocTo x _1 y)
              ◯ @FunnyL (x □ _1) y d)
           (fun _ _ => eq_refl)).
  - (* lstep f: route 1 folds to [lstep (id ∘ f)], route 2 to [lstep f]. *)
    intros c c' f u0.
    apply feq_consL; [ apply id_left | apply feq_refl ].
  - (* rstep g (g : 1-step): route 1 gives [lstep (id ∘ id)], route 2
       [rstep (id ∘ id)]; both collapse to fnil. *)
    intros c u0 u1 g.
    eapply feq_trans.
    { apply feq_consL; [ apply id_left | apply feq_refl ]. }
    eapply feq_trans.
    { apply feq_idL. }
    apply feq_sym.
    eapply feq_trans.
    { apply feq_consR; [ apply id_left | apply feq_refl ]. }
    apply feq_idR.
Qed.

Lemma Funny_triangle {x y : Category} :
  @equiv _ (@Functor_StrictEq_Setoid ((x □ _1) □ y) (x □ y))
    (FunnyBimap Funny_unit_right_to Id[y])
    (FunnyBimap Id[x] Funny_unit_left_to ◯ @FunnyAssocTo x _1 y).
Proof.
  apply (Funny_strict_eq
           (FunnyBimap Funny_unit_right_to Id[y])
           (FunnyBimap Id[x] Funny_unit_left_to ◯ @FunnyAssocTo x _1 y)
           (fun _ _ => eq_refl)).
  - intros [a u] [a' u'] w d.
    exact (Funny_triangle_word d w).
  - (* rstep h: route 1 gives [rstep h], route 2 [rstep (id ∘ h)]. *)
    intros c d d' h.
    apply feq_consR; [ symmetry; apply id_left | apply feq_refl ].
Qed.

(** ** The pentagon identity

    Both routes send every generating step of [((x □ y) □ z) □ w] to the
    same nested generator on the nose, so after three iterations of the
    master lemma every leaf closes by reflexivity. *)

Lemma Funny_pentagon_word2 {x y z w : Category} (d : w) (k : z)
  {a : x} {b : y} {a' : x} {b' : y} (v : FunHom a b a' b') :
  @fmap (x □ y) (x □ (y □ (z □ w)))
    ((((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
         ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w])
        ◯ @FunnyL ((x □ y) □ z) w d) ◯ @FunnyL (x □ y) z k)
    (a, b) (a', b') v
  ≈ @fmap (x □ y) (x □ (y □ (z □ w)))
    (((@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w)
        ◯ @FunnyL ((x □ y) □ z) w d) ◯ @FunnyL (x □ y) z k)
    (a, b) (a', b') v.
Proof.
  apply (Funny_strict_eq_word
           ((((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
                ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w])
               ◯ @FunnyL ((x □ y) □ z) w d) ◯ @FunnyL (x □ y) z k)
           (((@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w)
               ◯ @FunnyL ((x □ y) □ z) w d) ◯ @FunnyL (x □ y) z k)
           (fun _ _ => eq_refl)).
  - intros c c' f b0. reflexivity.
  - intros c b0 b1 g. reflexivity.
Qed.

Lemma Funny_pentagon_word {x y z w : Category} (d : w)
  {q : x □ y} {k : z} {q' : x □ y} {k' : z} (v : FunHom q k q' k') :
  @fmap ((x □ y) □ z) (x □ (y □ (z □ w)))
    (((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
        ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w]) ◯ @FunnyL ((x □ y) □ z) w d)
    (q, k) (q', k') v
  ≈ @fmap ((x □ y) □ z) (x □ (y □ (z □ w)))
    ((@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w)
       ◯ @FunnyL ((x □ y) □ z) w d)
    (q, k) (q', k') v.
Proof.
  apply (Funny_strict_eq_word
           (((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
               ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w])
              ◯ @FunnyL ((x □ y) □ z) w d)
           ((@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w)
              ◯ @FunnyL ((x □ y) □ z) w d)
           (fun _ _ => eq_refl)).
  - intros [a b] [a' b'] V k0.
    exact (Funny_pentagon_word2 d k0 V).
  - intros c k0 k1 h. reflexivity.
Qed.

Lemma Funny_pentagon {x y z w : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (((x □ y) □ z) □ w) (x □ (y □ (z □ w))))
    ((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
       ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w])
    (@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w).
Proof.
  apply (Funny_strict_eq
           ((FunnyBimap Id[x] (@FunnyAssocTo y z w) ◯ @FunnyAssocTo x (y □ z) w)
              ◯ FunnyBimap (@FunnyAssocTo x y z) Id[w])
           (@FunnyAssocTo x y (z □ w) ◯ @FunnyAssocTo (x □ y) z w)
           (fun _ _ => eq_refl)).
  - intros [q k] [q' k'] W d.
    exact (Funny_pentagon_word d W).
  - intros c d d' h. reflexivity.
Qed.

(** ** The monoidal instance *)

#[export] Program Instance Funny_Monoidal : @Monoidal StrictCat := {
  I := _1;
  tensor := FunnyTensor;
  unit_left := fun x => @Funny_unit_left x;
  unit_right := fun x => @Funny_unit_right x;
  tensor_assoc := fun x y z => @Funny_assoc x y z
}.
Next Obligation.
  intros x y g. exact (Funny_unit_left_natural g).
Qed.
Next Obligation.
  intros x y g. exact (Funny_unit_left_from_natural g).
Qed.
Next Obligation.
  intros x y g. exact (Funny_unit_right_natural g).
Qed.
Next Obligation.
  intros x y g. exact (Funny_unit_right_from_natural g).
Qed.
Next Obligation.
  intros x y z w v u g h i. exact (FunnyAssoc_natural g h i).
Qed.
Next Obligation.
  intros x y z w v u g h i. exact (FunnyAssocFrom_natural g h i).
Qed.
Next Obligation.
  intros x y. exact (@Funny_triangle x y).
Qed.
Next Obligation.
  intros x y z w. exact (@Funny_pentagon x y z w).
Qed.

(** ** Naturality of the braiding

    The joint (arity-2) naturality square consumed by [braid_natural]:
    both routes send [lstep f] to [rstep (fmap[g] f)] and [rstep k] to
    [lstep (fmap[h] k)] definitionally. *)

Lemma Funny_braid_natural {x y z w : Category} (g : x ⟶ y) (h : z ⟶ w) :
  @equiv _ (@Functor_StrictEq_Setoid (x □ z) (w □ y))
    ((FunnyBimap h Id[y] ◯ FunnyBimap Id[z] g) ◯ @FunnySwap x z)
    ((@FunnySwap y w ◯ FunnyBimap Id[y] h) ◯ FunnyBimap g Id[z]).
Proof.
  apply (Funny_strict_eq
           ((FunnyBimap h Id[y] ◯ FunnyBimap Id[z] g) ◯ @FunnySwap x z)
           ((@FunnySwap y w ◯ FunnyBimap Id[y] h) ◯ FunnyBimap g Id[z])
           (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' k. reflexivity.
Qed.

(** ** The hexagon identities

    As with the pentagon, every generating step is sent to the same nested
    generator by both routes, so the leaves close by reflexivity after
    iterating the master lemma through the nested domain. *)

Lemma Funny_hexagon_word {x y z : Category} (k : z)
  {a : x} {b : y} {a' : x} {b' : y} (v : FunHom a b a' b') :
  @fmap (x □ y) (y □ (z □ x))
    (((@FunnyAssocTo y z x ◯ @FunnySwap x (y □ z)) ◯ @FunnyAssocTo x y z)
       ◯ @FunnyL (x □ y) z k)
    (a, b) (a', b') v
  ≈ @fmap (x □ y) (y □ (z □ x))
    (((FunnyBimap Id[y] (@FunnySwap x z) ◯ @FunnyAssocTo y x z)
        ◯ FunnyBimap (@FunnySwap x y) Id[z]) ◯ @FunnyL (x □ y) z k)
    (a, b) (a', b') v.
Proof.
  apply (Funny_strict_eq_word
           (((@FunnyAssocTo y z x ◯ @FunnySwap x (y □ z)) ◯ @FunnyAssocTo x y z)
              ◯ @FunnyL (x □ y) z k)
           (((FunnyBimap Id[y] (@FunnySwap x z) ◯ @FunnyAssocTo y x z)
               ◯ FunnyBimap (@FunnySwap x y) Id[z]) ◯ @FunnyL (x □ y) z k)
           (fun _ _ => eq_refl)).
  - intros c c' f b0. reflexivity.
  - intros c b0 b1 g. reflexivity.
Qed.

Lemma Funny_hexagon {x y z : Category} :
  @equiv _ (@Functor_StrictEq_Setoid ((x □ y) □ z) (y □ (z □ x)))
    ((@FunnyAssocTo y z x ◯ @FunnySwap x (y □ z)) ◯ @FunnyAssocTo x y z)
    ((FunnyBimap Id[y] (@FunnySwap x z) ◯ @FunnyAssocTo y x z)
       ◯ FunnyBimap (@FunnySwap x y) Id[z]).
Proof.
  apply (Funny_strict_eq
           ((@FunnyAssocTo y z x ◯ @FunnySwap x (y □ z)) ◯ @FunnyAssocTo x y z)
           ((FunnyBimap Id[y] (@FunnySwap x z) ◯ @FunnyAssocTo y x z)
              ◯ FunnyBimap (@FunnySwap x y) Id[z])
           (fun _ _ => eq_refl)).
  - intros [a b] [a' b'] V k.
    exact (Funny_hexagon_word k V).
  - intros c k k' h. reflexivity.
Qed.

Lemma Funny_hexagon_sym_word {x y z : Category} (c : x)
  {b : y} {e : z} {b' : y} {e' : z} (v : FunHom b e b' e') :
  @fmap (y □ z) ((z □ x) □ y)
    (((@FunnyAssocFrom z x y ◯ @FunnySwap (x □ y) z) ◯ @FunnyAssocFrom x y z)
       ◯ @FunnyR x (y □ z) c)
    (b, e) (b', e') v
  ≈ @fmap (y □ z) ((z □ x) □ y)
    (((FunnyBimap (@FunnySwap x z) Id[y] ◯ @FunnyAssocFrom x z y)
        ◯ FunnyBimap Id[x] (@FunnySwap y z)) ◯ @FunnyR x (y □ z) c)
    (b, e) (b', e') v.
Proof.
  apply (Funny_strict_eq_word
           (((@FunnyAssocFrom z x y ◯ @FunnySwap (x □ y) z) ◯ @FunnyAssocFrom x y z)
              ◯ @FunnyR x (y □ z) c)
           (((FunnyBimap (@FunnySwap x z) Id[y] ◯ @FunnyAssocFrom x z y)
               ◯ FunnyBimap Id[x] (@FunnySwap y z)) ◯ @FunnyR x (y □ z) c)
           (fun _ _ => eq_refl)).
  - intros b0 b1 g e0. reflexivity.
  - intros b0 e0 e1 h. reflexivity.
Qed.

Lemma Funny_hexagon_sym {x y z : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (x □ (y □ z)) ((z □ x) □ y))
    ((@FunnyAssocFrom z x y ◯ @FunnySwap (x □ y) z) ◯ @FunnyAssocFrom x y z)
    ((FunnyBimap (@FunnySwap x z) Id[y] ◯ @FunnyAssocFrom x z y)
       ◯ FunnyBimap Id[x] (@FunnySwap y z)).
Proof.
  apply (Funny_strict_eq
           ((@FunnyAssocFrom z x y ◯ @FunnySwap (x □ y) z) ◯ @FunnyAssocFrom x y z)
           ((FunnyBimap (@FunnySwap x z) Id[y] ◯ @FunnyAssocFrom x z y)
              ◯ FunnyBimap Id[x] (@FunnySwap y z))
           (fun _ _ => eq_refl)).
  - intros c c' f q. reflexivity.
  - intros c [b e] [b' e'] W.
    exact (Funny_hexagon_sym_word c W).
Qed.

(** ** The braided and symmetric instances *)

#[export] Program Instance Funny_Braided : @BraidedMonoidal StrictCat := {
  braided_is_monoidal := Funny_Monoidal;
  braid := fun x y => @FunnySwap x y
}.
Next Obligation.
  intros x y g z w h.
  exact (Funny_braid_natural g h).
Qed.
Next Obligation.
  intros x y z. exact (@Funny_hexagon x y z).
Qed.
Next Obligation.
  intros x y z. exact (@Funny_hexagon_sym x y z).
Qed.

#[export] Program Instance Funny_Symmetric : @SymmetricMonoidal StrictCat := {
  symmetric_is_braided := Funny_Braided
}.
Next Obligation.
  intros x y. exact (@FunnySwap_invol x y).
Qed.

(** ** The semicartesian instance

    The unit [1] of the funny tensor is the terminal object of StrictCat
    (Instance/StrictCat/Terminal.v), on the nose, so the generic
    [Terminal_SemicartesianMonoidal] applies with [Heq := eq_refl]. *)

#[export] Instance Funny_Semicartesian :
  @SemicartesianMonoidal StrictCat Funny_Monoidal :=
  @Terminal_SemicartesianMonoidal StrictCat Funny_Monoidal StrictCat_Terminal
    eq_refl.
