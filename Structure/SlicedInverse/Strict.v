Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Structure.SlicedInverse.

(** * Sliced adjoint inverses, the strict half: the bridge to
      left-adjoint-left-inverses, and the dual of Proposition V.9.1 as a
      left-adjoint-right-inverse statement

    nLab: https://ncatlab.org/nlab/show/quotient+space
    nLab: https://ncatlab.org/nlab/show/topological+concrete+category

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, SS IV.4 (printed p. 94, the
          left-adjoint-left-inverse; p. 95, Exercise 3, the
          left-adjoint-right-inverse) and SS V.9, read from the page
          images: the quotient construction (book pp. 133-134, PDF
          pp. 142-143; catalog id maclane:V.9:construction3) and the one
          sentence stating the dual of Proposition 1 (book p. 134, PDF
          p. 143), the first clause of maclane:V.9:remark2, #458's
          catalog item.  The book numbers neither; the catalog ids are
          names, not book numbering.

    ** Background

    Mac Lane names an adjoint pair by which functor is the inverse and on
    which side.  In SS IV.4 a left adjoint [F] of [G] whose counit is the
    identity is a LEFT-ADJOINT-LEFT-INVERSE of [G]
    (Adjunction/LeftInverse.v), and a left adjoint [T] of [S] whose unit
    is the identity is a LEFT-ADJOINT-RIGHT-INVERSE of [S]
    (Theory/Equivalence/Strict.v).  SS V.9 adds the
    RIGHT-ADJOINT-RIGHT-INVERSE: the subspace topology is one for the
    sliced forgetful functor, and Proposition 1 builds equalizers from
    them (Structure/SlicedInverse.v, whose header carries the background
    essay).  Its dual -- one sentence of the book, "Now Proposition 1 was
    proved just from the axioms for a category, so its dual is also
    true" -- builds coequalizers from sliced left-adjoint-right-inverses,
    of which the quotient, or final, topology is the example (nLab,
    "quotient space"; Instance/Top/Subspace.v's [quotient_LARI]).

    Two of those names are one notion seen from its two ends.  "[S ⊣ R]
    with counit the identity" says that [R] is a
    right-adjoint-right-inverse of [S] AND that [S] is a
    left-adjoint-left-inverse of [R]; the library's two records differ
    only in which functor is the parameter.  This file makes that exact,
    and states the dual of Proposition 1 over the tree's existing
    [LeftAdjointRightInverse].  It is a satellite because its two donors
    are the only consumers of 14 modules (see Route and cost).

    ** What is delivered

    - [rari_lali : RightAdjointRightInverse S → LeftAdjointLeftInverse
      (rari_right P)] and [lali_rari : LeftAdjointLeftInverse R →
      RightAdjointRightInverse (lali_left P)], field for field, with
      [rari_lali_left] and [lali_rari_right] reading the moved functor
      back, and [rari_lali_rari] and [lali_rari_lali] stating both round
      trips as the identity.
    - [coequalizers_from_sliced_LARI]: the dual of Proposition 1, as the
      catalog's maclane:V.9:remark2 spells it out -- a faithful [G],
      coequalizers downstairs and a left-adjoint-right-inverse of every
      [Cosliced G a] give coequalizers upstairs.  It is
      Structure/SlicedInverse.v's [coequalizers_from_sliced_left_adjoints]
      applied to [lari_left] and [lari_adj]; the fields [lari_obj] and
      [lari_unit] do not occur in its body, so the right-inverse clause is
      not used, exactly as for Proposition 1.
    - What the clause buys, dually: [lari_preserves], [G] of the lifted
      coequalizer is a coequalizer of [fmap[G] f] and [fmap[G] g] (its
      object is [Q] up to the Leibniz [lari_under], its arrow [q] up to
      that cast, [lari_arrow_under]), assembled by
      [IsCoequalizer_transport]; [coequalizers_from_sliced_LARI_preserved]
      states it for every coequalizer the book form builds.
    - [prop1_dual_needs_faithfulness]: the dual with the faithfulness
      hypothesis deleted is refuted at [Erase Parallel : Parallel ⟶ _1],
      the main file's countermodel read in coslices.  Every coslice of
      [Parallel] has the initial object [(a; id)], the functor constant at
      it is a left-adjoint-right-inverse of each
      [Cosliced (Erase Parallel) a] ([erase_coslice_LARI]), [_1] has
      coequalizers ([One_HasCoequalizers]), and the parallel pair has no
      coforking arrow ([parallel_pair_uncoforked],
      [Parallel_no_coequalizers]); [cosliced_LARI_without_faithfulness]
      packages the four facts.

    ** Strengths

    Holding at [eq_refl], as [Example]s: [rari_lali_left],
    [lali_rari_right], the two round trips [rari_lali_rari] and
    [lali_rari_lali] (record eta, the records having primitive
    projections), [coequalizers_from_sliced_LARI_obj] and
    [coequalizers_from_sliced_LARI_arrow] (the coequalizer built is
    [lari_left (L y)] of the downstairs one, on the nose), and
    [lari_coeq_obj] and [lari_coeq_arrow] (the pointwise form).  Eight in
    all.  Leibniz but not [eq_refl]: [lari_under], from the field
    [lari_obj], and [coslice_id_cast_1], the coslice twin of the main
    file's [slice_id_cast_1], by [destruct].  Up to [≈]:
    [lari_arrow_under].  The four [Defined]
    ([IsCoequalizer_transport], the second obligation of
    [One_HasCoequalizers], [erase_coslice_adj], [erase_coslice_LARI])
    carry data and are kept [Defined] by the data convention; flipped to
    [Qed] in a scratch copy together with the main file's six, both files
    compile, so none is load-bearing.

    ** Universes, measured by About on every constant

    Every constant over two categories binds them at one hom level,
    [Category@{oA h h}] and [Category@{oX h h}] (or [oC]), in the binder;
    the identification is the records' own (a functor in each direction,
    and [Adjunction]'s block) and the main file's, and is inherited.
    Across the 39 constants of this file (Print Module and every
    [Program] obligation) the About log has zero word-bounded [Set] and no
    block carries an equation; in every block whose constant binds
    categories, each strict bound relates a hom level to an auxiliary
    universe that no category binder names.  [One_HasCoequalizers] is
    annotated [@{o h}] for the reason the main file measured for
    [One_HasEqualizers], and reads [HasCoequalizers@{o h} _1@{o h h}].
    [prop1_dual_needs_faithfulness] quantifies over
    [A : Category@{u4 u5 u5}] and [X : Category@{u2 u5 u5}] with the one
    strict bound [u5 < u3].  The main file's identification of the two
    slice-auxiliary universes holds here too: [coequalizers_from_sliced_LARI]
    reads [Cosliced@{oA h oX h u3 u3 u6 u7}], and the refutation
    [Cosliced@{u4 u5 u2 u5 u3 u3 u u1}].

    ** Route and cost

    Closure: 56 [Category.*] modules excluding this file ([Print
    Libraries] on its [Require] list).  Without
    Theory/Equivalence/Strict.v and Adjunction/LeftInverse.v the same list
    gives 42, Structure/SlicedInverse.v and its own closure; so the two
    donors cost 14, the figure the main file's header measures from its
    side (41 to 55).  Dropping each [Require] alone:
    Structure/SlicedInverse.v costs 5, Theory/Equivalence/Strict.v 2
    (Adjunction/LeftInverse.v, which it requires, is required here too),
    and the other thirteen 0.  [IsCoequalizer_transport] is rebuilt
    rather than consumed: Monad/Monadicity/Beck.v's
    [coequalizer_along_iso] moves an [IsCoequalizer] along an isomorphism
    of apexes (closed, [Defined]) and would serve through
    Construction/Quotient.v's [id_cast_iso], but requiring Beck.v would
    add 12 modules (56 to 68), measured the same way.  [lari_under] is
    stated
    as [Q = G (...)] rather than in [rari_over]'s orientation because the
    unit, not the counit, is the transported identity here, and
    [lari_unit] already carries the [eq_sym].

    ** Prior art, measured

    Theory/Equivalence/Strict.v's own NOT DELIVERED list includes "no
    comparison of [LeftAdjointRightInverse] with Adjunction/LeftInverse.v's
    [LeftAdjointLeftInverse] beyond naming the pair"; that remains true --
    the comparison made here is between the new
    [RightAdjointRightInverse] and [LeftAdjointLeftInverse], the two
    records that are one notion.  Collisions: see the main file.

    ** NOT DELIVERED

    - No comparison of [LeftAdjointRightInverse] with the other two
      records (it is a different notion: the UNIT is the identity).
    - No concrete witness in this file: the quotient topology is
      Instance/Top/Subspace.v's [quotient_LARI], at [Cosliced PForget X],
      and the coequalizers it gives are that file's
      [PTop_HasCoequalizers], built by [coequalizers_from_sliced_LARI].
    - No transport of the right-inverse clause's consequences along the
      bridges (e.g. [lali_Full] and [lali_Faithful] of
      Adjunction/LeftInverse.v read as statements about [rari_right]);
      they apply through [rari_lali] but are not restated. *)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Right-adjoint-right-inverses ARE left-adjoint-left-inverses *)

(* The two records carry the same four fields; only the parameter moves,
   from the left adjoint to the right one. *)
Definition rari_lali@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C}
  (P : RightAdjointRightInverse S) : LeftAdjointLeftInverse (rari_right P) :=
  {| lali_left := S; lali_adj := rari_adj P;
     lali_obj := rari_obj P; lali_counit := rari_counit P |}.

Definition lali_rari@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X}
  (P : LeftAdjointLeftInverse R) : RightAdjointRightInverse (lali_left P) :=
  {| rari_right := R; rari_adj := lali_adj P;
     rari_obj := lali_obj P; rari_counit := lali_counit P |}.

Example rari_lali_left@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_left (rari_lali P) = S := eq_refl.

Example lali_rari_right@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_right (lali_rari P) = R := eq_refl.

(* Both round trips are the identity on the nose (record eta). *)
Example rari_lali_rari@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_rari (rari_lali P) = P := eq_refl.

Example lali_rari_lali@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_lali (lali_rari P) = P := eq_refl.

(** ** The dual of Proposition 1, over left-adjoint-right-inverses *)

(* Coequalizers from sliced left-adjoint-right-inverses, over
   Theory/Equivalence/Strict.v's [LeftAdjointRightInverse].  The
   right-inverse clause is not consulted: only [lari_left] and [lari_adj]
   occur in the body. *)
Definition coequalizers_from_sliced_LARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) :
  @HasCoequalizers A :=
  coequalizers_from_sliced_left_adjoints G
    (fun a => lari_left (L a)) (fun a => lari_adj (L a)).

Example coequalizers_from_sliced_LARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)
    = `1 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_LARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g))
    = `2 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(** ** What the right-inverse clause adds, dually *)

Lemma coslice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Coslice C u} (e : p = q) :
  `1 (@id_cast (@Coslice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* A coequalizer moved along a Leibniz equation of apexes. *)
Definition IsCoequalizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : b ~> q} {e' : b ~> q'}
  (p : q = q') :
  e' ≈ id_cast p ∘ e → IsCoequalizer f g q e → IsCoequalizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_left in He.
  unshelve econstructor.
  - rewrite He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (coeq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section LARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (L : LeftAdjointRightInverse (Cosliced G y)).

Definition lari_universal :
  UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y) :=
  adj_unit_universal_op (lari_adj L) (Q; q).

Example lari_coeq_obj :
  cosliced_coeq_obj G q lari_universal = `1 (lari_left L (Q; q)) := eq_refl.

Example lari_coeq_arrow :
  cosliced_coeq_arrow G q lari_universal = `2 (lari_left L (Q; q)) := eq_refl.

(* The lifted object sits under Q: Leibniz, from the field [lari_obj]. *)
Definition lari_under : Q = G (`1 (lari_left L (Q; q))) :=
  f_equal (@projT1 _ _) (eq_sym (lari_obj L (Q; q))).

Lemma lari_arrow_under :
  fmap[G] (`2 (lari_left L (Q; q))) ≈ id_cast lari_under ∘ q.
Proof using Type.
  pose proof (`2 (@unit _ _ _ _ (lari_adj L) (Q; q))) as H; simpl in H.
  rewrite H.
  apply compose_respects; [|reflexivity].
  transitivity (`1 (@id_cast (@Coslice X (G y)) _ _
                     (eq_sym (lari_obj L (Q; q))))).
  - exact (lari_unit L (Q; q)).
  - rewrite (coslice_id_cast_1 (eq_sym (lari_obj L (Q; q)))).
    reflexivity.
Qed.

(* G carries the lifted coequalizer onto a coequalizer of the images. *)
Definition lari_preserves :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (lari_left L (Q; q)))) (fmap[G] (`2 (lari_left L (Q; q)))) :=
  IsCoequalizer_transport lari_under lari_arrow_under E.

End LARIPreserves.

Definition coequalizers_from_sliced_LARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L)
                         x y f g)))) :=
  lari_preserves G f g _ (`2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L y).

(** ** Faithfulness cannot be dropped from the dual either *)

Lemma parallel_pair_uncoforked {q : Parallel} (e : ParY ~{Parallel}~> q) :
  e ∘ par_arrow_one ≈ e ∘ par_arrow_two → False.
Proof.
  destruct q, e as [b h].
  - destruct (ParHom_Y_X_absurd _ h).
  - inversion h; subst. simpl. discriminate.
Qed.

Definition Parallel_no_coequalizers : @HasCoequalizers Parallel → False :=
  fun H =>
    parallel_pair_uncoforked
      (`1 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))
      (cofork (`2 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))).

Program Definition One_HasCoequalizers@{o h} :
  @HasCoequalizers _1@{o h h} := {|
  coeq := fun x y f g => (y; (id; {| cofork := _; coeq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma coslice_one_hom_eq@{o h +} (u : _1@{o h h})
  (x y : @Coslice _1@{o h h} u) (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseCoslice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(* The left adjoint of [Cosliced B a] is constant at the initial object
   (a; id) of the coslice under [a]. *)
Program Definition erase_coslice_left :
  @Coslice _1 (B a) ⟶ @Coslice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_coslice_hom_iso (c : @Coslice _1 (B a))
  (h : @Coslice Parallel a) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice Parallel a) (erase_coslice_left c) h;
       is_setoid := @homset (@Coslice Parallel a) (erase_coslice_left c) h |}
    {| carrier := @hom (@Coslice _1 (B a)) c (Cosliced B a h);
       is_setoid := @homset (@Coslice _1 (B a)) c (Cosliced B a h) |} := {|
  to := {| morphism := fun _ => (ttt; _) |};
  from := {| morphism := fun _ => (`2 h; _) |}
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; exact (symmetry (@id_right Parallel _ _ (`2 h))). Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite Hv; apply id_right.
Qed.

Definition erase_coslice_adj : erase_coslice_left ⊣ Cosliced B a.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ erase_coslice_left (Cosliced B a)
       erase_coslice_hom_iso).
  - intros x y z f g; simpl.
    reflexivity.
  - intros x y z f g; simpl.
    reflexivity.
Defined.

Definition erase_coslice_LARI : LeftAdjointRightInverse (Cosliced B a).
Proof.
  unshelve refine {| lari_left := erase_coslice_left;
                     lari_adj := erase_coslice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply coslice_one_hom_eq.
Defined.

End EraseCoslice.

Definition cosliced_LARI_without_faithfulness :
  (∀ a : Parallel, LeftAdjointRightInverse (Cosliced (Erase Parallel) a))
  * @HasCoequalizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasCoequalizers Parallel → False) :=
  (erase_coslice_LARI, One_HasCoequalizers, Erase_Parallel_not_faithful,
   Parallel_no_coequalizers).

(* The dual with the faithfulness hypothesis deleted is false. *)
Definition prop1_dual_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasCoequalizers X →
     (∀ a : A, LeftAdjointRightInverse (Cosliced G a)) →
     @HasCoequalizers A)
  → False :=
  fun P => Parallel_no_coequalizers
             (P Parallel _1 (Erase Parallel) One_HasCoequalizers
                erase_coslice_LARI).
