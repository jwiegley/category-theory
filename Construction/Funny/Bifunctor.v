Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * The funny tensor product of functors

    [FunnyBimap F G : C □ D ⟶ C' □ D'] acts on the funny tensor product of
    categories (Construction/Funny.v) one generating step at a time:

      lstep f ↦ lstep (fmap[F] f)        rstep g ↦ rstep (fmap[G] g)

    packaged through the separately-functorial eliminator [FunnyUP], so
    functoriality is inherited from the universal property rather than
    re-proved by word induction.

    The bifunctor laws ([FunnyBimap_id], [FunnyBimap_comp]) and properness
    ([FunnyBimap_respects]) are stated in [Functor_StrictEq_Setoid]
    (Theory/Functor.v).  This is essential and not a stylistic choice: the
    funny tensor product is NOT invariant under equivalence of categories
    (see the header of Construction/Funny.v for the [I □ I ≃ ℤ]
    counterexample), so [FunnyBimap] does NOT respect the
    natural-isomorphism setoid [Functor_Setoid] used by the weak [Cat]
    (Instance/Cat.v) — the corresponding [fmap_respects] is false.  Its
    properness is real only over strict functor equality, which is the
    hom-setoid of [StrictCat] (Instance/StrictCat.v); the symmetric monoidal
    structure downstream (Instance/StrictCat/Funny.v) lives there. *)

(** ** The action of [F □ G], as separately functorial data *)

Program Definition FunnyBimap_sep {C C' D D' : Category}
  (F : C ⟶ C') (G : D ⟶ D') :
  SepFunctorial (E:=C' □ D') (fun (c : C) (d : D) => (F c, G d)) := {|
  sf_lmap := fun c c' f d => lstep (fmap[F] f);
  sf_rmap := fun c d d' g => rstep (fmap[G] g)
|}.
Next Obligation.
  proper.
  apply feq_consL; [ now apply fmap_respects | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  apply feq_consR; [ now apply fmap_respects | apply feq_refl ].
Qed.
Next Obligation.
  eapply feq_trans.
  - apply feq_consL; [ apply fmap_id | apply feq_refl ].
  - apply feq_idL.
Qed.
Next Obligation.
  eapply feq_trans.
  - apply feq_consR; [ apply fmap_id | apply feq_refl ].
  - apply feq_idR.
Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseL.
  - apply feq_consL; [ symmetry; apply fmap_comp | apply feq_refl ].
Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseR.
  - apply feq_consR; [ symmetry; apply fmap_comp | apply feq_refl ].
Qed.

Definition FunnyBimap {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D') :
  (C □ D) ⟶ (C' □ D') := FunnyUP (FunnyBimap_sep F G).

(** ** Computation lemmas

    [ffold] and [fapp] compute, so the action of [FunnyBimap] on words is
    definitional, constructor by constructor. *)

Lemma FunnyBimap_fnil {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D')
  {c : C} {d : D} :
  @fmap (C □ D) (C' □ D') (FunnyBimap F G) (c, d) (c, d) fnil = fnil.
Proof. reflexivity. Qed.

Lemma FunnyBimap_fconsL {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D')
  {c1 c2 : C} {d1 : D} {c3 : C} {d3 : D}
  (f : c1 ~{C}~> c2) (t : FunHom c2 d1 c3 d3) :
  @fmap (C □ D) (C' □ D') (FunnyBimap F G) (c1, d1) (c3, d3) (fconsL f t)
    = fconsL (fmap[F] f)
        (@fmap (C □ D) (C' □ D') (FunnyBimap F G) (c2, d1) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnyBimap_fconsR {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D')
  {c1 : C} {d1 d2 : D} {c3 : C} {d3 : D}
  (g : d1 ~{D}~> d2) (t : FunHom c1 d2 c3 d3) :
  @fmap (C □ D) (C' □ D') (FunnyBimap F G) (c1, d1) (c3, d3) (fconsR g t)
    = fconsR (fmap[G] g)
        (@fmap (C □ D) (C' □ D') (FunnyBimap F G) (c1, d2) (c3, d3) t).
Proof. reflexivity. Qed.

Lemma FunnyBimap_lstep {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D')
  {c1 c2 : C} {d : D} (f : c1 ~{C}~> c2) :
  @fmap (C □ D) (C' □ D') (FunnyBimap F G) (c1, d) (c2, d) (lstep f)
    = lstep (fmap[F] f).
Proof. reflexivity. Qed.

Lemma FunnyBimap_rstep {C C' D D' : Category} (F : C ⟶ C') (G : D ⟶ D')
  {c : C} {d1 d2 : D} (g : d1 ~{D}~> d2) :
  @fmap (C □ D) (C' □ D') (FunnyBimap F G) (c, d1) (c, d2) (rstep g)
    = rstep (fmap[G] g).
Proof. reflexivity. Qed.

(** ** Strict bifunctor laws *)

Lemma FunnyBimap_id {C D : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C □ D))
    (FunnyBimap Id[C] Id[D]) Id.
Proof.
  apply (Funny_strict_eq (FunnyBimap Id[C] Id[D]) Id (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

Lemma FunnyBimap_comp {C C' C'' D D' D'' : Category}
  (F' : C' ⟶ C'') (F : C ⟶ C') (G' : D' ⟶ D'') (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C'' □ D''))
    (FunnyBimap (F' ◯ F) (G' ◯ G)) (FunnyBimap F' G' ◯ FunnyBimap F G).
Proof.
  apply (Funny_strict_eq (FunnyBimap (F' ◯ F) (G' ◯ G))
           (FunnyBimap F' G' ◯ FunnyBimap F G) (fun _ _ => eq_refl)).
  - intros c c' f d. reflexivity.
  - intros c d d' g. reflexivity.
Qed.

(** ** Transport helpers

    Properness of [FunnyBimap] transports morphisms of [C' □ D'] along
    object equalities that are [f_equal] images of SCALAR equalities in one
    coordinate ([eF c], resp. [eG d]).  Each helper destructs the scalar
    equalities — after which every transport vanishes definitionally — so
    downstream proofs never manipulate transports over pair types.  The
    left/right suffix [_l]/[_r] names the argument being varied (the
    [C]-side functor, resp. the [D]-side one); [lstep]/[rstep] names the
    generating step being transported. *)

Lemma funny_transport_lstep_l {C D : Category} {a a' b b' : C} {y : D}
  (p : a = a') (q : b = b') (s : a ~{C}~> b) (s' : a' ~{C}~> b')
  (E : transport (fun z => a ~{C}~> z) q s
         ≈ transport_r (fun z => z ~{C}~> b') p s') :
  transport (fun z => (a, y) ~{C □ D}~> z)
            (f_equal (fun x : C => (x, y)) q) (lstep s)
    ≈ transport_r (fun z => z ~{C □ D}~> (b', y))
                  (f_equal (fun x : C => (x, y)) p) (lstep s').
Proof.
  revert s s' E; destruct p, q; intros s s' E.
  apply feq_consL; [ exact E | apply feq_refl ].
Qed.

Lemma funny_transport_rstep_l {C D : Category} {a a' : C} {y y' : D}
  (p : a = a') (s : y ~{D}~> y') :
  transport (fun z => (a, y) ~{C □ D}~> z)
            (f_equal (fun x : C => (x, y')) p) (rstep s)
    ≈ transport_r (fun z => z ~{C □ D}~> (a', y'))
                  (f_equal (fun x : C => (x, y)) p) (rstep s).
Proof.
  destruct p.
  apply feq_refl.
Qed.

Lemma funny_transport_lstep_r {C D : Category} {x x' : C} {b b' : D}
  (p : b = b') (s : x ~{C}~> x') :
  transport (fun z => (x, b) ~{C □ D}~> z)
            (f_equal (fun y : D => (x', y)) p) (lstep s)
    ≈ transport_r (fun z => z ~{C □ D}~> (x', b'))
                  (f_equal (fun y : D => (x, y)) p) (lstep s).
Proof.
  destruct p.
  apply feq_refl.
Qed.

Lemma funny_transport_rstep_r {C D : Category} {x : C} {a a' b b' : D}
  (p : a = a') (q : b = b') (s : a ~{D}~> b) (s' : a' ~{D}~> b')
  (E : transport (fun z => a ~{D}~> z) q s
         ≈ transport_r (fun z => z ~{D}~> b') p s') :
  transport (fun z => (x, a) ~{C □ D}~> z)
            (f_equal (fun y : D => (x, y)) q) (rstep s)
    ≈ transport_r (fun z => z ~{C □ D}~> (x, b'))
                  (f_equal (fun y : D => (x, y)) p) (rstep s').
Proof.
  revert s s' E; destruct p, q; intros s s' E.
  apply feq_consR; [ exact E | apply feq_refl ].
Qed.

(** ** Properness with respect to strict functor equality

    Split per argument: each half varies one functor while the other is
    fixed, so all object equalities are [f_equal] images of one scalar
    family and the helpers above apply verbatim on the generating steps;
    [Funny_strict_eq] then extends the agreement to all words. *)

Lemma FunnyBimap_respects_l {C C' D D' : Category}
  {F F' : C ⟶ C'} (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid C C') F F' →
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' □ D'))
    (FunnyBimap F G) (FunnyBimap F' G).
Proof.
  intros [eF hF].
  apply (Funny_strict_eq (FunnyBimap F G) (FunnyBimap F' G)
           (fun c d => f_equal (fun a : C' => (a, G d)) (eF c))).
  - intros c c' f d.
    exact (funny_transport_lstep_l (eF c) (eF c')
             (fmap[F] f) (fmap[F'] f) (hF c c' f)).
  - intros c d d' g.
    exact (funny_transport_rstep_l (eF c) (fmap[G] g)).
Qed.

Lemma FunnyBimap_respects_r {C C' D D' : Category}
  (F : C ⟶ C') {G G' : D ⟶ D'} :
  @equiv _ (@Functor_StrictEq_Setoid D D') G G' →
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' □ D'))
    (FunnyBimap F G) (FunnyBimap F G').
Proof.
  intros [eG hG].
  apply (Funny_strict_eq (FunnyBimap F G) (FunnyBimap F G')
           (fun c d => f_equal (fun b : D' => (F c, b)) (eG d))).
  - intros c c' f d.
    exact (funny_transport_lstep_r (eG d) (fmap[F] f)).
  - intros c d d' g.
    exact (funny_transport_rstep_r (eG d) (eG d')
             (fmap[G] g) (fmap[G'] g) (hG d d' g)).
Qed.

Lemma FunnyBimap_respects {C C' D D' : Category} :
  Proper (@equiv _ (@Functor_StrictEq_Setoid C C') ==>
          @equiv _ (@Functor_StrictEq_Setoid D D') ==>
          @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' □ D')))
    (@FunnyBimap C C' D D').
Proof.
  intros F F' EF G G' EG.
  exact (@Equivalence_Transitive _ _
           (@setoid_equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' □ D')))
           (FunnyBimap F G) (FunnyBimap F' G) (FunnyBimap F' G')
           (FunnyBimap_respects_l G EF) (FunnyBimap_respects_r F' EG)).
Qed.
