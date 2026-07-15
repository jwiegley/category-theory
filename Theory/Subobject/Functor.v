Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* The subobject presheaf Sub : C^op ⟶ Sets.

   nLab: https://ncatlab.org/nlab/show/subobject

   In a category with chosen pullbacks, a morphism f : y ~> x induces a
   reindexing map SubObj x → SubObj y: pull the mono u ↪ x back along f; the
   projection opposite u is again monic (monic_pullback_stable), so it is a
   subobject of y.  Reindexing respects the SubObj setoid (equivalent monos
   pull back to equivalent monos), is the identity on subobjects when f is
   the identity, and turns composition into composition of reindexings — the
   last by the pasting law for pullbacks (pullback_paste).  Assembled, this
   is a contravariant functor from C to the category of setoids. *)

Section SubFunctor.

Context {C : Category}.
Context `{@HasPullbacks C}.

(* Reindex a subobject of x along f : y ~> x, via the chosen pullback.  The
   reindexed mono is the projection opposite sub_mono u, monic because monos
   are stable under pullback. *)
Definition sub_reindex {x y : C} (f : y ~> x) (u : SubObj x) : SubObj y := {|
  sub_dom  := Pull f (sub_mono u) (pullback f (sub_mono u));
  sub_mono := pullback_fst f (sub_mono u) (pullback f (sub_mono u));
  sub_is_monic := monic_pullback_stable f (sub_mono u) (sub_is_monic u)
                    (pullback f (sub_mono u))
|}.

(* The workhorse: if a given subobject v of y sits atop ANY pullback square
   of sub_mono u along f, then v is the reindexing of u along f, up to the
   SubObj setoid.  The isomorphism of apexes and its triangle with the two
   first projections come from pullback_transport. *)
Lemma sub_reindex_transport {x y : C} (f : y ~> x) (u : SubObj x)
      (v : SubObj y) (p2 : sub_dom v ~> sub_dom u)
      (HP : IsPullback f (sub_mono u) (sub_dom v) (sub_mono v) p2) :
  sub_reindex f u ≈ v.
Proof.
  pose proof (pullback_transport (pullback f (sub_mono u))
                                 (is_pullback_pullback HP)) as T.
  exists (transport_iso T).
  exact (transport_fst T).
Qed.

(* Reindexing respects the SubObj setoid: if u ≈ v via a domain isomorphism
   i, then the chosen pullback of v along f, corrected by i, is itself a
   pullback square for sub_mono u along f; sub_reindex_transport concludes. *)
#[export] Instance sub_reindex_respects {x y : C} (f : y ~> x) :
  Proper (equiv ==> equiv) (@sub_reindex x y f).
Proof.
  intros u v [i Hi].
  apply (sub_reindex_transport
           f u (sub_reindex f v)
           (from i ∘ pullback_snd f (sub_mono v) (pullback f (sub_mono v)))).
  constructor; simpl.
  - (* the corrected square commutes *)
    rewrite (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))).
    rewrite <- Hi.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i)).
    rewrite iso_to_from; cat.
  - intros Q q1 q2 Hq.
    (* transport the cone across i and mediate into the chosen pullback *)
    assert (Hq' : f ∘ q1 ≈ sub_mono v ∘ (to i ∘ q2)).
    { rewrite Hq, <- Hi.
      now rewrite comp_assoc. }
    pose proof (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
                              Q q1 (to i ∘ q2) Hq') as W.
    destruct (unique_property W) as [W1 W2].
    unshelve refine {| unique_obj := unique_obj W |}.
    + split.
      * exact W1.
      * rewrite <- comp_assoc.
        rewrite W2.
        rewrite comp_assoc.
        rewrite iso_from_to; cat.
    + intros w [Hw1 Hw2].
      apply (uniqueness W); split.
      * exact Hw1.
      * rewrite <- Hw2.
        rewrite !comp_assoc.
        rewrite iso_to_from; cat.
Qed.

(* A pullback square is stable under replacing the left leg of its cospan by
   an ≈-equal morphism; both fields transport by rewriting. *)
Lemma is_pullback_respects_left {x y z : C} {f f' : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} (Hf : f ≈ f') :
  IsPullback f g P p1 p2 → IsPullback f' g P p1 p2.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hf.
  - intros Q q1 q2 Hq.
    apply Hu.
    now rewrite Hf.
Qed.

(* Reindexing along ≈-equal morphisms yields equivalent subobjects: the
   chosen pullback along f is also a pullback square along f'. *)
Lemma sub_reindex_respects_mor {x y : C} (f f' : y ~> x) (Hf : f ≈ f')
      (u : SubObj x) :
  sub_reindex f u ≈ sub_reindex f' u.
Proof.
  symmetry.
  apply (sub_reindex_transport
           f' u (sub_reindex f u)
           (pullback_snd f (sub_mono u) (pullback f (sub_mono u)))).
  apply (is_pullback_respects_left Hf).
  apply pullback_is_pullback.
Qed.

(* The square with id on top and bottom and m on both sides is a pullback:
   the mediator for a cone (q1, q2) is q2 itself. *)
Lemma is_pullback_along_id {x y : C} (m : y ~> x) :
  IsPullback id m y m id.
Proof.
  constructor.
  - cat.
  - intros Q q1 q2 Hq.
    rewrite id_left in Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split.
      * now rewrite <- Hq.
      * cat.
    + intros w [Hw1 Hw2].
      now rewrite <- Hw2; cat.
Qed.

(* Reindexing along the identity is the identity on subobjects. *)
Lemma sub_reindex_id {x : C} (u : SubObj x) : sub_reindex id u ≈ u.
Proof.
  apply (sub_reindex_transport id u u id).
  apply is_pullback_along_id.
Qed.

(* Reindexing along a composite g ∘ f is reindexing along g and then along
   f: pasting the two chosen squares exhibits the double pullback as one
   pullback square for the composite. *)
Lemma sub_reindex_comp {x y z : C} (g : y ~> x) (f : z ~> y)
      (u : SubObj x) :
  sub_reindex (g ∘ f) u ≈ sub_reindex f (sub_reindex g u).
Proof.
  apply (sub_reindex_transport
           (g ∘ f) u (sub_reindex f (sub_reindex g u))
           (pullback_snd g (sub_mono u) (pullback g (sub_mono u))
              ∘ pullback_snd f (sub_mono (sub_reindex g u))
                  (pullback f (sub_mono (sub_reindex g u))))).
  apply (pullback_paste
           (pullback_is_pullback g (sub_mono u) (pullback g (sub_mono u)))
           (pullback_is_pullback f (sub_mono (sub_reindex g u))
              (pullback f (sub_mono (sub_reindex g u))))).
Qed.

(* The subobject presheaf: contravariant on C, valued in setoids.  A
   C^op-arrow f : x ~> y is a C-arrow y ~> x, and acts by pullback
   reindexing; the functor laws are the three lemmas above, read at the
   pointwise hom-setoid of Sets.  Naming note: [Sub] is the work
   order's name and coexists with Construction/Subcategory.v's
   category [Sub]; the two live in different modules, so qualify the
   reference in any file importing both.  The generic transport lemma
   [is_pullback_respects_left] above (and its companion
   [is_pullback_respects_snd] in Structure/SubobjectClassifier.v) are
   candidates for promotion into Theory/Morphisms/Stability.v beside
   [IsPullback]. *)
Local Obligation Tactic := simpl; intros.

Program Definition Sub : C^op ⟶ Sets := {|
  fobj := fun x : C => {| carrier   := SubObj x
                        ; is_setoid := @SubObj_Setoid C x |};
  fmap := fun x y (f : x ~{C^op}~> y) =>
            {| morphism := sub_reindex (unop f)
             ; proper_morphism := sub_reindex_respects (unop f) |}
|}.
Next Obligation.
  repeat intro.
  apply sub_reindex_respects_mor.
  exact X.
Qed.
Next Obligation.
  apply sub_reindex_id.
Qed.
Next Obligation.
  apply sub_reindex_comp.
Qed.

End SubFunctor.
