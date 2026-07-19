Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Sheaf.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(** * The category of sheaves over a site

    nLab: https://ncatlab.org/nlab/show/category+of+sheaves
    Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

    [Sheaves C] is the FULL subcategory of the presheaf category
    [Presheaves C Sets] (= [C^op, Sets]) on the [Sheaf] predicate of
    Theory/Sheaf.v, built with Construction/Subcategory.v exactly as
    Construction/Reflective.v, Construction/Localization.v and
    Theory/Lawvere/Model.v build their full subcategories: [sobj]
    selects the sheaf witnesses and [shom] retains every natural
    transformation ([True]/[I]).

    SCOPE NOTE, stating the weaknesses of the underlying donor
    precisely.  (i) The [Site] encoding in Theory/Sheaf.v picks a
    SINGLE covering family per object rather than the usual collection
    of covering families — less general than a full coverage.  (ii)
    Deeper, found during this phase's review: the inherited [Sheaf]
    predicate is NOT the textbook unique-gluing condition even for
    that one family.  Its gluing clause is per-leg (a single section
    over one [u_i], not a simultaneous matching family), and its
    compatibility antecedent quantifies over ALL sections of the other
    leg — instantiating [v := u_i], [g := h := id] and the SAME leg
    [j := i] makes the antecedent force [x_i ≈ x_j] for every
    [x_j : X u_i], so the hypothesis is satisfiable only when [X u_i]
    is a subsingleton, and the condition is vacuous at any covered
    object with two inequivalent sections.  "Sheaf" throughout this
    file therefore means: EXACTLY Theory/Sheaf.v's predicate, no more.
    Everything below (the category, the fully faithful inclusion,
    closure under isomorphism) is a genuine theorem about that
    predicate and survives a future repair structurally; the repair
    itself — re-founding [Sheaf] on honest matching families — is a
    named deferral alongside sheafification (ledger entry 1).

    Sheafification (the left adjoint to [Sheaves_Incl], exhibiting
    [Sheaves C] as a reflective subcategory of presheaves) is a named
    deferral: LEDGER ENTRY 1. *)

(** Pointwise implication for the Type-valued [ForallT] of
    Theory/Sheaf.v: a function of witnesses at every element maps a
    [ForallT P] witness over a vector to a [ForallT Q] witness over
    the same vector.  Used twice below, once for the outer family of
    gluing statements and once for the inner compatibility family. *)
Lemma ForallT_impl {A : Type} (P Q : A → Type)
  (h : ∀ a : A, P a → Q a) :
  ∀ {n : nat} (v : Vector.t A n), ForallT P v → ForallT Q v.
Proof.
  intros n v HP; induction HP; constructor; auto.
Qed.

Section SheafCategory.

Context (C : Category).
Context `{@Site C}.

(** The full subcategory data: objects are presheaves equipped with a
    [Sheaf] witness; every natural transformation between two sheaves
    is a morphism of sheaves ([True]), so closure under identity and
    composition is trivial ([I]). *)
Definition Sheaves_sub : Subcategory (@Presheaves C Sets) :=
  @Build_Subcategory (@Presheaves C Sets)
    (fun X : Presheaf C Sets => Sheaf X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Sheaves : Category := Sub (@Presheaves C Sets) Sheaves_sub.

(** The inclusion of sheaves into presheaves. *)
Definition Sheaves_Incl : Sheaves ⟶ @Presheaves C Sets :=
  Incl (@Presheaves C Sets) Sheaves_sub.

(** The subcategory is full by construction, so the inclusion is a
    full functor (via [Full_Implies_Full_Functor]).  Kept [Defined]
    for uniformity, though [Full_Implies_Full_Functor] is itself
    opaque, so the chosen preimage does not compute through this
    route; a transparent inline construction (the preimage is
    literally [(g; I)]) is available should a consumer ever need it
    to compute. *)
Lemma Sheaves_Full : Functor.Full Sheaves_Incl.
Proof.
  apply Full_Implies_Full_Functor.
  intros x y ox oy f; exact I.
Defined.

(** The inclusion is faithful: on hom-sets it is the first projection
    out of a sigma type, and the hom-setoid of [Sub] is equality of
    first projections, so injectivity is immediate. *)
Lemma Sheaves_Faithful : Functor.Faithful Sheaves_Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(** ** Repleteness: the sheaf condition is closed under isomorphism

    If X ≅ Y in [Presheaves C Sets] and X is a sheaf, then Y is a
    sheaf.  The unique-gluing data is transported componentwise across
    the natural isomorphism: a matching family for Y is pulled back
    along [from iso] to a matching family for X (naturality moves the
    restriction maps across the components), X's unique glued section
    is pushed forward along [to iso], and its uniqueness transfers
    because the components are mutually inverse setoid bijections.
    Kept [Defined] so downstream users can compute with the
    transported gluing data. *)
Theorem sheaf_iso_closed
  (X Y : Presheaf C Sets) (iso : X ≅[@Presheaves C Sets] Y) :
  Sheaf X → Sheaf Y.
Proof.
  intros HX.
  constructor; intro u.
  pose proof (@restriction C _ X HX u) as HR.
  revert HR.
  destruct (coverage u) as [n fam].
  apply ForallT_impl.
  intros [uᵢ fᵢ] Hglue yᵢ Hcompat.
  (* Pull the matching family for Y back along [from iso], obtaining a
     matching family for X at the pulled-back section. *)
  assert (HXc : ∀ (v : C) (g : v ~> uᵢ),
            ForallT (A := ∃ uⱼ, uⱼ ~> u)
              (λ '(uⱼ; fⱼ),
                ∀ h : v ~> uⱼ,
                  fᵢ ∘ g ≈ fⱼ ∘ h →
                  ∀ xⱼ : X uⱼ,
                    fmap[X] g (transform[from iso] uᵢ yᵢ) ≈ fmap[X] h xⱼ)
              fam).
  { intros v g.
    generalize (Hcompat v g).
    apply ForallT_impl.
    intros [uⱼ fⱼ] Hj h e xⱼ.
    (* Naturality of [from iso] at g and at h, plus the iso round
       trip at uⱼ, reduce the X-compatibility square to the given
       Y-compatibility square. *)
    pose proof (naturality (from iso) uᵢ v g yᵢ) as HA; simpl in HA.
    pose proof (naturality (from iso) uⱼ v h (transform[to iso] uⱼ xⱼ)) as HB;
      simpl in HB.
    pose proof (iso_from_to iso uⱼ xⱼ) as HC; simpl in HC.
    rewrite HA.
    rewrite (Hj h e (transform[to iso] uⱼ xⱼ)).
    rewrite <- HB.
    apply (proper_morphism (fmap[X] h)).
    rewrite HC.
    exact (@fmap_id _ _ X uⱼ xⱼ). }
  destruct (Hglue (transform[from iso] uᵢ yᵢ) HXc) as [x Hx Hun].
  unshelve econstructor.
  - (* the glued section for Y: push X's glued section forward *)
    exact (transform[to iso] u x).
  - (* it restricts correctly, by naturality of [to iso] *)
    pose proof (naturality (to iso) u uᵢ fᵢ x) as HN; simpl in HN.
    pose proof (iso_to_from iso uᵢ yᵢ) as HD; simpl in HD.
    rewrite HN, Hx, HD.
    exact (@fmap_id _ _ Y uᵢ yᵢ).
  - (* uniqueness: any other glued section for Y pulls back to a glued
       section for X, so it agrees with x, hence with [to iso u x] *)
    intros y' Hy'; simpl in Hy'.
    pose proof (naturality (from iso) u uᵢ fᵢ y') as HN; simpl in HN.
    assert (Hx' : x ≈ transform[from iso] u y'). {
      apply Hun.
      rewrite HN.
      now rewrite Hy'.
    }
    pose proof (iso_to_from iso u y') as HD; simpl in HD.
    rewrite Hx', HD.
    exact (@fmap_id _ _ Y u y').
Defined.

End SheafCategory.
