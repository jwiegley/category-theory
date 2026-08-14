Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Construction.Product.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.FreeMonoidal.
Require Import Category.Construction.FreeMonoidal.Normal.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Theorem 1: W is the free monoidal category on one generator

    Mac Lane, CWM 2nd ed., §VII.2, Theorem 1 [maclane:VII.2:thm1]: for any
    monoidal category [B] and object [b : B] there is a unique morphism
    [W ⟶ B] of monoidal categories carrying the generator to [b] — namely
    substitution of [b] into all blanks.

    THE MORPHISM NOTION IS STRICT, and that is Mac Lane's own reading, not a
    weakening: his Moncat (§VII.1, [maclane:VII.1:construction2]) is "the
    category of all small monoidal categories with STRICT morphisms as
    arrows", and a strict morphism ([maclane:VII.1:def3]) carries α, λ, ρ to
    α', λ', ρ' on the nose.  Uniqueness among merely strong monoidal functors
    is false — any conjugate of [Subst] by a nonidentity natural isomorphism
    is again strong monoidal and sends the generator to an isomorph of [b] —
    so the strict reading is the only one under which Theorem 1 can hold.
    Existence is nevertheless delivered at BOTH strengths below:
    [Subst_Monoidal] (strong) and [Subst_Strict] (strict, with both object
    equations [eq_refl] on the nose).

    What is deliberately NOT delivered here, and where it is recorded:
    uniqueness up to monoidal natural isomorphism among STRONG monoidal
    functors.  The library has no monoidal-natural-transformation class for
    strong functors (Theory/Natural/Transformation/Monoidal.v states
    [LaxMonoidal_Transform] for lax functors only), so that statement has no
    home; it is ledgered in doc/classical-completion-plan.md rather than
    approximated. *)

Section Universal.

Context {B : Category}.
Context `{MB : @Monoidal B}.
Context (b : B).

(** ** The substitution functor *)

(* On objects, [subst b]; on the unique arrow [p : wlen v = wlen w],
   normalise, transport along [p], denormalise. *)
Program Definition Subst : W ⟶ B := {|
  fobj := subst b;
  fmap := fun v w (p : v ~{W}~> w) =>
    from (can b w)
      ∘ id_cast (f_equal (fun i => nf b i I) p)
      ∘ to (can b v)
|}.
Next Obligation.
  (* fmap_respects: W's hom-setoid identifies ALL parallel arrows, so the
     cast must not depend on the proof — nat-UIP, the only place it is
     needed for functoriality. *)
  proper.
  apply compose_respects; [| reflexivity ].
  apply compose_respects; [ reflexivity |].
  apply nf_cast_irr.
Qed.
Next Obligation.
  (* fmap_id: the cast at eq_refl is the identity by conversion. *)
  rewrite id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  (* fmap_comp: cancel the inner normalise/denormalise pair, fuse casts. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (can b y))).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (id_cast _)).
  rewrite nf_cast_trans.
  reflexivity.
Qed.

(** ** The tensor comparison *)

(* Mac Lane's T(f □ g) = Tf □' Tg. *)
Theorem Subst_tensor {v v' u u' : Word}
  (p : v ~{W}~> v') (q : u ~{W}~> u') :
  fmap[Subst] (fmap[W_tensor] ((p, q) : (v, u) ~{W ∏ W}~> (v', u')))
    ≈ bimap (fmap[Subst] p) (fmap[Subst] q).
Proof.
  simpl.
  (* Peel the join off the cast with [J_cast], then cancel it against its
     inverse; the residue is the bimap of the two component fmaps. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (id_cast _) (to (J b (wlen v) (wlen u) I))).
  rewrite (J_cast b p q).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (J b (wlen v') (wlen u') I))
                      (to (J b (wlen v') (wlen u') I))).
  rewrite iso_from_to, id_left.
  normal.
  reflexivity.
Qed.

(* From here on the goals are monoidal-coherence shaped, and the global
   [cat_simpl] obligation tactic pre-processes them unpredictably; take manual
   control instead (precedent: Functor/Structure/Monoidal/Id.v). *)
#[local] Obligation Tactic := idtac.

(* The comparison natural isomorphism has identity components: [subst] is
   strict on objects, so the two composite functors agree definitionally on
   objects and the comparison square is [Subst_tensor]. *)
Program Definition Subst_ap_to :
  ((⨂) ◯ Subst ∏⟶ Subst) ~{[W ∏ W, B]}~> (Subst ◯ (⨂)) := {|
  transform := fun _ => id
|}.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.

Program Definition Subst_ap_from :
  (Subst ◯ (⨂)) ~{[W ∏ W, B]}~> ((⨂) ◯ Subst ∏⟶ Subst) := {|
  transform := fun _ => id
|}.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.
Next Obligation.
  intros [v u] [v' u'] [p q]; simpl.
  rewrite id_left, id_right.
  first [ exact (@Subst_tensor v v' u u' p q)
        | symmetry; exact (@Subst_tensor v v' u u' p q) ].
Qed.

Program Definition Subst_ap :
  ((⨂) ◯ Subst ∏⟶ Subst) ≅[[W ∏ W, B]] (Subst ◯ (⨂)) := {|
  to   := Subst_ap_to;
  from := Subst_ap_from
|}.
Next Obligation.
  intros [v u]; simpl; cat.
  symmetry.
  rewrite nf_cast_loop, id_right.
  rewrite <- (comp_assoc _ (from (J b (wlen v) (wlen u) I))).
  rewrite (comp_assoc (from (J b (wlen v) (wlen u) I))
             (to (J b (wlen v) (wlen u) I))).
  rewrite iso_from_to, id_left.
  normal.
  rewrite !iso_from_to.
  normal.
  reflexivity.
Qed.
Next Obligation.
  intros [v u]; simpl; cat.
  symmetry.
  etransitivity; [| apply bimap_id_id ].
  apply fmap_respects.
  split; apply iso_from_to.
Qed.

(** ** The three strictness equations

    Stated standalone so the coherence corollary (#497) can consume them. *)

Theorem Subst_unit_left (x : Word) :
  fmap[Subst] (to (@unit_left W W_Monoidal x))
    ≈ to (@unit_left B MB (subst b x)).
Proof.
  simpl.
  rewrite id_right.
  rewrite <- (to_unit_left_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Subst_unit_right (x : Word) :
  fmap[Subst] (to (@unit_right W W_Monoidal x))
    ≈ to (@unit_right B MB (subst b x)).
Proof.
  simpl.
  (* Group the cast against the join; that pair is exactly [J_right_unit]. *)
  rewrite comp_assoc.
  rewrite <- (comp_assoc (from (can b x))).
  rewrite (J_right_unit b (wlen x)).
  rewrite <- (comp_assoc (from (can b x))).
  rewrite <- (to_unit_right_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Subst_assoc (x y z : Word) :
  fmap[Subst] (to (@tensor_assoc W W_Monoidal x y z))
    ≈ to (@tensor_assoc B MB (subst b x) (subst b y) (subst b z)).
Proof.
  simpl.
  (* Read J_assoc across the eq_sym cast first: composing both sides of
     [J_assoc] with the loop kills its cast. *)
  assert (JA' :
    id_cast (f_equal (fun i => nf b i I)
               (eq_sym (Nat.add_assoc (wlen x) (wlen y) (wlen z))))
      ∘ to (J b (wlen x + wlen y) (wlen z) I)
      ∘ bimap (to (J b (wlen x) (wlen y) I)) id
      ≈ to (J b (wlen x) (wlen y + wlen z) I)
          ∘ bimap id (to (J b (wlen y) (wlen z) I))
          ∘ to tensor_assoc).
  { rewrite <- comp_assoc.
    rewrite (J_assoc b (wlen x) (wlen y) (wlen z) I).
    rewrite !comp_assoc.
    rewrite nf_cast_trans.
    rewrite nf_cast_loop, id_left.
    reflexivity. }
  (* Assemble the left side into cast-join-components form and fire JA'. *)
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ (id_cast _)
                (to (J b (wlen x + wlen y) (wlen z) I))).
  rewrite <- (id_left (to (can b z))) at 1.
  rewrite bimap_comp.
  rewrite (comp_assoc _ (bimap (to (J b (wlen x) (wlen y) I)) id)
             (bimap (bimap (to (can b x)) (to (can b y))) (to (can b z)))).
  rewrite <- (comp_assoc _
                (id_cast _ ∘ to (J b (wlen x + wlen y) (wlen z) I))
                (bimap (to (J b (wlen x) (wlen y) I)) id)).
  rewrite JA'.
  (* Cancel the outer join pair, carry α across the components, and let the
     remaining conjugates cancel. *)
  rewrite <- (comp_assoc _ (from (J b (wlen x) (wlen y + wlen z) I))).
  rewrite (comp_assoc (from (J b (wlen x) (wlen y + wlen z) I))
             (to (J b (wlen x) (wlen y + wlen z) I)
                ∘ bimap id (to (J b (wlen y) (wlen z) I)))
             (to tensor_assoc)).
  rewrite (comp_assoc (from (J b (wlen x) (wlen y + wlen z) I))
             (to (J b (wlen x) (wlen y + wlen z) I))).
  rewrite iso_from_to, id_left.
  rewrite <- (comp_assoc _
                (bimap id (to (J b (wlen y) (wlen z) I)) ∘ to tensor_assoc)).
  rewrite <- (comp_assoc (bimap id (to (J b (wlen y) (wlen z) I)))
                (to tensor_assoc)).
  rewrite <- (to_tensor_assoc_natural
                (to (can b x)) (to (can b y)) (to (can b z))).
  normal.
  (* The residue is [bimap id CONJ ∘ α ≈ α] with CONJ a conjugate of the
     y/z-join by its inverse; close by congruence so the argument does not
     depend on how [normal] grouped the composite. *)
  etransitivity; [| apply id_left ].
  apply compose_respects; [| reflexivity ].
  etransitivity; [| apply bimap_id_id ].
  apply fmap_respects; split; simpl.
  - apply iso_from_to.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc (from (J b (wlen y) (wlen z) I))
                        (to (J b (wlen y) (wlen z) I))).
    rewrite iso_from_to, id_left.
    normal.
    rewrite ?iso_from_to.
    normal.
    reflexivity.
Qed.

(** ** The strong and strict monoidal packagings *)

Program Definition Subst_Monoidal :
  @MonoidalFunctor W B W_Monoidal MB Subst := {|
  pure_iso       := iso_id;
  ap_functor_iso := Subst_ap;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc   := fun x y z => tensor_assoc
|}.
Next Obligation.
  intros x; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- (to_unit_left_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.
Next Obligation.
  intros x; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  symmetry.
  rewrite <- (comp_assoc (from (can b x)) (id_cast _)
                (to (J b (wlen x) 0 I))).
  rewrite (J_right_unit b (wlen x)).
  rewrite <- comp_assoc.
  rewrite <- (to_unit_right_natural (to (can b x))).
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.
Next Obligation.
  intros x y z; simpl.
  normal.
  rewrite ?id_left, ?id_right.
  (* [normal] left-associated one node further than [fmap]'s definitional
     grouping; put it back and the goal IS [Subst_assoc], by conversion. *)
  rewrite <- (comp_assoc _ (to (J b (wlen x + wlen y) (wlen z) I))
                (bimap (to (J b (wlen x) (wlen y) I)
                          ∘ bimap (to (can b x)) (to (can b y)))
                       (to (can b z)))).
  exact (Subst_assoc x y z).
Qed.

Program Definition Subst_Strict :
  @StrictMonoidalFunctor W B W_Monoidal MB Subst := {|
  strict_functor_is_monoidal := Subst_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj   := fun _ _ => eq_refl
|}.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros x y; simpl; reflexivity. Qed.

(** ** Acceptance tests *)

(* The generator condition, definitionally. *)
Example Subst_generator : Subst WI = b := eq_refl.

(* Strictness on the nose: both object equalities of [Subst_Strict] are
   literally [eq_refl], stronger than the class demands. *)
Example Subst_strict_pure_on_the_nose :
  @strict_pure_obj W B W_Monoidal MB Subst Subst_Strict = eq_refl := eq_refl.
Example Subst_strict_ap_on_the_nose (x y : Word) :
  @strict_ap_obj W B W_Monoidal MB Subst Subst_Strict x y = eq_refl := eq_refl.

(* The associator instance at length 3, and the unitors at length 1. *)
Corollary Subst_assoc_words :
  fmap[Subst] (to (@tensor_assoc W W_Monoidal WI WI WI))
    ≈ to (@tensor_assoc B MB b b b).
Proof. apply Subst_assoc. Qed.

Corollary Subst_unit_left_word :
  fmap[Subst] (to (@unit_left W W_Monoidal WI))
    ≈ to (@unit_left B MB b).
Proof. apply Subst_unit_left. Qed.

Corollary Subst_unit_right_word :
  fmap[Subst] (to (@unit_right W W_Monoidal WI))
    ≈ to (@unit_right B MB b).
Proof. apply Subst_unit_right. Qed.

(** ** Uniqueness

    Any strict monoidal functor sending the generator to [b] agrees with
    [Subst] — on objects by a derived Leibniz equality [Theta], on morphisms
    up to conjugation by the [Theta]-transports.  The statements are given in
    SQUARE form ([id_cast (Theta -)] naturality squares) rather than through
    [hom_cast], because squares compose; the [hom_cast] reading is recovered
    by composing with the invertible casts. *)

(* The W-side mirrors of the join and the normaliser.  Their RECURSIVE
   STRUCTURE is the point (each branch is a structure map of W, which [G]'s
   strictness translates), not the underlying arrows — W is thin. *)
Fixpoint JW (m n : nat) : WT (nfword m) (nfword n) ≅[W] nfword (m + n) :=
  match m with
  | O   => @unit_left W W_Monoidal (nfword n)
  | S k => @tensor_iso W W_Monoidal WI WI _ _ iso_id (JW k n)
             ⊙ @tensor_assoc W W_Monoidal WI (nfword k) (nfword n)
  end.

Fixpoint canW (w : Word) : w ≅[W] nfword (wlen w) :=
  match w with
  | WE     => iso_id
  | WI     => iso_sym (@unit_right W W_Monoidal WI)
  | WT v u => JW (wlen v) (wlen u)
                ⊙ @tensor_iso W W_Monoidal
                    v (nfword (wlen v)) u (nfword (wlen u))
                    (canW v) (canW u)
  end.

(* Transparent tensor-congruence for object equalities.  [f_equal2] is
   opaque (Qed) in the stdlib, so casts along it can only be discharged by
   UIP — unavailable at an arbitrary [B].  This match-defined twin reduces. *)
Definition tensor_eq {X X' Y Y' : B} (e1 : X = X') (e2 : Y = Y') :
  (X ⨂ Y)%object = (X' ⨂ Y')%object :=
  match e1 with eq_refl => match e2 with eq_refl => eq_refl end end.

Lemma id_cast_tensor_eq {X X' Y Y' : B} (e1 : X = X') (e2 : Y = Y') :
  id_cast (tensor_eq e1 e2) ≈ bimap (id_cast e1) (id_cast e2).
Proof. destruct e1, e2; simpl; now rewrite bimap_id_id. Qed.

Section Uniqueness.

Context (G : W ⟶ B).
Context (SG : @StrictMonoidalFunctor W B W_Monoidal MB G).
Context (Hb : G WI = b).

(* Object agreement, DERIVED from strictness plus the single generator
   datum — where the PROP development takes the whole family as a
   hypothesis. *)
Fixpoint Theta (w : Word) : G w = subst b w :=
  match w with
  | WE     => eq_sym (@strict_pure_obj _ _ _ _ G SG)
  | WI     => Hb
  | WT v u => eq_trans
                (eq_sym (@strict_ap_obj _ _ _ _ G SG v u))
                (tensor_eq (Theta v) (Theta u))
  end.

(* Mac Lane's T(f □ g) = Tf □' Tg, extracted from strictness once: the
   naturality square of the tensor comparison, with both components rewritten
   to transported identities. *)
Lemma strict_fmap_bimap {v v' u u' : Word}
  (f : v ~{W}~> v') (g : u ~{W}~> u') :
  id_cast (@strict_ap_obj _ _ _ _ G SG v' u')
      ∘ bimap (fmap[G] f) (fmap[G] g)
    ≈ fmap[G] (fmap[W_tensor] ((f, g) : (v, u) ~{W ∏ W}~> (v', u')))
        ∘ id_cast (@strict_ap_obj _ _ _ _ G SG v u).
Proof.
  pose proof (naturality
                (to (@ap_functor_iso _ _ _ _ G
                       (@strict_functor_is_monoidal _ _ _ _ G SG)))
                (v, u) (v', u') (f, g)) as N.
  simpl in N.
  rewrite <- (@strict_ap_iso_id _ _ _ _ G SG v' u').
  rewrite <- (@strict_ap_iso_id _ _ _ _ G SG v u).
  symmetry in N; exact N.
Qed.

(* W is thin, so G cannot distinguish parallel arrows — the license to pick
   the structurally convenient representative in every proof below. *)
Lemma G_irr {v w : Word} (p q : v ~{W}~> w) : fmap[G] p ≈ fmap[G] q.
Proof. apply fmap_respects; constructor. Qed.

(* The canonical arrow between normalised words of equal length, and its
   G-image: a transported identity.  Stated over bare naturals so [destruct]
   applies. *)
Definition nfword_arrow {m n : nat} (e : m = n) :
  nfword m ~{W}~> nfword n :=
  match e in _ = k return nfword m ~{W}~> nfword k with
  | eq_refl => eq_refl
  end.

Lemma G_nfword_cast {m n : nat} (e : m = n) :
  fmap[G] (nfword_arrow e)
    ≈ id_cast (f_equal (fun i => G (nfword i)) e).
Proof.
  destruct e; simpl.
  change (fmap[G] (@id W (nfword m)) ≈ id).
  apply fmap_id.
Qed.

(* Shorthand for the object-agreement transport. *)
Notation thc w := (id_cast (Theta w)).

(* [subst (nfword n) = nf n I] holds by induction, NOT by conversion — at an
   open [n] neither side reduces.  Transparent so its casts destruct. *)
Fixpoint subst_nfword (n : nat) : subst b (nfword n) = nf b n I :=
  match n with
  | O   => eq_refl
  | S k => tensor_eq eq_refl (subst_nfword k)
  end.

Notation sigma n := (id_cast (subst_nfword n)).

(* Bridges: Strict.v's transported-identity matches ARE [id_cast] — the
   to-direction definitionally, the from-direction along the symmetric
   equality.  Stated as Leibniz equalities so they rewrite match-forms into
   cast-forms that the kit lemmas can see. *)
Lemma id_cast_match {X Y : B} (e : X = Y) :
  (match e in _ = T return X ~{B}~> T with eq_refl => id end) = id_cast e.
Proof. reflexivity. Qed.
(* Bridge: the [from]-direction matches of Strict.v are the casts along the
   symmetric equalities. *)
Lemma id_cast_sym_match {X Y : B} (e : X = Y) :
  (match e in _ = T return T ~{B}~> X with eq_refl => id end)
    = id_cast (eq_sym e).
Proof. destruct e; reflexivity. Qed.

(* [sigma (S k)] and its kin display as the partially-reduced [tensor_eq]
   match; this is that shape's split lemma. *)
Lemma id_cast_tensor_match {Y Y' : B} (e : Y = Y') :
  id_cast (match e in _ = o
           return ((b ⨂ Y)%object = (b ⨂ o)%object)
           with eq_refl => eq_refl end)
    ≈ bimap id[b] (id_cast e).
Proof. destruct e; simpl; now rewrite bimap_id_id. Qed.

(* The tensor of two object agreements is the agreement at the tensor,
   across the strictness cast. *)
Lemma thc_tensor (v u : Word) :
  bimap (thc v) (thc u)
    ≈ thc (WT v u) ∘ id_cast (@strict_ap_obj _ _ _ _ G SG v u).
Proof.
  simpl.
  rewrite <- id_cast_trans, id_cast_tensor_eq.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(* The join square: G carries the W-side join to the B-side join, across the
   object agreement.  Induction on m; the base is SG's left unitality, the
   step is SG's associativity coherence. *)
Lemma JW_unique (m n : nat) :
  to (J b m n I)
      ∘ bimap (sigma m) (sigma n)
      ∘ thc (WT (nfword m) (nfword n))
    ≈ sigma (m + n) ∘ thc (nfword (m + n)) ∘ fmap[G] (to (JW m n)).
Proof.
  induction m; simpl.
  - (* SG's left unitality, solved for the G-image of the W-side unitor in
       ISO form first (pure inverse cancellations), converting the inverses
       to transported identities only at the interface. *)
    pose proof (@monoidal_unit_left _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG) (nfword n)) as UL.
    assert (GL : fmap[G] (to (@unit_left W W_Monoidal (nfword n)))
              ≈ to (@unit_left B MB (G (nfword n)))
                  ∘ bimap (from (@pure_iso _ _ _ _ G
                            (@strict_functor_is_monoidal _ _ _ _ G SG))) id
                  ∘ from (@ap_iso _ _ _ _ G
                            (@strict_functor_is_monoidal _ _ _ _ G SG)
                            WE (nfword n))).
    { symmetry.
      rewrite UL.
      etransitivity; [| apply id_right ].
      rewrite <- !comp_assoc.
      apply compose_respects; [ reflexivity |].
      rewrite (comp_assoc (bimap (to (@pure_iso _ _ _ _ G _)) id)
                          (bimap (from (@pure_iso _ _ _ _ G _)) id)).
      rewrite <- bimap_comp.
      rewrite iso_to_from.
      normal.
      rewrite iso_to_from.
      reflexivity. }
    rewrite GL.
    rewrite (@strict_ap_iso_from _ _ _ _ G SG WE (nfword n)).
    rewrite (@strict_pure_iso_from _ _ _ _ G SG).
    rewrite !id_cast_sym_match.
    (* Split the composite object-agreement cast. *)
    rewrite <- id_cast_trans.
    rewrite id_cast_tensor_eq.
    (* Carry the agreement across the left unitor by naturality. *)
    rewrite !comp_assoc.
    rewrite (to_unit_left_natural (id_cast (subst_nfword n) ∘ thc (nfword n))).
    rewrite <- (comp_assoc _
                  (bimap id (id_cast (subst_nfword n) ∘ thc (nfword n)))
                  (bimap (id_cast (eq_sym (@strict_pure_obj _ _ _ _ G SG))) id)).
    rewrite bimap_id_left_right.
    (* Fuse the left side's cast pair into the same shape. *)
    rewrite <- (comp_assoc _
                  (bimap (id_cast (subst_nfword 0)) (id_cast (subst_nfword n)))
                  (bimap (id_cast (eq_sym (@strict_pure_obj _ _ _ _ G SG)))
                         (thc (nfword n)))).
    rewrite <- bimap_comp.
    normal.
    change (id_cast (subst_nfword 0)) with (@id B (@I B MB)).
    normal.
    reflexivity.
  - (* Split G over the S-branch composite, solve SG's associativity law for
       the G-image of the W-side associator, and reduce to the IH. *)
    (* simpl dissolved W's composition into eq_trans; thinness lets us swap
       in the explicit composite representative before splitting G over it. *)
    rewrite (G_irr _ (bimap (@id W WI) (to (JW m n))
                        ∘ to (@tensor_assoc W W_Monoidal
                                WI (nfword m) (nfword n)))).
    rewrite fmap_comp.
    pose proof (@monoidal_assoc _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG)
                  WI (nfword m) (nfword n)) as MA.
    simpl in MA.
    (* LHS -> RHS.  Split every composite cast, push the associator across
       the components, fold the IH back in, then let strictness translate the
       remaining G-images. *)
    rewrite <- !id_cast_trans.
    rewrite !id_cast_tensor_eq.
    rewrite !id_cast_tensor_match.
    (* Split the inner layer of composite casts as well. *)
    rewrite <- !id_cast_trans.
    rewrite !id_cast_tensor_eq.
    rewrite <- (id_right (thc (nfword n))).
    rewrite bimap_comp.
    normal.
    rewrite <- (id_right (sigma n ∘ thc (nfword n))).
    rewrite bimap_comp.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _ (to tensor_assoc)
                  (bimap (bimap (id_cast Hb) (sigma m ∘ thc (nfword m)))
                         (sigma n ∘ thc (nfword n)))).
    rewrite <- (to_tensor_assoc_natural
                  (id_cast Hb) (sigma m ∘ thc (nfword m))
                  (sigma n ∘ thc (nfword n))).
    normal.
    rewrite (bimap_comp (id_cast (subst_nfword m)) (thc (nfword m))
                        (id_cast (subst_nfword n)) (thc (nfword n))).
    rewrite (thc_tensor (nfword m) (nfword n)).
    rewrite (comp_assoc (sigma m ⨂ sigma n)
               (thc (WT (nfword m) (nfword n)))).
    rewrite (comp_assoc (to (J b m n I))
               (sigma m ⨂ sigma n ∘ thc (WT (nfword m) (nfword n)))).
    rewrite (comp_assoc (to (J b m n I)) (sigma m ⨂ sigma n)).
    rewrite IHm.
    (* Expand G over the bimap via strictness. *)
    assert (GB : fmap[G] (bimap (@id W WI) (to (JW m n)))
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG WI (nfword (m + n)))
                  ∘ bimap (fmap[G] (@id W WI)) (fmap[G] (to (JW m n)))
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                               WI (WT (nfword m) (nfword n))))).
    { symmetry.
      rewrite (strict_fmap_bimap (@id W WI) (to (JW m n))).
      rewrite <- comp_assoc.
      rewrite id_cast_inv_r.
      now rewrite id_right. }
    rewrite (G_irr (fmap[W_tensor]
                      ((@id W WI, to (JW m n))
                        : (WI, WT (nfword m) (nfword n)) ~{W ∏ W}~>
                          (WI, nfword (m + n))))
                   (bimap (@id W WI) (to (JW m n)))) in GB.
    rewrite GB.
    rewrite fmap_id.
    (* Cancel the adjacent inverse pair the GB insertion created. *)
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _
                  (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                               WI (nfword (m + n)))))
                  (id_cast (@strict_ap_obj _ _ _ _ G SG WI (nfword (m + n))))).
    rewrite id_cast_inv_l, id_right.
    (* The G-image of the W-associator, in all-cast form, from MA. *)
    assert (GAc : fmap[G] (to (@tensor_assoc W W_Monoidal
                                 WI (nfword m) (nfword n)))
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG
                           WI (WT (nfword m) (nfword n)))
                  ∘ bimap id (id_cast (@strict_ap_obj _ _ _ _ G SG
                           (nfword m) (nfword n)))
                  ∘ to (@tensor_assoc B MB (G WI) (G (nfword m)) (G (nfword n)))
                  ∘ bimap (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                           WI (nfword m)))) id
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                           (WT WI (nfword m)) (nfword n)))).
    { pose proof (@strict_ap_iso_id _ _ _ _ G SG WI (nfword m)) as C2.
      pose proof (@strict_ap_iso_id _ _ _ _ G SG
                    (WT WI (nfword m)) (nfword n)) as C4.
      pose proof (@strict_ap_iso_id _ _ _ _ G SG
                    WI (WT (nfword m) (nfword n))) as C1.
      pose proof (@strict_ap_iso_id _ _ _ _ G SG (nfword m) (nfword n)) as Cmn.
      simpl in C1, C2, C4, Cmn.
      rewrite C1, C2, C4, Cmn in MA.
      rewrite !id_cast_match in MA.
      rewrite (@G_irr (WT (WT WI (nfword m)) (nfword n))
                      (WT WI (WT (nfword m) (nfword n))) _
                 (Compat.eq_sym
                    (Nat.add_assoc 1 (wlen (nfword m)) (wlen (nfword n))))).
      symmetry.
      rewrite <- MA.
      etransitivity; [| apply id_right ].
      rewrite <- !comp_assoc.
      apply compose_respects; [ reflexivity |].
      rewrite (comp_assoc
                 (bimap (id_cast (@strict_ap_obj _ _ _ _ G SG WI (nfword m))) id)
                 (bimap (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                            WI (nfword m)))) id)).
      rewrite <- bimap_comp.
      rewrite id_cast_inv_r.
      normal.
      rewrite id_cast_inv_r.
      reflexivity. }
    rewrite GAc.
    (* Cancel the WT-pair the GAc insertion created, split the leftover inner
       cast on the left, and the two sides fuse to the same normal form. *)
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _
                  (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG
                               WI (WT (nfword m) (nfword n)))))
                  (id_cast (@strict_ap_obj _ _ _ _ G SG
                               WI (WT (nfword m) (nfword n))))).
    rewrite id_cast_inv_l, id_right.
    rewrite <- (id_right (id_cast Hb)).
    rewrite bimap_comp.
    normal.
    reflexivity.
Qed.

(* The normaliser square: G agrees with the canonical normalisation maps,
   across the object agreement.  Structural induction; the generator case is
   SG's right unitality read backwards through the iso inverses, the tensor
   case is [strict_fmap_bimap] + the tensored IHs + [JW_unique]. *)
Lemma canW_unique (w : Word) :
  to (can b w) ∘ thc w
    ≈ sigma (wlen w) ∘ thc (nfword (wlen w)) ∘ fmap[G] (to (canW w)).
Proof.
  induction w as [ | | v IHv u IHu ]; simpl.
  - (* WE: everything is an identity; the fmap argument is W's identity by
       conversion, but its implicit endpoints resist rewriting — go through
       change + fmap_id. *)
    rewrite !id_left.
    symmetry.
    etransitivity; [| apply id_right ].
    apply compose_respects; [ reflexivity |].
    change (fmap[G] (@id W WE) ≈ @id B (fobj[G] WE)).
    apply fmap_id.
  - (* WI: SG's right unitality, inverted. *)
    pose proof (@monoidal_unit_right _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG) WI) as UR.
    assert (GRinv : fmap[G] (from (@unit_right W W_Monoidal WI))
                      ∘ fmap[G] (to (@unit_right W W_Monoidal WI)) ≈ id).
    { rewrite <- fmap_comp.
      rewrite (@G_irr (WT WI WE) (WT WI WE) _ (@id W (WT WI WE))).
      apply fmap_id. }
    assert (K : fmap[G] (from (@unit_right W W_Monoidal WI))
                  ∘ to (@unit_right B MB (G WI))
              ≈ to (@ap_iso _ _ _ _ G
                      (@strict_functor_is_monoidal _ _ _ _ G SG) WI WE)
                  ∘ bimap id (to (@pure_iso _ _ _ _ G
                      (@strict_functor_is_monoidal _ _ _ _ G SG)))).
    { rewrite UR.
      rewrite !comp_assoc.
      rewrite GRinv.
      now rewrite id_left. }
    assert (GFR : fmap[G] (from (@unit_right W W_Monoidal WI))
              ≈ to (@ap_iso _ _ _ _ G
                      (@strict_functor_is_monoidal _ _ _ _ G SG) WI WE)
                  ∘ bimap id (to (@pure_iso _ _ _ _ G
                      (@strict_functor_is_monoidal _ _ _ _ G SG)))
                  ∘ from (@unit_right B MB (G WI))).
    { symmetry.
      rewrite <- K.
      rewrite <- comp_assoc.
      rewrite iso_to_from.
      now rewrite id_right. }
    clear K.
    rewrite (@G_irr WI (WT WI WE) _ (from (@unit_right W W_Monoidal WI))).
    rewrite GFR.
    rewrite id_left.
    rewrite <- id_cast_trans.
    rewrite id_cast_tensor_eq.
    pose proof (@strict_ap_iso_id _ _ _ _ G SG WI WE) as CA.
    pose proof (@strict_pure_iso_id _ _ _ _ G SG) as CP.
    rewrite CA, CP.
    rewrite !id_cast_match.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _
                  (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG WI WE)))
                  (id_cast (@strict_ap_obj _ _ _ _ G SG WI WE))).
    rewrite id_cast_inv_l, id_right.
    rewrite <- bimap_comp.
    rewrite id_cast_inv_l.
    normal.
    rewrite (from_unit_right_natural (id_cast Hb)).
    reflexivity.
  - (* WT: expand G over the composite and the component bimap, tensor the
       IHs, and finish with the join square. *)
    rewrite (@G_irr (WT v u) (nfword (wlen v + wlen u)) _
               (to (JW (wlen v) (wlen u))
                  ∘ bimap[W_tensor] (to (canW v)) (to (canW u)))).
    rewrite fmap_comp.
    assert (GBc : fmap[G] (bimap[W_tensor] (to (canW v)) (to (canW u)))
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG
                           (nfword (wlen v)) (nfword (wlen u)))
                  ∘ bimap (fmap[G] (to (canW v))) (fmap[G] (to (canW u)))
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG v u))).
    { symmetry.
      rewrite (strict_fmap_bimap (to (canW v)) (to (canW u))).
      rewrite <- comp_assoc.
      rewrite id_cast_inv_r.
      rewrite id_right.
      apply G_irr. }
    rewrite GBc.
    rewrite <- !id_cast_trans.
    rewrite !id_cast_tensor_eq.
    rewrite (comp_assoc _ (bimap (thc v) (thc u))
               (id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG v u)))).
    rewrite <- (comp_assoc (to (J b (wlen v) (wlen u) I))
                  (bimap (to (can b v)) (to (can b u)))
                  (bimap (thc v) (thc u))).
    rewrite <- bimap_comp.
    rewrite IHv, IHu.
    rewrite (bimap_comp
               (id_cast (subst_nfword (wlen v)) ∘ thc (nfword (wlen v)))
               (fmap[G] (to (canW v)))
               (id_cast (subst_nfword (wlen u)) ∘ thc (nfword (wlen u)))
               (fmap[G] (to (canW u)))).
    rewrite (bimap_comp
               (id_cast (subst_nfword (wlen v))) (thc (nfword (wlen v)))
               (id_cast (subst_nfword (wlen u))) (thc (nfword (wlen u)))).
    rewrite (thc_tensor (nfword (wlen v)) (nfword (wlen u))).
    rewrite !comp_assoc.
    rewrite (JW_unique (wlen v) (wlen u)).
    normal.
    reflexivity.
Qed.

(* Two cast-naturality squares along a length equality, both by destruct
   over bare naturals. *)
Lemma thc_nfword_cast (m n : nat) (e : m = n) :
  thc (nfword n) ∘ id_cast (f_equal (fun i => G (nfword i)) e)
    ≈ id_cast (f_equal (fun i => subst b (nfword i)) e) ∘ thc (nfword m).
Proof. destruct e; simpl; now rewrite id_left, id_right. Qed.

Lemma sigma_nfword_cast (m n : nat) (e : m = n) :
  sigma n ∘ id_cast (f_equal (fun i => subst b (nfword i)) e)
    ≈ id_cast (f_equal (fun i => nf b i I) e) ∘ sigma m.
Proof. destruct e; simpl; now rewrite id_left, id_right. Qed.

(* Mac Lane's uniqueness: on EVERY arrow, G agrees with substitution across
   the object agreement.  W is thin, so the proof decomposes the arrow
   through the normalisers — for free — and the three squares compose. *)
Theorem Subst_unique {v w : Word} (p : v ~{W}~> w) :
  fmap[Subst] p ∘ thc v ≈ thc w ∘ fmap[G] p.
Proof.
  assert (GG : fmap[G] (to (canW w)) ∘ fmap[G] (from (canW w)) ≈ id).
  { rewrite <- fmap_comp.
    rewrite (@G_irr (nfword (wlen w)) (nfword (wlen w)) _
               (@id W (nfword (wlen w)))).
    apply fmap_id. }
  assert (SQf : thc w ∘ fmap[G] (from (canW w))
            ≈ from (can b w) ∘ sigma (wlen w) ∘ thc (nfword (wlen w))).
  { transitivity
      (from (can b w)
         ∘ (sigma (wlen w) ∘ thc (nfword (wlen w)) ∘ fmap[G] (to (canW w)))
         ∘ fmap[G] (from (canW w))).
    { symmetry.
      rewrite <- (canW_unique w).
      rewrite !comp_assoc.
      rewrite iso_from_to.
      now rewrite id_left. }
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _ (fmap[G] (to (canW w)))
                  (fmap[G] (from (canW w)))).
    rewrite GG.
    now rewrite id_right. }
  rewrite (@G_irr v w _
             (from (canW w) ∘ (nfword_arrow p ∘ to (canW v)))).
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite SQf.
  rewrite (G_nfword_cast p).
  rewrite <- (comp_assoc _ (thc (nfword (wlen w)))
                (id_cast (f_equal (fun i => G (nfword i)) p))).
  rewrite (thc_nfword_cast (wlen v) (wlen w) p).
  rewrite (comp_assoc _ (id_cast (f_equal (fun i => subst b (nfword i)) p))
                        (thc (nfword (wlen v)))).
  rewrite <- (comp_assoc (from (can b w)) (sigma (wlen w))
                (id_cast (f_equal (fun i => subst b (nfword i)) p))).
  rewrite (sigma_nfword_cast (wlen v) (wlen w) p).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (sigma (wlen v)) (thc (nfword (wlen v)))).
  rewrite <- (comp_assoc _ (sigma (wlen v) ∘ thc (nfword (wlen v)))
                (fmap[G] (to (canW v)))).
  rewrite <- (canW_unique v).
  rewrite !comp_assoc.
  reflexivity.
Qed.

End Uniqueness.

(** ** Theorem 1, packaged

    [maclane:VII.2:thm1]: substitution is a strict monoidal functor sending
    the generator to [b] — with both object equations [eq_refl] — and it is
    the ONLY one: any strict monoidal [G] with [G WI = b] agrees with it on
    objects by a derived Leibniz equality and on every arrow up to transport
    along that equality. *)
Theorem FreeMonoidal_universal :
  (((@StrictMonoidalFunctor W B W_Monoidal MB Subst) *
    (Subst WI = b)) *
   (forall (G : W ⟶ B)
           (SG : @StrictMonoidalFunctor W B W_Monoidal MB G)
           (Hb : G WI = b),
      (forall w : Word, G w = subst b w) *
      (forall (v w : Word) (p : v ~{W}~> w),
         fmap[Subst] p ∘ id_cast (Theta G SG Hb v)
           ≈ id_cast (Theta G SG Hb w) ∘ fmap[G] p)))%type.
Proof.
  split.
  - exact (Subst_Strict, eq_refl).
  - intros G SG Hb.
    exact (Theta G SG Hb, fun v w p => Subst_unique G SG Hb p).
Qed.

End Universal.
