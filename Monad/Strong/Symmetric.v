Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Naturality.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Functor.Strong.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Monad.Strong.

Generalizable All Variables.

(** Strong monads over a symmetric monoidal base: the full right strength. *)

(* nLab: https://ncatlab.org/nlab/show/strong+monad
   nLab: https://ncatlab.org/nlab/show/commutative+monad

   Monad/Strong.v derives, for a strong monad M over a symmetric monoidal
   base, the braid-conjugated right strength

       rstr = M(β) ∘ t ∘ β  :  M x ⨂ y ~> M (x ⨂ y)

   together with its naturality ([rstr_natural]) and its two
   monad-compatibility laws ([rstr_ret], [rstr_join]) — but stops short of
   packaging it as a [RightStrongFunctor]: the two functor-level coherences
   (the ρ-law [rrstrength_id_right] and the α-law [rstrength_assoc]) need the
   braid/unitor coherence ρ ≈ λ ∘ β of Joyal & Street ("Braided tensor
   categories", Adv. Math. 102, 1993, Prop. 2.1), which the bare
   [SymmetricMonoidal] axiomatization does not hand out directly.  That
   coherence is now proved from the hexagons in
   Structure/Monoidal/Braided/Proofs.v ([braid_unit_left],
   [braid_unit_right]), and this file completes the programme:

   1. the naturality corollaries of the left and right strengths in
      single-variable rewrite form ([strength_natural_l/r],
      [rstr_natural_l/r]), the workhorses of every proof below and of the
      Kleisli premonoidal development (Monad/Kleisli/Premonoidal.v);

   2. the double-strength toolkit: unit laws for [dstr] and [dstr'] against
      ret in either factor ([dstr_ret_left], [dstr_ret_right],
      [dstr'_ret_left], [dstr'_ret_right]), joint naturality
      ([dstr_natural], [dstr'_natural]), and Führmann-style reassociation
      lemmas ([dstr_reassoc_left], [dstr_reassoc_left'],
      [dstr'_reassoc_right], [dstr'_reassoc_right']) that rebracket a double
      strength through an extra M-layer (Führmann, "Direct models of the
      computational lambda-calculus", MFPS 1999);

   3. the two missing coherences [rstr_id_right] and [rstr_assoc], plus the
      mixed associativity coherence [strength_rstr_assoc] relating the left
      and the derived right strength across the associator — the key lemma
      behind associativity of the premonoidal tensor on Kl(M);

   4. the packaging: [rstr_nat] (the right strength as a natural
      transformation (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂)), the instances
      [rstr_RightStrongFunctor] and [rstr_RightStrongMonad], and the bridge
      between the concrete commutativity predicate [commutative_sm] and the
      abstract [CommutativeStrongMonad] class, in both directions
      ([commutative_CommutativeStrongMonad], [CSM_commutative_sm]) with the
      round trip [commutative_sm_round_trip].

   The bridge's converse direction is honest: an abstract
   [CommutativeStrongMonad] bundles its own right strength, which need not
   be the braid-derived one, so the converse takes the agreement of the two
   right strengths as an explicit hypothesis.  At the instance produced by
   the forward direction that hypothesis holds by reflexivity, which is
   exactly the round-trip corollary. *)

Section StrongSymmetric.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Naturality corollaries in single-variable rewrite form.          *)
(* ------------------------------------------------------------------ *)

(* Clean the identity components out of a joint naturality square. *)
Local Ltac cleanup_nat SN :=
  repeat (rewrite ?bimap_id_id in SN; rewrite ?fmap_id in SN);
  rewrite ?id_left, ?id_right in SN.

(* Massage a joint (factored) naturality square into single-bimap form. *)
Local Ltac fuse_nat SN :=
  rewrite <- ?fmap_comp in SN;
  rewrite <- ?comp_assoc in SN;
  rewrite ?bimap_id_left_right in SN.

Lemma strength_natural_l {x y z} (g : x ~> y) :
  fmap[M] (g ⨂ id[z]) ∘ strength[M] ≈ strength[M] ∘ (g ⨂ id[M z]).
Proof.
  pose proof (@strength_natural _ _ M _ x y g z z (id[z])) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma strength_natural_r {x z w} (h : z ~> w) :
  fmap[M] (id[x] ⨂ h) ∘ strength[M] ≈ strength[M] ∘ (id[x] ⨂ fmap[M] h).
Proof.
  pose proof (@strength_natural _ _ M _ x x (id[x]) z w h) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma rstr_natural_l {x z y} (f : x ~> z) :
  fmap[M] (f ⨂ id[y]) ∘ rstr ≈ rstr ∘ (fmap[M] f ⨂ id[y]).
Proof.
  pose proof (@rstr_natural _ _ M _ x z y y f (id[y])) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

Lemma rstr_natural_r {x y w} (g : y ~> w) :
  fmap[M] (id[x] ⨂ g) ∘ rstr ≈ rstr ∘ (id[M x] ⨂ g).
Proof.
  pose proof (@rstr_natural _ _ M _ x x y w (id[x]) g) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The double-strength toolkit: unit laws and naturality.           *)
(* ------------------------------------------------------------------ *)

(* Feeding a returned value into the left factor of [dstr] leaves just the
   left strength: the rstr leg collapses by [rstr_ret] and [join_ret]. *)
Lemma dstr_ret_left {x y} :
  dstr ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite rstr_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* Mirror: feeding a returned value into the right factor of [dstr'] leaves
   just the derived right strength. *)
Lemma dstr'_ret_right {x y} :
  dstr' ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite strength_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* The two cross unit laws: [dstr'] against ret on the left and [dstr]
   against ret on the right.  Here the returned value enters the *outer*
   strength of the composite, so the collapse goes through naturality
   (pushing ret across the strength), the opposite compatibility law under
   fmap, and [join_fmap_ret]. *)
Lemma dstr'_ret_left {x y} :
  dstr' ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite <- strength_natural_l.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

Lemma dstr_ret_right {x y} :
  dstr ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite <- rstr_natural_r.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

Lemma dstr_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr ≈ dstr ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ x z u y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- (@rstr_natural _ _ M _ x z (fobj[M] y) (fobj[M] w) u (fmap[M] v)).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite SN.
  reflexivity.
Qed.

Lemma dstr'_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr' ≈ dstr' ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr'.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ (fobj[M] x) (fobj[M] z) (fmap[M] u) y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- SN.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite (@rstr_natural _ _ M _ x z y w u v).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Führmann's reassociation lemmas.                                 *)
(* ------------------------------------------------------------------ *)

(* Rebracketing [dstr] through an extra M-layer on the left factor: for ANY
   f, applying [fmap ret] to the left component and then collapsing with
   join ∘ fmap rstr computes [dstr] again. *)
Lemma dstr_reassoc_left {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((fmap[M] ret[M] ∘ f) ⨂ g)
    ≈ dstr ∘ (f ⨂ g).
Proof.
  assert (E : (fmap[M] ret[M] ∘ f) ⨂ g ≈ (fmap[M] ret[M] ⨂ id) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite <- dstr_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* The same expression with a bare ret in place of fmap ret instead
   computes the sibling double strength [dstr']. *)
Lemma dstr_reassoc_left' {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((ret[M] ∘ f) ⨂ g)
    ≈ dstr' ∘ (f ⨂ g).
Proof.
  assert (E : (ret[M] ∘ f) ⨂ g ≈ (ret[M] ⨂ id[M d]) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite dstr_ret_left.
  unfold dstr'.
  reflexivity.
Qed.

(* Mirror reassociation on the right factor of [dstr']. *)
Lemma dstr'_reassoc_right {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (fmap[M] ret[M] ∘ f))
    ≈ dstr' ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (fmap[M] ret[M] ∘ f) ≈ (id ⨂ fmap[M] ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite <- dstr'_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* Mirror: the bare-ret variant computes [dstr]. *)
Lemma dstr'_reassoc_right' {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (ret[M] ∘ f))
    ≈ dstr ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (ret[M] ∘ f) ≈ (id[M d] ⨂ ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite dstr'_ret_right.
  unfold dstr.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The two right-strength coherences.                               *)
(* ------------------------------------------------------------------ *)

(* Kock's associativity law for the left strength, solved for the composite
   strength ∘ (id ⨂ strength): every proof below uses it in this
   orientation, which requires no bracket surgery at the rewrite site. *)
Lemma strength_assoc_solved {a b c} :
  strength[M] ∘ (id[a] ⨂ strength[M])
    ≈ fmap[M] (to (@tensor_assoc _ _ a b c)) ∘ strength[M]
        ∘ from (@tensor_assoc _ _ a b (M c)).
Proof.
  rewrite strength_assoc.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* The braid-word coherence at the heart of both associativity proofs: the
   two ways of moving the outer factor a of (c ⨂ b) ⨂ a to the front — braid
   the inner pair first and then braid a across the tensor, or braid a
   across in one step on either side of the associator — agree.  It is the
   hexagon [hexagon_b] composed against the solved hexagon
   [hexagon_a_solved], glued by naturality of the braiding. *)
Lemma braid_swap_assoc {a b c} :
  from (@tensor_assoc _ _ a b c) ∘ (braid ∘ (braid ⨂ id[a]))
    ≈ (braid ∘ ((id[c] ⨂ braid) ∘ to (@tensor_assoc _ _ c b a))
         : (c ⨂ b) ⨂ a ~> (a ⨂ b) ⨂ c).
Proof.
  rewrite <- bimap_braid.
  rewrite hexagon_b.
  rewrite hexagon_a_solved.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The same coherence solved against the associator: precomposing the braid
   word with to tensor_assoc on the left cancels the inverse associator. *)
Lemma braid_swap_assoc_solved {a b c} :
  to (@tensor_assoc _ _ a b c) ∘ braid ∘ (id[c] ⨂ braid)
    ∘ to (@tensor_assoc _ _ c b a)
    ≈ (braid ∘ (braid ⨂ id[a]) : (c ⨂ b) ⨂ a ~> a ⨂ (b ⨂ c)).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- braid_swap_assoc.
  rewrite (cancel_to_from_cons tensor_assoc).
  reflexivity.
Qed.

(* The ρ-coherence of the derived right strength: M(ρ) ∘ rstr ≈ ρ.  The
   braid/unitor exchange of Joyal & Street ([braid_unit_right]) turns the
   fused fmap argument ρ ∘ β into λ, the left strength's own unit coherence
   [strength_id_left] absorbs it, and [braid_unit_left] at M x closes the
   remaining λ ∘ β. *)
Lemma rstr_id_right {x} :
  fmap[M] (to unit_right) ∘ rstr ≈ to (@unit_right _ _ (M x)).
Proof.
  unfold rstr.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite braid_unit_right.
  rewrite strength_id_left.
  apply braid_unit_left.
Qed.

(* The α-coherence of the derived right strength, in the to-oriented form
   from which the class field's from-oriented form follows by iso
   cancellation.  The chase: unfold rstr, slide the braids outward by
   naturality of the braiding and of the strength, absorb the two stacked
   strengths with [strength_assoc_solved], convert the residual braid word
   with [braid_swap_assoc], and finish with [braid_swap_assoc_solved] inside
   the fmap argument. *)
Lemma rstr_assoc_to {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap rstr id
    ≈ rstr ∘ to (@tensor_assoc _ _ (M x) y z).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite braid_swap_assoc.
  rewrite (comp_assoc braid (id[M x] ⨂ braid)).
  rewrite <- bimap_braid.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M x])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite braid_swap_assoc_solved.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* The α-coherence in the [RightStrongFunctor] field orientation. *)
Lemma rstr_assoc {x y z} :
  rstr ∘ bimap rstr id ∘ from (@tensor_assoc _ _ (M x) y z)
    ≈ fmap[M] (from (@tensor_assoc _ _ x y z)) ∘ rstr.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to.
  rewrite id_right.
  rewrite <- rstr_assoc_to.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite iso_from_to.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The mixed associativity coherence.                               *)
(* ------------------------------------------------------------------ *)

(* The coherence that mixes the left strength and the derived right
   strength across the associator:

       M(α) ∘ rstr ∘ (t ⨂ id) ≈ t ∘ (id ⨂ rstr) ∘ α

   on (x ⨂ M y) ⨂ z.  This is the hardest single equation of the
   development; its sole consumer is the middle-associativity naturality
   square of the Kleisli premonoidal tensor
   (kl_assoc_natural_middle in Monad/Kleisli/Premonoidal.v).

   The proof is staged: first the symmetric hexagon in solved "cons" form
   (assert S1), which rewrites the inverse-associator-after-braid tail of
   the unfolded left side; then naturality of the strength slides the
   remaining braid under fmap; both sides collapse onto a common
   strength-spine, and the residual fmap argument is the first hexagon plus
   [braid_invol].

   A fallback route, recorded for maintainers: the same equation can
   instead be established at its point of use, by inlining the statement
   into the proof of [kl_assoc_natural_middle] and staging further
   intermediate asserts there against the unfolded Kleisli composite; the
   ingredients — the hexagon lemmas, the strength coherences and
   [braid_invol] — are unchanged, only the staging site moves. *)
Lemma strength_rstr_assoc {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap strength[M] id
    ≈ strength[M] ∘ bimap id rstr ∘ to (@tensor_assoc _ _ x (M y) z).
Proof.
  (* Stage 1: the symmetric hexagon, solved for α⁻¹ ∘ β. *)
  assert (S1 : from (@tensor_assoc _ _ z x (M y))
                 ∘ @braid C _ (x ⨂ M y)%object z
                 ≈ (braid ⨂ id[M y])
                     ∘ (from (@tensor_assoc _ _ x z (M y))
                          ∘ ((id[x] ⨂ braid)
                               ∘ to (@tensor_assoc _ _ x (M y) z)))).
  { apply (iso_to_epic (iso_sym tensor_assoc)).
    rewrite <- !comp_assoc.
    rewrite iso_to_from.
    rewrite id_right.
    rewrite !comp_assoc.
    apply hexagon_identity_sym. }
  unfold rstr.
  rewrite <- !comp_assoc.
  (* Stage 2: normalize both sides onto the common strength-spine. *)
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[x] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite (comp_assoc strength[M] (id[x] ⨂ strength[M])).
  rewrite !strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite S1.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M y])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  (* Stage 3: the residual braid word is the first hexagon plus invol. *)
  rewrite hexagon_identity.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Packaging: the right strong functor and right strong monad.      *)
(* ------------------------------------------------------------------ *)

(* The derived right strength as a natural transformation
   (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂): the shape demanded by the
   [RightStrongFunctor] field.  The component at (x, y) is definitionally
   [rstr], so the coherence laws transfer on the nose. *)
Definition rstr_nat : (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂).
Proof using C M SM SMon.
  refine (@Build_Transform' (C ∏ C) C ((⨂) ◯ M ∏⟶ Id) (M ◯ (⨂))
            (fun p => match p with (x, y) => @rstr C SM M SMon x y end) _).
  intros [x1 x2] [y1 y2] [f g]; simpl.
  exact (@rstr_natural C SM M SMon x1 y1 x2 y2 f g).
Defined.

(* The packaging that Monad/Strong.v deferred: rstr, with the ρ- and
   α-coherences proved above, is a [RightStrongFunctor] structure on M. *)
#[export] Instance rstr_RightStrongFunctor : @RightStrongFunctor C _ M :=
  @Build_RightStrongFunctor C _ M
    rstr_nat
    (fun x => @rstr_id_right x)
    (fun x y z => @rstr_assoc x y z).

(* Sanity check: the packaged right strength is definitionally [rstr]. *)
Corollary rstrength_is_rstr {x y} :
  @rstrength C _ M rstr_RightStrongFunctor x y ≈ rstr.
Proof. reflexivity. Qed.

(* Together with the monad-compatibility laws [rstr_ret] and [rstr_join]
   from Monad/Strong.v, every strong monad over a symmetric base is a right
   strong monad. *)
#[export] Instance rstr_RightStrongMonad : @RightStrongMonad C _ M :=
  @Build_RightStrongMonad C _ M
    strongmonad_is_monad
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y).

(* ------------------------------------------------------------------ *)
(** ** The bridge to [CommutativeStrongMonad].                          *)
(* ------------------------------------------------------------------ *)

(* Forward direction: the concrete commutativity predicate over the derived
   right strength yields the abstract class.  Both sides of the
   [commutativity] field are definitionally [dstr] and [dstr'] once the
   packaged rstrength unfolds to [rstr]. *)
Definition commutative_CommutativeStrongMonad
  (comm : @commutative_sm C SM M SMon) : @CommutativeStrongMonad C _ M :=
  @Build_CommutativeStrongMonad C _ M
    SMon
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y)
    (fun x y => comm x y).

(* Converse direction.  An abstract [CommutativeStrongMonad] carries its own
   bundled right strength, which need not be the braid-derived one, so the
   honest converse takes the agreement E of the two right strengths — over
   the strong monad bundled in H' itself — as an explicit hypothesis and
   produces the concrete predicate for that strong monad. *)
Definition CSM_commutative_sm
  (H' : @CommutativeStrongMonad C _ M)
  (E : ∀ x y, @rstrength C _ M (@comm_is_rstrong C _ M H') x y
                ≈ @rstr C SM M (@comm_is_strong C _ M H') x y) :
  @commutative_sm C SM M (@comm_is_strong C _ M H').
Proof.
  intros x y.
  unfold dstr, dstr'.
  rewrite <- !E.
  exact (@commutativity C _ M H' x y).
Qed.

(* Round trip: at the instance produced by the forward direction, the
   agreement hypothesis holds by reflexivity — the packaged right strength
   IS rstr — and the underlying strong monad is definitionally the ambient
   one, so the composite of the two bridges reproduces a commutativity
   witness for the ambient strong monad. *)
Corollary commutative_sm_round_trip
  (comm : @commutative_sm C SM M SMon) : @commutative_sm C SM M SMon.
Proof.
  apply (CSM_commutative_sm (commutative_CommutativeStrongMonad comm)).
  intros x y.
  reflexivity.
Qed.

End StrongSymmetric.
