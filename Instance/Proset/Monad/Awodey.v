Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Awodey's adjunction from a closure operator *)

(* nLab: https://ncatlab.org/nlab/show/closure+operator
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         SS 10.2, printed p. 271, the unnumbered construction after
         Example 10.4
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
         SS 1.4.4, Example 1.122, printed p. 34

   Awodey, p. 271: "In the poset case, we can easily recover an
   adjunction from the monad.  First, let K = im(T)(P) (the fixed points
   of T), and let i : K → P be the inclusion.  Then let t be the
   factorization of T through K ...  Observe that since TTp = Tp, for any
   element k ∈ K we then have, for some p ∈ P, the equation
   itik = ititp = itp = ik, whence tik = k since i is monic.  We therefore
   have: p ≤ ik implies tp ≤ tik = k; tp ≤ k implies p ≤ itp ≤ ik.  So
   indeed t ⊣ i."  Seven Sketches' Example 1.122 builds the same
   adjunction on a preorder, with fix_j = {p | j(p) ≅ p}.

   WHAT IS BUILT.  For a closure operator [c] on a PREORDER
   (Instance/Proset/Monad.v's [ClosureOperator]), K is [ClosedElt c], the
   elements x with cl x ≤ x, ordered as in P ([closed_le],
   [closed_PreOrder]).  [closed_t] sends x to cl x, whose membership proof
   is the field [cl_mult] itself, and [closed_i] is the first projection.
   Awodey's two displayed implications are the unit [cl_ext] and the
   counit (the membership proof) fed to Instance/Proset/Galois.v's
   [galois_of_unit_counit], which gives the Galois connection
   [closed_galois]; [closed_adj] is its [GaloisAdjunction], t ⊣ i between
   the thin categories.

   WHICH K.  Awodey writes K = im(T) and calls it the fixed points.  Over
   a preorder the image, the fixed points and the closed elements agree
   only up to ≅: every cl p is closed ([cl_mult]), and every closed k is
   isomorphic to cl k ([closed_tik_iso]).  The file takes the closed
   elements, which is Seven Sketches' fix_j (j p ≅ p holds exactly when
   j p ≤ p, extensivity giving the other half), because membership is
   then a single inequality with a canonical witness, where the image
   would carry an existential.

   "tik = k SINCE i IS MONIC".  Awodey's i is monic as a map of posets,
   that is, injective, and cancelling it turns i t i k = i k into
   t i k = k.  Over a preorder neither step survives: i t i k is cl k,
   which is only isomorphic to k, and i = proj1_sig identifies two
   elements of K only when their membership proofs are identified, which
   is proof irrelevance.  What holds is: the first component of t (i k)
   is cl k by [eq_refl] ([closed_tik_fst]); t (i k) ≅ k in the order of
   K ([closed_tik_iso]); and under an explicit [Antisymmetric] hypothesis
   the first components are equal
   ([closed_tik_eq]).  The equation t (i k) = k itself is refused by
   conversion: the first components are cl k and k, and the second are
   proofs of a [Prop], which are identified only under proof
   irrelevance, not assumed here.  Awodey's argument is for a poset,
   where his K and the closed elements coincide as sets; this file
   records what survives over a preorder.

   THE INDUCED MONAD IS T.  On objects and on arrows T = i ∘ t by
   [eq_refl] ([closed_factorisation_obj], [closed_factorisation_fmap]).
   The monad induced by t ⊣ i (Monad/Comparison.v's
   [Adjunction_Induced_Monad]), read back through
   Instance/Proset/Monad.v's [closure_of_monad], has a monotone map EQUAL
   to c's, as a whole [MonotoneFun], by [eq_refl] ([closed_induced_is_c]):
   the order-level form of Construction/Reflective/Idempotent/Induced.v.
   As functors, i ◯ t ≈ [closure_functor c] with identity components
   ([closed_induced_functor]).  Awodey does not say in words that the
   adjunction induces T; the construction makes it so, and these are the
   readbacks.  The route through Idempotent.v, with K the M-local
   subcategory, is Instance/Proset/Monad.v's [proset_fixed_adj].

   STRENGTHS, measured.  [eq_refl]: [closed_factorisation_obj],
   [closed_factorisation_fmap], [closed_induced_is_c] (the whole monotone
   map), [closed_tik_fst].  At ≈ or ≅ only, each with its [=] refused by
   conversion in a stripped copy: the functor equation
   i ◯ t = [closure_functor c], whose [fobj] and [fmap] agree by
   [eq_refl] (the two Examples above), so that the refusal sits in the
   law fields.  Flipped first, in a copy of the 55-file dependency closure:
   with [Compose]'s two proved obligations and [Functor_of_monotone]'s
   three made [Defined], and Instance/Proset.v and Galois.v compiled with
   transparent obligations, it is still refused.  The composite's
   [fmap_respects] and [fmap_comp] then reduce to terms stuck on the
   stdlib's opaque [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1],
   left by the setoid rewriting in [Compose]'s proofs, and its [fmap_id]
   on [Compose]'s automatically solved obligation, whose transparency
   breaks a proof script of Structure/Limit/Preservation.v.  So ≈ is the
   strongest available short of re-proving [Compose].  Also refused: the
   WHOLE closure-operator record read back from the induced monad, whose
   two proof fields reduce to c's own [cl_ext] and [cl_mult] each
   composed with a reflexivity by the transitivity of P (the composites
   made by [galois_of_unit_counit]); P is a variable, so no flip can
   identify them with c's.  And t (i k) = k, above.

   UNIVERSES, read off [About].  [ClosedElt@{u}] lives in [Type@{u}].
   Every constant that projects out of the subset type carries the cap
   [u <= Subset_projections.u0] of the stdlib's [proj1_sig], first used by
   [closed_le].  [closed_adj@{u h s a}] has [h < s], introduced by
   Instance/Sets.v's [Sets] ([o < so]) where the hom-setoid isomorphism of
   [Adjunction] lives, and [a] is a level of [GaloisAdjunction] free in
   its block.  [closed_induced_is_c] pins the adjunction to
   [closed_adj@{u h s a}]: unpinned, the adjunction took fresh levels and
   the declared [h] occurred nowhere in the statement (measured by a check
   of every instance level against the printed type).  The composites add
   Theory/Functor.v's [Compose] bound ([u3 < u2]) and the ≈ its
   [Functor_Setoid] bound; each is unified into one strict level per
   constant.  [closed_adj] and [closed_induced_is_c] also carry the
   stdlib caps [h <= compose.u0, compose.u1, compose.u2, ID.u0], first
   carried by [Sets] ([Sets@{o so}] has them at its level o) through
   [Adjunction].  No level occurs only in a body, and no constant carries
   [Set].  Both copies of [Thin] are loaded here (Structure/Thin.v through
   Instance/Proset/Monad.v, and Instance/Proset/Galois.v directly); this
   file names neither.

   NOT DELIVERED.  No comparison between [ClosedElt c] and the M-local
   subcategory of the other route beyond both being reflective with the
   same T; no identification of K with the image of T as a set; no
   whole-record identification of the induced closure operator with c,
   which is refused as above; and no interior-operator dual of this
   order-theoretic construction (the coreflection onto the open elements
   is Instance/Proset/Monad/Interior.v's [proset_open_coreflective],
   through Structure/Thin/Monad.v). *)

(** ** The closed elements, with the inherited order *)

(* K: the elements with cl x ≤ x, i.e. Seven Sketches' fix_j. *)
Definition ClosedElt@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : Type@{u} :=
  { x : A | R (cl_fun c x) x }.

Definition closed_le@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : relation (ClosedElt c) :=
  fun a b => R (proj1_sig a) (proj1_sig b).

Definition closed_PreOrder@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) : PreOrder (closed_le c) :=
  {| PreOrder_Reflexive  := fun a => @PreOrder_Reflexive A R P (proj1_sig a)
   ; PreOrder_Transitive := fun a b d (H1 : closed_le c a b)
                                (H2 : closed_le c b d) =>
       @PreOrder_Transitive A R P _ _ _ H1 H2 |}.

(** ** Awodey's t and i *)

(* t : P → K, the factorisation of cl through K. *)
Definition closed_t@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) : ClosedElt c :=
  exist _ (cl_fun c x) (cl_mult c x).

(* i : K → P, the inclusion. *)
Definition closed_i@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (k : ClosedElt c) : A :=
  proj1_sig k.

(* Awodey's two implications, as the unit and counit inequalities. *)
Definition closed_galois@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisConnection R (closed_le c) :=
  galois_of_unit_counit P (closed_PreOrder c) (closed_t c) (closed_i c)
    (fun a a' h => mono_pres (cl_fun c) a a' h)
    (fun b b' h => h)
    (fun a => cl_ext c a)
    (fun b => proj2_sig b).

(* t ⊣ i. *)
Definition closed_adj@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :=
  GaloisAdjunction@{u u s a h} P (closed_PreOrder c) (closed_galois c).

(** ** T = i ∘ t, and the induced monad is T *)

(* T = i ∘ t on objects, on the nose. *)
Example closed_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x : A) :
  fobj[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] x
    = cl_fun c x := eq_refl.

(* ...and on arrows, so that i ◯ t = [closure_functor c] is refused in
   the law fields alone. *)
Example closed_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x y : A) (f : R x y) :
  fmap[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] f
    = fmap[closure_functor@{u h} c] f := eq_refl.

(* The induced monad, read back as a closure operator, has c's monotone
   map on the nose. *)
Example closed_induced_is_c@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :
  cl_fun (closure_of_monad _
            (MM := Adjunction_Induced_Monad (closed_adj@{u h s a} c)))
    = cl_fun c := eq_refl.

(* i ◯ t is the closure functor, with identity components. *)
Lemma closed_induced_functor@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
    ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)
    ≈ closure_functor@{u h} c.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(** ** "tik = k": up to ≅, and on first projections under antisymmetry *)

(* t (i k) has first component cl k... *)
Example closed_tik_fst@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = cl_fun c (proj1_sig k)
  := eq_refl.

(* ...and is isomorphic to k in K... *)
Definition closed_tik_iso@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  closed_t c (closed_i c k) ≅[Proset@{u h} (closed_PreOrder c)] k :=
  @Build_Isomorphism (Proset@{u h} (closed_PreOrder c))
    (closed_t c (closed_i c k)) k (proj2_sig k) (cl_ext c (proj1_sig k)) I I.

(* ...and equal to k on first components under antisymmetry. *)
Lemma closed_tik_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = proj1_sig k.
Proof. exact (AS _ _ (proj2_sig k) (cl_ext c (proj1_sig k))). Qed.
