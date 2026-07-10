Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Indexed categories: the coherent pseudofunctor-lite *)

(* nLab:      https://ncatlab.org/nlab/show/indexed+category
   nLab:      https://ncatlab.org/nlab/show/pseudofunctor
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

   An indexed category over a base category [B] assigns to every object
   [x : B] a fibre category [idx_fib x] and to every morphism [f : x ~> y] a
   reindexing functor [idx_map f : idx_fib x ⟶ idx_fib y] — covariantly here,
   matching the opfibration that the Grothendieck construction
   (Construction/Grothendieck.v) produces; the classical contravariant
   presentation of an indexed category as a pseudofunctor out of [B^op] is
   recovered by instantiating the base at [B^op].  Functoriality holds only up
   to *chosen, coherent* natural isomorphisms:

   - [idx_resp] mediates reindexing along equivalent base morphisms (B's homs
     are setoids, so [idx_map] can respect [≈] only up to isomorphism),
   - [idx_id] compares [idx_map id] with the identity functor,
   - [idx_comp] compares [idx_map f ∘ idx_map g] with [idx_map (f ∘ g)],

   subject to naturality in the fibre argument and to the pseudofunctor
   coherence laws: proof irrelevance and transitivity for [idx_resp]
   ([idx_resp_id], [idx_resp_trans]), the unit laws [idx_unit_left] and
   [idx_unit_right], the associativity cocycle [idx_cocycle], and
   compatibility of [idx_comp] with [idx_resp] in each base-morphism
   argument ([idx_comp_resp_l], [idx_comp_resp_r]).  This is
   "pseudofunctor-lite": exactly the coherent data that the Grothendieck
   construction consumes, with no 2-categorical superstructure.

   HONESTY NOTE (binding design decision).  In this library a bare
   [Functor B Cat] does NOT suffice for the Grothendieck construction: Cat's
   hom-equivalence is [Functor_Setoid], so [fmap_comp], [fmap_id] and
   [fmap_respects] are *chosen natural isos carrying no coherence between
   different applications* — an adversarial instance can twist [fmap_comp] by
   a nontrivial central automorphism in a fibre, and the total category's
   associativity becomes unprovable.  [StrictCat]-valued functors shift the
   problem to coherence of propositional object-equality proofs (no UIP in
   general).  The honest "pseudofunctor-lite" is therefore an explicit
   coherent-data record, [IndexedCat], with the cocycle and unit coherence as
   fields; constructors are provided elsewhere in this development (a) from
   split cleavages, where the coherence is trivial
   (Construction/Grothendieck/RoundTrip.v), and (b) from [F : B ⟶ StrictCat]
   under fibrewise UIP, dischargeable via Hedberg from decidable object
   equality, e.g. for FinSet-like fibres (Construction/Grothendieck/Strict.v).
   Displayed categories (Theory/Displayed.v) remain the primitive Coq-friendly
   presentation.

   Shape of the twist counterexample.  Fix any [F : B ⟶ Cat] having a fibre
   with a nontrivial central automorphism [θ] (e.g. a one-object fibre given
   by a group with nontrivial centre), and fix one composable pair [(f, g)]
   in [B].  Because [Cat] compares functors by [Functor_Setoid], the functor
   law [fmap_comp f g : fmap (f ∘ g) ≈ fmap f ∘ fmap g] is *data*: a natural
   isomorphism chosen independently at each pair of morphisms.  Replace the
   chosen iso at exactly the pair [(f, g)] by its composite with [θ].
   Centrality keeps every component natural, and every [Functor] law still
   holds, because each law constrains one application at a time and never
   relates [fmap_comp f g] to [fmap_comp (f ∘ g) h] or to [fmap_comp g h].
   Yet associativity of composition in the would-be total category is
   precisely such a cross-application equation — the cocycle [idx_cocycle]
   below — and the twist breaks it, since it introduces a stray factor of
   [θ ≠ id] on one side only.  Hence the coherence must be carried as data,
   in the fields below, rather than recovered from bare functoriality. *)

Record IndexedCat (B : Category) : Type := {
  idx_fib : B → Category;

  idx_map {x y : B} (f : x ~> y) : idx_fib x ⟶ idx_fib y;

  (* Reindexing respects ≈ on base morphisms, up to a chosen fibre iso,
     natural in the fibre argument and proof-irrelevant ([idx_resp_id],
     [idx_resp_trans] make any two such isos agree). *)
  idx_resp {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib x) :
    idx_map f a ≅[idx_fib y] idx_map g a;
  idx_resp_natural {x y : B} {f g : x ~> y} (e : f ≈ g)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map g] k ∘ to (idx_resp e a)
      ≈ to (idx_resp e b) ∘ fmap[idx_map f] k;
  idx_resp_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib x) :
    to (idx_resp e a) ≈ id;
  idx_resp_trans {x y : B} {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h)
                 (a : idx_fib x) :
    to (idx_resp e2 a) ∘ to (idx_resp e1 a)
      ≈ to (idx_resp (Equivalence_Transitive _ _ _ e1 e2) a);

  (* Unit: reindexing along the identity is isomorphic to doing nothing,
     naturally in the fibre argument. *)
  idx_id {x : B} (a : idx_fib x) : idx_map (@id B x) a ≅ a;
  idx_id_natural {x : B} {a b : idx_fib x} (k : a ~> b) :
    k ∘ to (idx_id a) ≈ to (idx_id b) ∘ fmap[idx_map (@id B x)] k;

  (* Composition: reindexing twice is isomorphic to reindexing along the
     composite, naturally in the fibre argument. *)
  idx_comp {x y z : B} (f : y ~> z) (g : x ~> y) (a : idx_fib x) :
    idx_map f (idx_map g a) ≅ idx_map (f ∘ g) a;
  idx_comp_natural {x y z : B} (f : y ~> z) (g : x ~> y)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map (f ∘ g)] k ∘ to (idx_comp f g a)
      ≈ to (idx_comp f g b) ∘ fmap[idx_map f] (fmap[idx_map g] k);

  (* Compatibility of the composition isos with the ≈-mediators: [idx_comp]
     is natural in each base-morphism argument, with [idx_resp] supplying
     the connecting components.  Bicategorically, a pseudofunctor's
     compositor is natural in both 1-cell arguments; here the 2-cells are
     proofs of ≈, so naturality says that reindexing along equivalent
     composites commutes with the chosen composition isos.  These fields
     are not derivable from the others: on the one-object base with
     hom-monoid (ℤ, +) under congruence mod 2, with a one-object fibre
     whose hom-group is (ℤ, +) and every [idx_map] the identity functor,
     take every [idx_resp] and [idx_id] iso to be the identity and
     [idx_comp f g] to be the bilinear twist f·g.  Bilinearity is exactly
     the cocycle, and f·g vanishes when either argument is 0, so every
     other field holds; yet [idx_comp (f+2) g] and [idx_comp f g] differ
     by 2·g ≠ 0, violating the left compatibility below.  The Grothendieck
     construction (Construction/Grothendieck.v) consumes exactly these
     fields to interchange [dtransport] with [dcomp] ([dtransport_comp_l]
     and [dtransport_comp_r] of Theory/Displayed.v).  The composite-side
     proof [e'] is universally quantified rather than pinned to the
     canonical [compose_respects] witness; by proof irrelevance of
     [idx_resp] the two phrasings are interderivable. *)
  idx_comp_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
                  (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib x) :
    to (idx_comp f' g a) ∘ to (idx_resp e (idx_map g a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);
  idx_comp_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
                  (e' : f ∘ g ≈ f ∘ g') (a : idx_fib x) :
    to (idx_comp f g' a) ∘ fmap[idx_map f] (to (idx_resp e a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);

  (* Pseudofunctor coherence: the unit isos and the composition isos agree
     with each other across applications.  These are the cross-application
     equations that a bare [Functor B Cat] cannot supply (see the honesty
     note above); Construction/Grothendieck.v discharges the [Displayed]
     laws of the total category from exactly these fields. *)
  idx_unit_left {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_left f) a) ∘ to (idx_comp id f a)
      ≈ to (idx_id (idx_map f a));
  idx_unit_right {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_right f) a) ∘ to (idx_comp f id a)
      ≈ fmap[idx_map f] (to (idx_id a));
  idx_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
              (a : idx_fib w) :
    to (idx_comp (f ∘ g) h a) ∘ to (idx_comp f g (idx_map h a))
      ≈ to (idx_resp (comp_assoc f g h) a)
          ∘ to (idx_comp f (g ∘ h) a) ∘ fmap[idx_map f] (to (idx_comp g h a))
}.

Arguments idx_fib {B} _ _.
Arguments idx_map {B} _ {x y} _.
Arguments idx_resp {B} _ {x y f g} _ _.
Arguments idx_resp_natural {B} _ {x y f g} _ {a b} _.
Arguments idx_resp_id {B} _ {x y f} _ _.
Arguments idx_resp_trans {B} _ {x y f g h} _ _ _.
Arguments idx_id {B} _ {x} _.
Arguments idx_id_natural {B} _ {x a b} _.
Arguments idx_comp {B} _ {x y z} _ _ _.
Arguments idx_comp_natural {B} _ {x y z} _ _ {a b} _.
Arguments idx_comp_resp_l {B} _ {x y z f f'} _ _ _ _.
Arguments idx_comp_resp_r {B} _ {x y z} _ {g g'} _ _ _.
Arguments idx_unit_left {B} _ {x y} _ _.
Arguments idx_unit_right {B} _ {x y} _ _.
Arguments idx_cocycle {B} _ {w x y z} _ _ _ _.

(* Derived corollaries of the [idx_resp] coherence fields.  These are the
   forms the Grothendieck construction actually consumes: its [dtransport]
   post-composes with [from (idx_resp _ _)], so the [from]-side restatements
   of identity, transitivity, proof irrelevance and naturality are collected
   here once, rather than re-derived at every use site. *)
Section IndexedCatLemmas.

Context {B : Category}.
Context (A : IndexedCat B).

(* [idx_resp] at a reflexivity-flavoured proof has identity inverse as well:
   the [from]-side companion to [idx_resp_id]. *)
Lemma idx_resp_from_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib A x) :
  from (idx_resp A e a) ≈ id.
Proof.
  rewrite <- (iso_from_to (idx_resp A e a)).
  rewrite (idx_resp_id A e a).
  now rewrite id_right.
Qed.

(* The chosen iso at a symmetric proof is the inverse of the chosen iso:
   [to] at [symmetry e] agrees with [from] at [e]. *)
Lemma idx_resp_to_sym {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib A x) :
  to (idx_resp A (symmetry e) a) ≈ from (idx_resp A e a).
Proof.
  apply (comp_inverse_unique (to (idx_resp A e a))).
  - rewrite (idx_resp_trans A (symmetry e) e a).
    apply idx_resp_id.
  - apply iso_from_to.
Qed.

(* Proof irrelevance: the chosen isos at any two proofs of [f ≈ g] agree.
   This is the [idx_resp_id]/[idx_resp_trans] pair in the form downstream
   proofs use directly. *)
Lemma idx_resp_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  to (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  apply (comp_inverse_unique (from (idx_resp A e' a))).
  - rewrite <- (idx_resp_to_sym e' a).
    rewrite (idx_resp_trans A e (symmetry e') a).
    apply idx_resp_id.
  - apply iso_to_from.
Qed.

(* [from] at [symmetry e] agrees with [to] at [e]. *)
Lemma idx_resp_from_sym {x y : B} {f g : x ~> y} (e : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A (symmetry e) a) ≈ to (idx_resp A e a).
Proof.
  rewrite <- (idx_resp_to_sym (symmetry e) a).
  apply idx_resp_irrel.
Qed.

(* Proof irrelevance on the [from] side. *)
Lemma idx_resp_from_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A e a) ≈ from (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym e a), <- (idx_resp_to_sym e' a).
  apply idx_resp_irrel.
Qed.

(* Transitivity on the [from] side: inverses compose in reverse order. *)
Lemma idx_resp_from_trans {x y : B} {f g h : x ~> y}
      (e1 : f ≈ g) (e2 : g ≈ h) (a : idx_fib A x) :
  from (idx_resp A e1 a) ∘ from (idx_resp A e2 a)
    ≈ from (idx_resp A (Equivalence_Transitive _ _ _ e1 e2) a).
Proof.
  rewrite <- (idx_resp_to_sym e1 a), <- (idx_resp_to_sym e2 a),
          <- (idx_resp_to_sym (Equivalence_Transitive _ _ _ e1 e2) a).
  rewrite (idx_resp_trans A (symmetry e2) (symmetry e1) a).
  apply idx_resp_irrel.
Qed.

(* Naturality of [idx_resp] on the [from] side, by conjugating
   [idx_resp_natural] with the inverses. *)
Lemma idx_resp_natural_from {x y : B} {f g : x ~> y} (e : f ≈ g)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] k ∘ from (idx_resp A e a)
    ≈ from (idx_resp A e b) ∘ fmap[idx_map A g] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] k)).
  rewrite <- (iso_from_to (idx_resp A e b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_resp_natural A e k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_resp A e a)).
  apply id_right.
Qed.

(* Naturality of [idx_id] on the [from] side. *)
Lemma idx_id_natural_from {x : B} {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A (@id B x)] k ∘ from (idx_id A a) ≈ from (idx_id A b) ∘ k.
Proof.
  rewrite <- (id_left (fmap[idx_map A (@id B x)] k)).
  rewrite <- (iso_from_to (idx_id A b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_id_natural A k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_id A a)).
  apply id_right.
Qed.

(* Naturality of [idx_comp] on the [from] side. *)
Lemma idx_comp_natural_from {x y z : B} (f : y ~> z) (g : x ~> y)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] (fmap[idx_map A g] k) ∘ from (idx_comp A f g a)
    ≈ from (idx_comp A f g b) ∘ fmap[idx_map A (f ∘ g)] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] (fmap[idx_map A g] k))).
  rewrite <- (iso_from_to (idx_comp A f g b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_comp_natural A f g k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_comp A f g a)).
  apply id_right.
Qed.

End IndexedCatLemmas.
