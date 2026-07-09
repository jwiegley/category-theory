Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The store (costate) comonad *)

(* nLab:      https://ncatlab.org/nlab/show/store+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   The store comonad — also called the costate comonad — over a fixed object
   s of "positions" sends x to (s ⇒ x) × s: a store is an observation
   function h from positions to values together with a currently focused
   position s0, with

       extract   (h, s0) = h s0                 (observe at the current focus)
       duplicate (h, s0) = ((λ σ, (h, σ)), s0)  (a store of stores: at every
                                                 position σ, the same
                                                 observation refocused at σ)

   Abstractly it is the comonad F ◯ U of the currying adjunction
   (− × s) ⊣ (s ⇒ −) on a cartesian closed category, dually to the state
   monad U ◯ F = s ⇒ (− × s).  Its coalgebras are the "very well-behaved
   lenses" of functional programming.

   Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
   [Store_Comonad] below is literally a [Monad] on the opposite category; the
   covariant accessors of Comonad/Core.v then read [extract], [duplicate] and
   [extend] off it definitionally (the *_spec lemmas at the end hold by
   [reflexivity]). *)

(** ** The store data over raw types, and why the witness is hosted on Sets

    Instance/Coq/Comonad/Env.v hosts the environment comonad on COQ, whose
    morphism equivalence is pointwise Leibniz equality.  For the store
    functor every comonad *equation* of the corresponding raw data likewise
    holds pointwise and definitionally: the [coq_store_*] lemmas below check
    all of them by destructuring alone, with no axiom involved.

    What resists is not any equation but the *setoid respectfulness* of the
    functor action, the [fmap_respects] field a [Functor] on COQ must carry.
    Because a store places the observation function h : s → x inside the
    object, respectfulness at pointwise-= homs asks for Leibniz equality of
    function components given only pointwise-equal inputs, and
    [coq_store_map_proper_entails_funext] shows that the very first instance
    of that obligation already implies functional extensionality for
    functions out of an inhabited s.  The obligation is therefore not merely
    inconvenient: it is out of reach for axiom-free Coq.

    This is precisely the corner named by the plan's Phase 6 risk note
    (doc/classical-completion-plan.md), together with the sanctioned move:
    "if a corner genuinely resists, move that single instance to Sets
    (setoid homs make the law proper-trivial) and record the move in the
    phase PR — the deliverable is the comonad witness, not its host
    category."  The bundled witness
    [Store_Comonad] accordingly lives on [Sets], where the store object
    carries a componentwise setoid and respectfulness is a one-line
    pointwise argument.  The file keeps its planned location. *)

(** The plan-prescribed action on raw types: apply f to every observation,
    keep the focus. *)
Definition coq_store_map {s x y : Type} (f : x → y) (p : (s → x) * s) :
  (s → y) * s :=
  match p with (h, s0) => ((λ σ, f (h σ)), s0) end.

(** The counit on raw types: observe at the current focus. *)
Definition coq_store_extract {s x : Type} (p : (s → x) * s) : x :=
  match p with (h, s0) => h s0 end.

(** The comultiplication on raw types: refocus at every position. *)
Definition coq_store_duplicate {s x : Type} (p : (s → x) * s) :
  (s → (s → x) * s) * s :=
  match p with (h, s0) => ((λ σ, (h, σ)), s0) end.

(** Both functor equations hold pointwise; eta for functions is part of
    Coq's definitional equality, so destructuring the pair suffices. *)

Lemma coq_store_map_id {s x : Type} (p : (s → x) * s) :
  coq_store_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma coq_store_map_comp {s x y z : Type} (f : y → z) (g : x → y)
  (p : (s → x) * s) :
  coq_store_map (λ v, f (g v)) p = coq_store_map f (coq_store_map g p).
Proof. now destruct p. Qed.

(** So do all five comonad equations, stated in the op-read orientation of
    Theory/Monad.v's monad laws (cf. Instance/Coq/Comonad/Env.v). *)

Lemma coq_store_extract_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  f (coq_store_extract p) = coq_store_extract (coq_store_map f p).
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_coassoc {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_duplicate (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_duplicate p).
Proof. now destruct p. Qed.

Lemma coq_store_fmap_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  coq_store_map (coq_store_map f) (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_map f p).
Proof. now destruct p. Qed.

(** The obstruction, machine-checked: the respectfulness a COQ-hosted store
    functor would owe — at the single instance x := s, with the identity
    observation as the store — is already the statement of functional
    extensionality for functions out of s, whenever s is inhabited (the
    final conversion step is definitional eta).  Restricted functional
    extensionality is independent of Coq's type theory, so no axiom-free
    [Functor] on COQ can carry this action, and the bundled witness below
    is hosted on [Sets] instead. *)

Lemma coq_store_map_proper_entails_funext {s y : Type} (s0 : s)
  (respects : ∀ f g : s → y,
      (∀ v, f v = g v) →
      ∀ p : (s → s) * s, coq_store_map f p = coq_store_map g p) :
  ∀ f g : s → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (f_equal fst (respects f g Hfg ((λ σ, σ), s0))).
Qed.

(** ** The store setoid on [Sets] *)

(* A store over the setoid s is an ≈-respecting observation map paired with
   a position; two stores are equivalent when the observations agree
   pointwise (up to the codomain's ≈) and the positions agree (up to s's ≈).
   This componentwise relation is exactly what makes every obligation below
   pointwise, in contrast to the Leibniz pairing over raw types above. *)

Definition store_equiv {s x : SetoidObject} :
  crelation (SetoidMorphism s x * carrier s) :=
  λ p q, ((∀ σ : carrier s, fst p σ ≈ fst q σ) * (snd p ≈ snd q))%type.

Arguments store_equiv {s x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition store_obj (s x : SetoidObject) : SetoidObject := {|
  carrier := SetoidMorphism s x * carrier s;
  is_setoid := {| equiv := store_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros s x; constructor.
  - intros p; split.
    + intros σ; reflexivity.
    + reflexivity.
  - intros p q [Hh Hs]; split.
    + intros σ; symmetry; apply Hh.
    + now symmetry.
  - intros p q r [Hh Hs] [Hg Ht]; split.
    + intros σ; etransitivity.
      * apply Hh.
      * apply Hg.
    + etransitivity.
      * exact Hs.
      * exact Ht.
Qed.

(** ** The functorial action *)

(* Post-composition under the observation map: f is applied to every
   observation, the focus is kept. *)
Program Definition store_map {s x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (store_obj s x) (store_obj s y) := {|
  morphism := λ p, (setoid_morphism_compose f (fst p), snd p)
|}.
Next Obligation.
  intros s x y f p q [Hh Hs]; split.
  - intros σ; simpl.
    apply proper_morphism, Hh.
  - exact Hs.
Qed.

(** [store_map] respects ≈ pointwise — the field whose COQ counterpart is
    the funext-entailing obligation above; here it is immediate. *)
Lemma store_map_respects {s x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ p : SetoidMorphism s x * carrier s,
    store_equiv (store_map f p) (store_map g p).
Proof.
  intros Hfg p; split.
  - intros σ; simpl.
    apply Hfg.
  - reflexivity.
Qed.

Lemma store_map_id {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map setoid_morphism_id p) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

Lemma store_map_comp {s x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (setoid_morphism_compose f g) p)
              (store_map f (store_map g p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** The store endofunctor (s ⇒ −) × s on [Sets]. *)
Definition StoreF (s : SetoidObject) : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, store_obj s x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @store_map s x y f)
  (λ x y : SetoidObject, @store_map_respects s x y)
  (λ x : SetoidObject, @store_map_id s x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @store_map_comp s x y z f g).

(** ** The comonad structure *)

(** The counit ε: observe at the current focus. *)
Program Definition store_extract {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) x := {|
  morphism := λ p, fst p (snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; simpl.
  etransitivity.
  - apply Hh.
  - now apply proper_morphism.
Qed.

(* Refocusing: pair the observation map with every position — the
   observation component of [duplicate]. *)
Program Definition store_seek {s x : SetoidObject} (h : SetoidMorphism s x) :
  SetoidMorphism s (store_obj s x) := {|
  morphism := λ σ, (h, σ)
|}.
Next Obligation.
  intros s x h σ τ Hστ; split.
  - intros ρ; reflexivity.
  - exact Hστ.
Qed.

(** The comultiplication δ: a store of stores, refocused at every position. *)
Program Definition store_duplicate {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) (store_obj s (store_obj s x)) := {|
  morphism := λ p, (store_seek (fst p), snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; split.
  - intros σ; split.
    + intros τ; apply Hh.
    + reflexivity.
  - exact Hs.
Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. *)
Lemma store_extract_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  f (store_extract p) ≈ store_extract (store_map f p).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma store_duplicate_coassoc {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_duplicate (store_duplicate p))
              (store_duplicate (store_duplicate p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma store_fmap_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma store_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. *)
Lemma store_duplicate_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (store_map f) (store_duplicate p))
              (store_duplicate (store_map f p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** The comonad witness: per Theory/Monad.v, a comonad on [Sets] IS a monad
    on [Sets^op], so the record is assembled with [Build_Monad] at (Sets^op,
    (StoreF s)^op) — [ret] is the counit and [join] the comultiplication,
    and each monad law is the corresponding lemma above, read through the
    opposite category's reversed composition. *)
#[export] Instance Store_Comonad (s : SetoidObject) :
  @Comonad Sets (StoreF s) :=
  @Build_Monad (Sets^op) ((StoreF s)^op)
    (λ x : SetoidObject, @store_extract s x)          (* ret  = ε *)
    (λ x : SetoidObject, @store_duplicate s x)        (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_extract_natural s y x f)
    (λ x : SetoidObject, @store_duplicate_coassoc s x)
    (λ x : SetoidObject, @store_fmap_extract_duplicate s x)
    (λ x : SetoidObject, @store_extract_duplicate s x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_duplicate_natural s y x f).

(** The covariant accessors of Comonad/Core.v compute on this witness
    exactly as the plan's skeleton promises: [extract] observes at the
    focus, [duplicate] refocuses at every position, and [extend f] runs the
    co-Kleisli arrow f on every refocused store while keeping the focus. *)

Lemma Store_extract_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  extract[StoreF s] (h, s0) = h s0.
Proof. reflexivity. Qed.

Lemma Store_duplicate_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  duplicate[StoreF s] (h, s0) = (store_seek h, s0).
Proof. reflexivity. Qed.

Lemma Store_seek_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 σ : carrier s) :
  fst (duplicate[StoreF s] (h, s0)) σ = (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 σ : carrier s) :
  fst (extend[StoreF s] f (h, s0)) σ = f (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_pos_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 : carrier s) :
  snd (extend[StoreF s] f (h, s0)) = s0.
Proof. reflexivity. Qed.
