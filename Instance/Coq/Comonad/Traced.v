Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The traced (cowriter, exponent) comonad *)

(* Haskell:   Control.Comonad.Traced (the comonad package)
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   The traced comonad over a monoid (m, mempty, mappend) — Haskell's Traced,
   also called the cowriter or exponent comonad — is the endofunctor m ⇒ −,
   sending x to the functions m → x, with

       extract   h = h mempty                  (evaluate at the neutral trace)
       duplicate h = λ w w', h (mappend w w')  (evaluate under every further
                                                translation of the context)

   It is dual to the writer monad m × −: the same monoid structure that lets
   a writer computation merge the output it emits lets a traced computation
   split the context it consumes.  Both arise by pushing the monoid m through
   a monoidal functor into the endofunctor category: m × − covariantly
   (giving a monad), m ⇒ − contravariantly (giving a comonad, since
   (m ⇒ −) ○ (m ⇒ −) ≅ (m × m) ⇒ − lets mappend and mempty land as the
   comultiplication δ and the counit ε).  Co-Kleisli arrows (m → x) → y
   consume a value together with all of its monoid translates — the comonad
   of cellular automata (m a grid of offsets) and of monoid-weighted contexts
   generally, with co-Kleisli composition accumulating the offsets.

   Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
   [Traced_Comonad] below is literally a [Monad] on the opposite category;
   the covariant accessors of Comonad/Core.v then read [extract], [duplicate]
   and [extend] off it definitionally (the *_spec lemmas at the end hold by
   [reflexivity]). *)

Section Traced.

(** The section-context monoid: ordinary Coq data — a bare type together
    with a unit, a multiplication, and the three monoid equations as Leibniz
    laws. *)

Context (m : Type).
Context (mempty : m).
Context (mappend : m → m → m).

Hypothesis mempty_left  : ∀ w : m, mappend mempty w = w.
Hypothesis mempty_right : ∀ w : m, mappend w mempty = w.
Hypothesis mappend_assoc :
  ∀ u v w : m, mappend u (mappend v w) = mappend (mappend u v) w.

(** ** The traced data over raw types, and why the witness is hosted on Sets

    Instance/Coq/Comonad/Env.v hosts the environment comonad on COQ, whose
    morphism equivalence is pointwise Leibniz equality.  For the traced
    functor, four of the seven functor/comonad equations of the corresponding
    raw data below are closed by Coq's definitional beta and eta alone, at
    the full function level (the Leibniz-valued lemmas below, all by
    [reflexivity]).  The remaining three equations are exactly the ones that
    consult the monoid laws, and their Leibniz forms compare functions that
    differ beneath a binder — (λ w', h (mappend mempty w')) against h, and so
    on.  Each of these holds pointwise, which is the restatement the plan
    prescribes for this file (doc/classical-completion-plan.md, Phase 6), and
    is proved below by rewriting the monoid law at the sampled point; the
    Leibniz form itself is out of reach for axiom-free Coq.  So, moreover, is
    the [fmap_respects] field a [Functor] on COQ must carry:
    [coq_traced_map_proper_entails_funext] shows that the very first instance
    of that obligation already implies functional extensionality for
    functions out of m — no inhabitation hypothesis needed, the identity
    trace exhibits it.

    This is precisely the corner named by the plan's Phase 6 risk note,
    together with the sanctioned move, already exercised by the store comonad
    in Instance/Coq/Comonad/Store.v: "if a corner genuinely resists, move
    that single instance to Sets (setoid homs make the law proper-trivial) —
    the deliverable is the comonad witness, not its host category."  The
    bundled witness [Traced_Comonad] accordingly lives on [Sets], where the
    traced object m → x is compared pointwise up to the codomain's ≈ and
    every equation above literally becomes its pointwise restatement.  The
    monoid itself remains the ordinary Coq data of this section, and the
    file keeps its planned location. *)

(** The plan-prescribed action on raw types: post-compose the observation. *)
Definition coq_traced_map {x y : Type} (f : x → y) (h : m → x) : m → y :=
  λ w, f (h w).

(** The counit on raw types: evaluate at the neutral trace. *)
Definition coq_traced_extract {x : Type} (h : m → x) : x := h mempty.

(** The comultiplication on raw types: evaluate under every translation. *)
Definition coq_traced_duplicate {x : Type} (h : m → x) : m → m → x :=
  λ w w', h (mappend w w').

(** Four of the equations are definitional at the function level: beta and
    eta for functions are part of Coq's conversion. *)

Lemma coq_traced_map_id {x : Type} (h : m → x) :
  coq_traced_map (λ v : x, v) h = h.
Proof. reflexivity. Qed.

Lemma coq_traced_map_comp {x y z : Type} (f : y → z) (g : x → y)
  (h : m → x) :
  coq_traced_map (λ v, f (g v)) h = coq_traced_map f (coq_traced_map g h).
Proof. reflexivity. Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. *)
Lemma coq_traced_extract_natural {x y : Type} (f : x → y) (h : m → x) :
  f (coq_traced_extract h) = coq_traced_extract (coq_traced_map f h).
Proof. reflexivity. Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. *)
Lemma coq_traced_duplicate_natural {x y : Type} (f : x → y) (h : m → x) :
  coq_traced_map (coq_traced_map f) (coq_traced_duplicate h)
    = coq_traced_duplicate (coq_traced_map f h).
Proof. reflexivity. Qed.

(** The remaining three equations consult the monoid laws and hold pointwise
    — each is the plan's restatement of the corresponding law at a sampled
    trace. *)

(** Counit law ε ∘ δ ≈ id, pointwise — the op-read of [join_ret]. *)
Lemma coq_traced_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_left.
  unfold coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_left.
Qed.

(** Counit law W ε ∘ δ ≈ id, pointwise — the op-read of [join_fmap_ret]. *)
Lemma coq_traced_fmap_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_map coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_right.
  unfold coq_traced_map, coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_right.
Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ, pointwise — the op-read of
    [join_fmap_join]. *)
Lemma coq_traced_duplicate_coassoc {x : Type} (h : m → x) (a b c : m) :
  coq_traced_map coq_traced_duplicate (coq_traced_duplicate h) a b c
    = coq_traced_duplicate (coq_traced_duplicate h) a b c.
Proof using mappend_assoc.
  unfold coq_traced_map, coq_traced_duplicate.
  now rewrite mappend_assoc.
Qed.

(** The obstruction, machine-checked: the respectfulness a COQ-hosted traced
    functor would owe — at the single instance x := m, with the identity
    trace as the argument — is already the statement of functional
    extensionality for functions out of the monoid (the final conversion
    step is definitional eta).  Restricted functional extensionality is
    independent of Coq's type theory, so no axiom-free [Functor] on COQ can
    carry this action, and the bundled witness below is hosted on [Sets]
    instead. *)

Lemma coq_traced_map_proper_entails_funext {y : Type}
  (respects : ∀ f g : m → y,
      (∀ v, f v = g v) →
      ∀ h : m → m, coq_traced_map f h = coq_traced_map g h) :
  ∀ f g : m → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (respects f g Hfg (λ w, w)).
Qed.

(** ** The traced setoid on [Sets] *)

(* A traced value over the raw monoid m is a bare function m → x into the
   setoid x; two of them are equivalent when they agree at every trace, up to
   the codomain's ≈.  This componentwise relation is exactly what makes every
   obligation below pointwise, in contrast to the Leibniz function
   equalities demanded over raw types above.  The monoid needs no setoid of
   its own: it enters only through the (Leibniz) rewriting of its laws at
   sampled points. *)

Definition traced_equiv {x : SetoidObject} : crelation (m → carrier x) :=
  λ h k, ∀ w : m, h w ≈ k w.

Arguments traced_equiv {x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition traced_obj (x : SetoidObject) : SetoidObject := {|
  carrier := m → carrier x;
  is_setoid := {| equiv := traced_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros x; constructor.
  - intros h w.
    reflexivity.
  - intros h k Hhk w.
    symmetry; apply Hhk.
  - intros h k l Hhk Hkl w.
    etransitivity.
    + apply Hhk.
    + apply Hkl.
Qed.

(** ** The functorial action *)

(* Post-composition under the trace: f is applied to the value observed at
   every trace. *)
Program Definition traced_map {x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (traced_obj x) (traced_obj y) := {|
  morphism := λ h w, f (h w)
|}.
Next Obligation.
  intros x y f h k Hhk w; simpl.
  apply proper_morphism, Hhk.
Qed.

(** [traced_map] respects ≈ pointwise — the field whose COQ counterpart is
    the funext-entailing obligation above; here it is immediate. *)
Lemma traced_map_respects {x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ h : m → carrier x, traced_equiv (traced_map f h) (traced_map g h).
Proof.
  intros Hfg h w; simpl.
  apply Hfg.
Qed.

Lemma traced_map_id {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map setoid_morphism_id h) h.
Proof.
  intros w; simpl.
  reflexivity.
Qed.

Lemma traced_map_comp {x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y) (h : m → carrier x) :
  traced_equiv (traced_map (setoid_morphism_compose f g) h)
               (traced_map f (traced_map g h)).
Proof.
  intros w; simpl.
  reflexivity.
Qed.

(** The traced endofunctor m ⇒ − on [Sets]. *)
Definition TracedF : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, traced_obj x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @traced_map x y f)
  (λ x y : SetoidObject, @traced_map_respects x y)
  (λ x : SetoidObject, @traced_map_id x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @traced_map_comp x y z f g).

(** ** The comonad structure *)

(** The counit ε: evaluate at the neutral trace. *)
Program Definition traced_extract {x : SetoidObject} :
  SetoidMorphism (traced_obj x) x := {|
  morphism := λ h, h mempty
|}.
Next Obligation.
  intros x h k Hhk; simpl.
  apply Hhk.
Qed.

(** The comultiplication δ: evaluate under every further translation. *)
Program Definition traced_duplicate {x : SetoidObject} :
  SetoidMorphism (traced_obj x) (traced_obj (traced_obj x)) := {|
  morphism := λ h w w', h (mappend w w')
|}.
Next Obligation.
  intros x h k Hhk w w'; simpl.
  apply Hhk.
Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. *)
Lemma traced_extract_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  f (traced_extract h) ≈ traced_extract (traced_map f h).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma traced_duplicate_coassoc {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_duplicate (traced_duplicate h))
               (traced_duplicate (traced_duplicate h)).
Proof using mappend_assoc.
  intros a b c; simpl.
  now rewrite mappend_assoc.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma traced_fmap_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_extract (traced_duplicate h)) h.
Proof using mempty_right.
  intros w; simpl.
  now rewrite mempty_right.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma traced_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_extract (traced_duplicate h)) h.
Proof using mempty_left.
  intros w; simpl.
  now rewrite mempty_left.
Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. *)
Lemma traced_duplicate_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  traced_equiv (traced_map (traced_map f) (traced_duplicate h))
               (traced_duplicate (traced_map f h)).
Proof.
  intros w w'; simpl.
  reflexivity.
Qed.

(** The comonad witness: per Theory/Monad.v, a comonad on [Sets] IS a monad
    on [Sets^op], so the record is assembled with [Build_Monad] at (Sets^op,
    TracedF^op) — [ret] is the counit and [join] the comultiplication, and
    each monad law is the corresponding lemma above, read through the
    opposite category's reversed composition. *)
Definition Traced_Comonad : @Comonad Sets TracedF :=
  @Build_Monad (Sets^op) (TracedF^op)
    (λ x : SetoidObject, @traced_extract x)           (* ret  = ε *)
    (λ x : SetoidObject, @traced_duplicate x)         (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_extract_natural y x f)
    (λ x : SetoidObject, @traced_duplicate_coassoc x)
    (λ x : SetoidObject, @traced_fmap_extract_duplicate x)
    (λ x : SetoidObject, @traced_extract_duplicate x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_duplicate_natural y x f).

#[local] Existing Instance Traced_Comonad.

(** The covariant accessors of Comonad/Core.v compute on this witness
    exactly as the plan's skeleton promises: [extract] evaluates at the
    neutral trace, [duplicate] evaluates under every further translation,
    and [extend f] runs the co-Kleisli arrow f on every translate of its
    argument. *)

Lemma Traced_extract_spec {x : SetoidObject} (h : m → carrier x) :
  extract[TracedF] h = h mempty.
Proof. reflexivity. Qed.

Lemma Traced_duplicate_spec {x : SetoidObject} (h : m → carrier x)
  (w w' : m) :
  duplicate[TracedF] h w w' = h (mappend w w').
Proof. reflexivity. Qed.

Lemma Traced_extend_spec {x y : SetoidObject}
  (f : SetoidMorphism (traced_obj x) y) (h : m → carrier x) (w : m) :
  extend[TracedF] f h w = f (λ w' : m, h (mappend w w')).
Proof. reflexivity. Qed.

End Traced.

(* No [#[export] Existing Instance] here: the monoid supply (mempty, mappend,
   and the three laws) is a section premise not determined by the instance
   head [@Comonad Sets (TracedF m)], so a global registration would force
   typeclass resolution to backtrack through undischargeable subgoals.
   Callers apply [Traced_Comonad] with explicit monoid arguments; the
   [#[local] Existing Instance] above already serves the in-section spec
   lemmas. *)
