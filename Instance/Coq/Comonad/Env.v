Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * The environment (coreader) comonad on COQ *)

(* nLab:      https://ncatlab.org/nlab/show/coreader+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)

   The environment comonad — also called the coreader, product, or (after
   Haskell's Control.Comonad.Env) Env comonad — is the endofunctor e × − on
   COQ, for a fixed type e of "environments", with

       extract   (e0, v) = v               (read the value, drop the context)
       duplicate (e0, v) = (e0, (e0, v))   (expose the context to the value)

   It is dual to the writer monad m × −: where writer requires a monoid
   structure on m to merge accumulated output, the environment comonad
   requires a comonoid structure on e to copy and discard the ambient
   context, and in the cartesian category COQ every type carries one
   canonically (the diagonal and the terminal map).  Morphisms W x ~> y of
   its co-Kleisli category (Comonad/CoKleisli.v) are exactly the functions
   e * x → y that consult an ambient environment.

   Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
   [Env_Comonad] below is literally a [Monad] on COQ^op; the covariant
   accessors of Comonad/Core.v then read [extract], [duplicate] and [extend]
   off it definitionally (the *_spec lemmas at the end hold by
   [reflexivity]).

   COQ's morphism equivalence is pointwise Leibniz equality, so every law
   here is proved by destructuring the pair argument and [reflexivity]: no
   functional extensionality — indeed no axiom of any kind — enters this
   file, and every definition below is closed under the global context. *)

(** The action of e × − on morphisms: apply f under the environment. *)
Definition env_map {e x y : Type} (f : x → y) (p : e * x) : e * y :=
  match p with (e0, v) => (e0, f v) end.

Lemma env_map_respects {e x y : Type} (f g : x → y) :
  (∀ v, f v = g v) → ∀ p : e * x, env_map f p = env_map g p.
Proof.
  intros Hfg [e0 v]; simpl.
  now rewrite Hfg.
Qed.

Lemma env_map_id {e x : Type} (p : e * x) : env_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma env_map_comp {e x y z : Type} (f : y → z) (g : x → y) (p : e * x) :
  env_map (λ v, f (g v)) p = env_map f (env_map g p).
Proof. now destruct p. Qed.

(** The environment endofunctor e × − on COQ. *)
Definition EnvF (e : Type) : Coq ⟶ Coq := @Build_Functor Coq Coq
  (λ x : Type, (e * x)%type)
  (λ (x y : Type) (f : x → y), @env_map e x y f)
  (λ x y : Type, @env_map_respects e x y)
  (λ x : Type, @env_map_id e x)
  (λ (x y z : Type) (f : y → z) (g : x → y), @env_map_comp e x y z f g).

(** The counit ε: project out the value. *)
Definition env_extract {e x : Type} (p : e * x) : x := snd p.

(** The comultiplication δ: copy the environment into the payload. *)
Definition env_duplicate {e x : Type} (p : e * x) : e * (e * x) :=
  match p with (e0, v) => (e0, (e0, v)) end.

(** Naturality of the counit — the op-read of [fmap_ret]. *)
Lemma env_extract_natural {e x y : Type} (f : x → y) (p : e * x) :
  f (env_extract p) = env_extract (env_map f p).
Proof. now destruct p. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma env_duplicate_coassoc {e x : Type} (p : e * x) :
  env_map env_duplicate (env_duplicate p) = env_duplicate (env_duplicate p).
Proof. now destruct p. Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma env_fmap_extract_duplicate {e x : Type} (p : e * x) :
  env_map env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma env_extract_duplicate {e x : Type} (p : e * x) :
  env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. *)
Lemma env_duplicate_natural {e x y : Type} (f : x → y) (p : e * x) :
  env_map (env_map f) (env_duplicate p) = env_duplicate (env_map f p).
Proof. now destruct p. Qed.

(** The comonad witness: per Theory/Monad.v, a comonad on COQ IS a monad on
    COQ^op, so the record is assembled with [Build_Monad] at (COQ^op,
    (EnvF e)^op) — [ret] is the counit and [join] the comultiplication, and
    each monad law is the corresponding lemma above, read through the
    opposite category's reversed composition. *)
#[export] Instance Env_Comonad (e : Type) : @Comonad Coq (EnvF e) :=
  @Build_Monad (Coq^op) ((EnvF e)^op)
    (λ x : Type, @env_extract e x)                (* ret  = ε *)
    (λ x : Type, @env_duplicate e x)              (* join = δ *)
    (λ (x y : Type) (f : y → x), @env_extract_natural e y x f)
    (λ x : Type, @env_duplicate_coassoc e x)
    (λ x : Type, @env_fmap_extract_duplicate e x)
    (λ x : Type, @env_extract_duplicate e x)
    (λ (x y : Type) (f : y → x), @env_duplicate_natural e y x f).

(** The covariant accessors of Comonad/Core.v compute on this witness
    exactly as promised: [extract] is [snd], [duplicate] copies the
    environment, and [extend f] runs f with the environment kept in scope. *)

Lemma Env_extract_spec {e x : Type} (p : e * x) :
  extract[EnvF e] p = snd p.
Proof. reflexivity. Qed.

Lemma Env_duplicate_spec {e x : Type} (e0 : e) (v : x) :
  duplicate[EnvF e] (e0, v) = (e0, (e0, v)).
Proof. reflexivity. Qed.

Lemma Env_extend_spec {e x y : Type} (f : e * x → y) (e0 : e) (v : x) :
  extend[EnvF e] f (e0, v) = (e0, f (e0, v)).
Proof. reflexivity. Qed.
