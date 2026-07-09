Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.

Generalizable All Variables.

(** * Adámek's initial-algebra theorem over the ω-chain *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   For an endofunctor [F] on a category [C] with an initial object [0],
   Adámek's theorem builds the initial [F]-algebra as the colimit of the
   ω-indexed chain

       0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

   ([Construction/Chain.v], packaged as [Chain F : Omega ⟶ C]).  Writing
   [A] for the apex of a colimit [L : Colimit (Chain F)], the structure map
   [α : F A ~> A] is the mediating morphism out of the shifted cocone, and
   [(A, α)] is initial in the category [FAlg F] of [F]-algebras.

   The colimit [A] is a colimit of the shifted diagram [F ◯ Chain F] with apex
   [F A] precisely when [F] preserves it.  An abstract [PreservesColimit]
   witness, however, only records that [F A] carries SOME colimit of
   [F ◯ Chain F]; two colimit cocones at the shared apex [F A] differ by a free
   apex-automorphism, so it does not expose that the cocone legs at [F A] are
   the image legs [fmap[F] (colimit_inj HL n)].  That leg agreement is genuine
   data the initiality argument consumes, so it is packaged here as the honest
   hypothesis [AdamekData] and [adamek] is proven directly from it.

   The discharge [PreservesColimit -> AdamekData] is therefore not carried in
   this file: it is routed to ledger 17 / Corollaries as a fast-follow, and the
   [AdamekData] interface is the load-bearing contract in the interim. *)

(* Shift of an order proof [m ≤ n] to [S m ≤ S n], by recursion on the
   derivation.  It only mentions [le_t] (Instance/Omega.v), so it lives above
   the category-indexed development. *)
Fixpoint le_S_shift@{u} {m n} (p : le_t@{u} m n) : le_t@{u} (S m) (S n) :=
  match p in le_t _ n' return le_t@{u} (S m) (S n') with
  | le_t_n    => le_t_n
  | le_t_S p' => le_t_S (le_S_shift p')
  end.

(* Predictable obligation alignment for the (op-)cocone records below: with
   [idtac] every obligation SHIFTS to an explicit [Next Obligation], rather
   than being silently discharged by the ambient [cat_simpl]. *)
#[local] Obligation Tactic := idtac.

Section Adamek.

(* [Colimit]/[IsALimit] force the diagram category and the target to share
   their hom/prop universe, and [Chain] pins [Omega]'s hom/prop to [Set]
   (Instance/Omega.v, Construction/Chain.v).  The target [C] therefore carries
   its hom/prop at [Set]; the object level [cobj] stays polymorphic, so every
   result below is universe-polymorphic in the size of the objects. *)
Universe cobj.
Context {C : Category@{cobj Set Set}}.
Context `{HI : @Initial C}.
Context (F : C ⟶ C).
Context (L : Colimit (Chain F)).

(* The colimit apex and its apex-pinned colimit witness, read covariantly. *)
Definition A : C := colimit_apex L.
Definition HL := colimit_is_acolimit L.

(* Definitional unfolding rules for the chain transports, used to control
   rewriting without unleashing [simpl] on the ambient fixpoints. *)
Lemma chain_hom_n {m} : chain_hom F (@le_t_n m) = id.
Proof. reflexivity. Qed.

Lemma chain_hom_step {m n} (p : le_t m n) :
  chain_hom F (le_t_S p) = chain_step F n ∘ chain_hom F p.
Proof. reflexivity. Qed.

Lemma chain_step_step (n : nat) :
  chain_step F (S n) = fmap[F] (chain_step F n).
Proof. reflexivity. Qed.

(* Transporting a shifted order proof is the image under [F] of transporting
   the original: [chain_hom (S p) ≈ F (chain_hom p)]. *)
Lemma chain_hom_S {m n} (p : le_t m n) :
  chain_hom F (le_S_shift p) ≈ fmap[F] (chain_hom F p).
Proof.
  induction p as [| n' p' IH].
  - cbn [le_S_shift chain_hom]. now rewrite fmap_id.
  - cbn [le_S_shift chain_hom].
    rewrite chain_step_step.
    rewrite IH.
    now rewrite fmap_comp.
Qed.

(* The honest hypothesis: [F A] carries a colimit of the shifted diagram whose
   injections are exactly the image legs [fmap[F] (colimit_inj HL n)]. *)
Record AdamekData : Type := {
  adamek_colim : IsAColimit (F ◯ Chain F) (F A) ;
  adamek_legs  : ∀ n : nat,
    colimit_inj adamek_colim n ≈ fmap[F] (colimit_inj HL n)
}.

Section WithData.

Context (D : AdamekData).

Local Notation HFL := (adamek_colim D).

(* The shifted cocone over [F ◯ Chain F] with apex [A], legs [inj (S n)]. *)
Program Definition Ashift : Cocone (F ◯ Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((F ◯ Chain F)^op) A
    (@Build_ACone (Omega^op) (C^op) A ((F ◯ Chain F)^op)
       (fun n => colimit_inj HL (S n)) _).
Next Obligation.
  intros x y f.
  change (colimit_inj HL (S x) ∘ fmap[F] (chain_hom F f)
            ≈ colimit_inj HL (S y)).
  rewrite <- chain_hom_S.
  exact (colimit_inj_coherence HL (le_S_shift f)).
Qed.

(* The [F]-algebra structure map, mediating out of the shifted cocone. *)
Definition alpha : F A ~> A := colimit_med HFL Ashift.

(* The defining step relation of the structure map, phrased through the image
   legs by folding in the leg agreement [adamek_legs]. *)
Lemma STEP (n : nat) :
  alpha ∘ fmap[F] (colimit_inj HL n) ≈ colimit_inj HL (S n).
Proof.
  rewrite <- (adamek_legs D n).
  exact (colimit_med_commutes HFL Ashift n).
Qed.

Section Mediator.

Context (aβ : FAlg F).

(* The competing cocone's legs into the carrier [``aβ], built by recursion on
   the chain index: [lam 0] is the unique map out of [0], and each step
   postcomposes the algebra map [`2 aβ] with the functorial image. *)
Fixpoint lam (n : nat) : chain_obj F n ~> ``aβ :=
  match n with
  | O   => zero
  | S k => `2 aβ ∘ fmap[F] (lam k)
  end.

(* [lam] respects the generating step of the chain. *)
Lemma LAMSTEP (n : nat) : lam (S n) ∘ chain_step F n ≈ lam n.
Proof.
  induction n as [| k IH].
  - apply zero_unique.
  - transitivity (`2 aβ ∘ (fmap[F] (lam (S k)) ∘ fmap[F] (chain_step F k))).
    + change (lam (S (S k))) with (`2 aβ ∘ fmap[F] (lam (S k))).
      change (chain_step F (S k)) with (fmap[F] (chain_step F k)).
      now rewrite <- comp_assoc.
    + rewrite <- fmap_comp.
      rewrite IH.
      reflexivity.
Qed.

(* [lam] is a cocone over the whole chain: it respects every transport. *)
Lemma lam_coh {m n} (f : le_t m n) : lam n ∘ chain_hom F f ≈ lam m.
Proof.
  induction f as [| n' f' IH].
  - rewrite chain_hom_n. now rewrite id_right.
  - rewrite (chain_hom_step f').
    rewrite comp_assoc.
    rewrite LAMSTEP.
    exact IH.
Qed.

(* The competing cocone itself, over [Chain F] with apex [``aβ]. *)
Program Definition Lam : Cocone (Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((Chain F)^op) (``aβ)
    (@Build_ACone (Omega^op) (C^op) (``aβ) ((Chain F)^op) lam _).
Next Obligation.
  intros x y f.
  change (lam x ∘ chain_hom F f ≈ lam y).
  exact (lam_coh f).
Qed.

(* The mediating carrier map out of the colimit apex. *)
Definition u : A ~> ``aβ := colimit_med HL Lam.

Lemma u_inj (n : nat) : u ∘ colimit_inj HL n ≈ lam n.
Proof. exact (colimit_med_commutes HL Lam n). Qed.

(* The shifted competing cocone over [F ◯ Chain F], apex [``aβ], legs
   [lam (S n)]; its mediators separate the two sides of the algebra square. *)
Program Definition T : Cocone (F ◯ Chain F) :=
  @Build_Cone (Omega^op) (C^op) ((F ◯ Chain F)^op) (``aβ)
    (@Build_ACone (Omega^op) (C^op) (``aβ) ((F ◯ Chain F)^op)
       (fun n => lam (S n)) _).
Next Obligation.
  intros x y f.
  change (lam (S x) ∘ fmap[F] (chain_hom F f) ≈ lam (S y)).
  rewrite <- chain_hom_S.
  exact (lam_coh (le_S_shift f)).
Qed.

(* The mediator [u] is a morphism of [F]-algebras [(A, α) ~> (``aβ, `2 aβ)]:
   both [u ∘ α] and [`2 aβ ∘ F u] mediate the shifted cocone [T]. *)
Lemma u_alg : u ∘ alpha ≈ `2 aβ ∘ fmap[F] u.
Proof.
  apply (colimit_med_eq HFL T).
  (* The colimit injections of [HFL] have domain [(F ◯ Chain F) n]; folding it
     to the [F]-image form [F ((Chain F) n)] lets the [F]-image lemmas
     [STEP]/[fmap_comp] key on the goal. *)
  - intro n.
    rewrite (adamek_legs D n).
    rewrite <- comp_assoc.
    change ((F ◯ Chain F) n) with (F ((Chain F) n)).
    rewrite STEP.
    exact (u_inj (S n)).
  - intro n.
    rewrite (adamek_legs D n).
    rewrite <- comp_assoc.
    change ((F ◯ Chain F) n) with (F ((Chain F) n)).
    rewrite <- fmap_comp.
    rewrite u_inj.
    reflexivity.
Qed.

(* Any [F]-algebra map out of [(A, α)] agrees with the mediator [u] on the
   underlying carrier, by induction along the chain injections. *)
Lemma hom_is_u (h : @FAlgHom C F A (``aβ) alpha (`2 aβ)) :
  falg_hom[h] ≈ u.
Proof.
  destruct h as [hh hcomm]; simpl.
  symmetry.
  unfold u.
  apply (colimit_med_unique HL Lam).
  intro n.
  induction n as [| k IH].
  - apply zero_unique.
  - rewrite <- STEP.
    rewrite comp_assoc.
    rewrite hcomm.
    rewrite <- comp_assoc.
    change ((Chain F) (S k)) with (F ((Chain F) k)).
    rewrite <- fmap_comp.
    rewrite IH.
    reflexivity.
Qed.

End Mediator.

(* The candidate initial algebra [(A, α)], as an object of [FAlg F].  Naming it
   with an explicit carrier type pins the sigma predicate to
   [fun a => FAlgebra F a], which bare [(A; alpha)] would otherwise leave
   ambiguous. *)
Definition muF : FAlg F := existT (fun a : C => FAlgebra F a) A alpha.

(* The unique [F]-algebra map from the initial algebra to any algebra [y]
   (an arrow [muF ~> y] in [FAlg F], i.e. into the terminal object of
   [(FAlg F)^op]).  The morphisms are stated inside [FAlg F] rather than through
   the opposite so the parser reads the category [^op], not the functor one. *)
Definition adamek_one (y : FAlg F) :
  muF ~{FAlg F}~> y :=
  {| falg_hom := u y ; falg_commutes := u_alg y |}.

Lemma adamek_one_unique (y : FAlg F)
  (f g : muF ~{FAlg F}~> y) : f ≈ g.
Proof.
  simpl.
  transitivity (u y).
  - exact (hom_is_u y f).
  - symmetry. exact (hom_is_u y g).
Qed.

(* [(A, α)] is initial in [FAlg F], i.e. terminal in [(FAlg F)^op].  The
   opposite category is named explicitly through [Opposite]: [FAlg F] and its
   opposite share objects, so a bare record literal cannot recover which side
   the terminal object lives on. *)
Definition adamek : @Initial (FAlg F) :=
  @Build_Terminal (Opposite (FAlg F)) muF adamek_one adamek_one_unique.

End WithData.

End Adamek.
