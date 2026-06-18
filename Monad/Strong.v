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
Require Import Category.Functor.Strong.
Require Import Category.Natural.Transformation.Strong.

Generalizable All Variables.

(** Strong monads (monads whose functor carries a compatible strength) *)

(* nLab:      https://ncatlab.org/nlab/show/strong+monad
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   A strong monad on a monoidal category (C, ⊗, I) is a monad (M, η, μ) whose
   underlying endofunctor M : C ⟶ C carries a (left) tensorial strength

     t = strength[M] : x ⨂ M y ~> M (x ⨂ y)          (left strength)

   — that is, M is a [StrongFunctor] (see Functor.Strong), so t already
   satisfies Kock's two coherence laws [strength_id_left] (w.r.t. the left
   unitor λ) and [strength_assoc] (w.r.t. the associator α) — and whose strength
   is *compatible with the monad structure* η and μ.  Following Kock (1972,
   "Strong functors and monoidal monads", Arch. Math. 23) and Moggi (1991,
   "Notions of computation and monads", Inf. & Comput. 93), the two
   compatibility conditions are, writing t = strength[M]:

     - η-compat ([strength_ret]):  t ∘ (id ⨂ η) ≈ η
                 at type  x ⨂ y ~> M (x ⨂ y)

     - μ-compat ([strength_join]): t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t
                 at type  x ⨂ M (M y) ~> M (x ⨂ y)

   In words: pulling η out of the right factor agrees with applying η to the
   whole tensor, and pulling μ out of the right factor agrees with sliding the
   strength through both M-layers and then multiplying.  These are exactly the
   diagrams that make t respect the monad structure in the tensor variable,
   which is what is needed to internalize Kleisli composition and to give the
   do-notation / `>>=` of a computational monad in the sense of Moggi: a strong
   monad's effects can be parameterized by an ambient context x.

   Deep structural fact (exploited below as a validation): the two compatibility
   laws are *precisely* the [Strong_Transform] squares for the monad's structure
   maps.  Since strength[Id] = id ([Id_StrongFunctor]), η-compat is exactly the
   strength-compatibility square of η : Id ⟹ M; and since strength[M ◯ M] =
   M t ∘ t ([Compose_StrongFunctor]), μ-compat is exactly the strength-
   compatibility square of μ : M ◯ M ⟹ M.  Thus a strong monad is exactly a
   monad whose unit and multiplication are *strong* natural transformations — a
   monoid object in the category of strong endofunctors and strong natural
   transformations.  We make this explicit at the end of the Tier-2 section
   ([ret_Strong_Transform], [join_Strong_Transform]).

   "Strong" here means tensorial strength, NOT "strong (i.e. pseudo) monoidal
   functor"; the two notions are unrelated.  On a symmetric monoidal base the
   left strength induces a *right* strength by conjugating with the braiding
   (see [rstr] below, with [rstr_natural], [rstr_ret], [rstr_join]), so every
   strong monad over a symmetric base is right-strong in the monad-relevant
   sense.  Two coherence notions for combining a pair of computations appear
   below.  Abstractly, a monad that is simultaneously left- and right-strong
   (over an arbitrary bundled right strength) is *commutative* when its two
   double strengths agree ([CommutativeStrongMonad]).  Concretely, over a
   symmetric base the derived right strength [rstr] yields named double
   strengths M x ⨂ M y ~> M (x ⨂ y) ([dstr], [dstr']) and the predicate
   [commutative_sm] asserting they agree; this double strength is the laxator
   that underlies the Applicative/Day structure of a commutative monad. *)

(* ================================================================== *)
(** ** The strong monad class.                                         *)
(* ================================================================== *)

Section StrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

(* A strong monad bundles, over a fixed endofunctor M, both a [Monad] structure
   and a [StrongFunctor] structure on M, together with the two compatibility
   laws relating the strength to η and μ.  The functor-level coherences (λ- and
   α-laws) live in the [StrongFunctor] field; only the monad-specific coherences
   are stated here.  The two structures are coercion fields (`::`) so that
   [ret], [join], [strength], and [fmap[M]] resolve uniformly inside the laws,
   and a [StrongMonad] is usable wherever a [Monad] or [StrongFunctor] is. *)

Class StrongMonad := {
  strongmonad_is_monad  :: @Monad C M;           (* the underlying monad (η, μ) *)
  strongmonad_is_strong :: @StrongFunctor C _ M; (* the underlying left strength t *)

  (* η-compat (Kock/Moggi): the strength carries the unit pushed into the right
     factor to the unit of the whole tensor.

         x ⨂ y ---- id ⨂ η ----> x ⨂ M y
            \                        |
             \                   strength
              η                     |
               \                    v
                ------------------> M (x ⨂ y)

       t ∘ (id ⨂ η) ≈ η      at  x ⨂ y ~> M (x ⨂ y) *)
  strength_ret {x y} :
    strength ∘ (id[x] ⨂ ret[M]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (* μ-compat (Kock/Moggi): the strength commutes past the multiplication of the
     right factor, sliding through both M-layers.

       x ⨂ M (M y) -- id ⨂ μ --> x ⨂ M y
            |                        |
        strength                 strength
            |                        |
            v                        v
       M (x ⨂ M y)              M (x ⨂ y)
            |                        ^
        M(strength)                  | μ
            v                        |
       M (M (x ⨂ y)) --------------- /

       t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t   at  x ⨂ M (M y) ~> M (x ⨂ y).
     The RHS associates left (∘ at level 40): (μ ∘ M t) ∘ t, which is exactly
     μ precomposed with strength[M ◯ M] = M t ∘ t (see [Compose_StrongFunctor]). *)
  strength_join {x y} :
    strength ∘ (id[x] ⨂ join[M])
      ≈ (join[M] ∘ fmap[M] strength ∘ strength
           : x ⨂ M (M y) ~> M (x ⨂ y))
}.

End StrongMonad.

Arguments StrongMonad {C} _ M.

(* ================================================================== *)
(** ** Tier 1 instance: the identity strong monad.                    *)
(* ================================================================== *)

Section IdStrongMonad.

Context `{@Monoidal C}.

(* There is no identity monad on an abstract category in the library yet, so we
   provide one here: Id[C] with ret = id and join = id.  All five monad laws are
   instances of the identity/composition equations, discharged automatically by
   the ambient obligation tactic (cat_simpl). *)
#[local] Program Instance Id_Monad : @Monad C Id[C] := {
  ret  := fun _ => id;
  join := fun _ => id
}.

(* Combining [Id_Monad] with [Id_StrongFunctor] (whose strength is id) gives the
   identity strong monad.  Both compatibility laws collapse to id ∘ id ≈ id
   (after id ⨂ id = id) and are discharged automatically.  [Id_Monad] is kept
   [local] so it is not leaked into library-wide [Monad] instance resolution. *)
#[export] Program Instance Id_StrongMonad : StrongMonad _ Id[C] := {
  strongmonad_is_monad  := Id_Monad;
  strongmonad_is_strong := Id_StrongFunctor
}.

End IdStrongMonad.

(* ================================================================== *)
(** ** Tier 2: validation — η and μ are strong natural transformations *)
(* ================================================================== *)

(* The deep structural content of the definition: the two compatibility laws are
   *exactly* the [Strong_Transform] squares for the unit and the multiplication.
   We package η and μ as natural-transformation objects (Id ⟹ M and M ◯ M ⟹ M)
   and prove each is a strong natural transformation, reusing [strength_ret] and
   [strength_join].  This confirms a strong monad is a monoid η : Id ⟹ M,
   μ : M ◯ M ⟹ M in the category of strong endofunctors and strong natural
   transformations: each structure map is itself strong. *)

Section StrongMonadValidation.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* η packaged as a natural transformation Id ⟹ M.  Its naturality square is the
   unit naturality law [fmap_ret] of the monad; [Build_Transform'] proves the
   symmetric orientation [naturality_sym] from this one square for free. *)
Definition Monad_unit : Id[C] ⟹ M :=
  Build_Transform' (F:=Id[C]) (G:=M) (fun _ => ret[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply fmap_ret)).

(* μ packaged as a natural transformation M ◯ M ⟹ M.  Its naturality square is
   the multiplication naturality law [join_fmap_fmap] of the monad. *)
Definition Monad_mult : M ◯ M ⟹ M :=
  Build_Transform' (F:=M ◯ M) (G:=M) (fun _ => join[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply join_fmap_fmap)).

(* η is a strong natural transformation Id ⟹ M.  Its source [Id] is strong with
   strength = id ([Id_StrongFunctor]), so the [Strong_Transform] square reads

       strength[M] ∘ (id ⨂ η_y) ≈ η_{x⨂y} ∘ strength[Id]

   and since strength[Id] = id this is precisely [strength_ret]. *)
#[export] Program Instance ret_Strong_Transform :
  @Strong_Transform C _ Id[C] Id_StrongFunctor M _ Monad_unit.
Next Obligation.
  simpl.
  rewrite id_right.
  apply strength_ret.
Qed.

(* μ is a strong natural transformation M ◯ M ⟹ M.  Its source [M ◯ M] is strong
   via [Compose_StrongFunctor] with strength = M(strength) ∘ strength, so the
   [Strong_Transform] square reads

       strength[M] ∘ (id ⨂ μ_y) ≈ μ_{x⨂y} ∘ (M(strength) ∘ strength)

   and one [comp_assoc] re-brackets this to exactly [strength_join]. *)
#[export] Program Instance join_Strong_Transform :
  @Strong_Transform C _ (M ◯ M) (Compose_StrongFunctor M M _ _) M _ Monad_mult.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  apply strength_join.
Qed.

End StrongMonadValidation.

(* ================================================================== *)
(** ** Tier 3: right-strong monads, the symmetric bridge,             *)
(**            commutativity, and the induced double strength.        *)
(* ================================================================== *)

(* nLab: https://ncatlab.org/nlab/show/strong+monad

   The mirror image of [StrongMonad]: a monad whose functor carries a *right*
   tensorial strength  rstrength : M x ⨂ y ~> M (x ⨂ y)  (so M is a
   [RightStrongFunctor]), compatible with η and μ via the right-hand factor.

     - η-compat ([rstrength_ret]):  rstrength ∘ (ret ⨂ id) ≈ ret
     - μ-compat ([rstrength_join]): rstrength ∘ (join ⨂ id)
                                      ≈ join ∘ fmap rstrength ∘ rstrength

   This dual is provided for completeness and symmetry with [StrongMonad]; no
   instance is built here.  [CommutativeStrongMonad] below deliberately inlines
   a [RightStrongFunctor] plus its two compatibility laws (rather than bundling
   a [RightStrongMonad]) so that the left and right strengths share the *same*
   underlying monad, keeping [join] unambiguous in the commutativity law. *)

Section RightStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class RightStrongMonad := {
  rstrongmonad_is_monad   :: @Monad C M;
  rstrongmonad_is_rstrong :: @RightStrongFunctor C _ M;

  (* η-compat (right): rstrength ∘ (ret ⨂ id) ≈ ret *)
  rstrength_ret {x y} :
    rstrength ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (* μ-compat (right): rstrength ∘ (join ⨂ id)
                         ≈ join ∘ fmap rstrength ∘ rstrength *)
  rstrength_join {x y} :
    rstrength ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] rstrength ∘ rstrength
           : M (M x) ⨂ y ~> M (x ⨂ y))
}.

End RightStrongMonad.

Arguments RightStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** Commutative strong monads (left and right strengths cohere).    *)
(* ------------------------------------------------------------------ *)

(* nLab: https://ncatlab.org/nlab/show/commutative+monad

   A *commutative* strong monad is a monad that is simultaneously left-strong
   and right-strong, whose two strengths agree on how to combine a pair of
   computations.  Out of the left strength t and the right strength t' one
   builds two "double strengths" M x ⨂ M y ~> M (x ⨂ y):

     dstr  = μ ∘ M t  ∘ t'   (sequence the right computation first)
     dstr' = μ ∘ M t' ∘ t    (sequence the left  computation first)

   and the monad is commutative when dstr ≈ dstr' — running the two effects in
   either order yields the same result.  This double strength is precisely the
   laxator that exhibits a commutative monad as a lax monoidal monad, and it is
   what underlies the Applicative instance of a commutative monad.

   We share a single underlying [Monad] between the two strengths, so that
   [join] is unambiguous in the commutativity law: the right strength is given
   as a [RightStrongFunctor] together with its two monad-compatibility laws
   relative to that shared monad. *)

Section CommutativeStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class CommutativeStrongMonad := {
  comm_is_strong :: @StrongMonad C _ M;

  (* the right strength over the *same* underlying monad *)
  comm_is_rstrong : @RightStrongFunctor C _ M;

  comm_rstrength_ret {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  comm_rstrength_join {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y)
                ∘ @rstrength _ _ _ comm_is_rstrong (M x) y
           : M (M x) ⨂ y ~> M (x ⨂ y));

  (* the two double strengths agree *)
  commutativity {x y} :
    join[M] ∘ fmap[M] strength ∘ @rstrength _ _ _ comm_is_rstrong x (M y)
      ≈ join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y) ∘ strength
}.

End CommutativeStrongMonad.

Arguments CommutativeStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** The symmetric bridge: a strong monad over a symmetric base      *)
(**     carries a right strength compatible with η and μ.              *)
(* ------------------------------------------------------------------ *)

(* On a symmetric monoidal base the left strength induces a right strength by
   conjugating with the braiding,

     rstr := M(β) ∘ t ∘ β  :  M x ⨂ y ~> M (x ⨂ y)

   (braid M x ⨂ y → y ⨂ M x, apply the left strength, then braid back inside
   M).  We prove that this derived right strength is natural and satisfies the
   two monad-compatibility laws — so every strong monad over a symmetric base is
   right-strong in the monad-relevant sense.

   We deliver this as a derived morphism family with its laws rather than as a
   full [RightStrongMonad] instance: the two [RightStrongFunctor] *coherence*
   laws (unit-object [rrstrength_id_right] and associator [rstrength_assoc])
   require braided-coherence lemmas relating the unitors and associator to the
   braiding (e.g. ρ ≈ λ ∘ β) that are not available from the library's bare
   [BraidedMonoidal]/[SymmetricMonoidal] axiomatization, so we omit them rather
   than assume any axiom. *)

Section SymmetricRightStrength.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* The derived right strength rstr = M(braid) ∘ strength ∘ braid. *)
Definition rstr {x y} : M x ⨂ y ~> M (x ⨂ y) :=
  fmap[M] braid ∘ strength ∘ braid.

(* Joint naturality of the derived right strength:
     fmap (f ⨂ g) ∘ rstr ≈ rstr ∘ (fmap f ⨂ g). *)
Lemma rstr_natural {x z y w} (f : x ~> z) (g : y ~> w) :
  fmap[M] (bimap f g) ∘ rstr ≈ rstr ∘ bimap (fmap[M] f) g.
Proof.
  unfold rstr.
  pose proof (@strength_natural _ _ M _ y w g x z f) as SN.
  simpl in SN.
  normal.
  (* LHS: fmap((f⨂g)∘braid) ∘ strength ∘ braid;  (f⨂g)∘braid = braid∘(g⨂f) *)
  rewrite bimap_braid.
  normal.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] (g ⨂ f))).
  rewrite SN.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  reflexivity.
Qed.

(* η-compat for the derived right strength: rstr ∘ (ret ⨂ id) ≈ ret. *)
Lemma rstr_ret {x y} :
  rstr ∘ (ret[M] ⨂ id[y]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(ret⨂id) = (id⨂ret)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  rewrite <- !comp_assoc.
  rewrite braid_invol.
  rewrite id_right.
  reflexivity.
Qed.

(* μ-compat for the derived right strength:
     rstr ∘ (join ⨂ id) ≈ join ∘ fmap rstr ∘ rstr. *)
Lemma rstr_join {x y} :
  rstr ∘ (join[M] ⨂ id[y])
    ≈ (join[M] ∘ fmap[M] rstr ∘ rstr : M (M x) ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(join⨂id) = (id⨂join)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_join.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.         (* fmap braid ∘ join = join ∘ fmap(fmap braid) *)
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite braid_invol.               (* braid ∘ braid = id collapses the RHS *)
  rewrite id_right.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The induced double strength M x ⨂ M y ~> M (x ⨂ y) built from the left
   strength and the derived right strength, and its mirror. *)
Definition dstr {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] strength ∘ rstr.

Definition dstr' {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] rstr ∘ strength.

(* Commutativity over a symmetric base: the two orders of combining a pair of
   computations agree.  This is a genuine extra property of the particular
   strong monad (false for non-commutative monads), recorded here as the
   predicate to be discharged per instance.

   This is the symmetric-base specialization, phrased with the *derived* right
   strength [rstr]; it is distinct from the abstract
   [CommutativeStrongMonad.commutativity] field (stated over an arbitrary
   bundled right strength).  The two are not formally bridged here: packaging
   [rstr] as a full [RightStrongFunctor] — and so obtaining a
   [CommutativeStrongMonad] over the symmetric base — would need the
   braid/unitor coherence ρ ≈ λ ∘ β, which the bare [SymmetricMonoidal]
   axiomatization used here does not provide. *)
Definition commutative_sm : Type := ∀ x y, @dstr x y ≈ @dstr' x y.

End SymmetricRightStrength.
