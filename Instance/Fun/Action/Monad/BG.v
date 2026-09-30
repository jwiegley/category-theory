(** * Riehl's Set^BG: evaluation is monadic, by the monadicity theorem *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Group.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Fun.Action.Monad.

Generalizable All Variables.

(* Book: Riehl, "Category Theory in Context", 2nd ed., Exercise
         5.5.iv, printed p. 208 (PDF p. 228) — riehl:5.5:exiv; with her
         Theorem 5.5.1, printed p. 202 (PDF p. 222), and Definition
         5.3.1, printed p. 196 (PDF p. 216)
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2, "Group actions", printed p. 141
         (PDF p. 150) — maclane:VI.2:remark2; and §VI.2 Exercise 3,
         printed p. 142 (PDF p. 151)
   nLab: https://ncatlab.org/nlab/show/monadicity+theorem
   nLab: https://ncatlab.org/nlab/show/action

   Riehl's Exercise 5.5.iv gives, "For any group G", the forgetful functor
   U : Set^BG → Set a left adjoint "that sends a set X to the G-set G × X,
   with G acting on the left", and asks: "Prove that this adjunction is
   monadic by appealing to the monadicity theorem."  Her Set^BG is the
   functor category [BG, Set], BG the one-object category of G, and U is
   evaluation at the one object.  Instance/Fun/Action/Monad.v proves the
   exercise at Instance/Fun/Action.v's category [MSet M] of actions, which
   [MSet_Fun_equiv] identifies with [Deloop M, Sets] in Cat; no lemma in the
   tree carries [Monadic] across such an identification, so this file states
   the exercise literally, on the functor category itself.  Every statement
   is over a monoid M, as there, since nothing below uses inverses.  The
   group instances are those of Instance/Fun/Action/Monad.v:
   [GSet_BG_Monadic] at Construction/Deloop.v's [GrpObject],
   [GSet_BG_Monadic_Grp] at Instance/Grp.v's, through Instance/Grp/Free.v's
   [grp_deloop_monoid], and [GSet_BG_Monadic_GroupObject] at
   Structure/Group.v's [GroupObject] in (Sets, ×), through Instance/Grp.v's
   [GroupObject_GrpObject], which needs [PropEquiv] of the carrier.  Both
   files that declare a [GrpObject] are imported, and each use is written
   with its full path.

   THE FUNCTOR CATEGORY AND ITS FORGETFUL FUNCTOR.  [SetBG M] is
   [Deloop M, Sets] with its hom level written out (UNIVERSES, below).
   [U_BG M] is Instance/Fun/Eval.v's [Eval] at the one object [ttt], and
   [F_BG M] is Instance/Fun/Action.v's [MSet_from] after the free M-set
   functor [MSet_Free] of Instance/Fun/Action/Monad.v: a setoid X goes to
   the functor whose value is M × X, acted on in the left factor.
   Evaluation agrees with [MSet_to] followed by [MSet_Forget] in both data
   fields at [eq_refl] ([U_BG_obj], [U_BG_map]), but not as a functor.

   THE ADJUNCTION.  [BG_adj : F_BG M ⊣ U_BG M] is built on hom-setoids by
   Theory/Adjunction.v's [Build_Adjunction'].  A transformation φ out of
   F X restricts to x ↦ φ (u, x) ([BG_restrict]); a map ψ : X → P ttt
   extends to (g, x) ↦ g · ψ x by Instance/Fun/Action/Monad.v's
   [MSet_extend], carried into the functor category by [MSet_from] and
   Instance/Fun/Action.v's round trip [MSet_round_iso] ([BG_extend]).

   CREATION, BY TRANSPORT.  By conversion, a split coequalizer of the
   U_BG-images of a pair p, q IS one of the [MSet_Forget]-images of
   [MSet_to p] and [MSet_to q], because [action_of_functor P] has carrier
   P ttt and action fmap[P].  So the creation of Instance/Fun/Action/
   Monad.v is used as it stands.  The created functor is [MSet_from] of
   its [CreatedAct]; the coequalizing transformation [BGCreatedE] has
   component e, and its naturality is [CreatedE]'s equivariance; the two
   clauses of the class are [CreatedE_is_coeq] and [Reflected_is_coeq]
   read back.  The one new lemma is [MSet_to_reflects_coeq]: a cofork of
   transformations whose [MSet_to]-image is a coequalizer of M-sets is a
   coequalizer of functors, a transformation out of the one object being
   one equivariant map.  The existence clause also passes through Monad/
   Monadicity/Beck.v's [coequalizer_along_iso], at Instance/Fun/Action.v's
   [MSet_action_round_iso].  No absorption lemma is proved again.  The
   lift is on the nose: its value is the split quotient Z, its action is
   g · z = e (g · s z), its arrow is e and its comparison isomorphism is
   the identity ([bg_created_carrier], [bg_created_action],
   [bg_created_arrow], [bg_created_iso]).

   MONADICITY.  [BG_beck_equivalence] is Beck.v's [beck_monadicity] at
   [BG_adj] and [U_BG_creates]; Instance/Fun/Action/Monad.v is the first
   use of that theorem in the tree, and this file the second.
   [U_BG_Monadic] packages it as Monad/Comparison.v's [Monadic].
   [U_BG_reflects] is Beck.v's [creates_split_reflects_isos] here: a
   transformation whose component at the one object is invertible in
   Sets is invertible.  [BG_EM_iso] is the isomorphism in Cat between
   [SetBG M] and the algebras of the induced monad [BGMonad M] (an
   isomorphism in Cat, inverse up to natural isomorphism, hence an
   equivalence), and its [to] leg IS the comparison functor
   ([BG_EM_iso_to]).

   TWO MONADS.  [BGMonad M] is Monad/Comparison.v's
   [Adjunction_Induced_Monad] at [BG_adj]; [ActMonad M] of
   Instance/Fun/Action/Monad.v is the same construction at the adjunction on
   [MSet M].  Their functors have the same object and arrow maps, M × X and
   M × f ([BG_T_obj], [BG_T_map]), and their multiplications agree at every
   p ([BG_join_ActMonad]); the two multiplications have the same underlying
   function, and differ as setoid morphisms only in their properness proofs
   (the probe's control beside N15).  [BGMonad]'s μ is Mac Lane's formula at
   his triple ([BG_join]) and as a function ([BG_join_fun]), which is
   stronger, since Coq's [prod] has no eta; its η likewise ([BG_ret],
   [BG_ret_fun]).  Their units differ.  Mac Lane's printed unit,
   η x = ⟨u, x⟩ (§VI.2, p. 141), is [ActMonad]'s on the nose, while
   [BGMonad]'s is (u u, x) ([BG_ret]): the unit is the restriction of the
   identity of F X, and the identity of the functor category is
   Theory/Natural/Transformation.v's [nat_id], whose component is fmap[F X]
   id, the action of u.  The functors are ≈ with identity components
   ([BG_T_ActF]), and the units agree at ≈ ([BG_ret_ActMonad]).

   THE TIE.  This file's comparison functor lands in the algebras of
   [BGMonad M], that of Instance/Fun/Action/Monad.v in those of
   [ActMonad M].  Mac Lane's §VI.2 Exercise 3(b) (p. 142) turns a morphism θ
   of monads into "a functor θ* : X^T' → X^T" with G^T ∘ θ* = G^T'; here θ
   is the identity-component isomorphism [BG_T_ActF], and θ* is built for
   this instance alone, with no general record of monad morphisms.
   [BG_Act_alg] reads an algebra of [BGMonad M] as one of [ActMonad M] with
   the SAME structure map: the unit law moves along mon_op_unit_l, and the
   action law passes unchanged, since the two monads' arrow maps and
   multiplications agree by conversion.  [Act_BG_alg] is the same reading
   the other way; it is kept as a map on algebras and is not assembled into
   a functor, only θ*'s direction being built.  [BG_Act_EM] is θ*, the
   identity on carriers, structure maps and arrows ([BG_Act_EM_carrier],
   [BG_Act_EM_alg]), and Mac Lane's G^T ∘ θ* = G^T' holds on the nose in
   both data fields ([BG_Act_EM_forget_obj], [BG_Act_EM_forget_map]).  [tie]
   states that θ* after this file's comparison functor is ≈, with identity
   components, the [to] leg of Instance/Fun/Action/Monad.v's [Fun_EM_iso],
   which is [EM_MSet_iso] after [MSet_Fun_equiv], that is,
   [EM_Comparison (MSet_adj M) ◯ MSet_to M] on the nose (the probe's control
   beside N19).  On objects the two agree at [eq_refl] in the carrier
   ([tie_carrier]) and in the structure map at each (g, z) and as a function
   ([tie_alg], [tie_alg_fun]); the whole algebras differ in their proof
   fields [t_id] and [t_action] (N19), and in the properness proof of the
   structure map, whose function agrees ([tie_alg_fun]; N20), so [tie] holds
   at ≈ only.  So the literal comparison functor, carried along θ*, is the
   equivalence of that file, at Set^BG itself.

   WHICH "MONADIC".  Riehl's Definition 5.3.1 (p. 196) calls an
   adjunction monadic when the comparison functor "defines an equivalence
   of categories": Monad/Comparison.v's [Monadic].  Her Theorem 5.5.1
   (p. 202) reads "A right adjoint functor U : D → C is monadic if and
   only if it creates coequalizers of U-split pairs"; its "if" half is
   Beck.v's [beck_monadicity], in that form.  The same page names the
   strict reading, K an isomorphism exactly when U "strictly creates"
   those coequalizers, and leaves its proof to her Exercise 5.5.i.  This
   file implements the equivalence reading.  The lift above is on the
   nose, but the class does not record uniqueness on the nose, and no
   isomorphism of categories on the nose is stated.

   STRENGTHS.  By [eq_refl]: evaluation's two data fields against
   [MSet_Forget ◯ MSet_to]; the created lift's value, action, arrow and
   isomorphism; the [to] leg of [BG_EM_iso]; the induced monad's object and
   arrow maps, its unit as (u u, x) at each x and as a function, and its
   multiplication at (g₁, (g₂, x)) and as a function; its multiplication
   against [ActMonad]'s at every p; θ* on carriers, structure maps and
   arrows, and G^T ∘ θ* against G^T' in both data fields; the tie on
   objects, in the carrier and in the structure map at each (g, z) and as a
   function.  At ≈ only: the two monads' functors ([BG_T_ActF]), their units
   ([BG_ret_ActMonad]), and θ* after the comparison functor against the [to]
   leg of [Fun_EM_iso] ([tie]).  Refused by conversion, each pinned in
   Test/ProbeGroupAction464.v (its N13-N16, N19 and N20) and stripped in a
   copy of the whole probe: the unit as (u, x); [U_BG M ◯ F_BG M] as
   [ActF M]; the two multiplications as one setoid morphism; [U_BG M] as
   [MSet_Forget M ◯ MSet_to M]; the tie on a whole object, and on the
   properness proof of its structure map.  The refusals are not opacity.  In
   a copy of this file's 111-file dependency closure, every [Qed] was turned
   into [Defined] and every [Unset Transparent Obligations] into [Set], with
   two exceptions.  Instance/Sets.v, Structure/Cartesian/Closed.v,
   Instance/Grp.v and Instance/Grp/Free.v keep their [Qed]s
   (Instance/Fun/Action/Monad.v's measurement keeps the first three).
   Instance/Grp/Free.v keeps them because the second builder kept every file
   the first had measured, although the first found that that file's flip
   alone builds.  The choice is harmless: copies of the two targets without
   the imports of Instance/Grp.v and Instance/Grp/Free.v and without the six
   group twins of the two files that use them compile and load neither file,
   so no refused or compared term depends on either.  One proof of
   Structure/Limit/Preservation.v, [preserves_colimit], had its bullets
   rewritten, since the added transparency leaves it one goal instead of
   two.  There the whole probe compiles, so all six refusals stand and every
   positive control holds, and each refusal stripped there prints the error
   of the unchanged tree.  Corelib's CMorphisms lemmas stay opaque in any
   such tree.  In the normal forms of N13-N16, each refused field differs at
   a neutral term of the variable data: M's unit, or the transitivity and
   symmetry of a variable setoid.  Unfolding those lemmas cannot close the
   gap.  N19's two algebras differ in both proof fields, [t_id] and
   [t_action], and in the properness proof of the structure map (N20), each
   refused alone there as well.

   UNIVERSES, read off [About].  Every constant binds [@{o so}], and the
   three that name Cat, [BG_EM_iso], [BG_EM_iso_to] and [tie], bind
   [@{o so c}]; M : MonObject@{o o o}.  The only strict bounds are o < so,
   first carried by Instance/Sets.v's [Sets], and o < c, so < c, first
   carried by Instance/Cat.v's [Cat@{c so so so o}].  There is no equation
   and no [Set].  The hom level of the functor category is not free, and
   [SetBG M] writes it out as [Fun@{o o so o so o so}], hom level o, the
   instance Instance/Fun/Action.v's [MSet_to] and [MSet_from] and
   Instance/Fun/Eval.v's [Eval] already use.  It is forced.
   Instance/Fun.v's block puts that level at or above the index category's
   hom level, o.  Theory/Functor.v's [Functor] block, h1 <= h2, puts it at
   or below the hom level of the target of any functor out of the category,
   so at or below o for U_BG.  Four more constants state the same
   identification in their own blocks:
   - [Compose], whose binder gives one hom universe to all three
     categories, so that the composite [F_BG] needs it on its own;
   - Theory/Adjunction.v's [Adjunction] (h1 = h2);
   - Beck.v's [beck_monadicity], which inherits it (u0 = u2);
   - Monad/Comparison.v's [Monadic], whose binder shares one hom
     universe.
   Measured in Test/ProbeGroupAction464.v (N17, N18) at the same category
   with hom level so: a functor type out of it into Sets is refused, and
   [MSet_from] into it is accepted while its composite with [MSet_Free]
   is refused ("Cannot enforce so = o because o < so").  The stdlib caps
   are the donors':
   - compose and ID from [Sets];
   - prod_rect and projections from [MSet_Free]'s product carrier;
   - Logic_lemmas.equality and so <= projections from
     [Build_Adjunction'];
   - prod_rect in the creation from [coequalizer_along_iso];
   - Projections from [beck_monadicity] and, in the [bg_created_*]
     readbacks, from the projections their statements apply; in θ* and
     the tie, from [EilenbergMoore], whose objects are sigma types;
   - eq_ind and eq_ind_r, in [GSet_BG_Monadic_GroupObject] only, from
     Instance/Grp.v's [GroupObject_GrpObject].
   A [simpl] in two proof bullets of [BG_Act_EM] added the strict bound
   o < Projections.u0 (implied by o < so and so <= Projections.u0) to nine
   constants, θ* and the eight that mention it ([tie_alg_fun] among them;
   measured again by putting the [simpl]s back in a copy of this file); the
   [simpl]s were removed and the bound is gone.  The adjunction is
   [Adjunction@{so o o so o o o o so o so}] and the witness
   [Monadic@{so so so so so o so so}], as in Instance/Fun/Action/Monad.v.

   NOT DELIVERED.
   - No general monad-morphism record; θ* for this instance is
     [BG_Act_EM] (THE TIE, above).
   - Transport of [Monadic], or of creation, along an equivalence of
     categories.
   - Mac Lane's and Riehl's strict monadicity, an isomorphism of
     categories on the nose.
   - The converse half of Riehl's theorem at [U_BG]: Beck.v's
     [monadic_creates] is stated at [EM_Forget]. *)

(** ** Riehl's Set^BG and its forgetful functor *)

(* The functor category [Deloop M, Sets], hom level o (see UNIVERSES). *)
Definition SetBG@{o so} (M : MonObject@{o o o}) : Category@{so o o} :=
  @Fun@{o o so o so o so} (Deloop@{o o} M) Sets@{o so}.

(* Riehl's U: evaluation at the one object of BM. *)
Definition U_BG@{o so} (M : MonObject@{o o o}) :
  SetBG@{o so} M ⟶ Sets@{o so} :=
  @Eval@{o o so o so so} (Deloop@{o o} M) Sets@{o so} ttt.

(* Riehl's left adjoint: X goes to the functor whose value is the free
   M-set M × X. *)
Definition F_BG@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ SetBG@{o so} M :=
  MSet_from@{so o o so o} M ◯ MSet_Free@{o so} M.

(* Evaluation is [MSet_to] followed by forgetting the action, in both data
   fields. *)
Example U_BG_obj@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  fobj[U_BG@{o so} M] P = fobj[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] P :=
  eq_refl.

Example U_BG_map@{o so} (M : MonObject@{o o o}) (P Q : SetBG@{o so} M)
  (η : P ~{SetBG@{o so} M}~> Q) :
  fmap[U_BG@{o so} M] η = fmap[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] η :=
  eq_refl.

(** ** The free/forgetful adjunction *)

(* A transformation φ : F X ⟹ P restricts to x ↦ φ (u, x). *)
Definition BG_restrict@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (φ : fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P) :
  X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P.
Proof.
  unshelve refine
    (@Build_SetoidMorphism X _ (fobj[P] ttt) _
       (fun x => transform[φ] ttt (mon_unit, x)) _).
  intros x y Hxy. apply (proper_morphism (transform[φ] ttt)).
  split; [ reflexivity | exact Hxy ].
Defined.

(* A map ψ : X → P ttt extends to (g, x) ↦ g · ψ x: [MSet_extend] at the
   action read off P, carried back along the round trip. *)
Definition BG_extend@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (ψ : X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P) :
  fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P :=
  to (MSet_round_iso@{so o o so o} P)
    ∘ fmap[MSet_from@{so o o so o} M]
        (@MSet_extend@{o so} M X (action_of_functor@{o o o so o} P) ψ).

Definition BG_adj_iso@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (P : SetBG@{o so} M) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
       (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
       (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P)))
       (@Build_SetoidMorphism
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (fun φ => @BG_restrict M X P φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (fun ψ => @BG_extend M X P ψ) _) _ _).
  - intros φ φ' Hφ x. exact (Hφ ttt (mon_unit, x)).
  - intros ψ ψ' Hψ [] [g x]; simpl.
    apply (proper_morphism (@fmap _ _ P ttt ttt g)). exact (Hψ x).
  - intros ψ x; simpl. exact (@fmap_id _ _ P ttt (ψ x)).
  - intros φ [] [g x]; simpl.
    transitivity
      (transform[φ] ttt
         (@fmap _ _ (fobj[F_BG@{o so} M] X) ttt ttt g (mon_unit, x))).
    + exact (@naturality _ _ _ _ φ ttt ttt g (mon_unit, x)).
    + apply (proper_morphism (transform[φ] ttt)).
      split; [ exact (mon_op_unit_r g) | reflexivity ].
Defined.

(* Riehl's adjunction, literally: F ⊣ U on Set^BM. *)
Definition BG_adj@{o so} (M : MonObject@{o o o}) :
  @Adjunction@{so o o so o o o o so o so} (SetBG@{o so} M) Sets@{o so}
    (F_BG@{o so} M) (U_BG@{o so} M).
Proof.
  unshelve refine
    (@Build_Adjunction' (SetBG@{o so} M) Sets@{o so}
       (F_BG@{o so} M) (U_BG@{o so} M) (fun X P => BG_adj_iso M X P) _ _).
  - intros X Y P f g x; simpl. reflexivity.
  - intros X P Q f g x; simpl. reflexivity.
Defined.

(** ** Creation of U-split coequalizers, transported from M-sets *)

(* A cofork of transformations whose [MSet_to]-image is a coequalizer of
   M-sets is a coequalizer of functors: the descended equivariant map is
   the one component of the descended transformation. *)
Definition MSet_to_reflects_coeq@{o so} {M : MonObject@{o o o}}
  {P Q R : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q) (e : Q ~{SetBG@{o so} M}~> R)
  (E : @IsCoequalizer (MSet@{so so o o o o o o} M) _ _
         (fmap[MSet_to@{so o} M] p) (fmap[MSet_to@{so o} M] q)
         (fobj[MSet_to@{so o} M] R) (fmap[MSet_to@{so o} M] e)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q R e.
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros [] y. exact (cofork E y).
  - intros W h Hh.
    pose (D := coeq_desc E (fmap[MSet_to@{so o} M] h) (fun y => Hh ttt y)).
    unshelve eapply Build_Unique.
    + unshelve refine (@Build_Transform _ _ _ _ _ _ _).
      * intros []. exact (equiv_map (unique_obj D)).
      * intros [] [] g z; simpl. symmetry. exact (equivar (unique_obj D) g z).
      * intros [] [] g z; simpl. exact (equivar (unique_obj D) g z).
    + intros [] y. exact (unique_property D y).
    + intros v Hv [] z.
      exact (uniqueness D (fmap[MSet_to@{so o} M] v) (fun y => Hv ttt y) z).
Defined.

(* The coequalizing transformation onto the created functor: component e,
   naturality the equivariance of Instance/Fun/Action/Monad.v's
   [CreatedE]. *)
Definition BGCreatedE@{o so} {M : MonObject@{o o o}} {P Q : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  Q ~{SetBG@{o so} M}~>
    fobj[MSet_from@{so o o so o} M]
      (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
         (fmap[MSet_to@{so o} M] q) S).
Proof.
  unshelve refine (@Build_Transform _ _ _ _ _ _ _).
  - intros []. exact (scoeq_e S).
  - intros [] [] g y; simpl. symmetry.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
  - intros [] [] g y; simpl.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
Defined.

(* [CreatedE_is_coeq], moved along [MSet_action_round_iso] and read back
   through [MSet_to]. *)
Definition BGCreatedE_is_coeq@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q
    (fobj[MSet_from@{so o o so o} M]
       (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
          (fmap[MSet_to@{so o} M] q) S))
    (BGCreatedE@{o so} p q S).
Proof.
  apply MSet_to_reflects_coeq.
  refine (coequalizer_along_iso _ _ _
            (CreatedE_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
               (fmap[MSet_to@{so o} M] q) S)
            (MSet_action_round_iso
               (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                  (fmap[MSet_to@{so o} M] q) S))
            (fmap[MSet_to@{so o} M] (BGCreatedE@{o so} p q S)) _).
  intros y. reflexivity.
Defined.

Definition U_BG_creates@{o so} (M : MonObject@{o o o}) :
  CreatesUSplitCoequalizers (U_BG@{o so} M).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros P Q p q S.
    exists (fobj[MSet_from@{so o o so o} M]
              (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                 (fmap[MSet_to@{so o} M] q) S)).
    exists (BGCreatedE@{o so} p q S).
    split.
    + exact (BGCreatedE_is_coeq@{o so} p q S).
    + exists (@iso_id Sets@{o so} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros P Q p q S R e He i Hi.
    apply MSet_to_reflects_coeq.
    refine (Reflected_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
              (fmap[MSet_to@{so o} M] q) S (fobj[MSet_to@{so o} M] R)
              (fmap[MSet_to@{so o} M] e) _ i Hi).
    intros y. exact (He ttt y).
Defined.

(* The lift is on the nose: value Z, action e (g · s z), arrow e and the
   identity comparison isomorphism. *)
Example bg_created_carrier@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  fobj[`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S)] ttt
  = scoeq_obj S := eq_refl.

Example bg_created_action@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q))
  (g : carrier M) (z : carrier (scoeq_obj S)) :
  @fmap _ _ (`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))
    ttt ttt g z
  = scoeq_e S (@fmap _ _ Q ttt ttt g (scoeq_s S z)) := eq_refl.

Example bg_created_arrow@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  transform[`1 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))]
    ttt
  = scoeq_e S := eq_refl.

Example bg_created_iso@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))))
  = @iso_id Sets@{o so} (scoeq_obj S) := eq_refl.

(** ** Riehl's Exercise 5.5.iv, literally, by the monadicity theorem *)

Definition BG_beck_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (BG_adj@{o so} M)) :=
  beck_monadicity (BG_adj@{o so} M) (U_BG_creates@{o so} M).

Definition U_BG_Monadic@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} M) Sets@{o so}
    (U_BG@{o so} M).
Proof.
  exists (F_BG@{o so} M).
  exists (BG_adj@{o so} M).
  exact (BG_beck_equivalence@{o so} M).
Defined.

(* A transformation invertible at the one object is invertible. *)
Definition U_BG_reflects@{o so} (M : MonObject@{o o o}) :
  ReflectsIsos (U_BG@{o so} M) :=
  creates_split_reflects_isos _ (U_BG_creates@{o so} M).

(** ** The induced monad *)

Definition BGMonad@{o so} (M : MonObject@{o o o}) :
  @Monad Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) :=
  Adjunction_Induced_Monad (BG_adj@{o so} M).

(* Set^BM is isomorphic in Cat to the algebras of its monad, by the
   comparison functor itself. *)
Definition BG_EM_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o} (SetBG@{o so} M)
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (BG_beck_equivalence@{o so} M).

Example BG_EM_iso_to@{o so c} (M : MonObject@{o o o}) :
  to (BG_EM_iso@{o so c} M) = EM_Comparison (BG_adj@{o so} M) := eq_refl.

(* The monad read back: T X = M × X, T f = M × f, η x = (u u, x) and
   μ (g₁, (g₂, x)) = (g₁ g₂, x). *)
Example BG_T_obj@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  fobj[U_BG@{o so} M ◯ F_BG@{o so} M] X = act_prod M X := eq_refl.

Example BG_T_map@{o so} (M : MonObject@{o o o}) (X Y : SetoidObject@{o o})
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[U_BG@{o so} M ◯ F_BG@{o so} M] f = act_prod_map M f := eq_refl.

Example BG_ret@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x = (mon_op mon_unit mon_unit, x) :=
  eq_refl.

Example BG_join@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (BGMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(* The same two readbacks as functions, which is stronger, since Coq's
   [prod] has no eta. *)
Example BG_ret_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun x : carrier X => (@ret _ _ (BGMonad@{o so} M) X) x)
  = (fun x => (mon_op mon_unit mon_unit, x)) := eq_refl.

Example BG_join_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (BGMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

(** ** Against the monad of Instance/Fun/Action/Monad.v *)

(* The two functors, with identity components. *)
Definition BG_T_ActF@{o so} (M : MonObject@{o o o}) :
  U_BG@{o so} M ◯ F_BG@{o so} M ≈ ActF@{o so} M.
Proof.
  exists (fun X => @iso_id Sets@{o so} (act_prod M X)).
  intros X Y f p. simpl. split; reflexivity.
Defined.

(* The two units, by the unit law of M. *)
Definition BG_ret_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x ≈ (@ret _ _ (ActMonad@{o so} M) X) x.
Proof.
  split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
Defined.

(* The two multiplications, on the nose at every triple. *)
Example BG_join_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (p : carrier M * (carrier M * carrier X)) :
  (@join _ _ (BGMonad@{o so} M) X) p = (@join _ _ (ActMonad@{o so} M) X) p :=
  eq_refl.

(** ** The tie: θ* from the algebras of [BGMonad] to those of [ActMonad] *)

(* An algebra of [BGMonad M] is one of [ActMonad M] with the same
   structure map; the unit law moves along mon_op_unit_l. *)
Definition BG_Act_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
         (BGMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a
       (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_op mon_unit mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(* The same reading the other way; it is not assembled into a functor. *)
Definition Act_BG_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
       (BGMonad@{o so} M) a (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(* Mac Lane's θ*, for the identity-component isomorphism [BG_T_ActF]:
   the identity on carriers, structure maps and arrows. *)
Definition BG_Act_EM@{o so} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
      (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (fun x => (`1 x; BG_Act_alg M (`1 x) (`2 x)))
       (fun x y f =>
          @Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
            (`1 x) (`1 y) (BG_Act_alg M (`1 x) (`2 x))
            (BG_Act_alg M (`1 y) (`2 y)) (@t_alg_hom _ _ _ _ _ _ _ f)
            (@t_alg_hom_commutes _ _ _ _ _ _ _ f)) _ _ _).
  - intros x y f g E. exact E.
  - intros x z. reflexivity.
  - intros x y z f g w. reflexivity.
Defined.

Example BG_Act_EM_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[BG_Act_EM@{o so} M] x) = `1 x := eq_refl.

Example BG_Act_EM_alg@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) = @t_alg _ _ _ _ (`2 x) :=
  eq_refl.

(* Mac Lane's G^T ∘ θ* = G^T', on the nose in both data fields. *)
Example BG_Act_EM_forget_obj@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  fobj[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] x
  = fobj[@EM_Forget _ _ (BGMonad@{o so} M)] x := eq_refl.

Example BG_Act_EM_forget_map@{o so} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  fmap[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] f
  = fmap[@EM_Forget _ _ (BGMonad@{o so} M)] f := eq_refl.

(* The tie on objects: θ* after this file's comparison functor, against
   the comparison functor of [MSet_adj] after [MSet_to], the [to] leg of
   [Fun_EM_iso]. *)
Example tie_carrier@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  `1 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)
  = `1 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P) :=
  eq_refl.

Example tie_alg@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M)
  (g : carrier M) (z : carrier (fobj[P] ttt)) :
  @t_alg _ _ _ _
    (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P))
    (g, z)
  = @t_alg _ _ _ _
      (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
      (g, z) := eq_refl.

(* The same, as a function of the pair. *)
Example tie_alg_fun@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  (fun p => @t_alg _ _ _ _
     (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)) p)
  = (fun p => @t_alg _ _ _ _
       (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
       p) := eq_refl.

(* The tie as a functor, in Cat, with identity components. *)
Definition tie@{o so c} (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o} (SetBG@{o so} M)
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M))
    (to (Fun_EM_iso@{o so c} M)).
Proof.
  unshelve eexists.
  - intros P.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + intros z. simpl. reflexivity.
    + intros z. simpl. reflexivity.
  - intros P Q f z. simpl. reflexivity.
Defined.

(** ** Groups *)

(* Riehl's statement for a group G, at Construction/Deloop.v's groups. *)
Definition GSet_BG_Monadic@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} G) Sets@{o so}
    (U_BG@{o so} G) :=
  U_BG_Monadic@{o so} G.

(* At Instance/Grp.v's groups, through Instance/Grp/Free.v's
   [grp_deloop_monoid]. *)
Definition GSet_BG_Monadic_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so} (grp_deloop_monoid@{o o o} G)) Sets@{o so}
    (U_BG@{o so} (grp_deloop_monoid@{o o o} G)) :=
  U_BG_Monadic@{o so} (grp_deloop_monoid@{o o o} G).

(* At Structure/Group.v's groups internal to (Sets, ×), through
   Instance/Grp.v's [GroupObject_GrpObject], which asks that the
   carrier's ≈ be a proposition. *)
Definition GSet_BG_Monadic_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)))
    Sets@{o so}
    (U_BG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  U_BG_Monadic@{o so}
    (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).
