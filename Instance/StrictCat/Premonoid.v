Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Construction.Funny.Swap.
Require Import Category.Construction.Funny.Associator.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Binoidal.

Generalizable All Variables.

(** * Strict premonoidal structures as monoid objects in (StrictCat, □)

    The funny bridge: a strict premonoidal structure on a category [c] is
    precisely a monoid object in the symmetric monoidal category
    [(StrictCat, □, 1)] of Instance/StrictCat/Funny.v.  This is the funny
    counterpart of the classical fact that a monoid in [(Cat, ∏, 1)] is a
    strict monoidal category:

      - the multiplication [mappend : c □ c ⟶ c] is a tensor that is
        functorial in each variable SEPARATELY — by the funny tensor's
        universal property (Construction/Funny.v: a functor out of [c □ c]
        is exactly a [SepFunctorial] assignment), with no interchange law
        relating the two partial actions.  This "separately functorial,
        jointly not" tensor is the binoidal core of a premonoidal category
        in the sense of Power–Robinson ("Premonoidal categories and notions
        of computation", MSCS 7(5), 1997); see also nLab, "funny tensor
        product" and "premonoidal category";
      - the unit [mempty : 1 ⟶ c] picks out the tensor unit object;
      - the monoid laws, read in StrictCat's strict hom-setoid
        [Functor_StrictEq_Setoid], say that unitality and associativity of
        the tensor hold on the nose, the comparison data being the funny
        unitors (Construction/Funny/Unitors.v) and the funny associator
        (Construction/Funny/Associator.v).  Strictness makes all of
        Power–Robinson's central coherence isomorphisms identities, so no
        centrality conditions need to be stated: this is the STRICT case of
        the premonoidal notion whose general, iso-weakened form lives in
        Structure/Premonoidal.v.

    The record [StrictPremonoidal] below spells out the three monoid laws in
    unfolded form (the field types ARE the types of [mempty_left],
    [mempty_right] and [mappend_assoc] at [(StrictCat, Funny_Monoidal, c)],
    up to definitional unfolding), so the two constructions

      [StrictPremonoidal_of_Monoid]  and  [Monoid_of_StrictPremonoidal]

    are pure repackagings, and all four data-projection round trips hold by
    [reflexivity].  The extractions [StrictPremonoidal_Binoidal] and
    [StrictPremonoidal_SepFunctorial] connect the multiplication to the
    [Binoidal] class of Structure/Binoidal.v and to the funny tensor's
    universal property, again definitionally on the generating steps.

    Universe scope.  [Funny_Monoidal@{u} : Monoidal@{u Set}] pins
    StrictCat's member categories to [Category@{Set Set Set}].  Re-declaring
    the instance at a rigid universe [v] is blocked: the compiled unitors of
    Construction/Funny/Unitors.v carry a minimized [Set] level, and
    [Build_Monoidal] at member level [v] reports the constraint [Set = v] as
    unsatisfiable (probe ProbeFunnyPoly.v — re-verified this session by
    recompiling the probe, which reproduces "Cannot enforce Set = v" at the
    [Build_Monoidal] unitor field; an earlier .vo of the probe was stale).
    Everything below therefore holds for [Set]-small carrier categories;
    lifting the restriction requires re-declaring the unitors with explicit
    universe binders in Construction/Funny/Unitors.v, which is outside this
    phase's envelope. *)

#[local] Obligation Tactic := idtac.

(** ** Strict premonoidal structures

    The three law fields are stated as strict equalities of functors, i.e.
    in [Functor_StrictEq_Setoid]: their right-hand sides are the funny
    unitors and associator, exactly as in the unfolded [MonoidObject] laws
    at [(StrictCat, Funny_Monoidal, c)].  In particular

      [to (@Funny_unit_left c)]  is definitionally [Funny_unit_left_to],
      [to (@Funny_unit_right c)] is definitionally [Funny_unit_right_to],
      [to (@Funny_assoc c c c)]  is definitionally [FunnyAssocTo],

    and [FunnyBimap F G] is definitionally [bimap[FunnyTensor] F G], so the
    types below convert to the [mempty_left]/[mempty_right]/[mappend_assoc]
    types on the nose.  The law fields are Type-valued (a
    [Functor_StrictEq_Setoid] equivalence is a sigma of an object-equality
    family and transported morphism agreement), which is why the round trips
    below compare the DATA projections and not whole records. *)

Record StrictPremonoidal (c : Category) : Type := {
  sp_tensor : (c □ c) ⟶ c;
  sp_unit   : _1 ⟶ c;

  (* left unit law: tensoring with the unit on the left is the left funny
     unitor, strictly *)
  sp_unit_left :
    @equiv _ (@Functor_StrictEq_Setoid (_1 □ c) c)
      (sp_tensor ◯ FunnyBimap sp_unit Id[c])
      (to (@Funny_unit_left c));

  (* right unit law: tensoring with the unit on the right is the right funny
     unitor, strictly *)
  sp_unit_right :
    @equiv _ (@Functor_StrictEq_Setoid (c □ _1) c)
      (sp_tensor ◯ FunnyBimap Id[c] sp_unit)
      (to (@Funny_unit_right c));

  (* associativity: the two reassociated double tensors agree across the
     funny associator, strictly *)
  sp_assoc :
    @equiv _ (@Functor_StrictEq_Setoid ((c □ c) □ c) c)
      (sp_tensor ◯ FunnyBimap sp_tensor Id[c])
      ((sp_tensor ◯ FunnyBimap Id[c] sp_tensor) ◯ to (@Funny_assoc c c c))
}.

Arguments sp_tensor {c} _.
Arguments sp_unit {c} _.
Arguments sp_unit_left {c} _.
Arguments sp_unit_right {c} _.
Arguments sp_assoc {c} _.

(** ** The correspondence

    Both directions are pure repackagings: the record fields were stated as
    the unfolded monoid-object laws, so each construction is an explicit
    constructor application whose arguments typecheck by conversion alone. *)

Definition StrictPremonoidal_of_Monoid {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) : StrictPremonoidal c :=
  @Build_StrictPremonoidal c
    mappend[m]
    mempty[m]
    (@mempty_left StrictCat Funny_Monoidal c m)
    (@mempty_right StrictCat Funny_Monoidal c m)
    (@mappend_assoc StrictCat Funny_Monoidal c m).

Definition Monoid_of_StrictPremonoidal {c : Category}
  (p : StrictPremonoidal c) : @MonoidObject StrictCat Funny_Monoidal c :=
  @Build_MonoidObject StrictCat Funny_Monoidal c
    (sp_unit p)
    (sp_tensor p)
    (sp_unit_left p)
    (sp_unit_right p)
    (sp_assoc p).

(** ** Round trips

    The two constructions are mutually inverse on the data.  The law fields
    are Type-valued [Functor_StrictEq] witnesses, so a record-level equality
    is not the right statement; the four data-projection equalities below
    are, and each holds by [reflexivity] because both constructions are
    constructor applications and projections compute. *)

Lemma roundtrip_mempty {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mempty[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mempty[m].
Proof. reflexivity. Qed.

Lemma roundtrip_mappend {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mappend[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mappend[m].
Proof. reflexivity. Qed.

Lemma roundtrip_sp_unit {c : Category} (p : StrictPremonoidal c) :
  sp_unit (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_unit p.
Proof. reflexivity. Qed.

Lemma roundtrip_sp_tensor {c : Category} (p : StrictPremonoidal c) :
  sp_tensor (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_tensor p.
Proof. reflexivity. Qed.

(** ** The binoidal payoff

    A functor out of [c □ c] is exactly a separately-functorial tensor, so a
    strict premonoidal structure yields a [Binoidal] structure on its
    carrier: the two one-argument tensoring functors are the composites of
    [sp_tensor] with the funny injections [FunnyL]/[FunnyR].  Since
    [fobj[FunnyL d] x ≡ (x, d)] and [fmap[FunnyL d] f ≡ lstep f] hold
    definitionally (Construction/Funny.v), the [AFunctor] index of each
    injection matches [λ x, fobj[sp_tensor p] (x, y')] up to beta, and the
    whole instance is assembled with no proof obligations. *)

Definition StrictPremonoidal_Binoidal {c : Category}
  (p : StrictPremonoidal c) : @Binoidal c :=
  @Build_Binoidal c
    (fun x y : c => fobj[sp_tensor p] (x, y))
    (fun y' : c => ToAFunctor (sp_tensor p ◯ @FunnyL c c y'))
    (fun x' : c => ToAFunctor (sp_tensor p ◯ @FunnyR c c x')).

(* The extracted tensor is the object action of the multiplication, on the
   nose. *)
Corollary StrictPremonoidal_Binoidal_tensor {c : Category}
  (p : StrictPremonoidal c) (x y : c) :
  @tensor c (StrictPremonoidal_Binoidal p) x y = fobj[sp_tensor p] (x, y).
Proof. reflexivity. Qed.

(* The two partial tensoring functors act on morphisms as the multiplication
   acts on the generating steps of the funny tensor — definitionally. *)
Corollary StrictPremonoidal_inj_left_fmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (y' : c) :
  fmap[@inj_left c (StrictPremonoidal_Binoidal p) y'] f
    = @fmap (c □ c) c (sp_tensor p) (x, y') (y, y') (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_inj_right_fmap {c : Category}
  (p : StrictPremonoidal c) (x' : c) {x y : c} (f : x ~{c}~> y) :
  fmap[@inj_right c (StrictPremonoidal_Binoidal p) x'] f
    = @fmap (c □ c) c (sp_tensor p) (x', x) (x', y) (rstep f).
Proof. reflexivity. Qed.

(** ** The universal-property payoff

    The same multiplication, restricted along the generating steps, is a
    [SepFunctorial] package for the funny tensor's universal property
    (Construction/Funny.v): separately functorial data with a shared object
    map and NO interchange condition. *)

Definition StrictPremonoidal_SepFunctorial {c : Category}
  (p : StrictPremonoidal c) :
  @SepFunctorial c c c (fun x y : c => fobj[sp_tensor p] (x, y)) :=
  toSep (sp_tensor p).

(* Its actions are likewise the images of the generating steps, on the
   nose. *)
Corollary StrictPremonoidal_sf_lmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (d : c) :
  sf_lmap (StrictPremonoidal_SepFunctorial p) f d
    = @fmap (c □ c) c (sp_tensor p) (x, d) (y, d) (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_sf_rmap {c : Category}
  (p : StrictPremonoidal c) (x : c) {d d' : c} (g : d ~{c}~> d') :
  sf_rmap (StrictPremonoidal_SepFunctorial p) x g
    = @fmap (c □ c) c (sp_tensor p) (x, d) (x, d') (rstep g).
Proof. reflexivity. Qed.
