Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.

(* [Monad] and [FAlg] are required only so that the two formability
   statements at the end of the file — [Powerset_Prop_Monad_statement] and
   [Powerset_Prop_FAlg] — can be entered into the environment.  Neither
   module depends on anything under Instance/, and nothing in the tree
   imports this file, so no cycle is introduced. *)
Require Import Category.Theory.Monad.
Require Import Category.Construction.FAlg.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * The covariant and contravariant power-set functors on [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/power+set
   Wikipedia: https://en.wikipedia.org/wiki/Power_set

   The power set of a set is the set of its subsets, and it carries two
   actions on functions.  Covariantly, a function f : X → Y sends a subset
   S ⊆ X to its DIRECT image f S = { y | ∃ x ∈ S, f x = y }, giving an
   endofunctor of Set; contravariantly, it sends a subset T ⊆ Y to its
   INVERSE image f^{-1} T = { x | f x ∈ T }, giving a functor Set^op ⟶ Set.
   This file builds both, together with the singleton transformation whose
   components pick out {a}, over TWO carriers of subsets — one
   proof-relevant, one truncated — for reasons set out below.

   ATTRIBUTION, and what was and was not consulted.  The construction is
   the first worked example of a functor in Mac Lane, "Categories for the
   Working Mathematician", 2nd ed. (GTM 5), §I.3, printed p. 13, with the
   contravariant companion at §II.2, printed p. 33; it is also Awodey,
   "Category Theory", §5.6, printed p. 120, and Riehl, "Category Theory in
   Context", §1.3 Example 1.3.2(i), with the singleton transformation at
   §1.4 Example 1.4.4(iii).  Both the section-and-page coordinates AND the
   one-line descriptions of what those passages contain are reproduced from
   the catalogue entry of the issue this file answers
   (jwiegley/category-theory#227).  The printed texts themselves were not
   consulted while writing this file, so every statement here about their
   content is the issue's characterization rather than a reading of the
   books.  The mathematical content below stands on its own proofs.

   WHAT IS ALREADY IN THE TREE, AND WHAT IS NEW HERE.  Several neighbouring
   constructions exist and none of them is either of these functors.
   [Structure/Topos.v:129] defines the INTERNAL power object of an
   elementary topos, [Pow a := Ω ^ a] — an assignment on objects with no
   action on morphisms.  [Theory/Subobject/Functor.v:180] defines
   [Sub : C^op ⟶ Sets] by chosen-pullback reindexing — the categorical
   generalization of the CONTRAVARIANT construction, at the level of
   subobjects of a general category.  Closest of all,
   [Instance/Sets/Image.v:75] builds [Sets_Image f], the image of ONE
   morphism as an object of [Sets] (carrier [∃ y, ∃ x, f x ≈ y], :76),
   together with its epi/mono factorization — that is the direct image of
   the whole domain, with no action on subsets.  And [Instance/Ens.v] is a
   category of ensembles, not a functor — though its objects
   ([∃ T : Type, Ensemble T], :35, with [Ensemble T] the [Prop]-valued
   predicates on [T]) are the in-tree precedent for the truncated carrier
   below, as are [Instance/Rel.v]'s homs ([A ~> Ensemble B], :47).  What
   this file adds is the concrete Set-level pair: an honest [Functor] whose
   morphism action is the direct image, and its contravariant partner whose
   morphism action is the inverse image, over carriers of predicates on a
   setoid.

   TWO CARRIERS ARE SHIPPED, AND ONE QUESTION DECIDES WHICH A CONSUMER
   NEEDS: does it require an ENDOfunctor?  The issue's shared-module note
   records that several further constructions are filed against this same
   module (jwiegley/category-theory#227 names #466 — the power-set monad —
   and #704; its QA correction lists the full claimant set as #227, #466,
   #704, #750, #871, #1005).  Those numbers, and the issue's description of
   what each covers, are quoted and not independently audited here.  What IS
   checked here is the consequence for consumers:

     [Powerset_obj] / [Powerset] / [Powerset_op] — PROOF-RELEVANT subsets:
       predicates valued in [Type@{o}], so the power set lands one universe
       up (the next section derives this).  A consumer that maps out of the
       power set, or that wants the witness of membership to carry data,
       wants this carrier.  It is not an endofunctor, and the price is
       concrete: [@Monad Sets Powerset] and [FAlg Powerset] are both
       rejected by the universe checker, because [Theory/Monad.v:90] and
       [Construction/FAlg.v:114] each require an endofunctor.  So the
       power-set monad (#466) and any initial-algebra reading (#750) cannot
       ride on this carrier, and [Sets_Lift ⟹ Powerset] below, though it is
       the singleton family, cannot serve as a monad unit.

     [Powerset_Prop_obj] / [Powerset_Prop] — the same subsets with
       membership truncated to a [Prop], which puts the power set at the
       SAME universe as the carriers and so gives a genuine endofunctor
       [Sets ⟶ Sets].  Both [@Monad Sets Powerset_Prop] and
       [FAlg Powerset_Prop] are formable over it; the two types are entered
       into the environment at the end of this file, as
       [Powerset_Prop_Monad_statement] and [Powerset_Prop_FAlg], so that
       claim is machine-checked rather than asserted in prose.  Neither the
       monad nor an initial algebra is BUILT here — this file establishes
       only that they have become statable.

   Truncation is what buys the endofunctor, and what it costs is exactly
   proof relevance: over [Powerset_Prop] one can no longer read back WHICH
   [x ∈ S] witnessed [y ∈ f S].  That is the whole reason both carriers are
   shipped instead of one, and [Powerset_truncate] at the end of the file is
   the comparison from the proof-relevant carrier to the truncated one.  The
   design point survives either way: build the carriers here once, and let
   the rest ride on them rather than on private copies. *)

(* ------------------------------------------------------------------------ *)
(** ** Universe placement, stated precisely *)

(* A PROOF-RELEVANT predicate carrier does not fit at the level of the setoid
   it is a power set of, and the discipline adopted here is to say so in the
   type of the functor rather than to hide it.  Everything in this section is
   about that carrier; the last section of the file shows that a TRUNCATED
   carrier does fit, and what the truncation costs.  Be careful throughout
   about which universe is which.

   [Sets@{o so} : Category@{so o o}] (Instance/Sets.v:188), and a
   [Category@{o h p}] has [obj : Type@{o}].  So QUA CATEGORY the object
   universe of [Sets@{o so}] is [so]: its objects are the [SetoidObject@{o o}]s,
   and [o] is the universe of those objects' CARRIERS — the level at which
   the small sets themselves live.  The constraint [o < so] is forced
   (printed by [About Sets] as `o so |= o < so`).

   Morphism equivalence in this library is [Type]-valued: [Setoid] carries
   [equiv : crelation A] (Lib/Setoid.v:33), so for [X : SetoidObject@{o o}]
   and [x y : carrier X] the proposition [x ≈ y] is a [Type@{o}], not a
   [Prop].  If a subset of [X] is CHOSEN to be a predicate valued in
   [Type@{o}] — recording, for each element, the data of why it belongs —
   then it is exactly the carrier of [PropSetoid] (Instance/Sets/Classifier.v:151
   — carrier [Type@{o}] under [↔], which denotes [iffT] here,
   Lib/Foundation.v:72).  And [Type@{o} : Type@{o+1}], so a predicate type
   [carrier X → Type@{o}] sits at [Type@{so}], one level above the carriers.

   The word CHOSEN is doing real work there, and an earlier version of this
   header wrote "therefore" instead — see the retraction below.  Nothing
   about a [Type@{o}]-valued [≈] forces subsets to be valued where [≈] is; a
   subset only has to RESPECT [≈].

   Hence [Powerset_obj@{o so} : SetoidObject@{o o} → SetoidObject@{so so}]:
   it takes an OBJECT OF [Sets@{o so}] to an OBJECT OF [Sets@{so sso}].  The
   functors below are stated at that honest cross-universe type,

       Powerset    : Sets@{o so} ⟶ Sets@{so sso}
       Powerset_op : (Sets@{o so})^op ⟶ Sets@{so sso}

   which is the same discipline, and the same donors, as
   Instance/Sets/Classifier.v: [Setoid_Lift] (:115) re-types a
   [SetoidObject@{o o}] as a [SetoidObject@{so so}] by rebuilding it (the
   library's records are not cumulative), and [PropSetoid] (:151) is the
   truth-value setoid one level up.  Instance/Sets.v:412-428 records where
   the want of a level-[o] truth-value object first bites: the reverse
   direction of [surjectivity_is_epic] (declared :429) ends in a
   non-completing proof, discarded at :476 by the command that throws a
   proof away, so that lemma never enters the environment.

   One consequence is worth stating plainly, and stating WITH ITS SCOPE.
   Because the codomain category differs from the domain category, the
   [Type@{o}]-valued power-set functor is NOT an endofunctor, and for THIS
   carrier Riehl's transformation [Id ⟹ P] is not typeable as written:
   [Transform] requires its two functors to share both domain and codomain,
   and here it is the codomains that differ, so [@Id Sets ⟹ Powerset] is
   rejected by the universe checker, with an inconsistency of the shape
   "Cannot enforce u = v because v < u".  That rejection was checked while
   writing this file; it is not reproduced here as a command, since a
   deliberately ill-typed command in the source would trip the repository's
   hygiene grep.  For this carrier the honest form is
   [Sets_Lift ⟹ Powerset], where [Sets_Lift] is the lifting functor built
   below from Classifier.v's [Setoid_Lift]/[SetoidMorphism_Lift] — a functor
   that changes nothing but the universe: it keeps the carrier verbatim
   ([Setoid_Lift]'s [carrier] field is [carrier X], Classifier.v:116) and
   the underlying function verbatim up to η ([SetoidMorphism_Lift]'s
   function is [λ a, f a], Classifier.v:127).

   A RETRACTION, BECAUSE AN EARLIER VERSION OF THIS HEADER OVERSTATED THAT
   SCOPE.  It said that Riehl's [Id ⟹ P] "is not statable" in this library,
   full stop, and offered the universe checker as the reason for it.  That
   is withdrawn.  What the universe checker rejects is [@Id Sets ⟹ Powerset]
   for the specific [Type@{o}]-valued carrier; the general claim does not
   follow from it, and is false.  The step that does not follow is the one
   above: from "[≈] is [Type@{o}]-valued" it was inferred that a subset must
   be valued in [Type@{o}].  A [Prop]-valued predicate respects a
   [Type@{o}]-valued [≈] perfectly well, because [Type@{o} → Prop] is itself
   a [Prop] by the impredicativity of [Prop].  Taking that route — subsets
   valued in [Prop], with the direct-image existential truncated
   impredicatively by [Powerset_squash] — puts the whole power set back at
   level [o] and yields a genuine endofunctor together with Riehl's
   transformation.  Both are built in the last section of this file, as
   [Powerset_Prop] and [Powerset_Prop_Singleton], and both are
   [Print Assumptions]-clean.  The one universe cost is [Set < o], since
   [Prop : Type@{Set+1}].

   The inherited justification does not carry over either.  This header
   claimed that Instance/Sets/Classifier.v "works through the same
   obstruction".  It does not, and that file says so in its own words at
   :138-142: [Prop] (with [iff]) "would fit at level o size-wise, but could
   not receive the [Type@{o}]-valued characteristic predicate
   [λ b, ∃ a, m a ≈ b] without truncating away the witness that
   [sets_char_pullback] and [sets_char_unique] must recover".  The
   classifier's obstruction is WITNESS RECOVERY, forced on it by a pullback
   universal property; a power set carries no such obligation, so truncation
   costs it nothing it is required to have.  In-tree precedent for
   [Prop]-valued subsets at the carrier's own level: Instance/Ens.v:35,
   whose objects are [∃ T : Type, Ensemble T] with [Ensemble T] the
   [Prop]-valued predicates on [T], and Instance/Rel.v:47, whose homs are
   [A ~> Ensemble B].

   What truncation genuinely costs is proof relevance, and that is the whole
   reason both carriers are shipped: over [Powerset_Prop] one can no longer
   read back WHICH [x ∈ S] witnessed [y ∈ f S].

   No universe hacks are used: no cumulativity assumptions, no disabled
   universe checking, and every definition below is [Print Assumptions]-clean.
   Impredicativity IS used, in one place and in its standard form —
   [Powerset_squash A := ∀ Q : Prop, (A → Q) → Q] is a [Prop] precisely
   because [Prop] is impredicative, and that is what keeps the truncated
   power set at level [o].  It is a property of the ambient theory rather
   than an added assumption, and it costs no axiom.  Nothing here uses
   [funext]: subsets are compared by pointwise [↔] (or, on the truncated
   carrier, pointwise implication both ways) and setoid maps by pointwise
   [≈], which is the whole point of the setoid discipline
   (Instance/Sets.v:131-136). *)

(* ------------------------------------------------------------------------ *)
(** ** The predicate setoid [P X] *)

(* A subset of [X] is a predicate on [carrier X] that respects [≈], and two
   subsets are equivalent — [≈], never [=] — when they hold of the same
   elements.  Both halves are already available: a [SetoidMorphism] into
   [PropSetoid] IS a [≈]-respecting [Type@{o}]-valued predicate, and
   [SetoidMorphism_Setoid] compares two of them pointwise in [PropSetoid],
   i.e. by [↔].  So the predicate setoid needs no new record — it is the
   hom-setoid [Setoid_Lift X ~> PropSetoid] of [Sets@{so sso}], packaged as
   an object of that same category. *)

Definition Powerset_obj@{o so} (X : SetoidObject@{o o}) :
  SetoidObject@{so so} :=
  {| carrier   := SetoidMorphism@{so so so} (Setoid_Lift@{o so} X)
                                            PropSetoid@{o so}
   ; is_setoid := @SetoidMorphism_Setoid@{so so so}
                    (Setoid_Lift@{o so} X) PropSetoid@{o so} |}.

(* Membership is application of the predicate; this lemma is the [≈]-respect
   of a subset, in the form the proofs below want it. *)
Lemma Powerset_mem_respects@{o so} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_obj@{o so} X)) {x y : carrier X}
  (H : @equiv _ (is_setoid X) x y) : S x → S y.
Proof. exact (fst (@proper_morphism _ _ _ _ S x y H)). Defined.

(* ------------------------------------------------------------------------ *)
(** ** The lifting functor [Sets_Lift] *)

(* [Setoid_Lift] and [SetoidMorphism_Lift] of Instance/Sets/Classifier.v
   assemble into a functor from [Sets] to [Sets] one universe up.  It is the
   identity on carriers and (up to η) on underlying functions, so both
   functor laws below are a reflexivity and [fmap_respects] hands back its
   own hypothesis; its only job is to give the singleton transformation a
   domain with the right codomain category. *)

Definition Sets_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Setoid_Lift@{o so} (@SetoidMorphism_Lift@{o so}) _ _ _).
  - (* fmap respects ≈: pointwise agreement is unchanged by the lift *)
    intros X Y f g H a; exact (H a).
  - (* fmap_id *)
    intros X a; reflexivity.
  - (* fmap_comp *)
    intros X Y Z f g a; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The direct image, and the covariant functor *)

(* The direct image of [S ⊆ X] along [f : X ~> Y]: the subset of those [y]
   for which some [x ∈ S] has [f x ≈ y].  Note the [≈]: this is the image in
   the setoid sense, and respectfulness in [y] then needs nothing beyond the
   transitivity and symmetry of [≈] in [Y]. *)

Definition Powerset_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, ∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) _).
  intros y y' Hyy'; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - now transitivity y.
  - exact Hx.
  - transitivity y'; [exact Hfx | now symmetry].
Defined.

(* Taking direct images is itself a setoid map on subsets: equivalent
   subsets have equivalent images. *)
Definition Powerset_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ S, Powerset_image@{o so} f S) _).
  intros S T HST y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact (fst (HST x) Hx).
  - exact Hfx.
  - exact (snd (HST x) Hx).
  - exact Hfx.
Defined.

Lemma Powerset_map_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : X ~{Sets@{o so}}~> Y) (H : f ≈ g) :
  Powerset_map@{o so} f ≈ Powerset_map@{o so} g.
Proof.
  intros S y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - exact Hx.
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(* Functoriality.  [fmap_id]: the direct image along the identity of [S] is
   the [≈]-saturation of [S], which is [S] itself because subsets respect
   [≈]. *)
Lemma Powerset_map_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_map@{o so} (@id Sets@{o so} X) ≈ @setoid_morphism_id@{so so so}
                                              (Powerset_obj@{o so} X).
Proof.
  intros S y; split.
  - intros [x [Hx Hxy]]; exact (Powerset_mem_respects S Hxy Hx).
  - intro Hy; exists y; split; [ exact Hy | reflexivity ].
Qed.

(* [fmap_comp]: the image along a composite is the image of the image; the
   intermediate witness is [g x]. *)
Lemma Powerset_map_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> Z) (g : X ~{Sets@{o so}}~> Y) :
  Powerset_map@{o so} (f ∘[Sets@{o so}] g)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_map@{o so} f) (Powerset_map@{o so} g).
Proof.
  intros S z; split.
  - intros [x [Hx Hfg]].
    exists (g x); split.
    + exists x; split; [ exact Hx | reflexivity ].
    + exact Hfg.
  - intros [y [[x [Hx Hgy]] Hfz]].
    exists x; split.
    + exact Hx.
    + transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(* The covariant power-set functor, at the cross-universe type argued for in
   the header. *)
Definition Powerset@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Powerset_obj@{o so} (@Powerset_map@{o so}) _ _ _).
  - intros X Y f g H; exact (Powerset_map_respects@{o so} f g H).
  - intros X; exact (@Powerset_map_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_map_comp@{o so} X Y Z f g).
Defined.

(* [fmap[Powerset]] IS the direct image: the two sides are the very same
   term, so the equality is Leibniz (=) rather than ≈.  This is the same
   situation as [bimap_fmap] in Functor/Bifunctor.v:42-45, whose comment
   records the identical justification. *)
Lemma Powerset_fmap_image@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset@{o so sso}] f S = Powerset_image@{o so} f S.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The inverse image, and the contravariant functor *)

(* The inverse image of [T ⊆ X] along [f : Y ~> X] is [λ y, T (f y)] — the
   underlying function of [T] composed with that of [f].  No image
   quantifier appears, which is exactly what makes the two actions different
   (see the [Fin]-sized witnesses below). *)

Definition Powerset_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

Definition Powerset_comap@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ T, Powerset_preimage@{o so} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_comap_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : Y ~{Sets@{o so}}~> X) (H : f ≈ g) :
  Powerset_comap@{o so} f ≈ Powerset_comap@{o so} g.
Proof.
  intros T y; split; intro Ht.
  - exact (Powerset_mem_respects T (H y) Ht).
  - exact (Powerset_mem_respects T (symmetry (H y)) Ht).
Qed.

Lemma Powerset_comap_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_comap@{o so} (@id Sets@{o so} X)
    ≈ @setoid_morphism_id@{so so so} (Powerset_obj@{o so} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

(* Contravariance: the inverse image along [g ∘ f] is the inverse image
   along [f] of the inverse image along [g] — the composition order in
   [Sets] is reversed, which is what [Opposite] arranges. *)
Lemma Powerset_comap_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Z ~{Sets@{o so}}~> Y) (g : Y ~{Sets@{o so}}~> X) :
  Powerset_comap@{o so} (g ∘[Sets@{o so}] f)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_comap@{o so} f) (Powerset_comap@{o so} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* The contravariant power-set functor. *)
Definition Powerset_op@{o so sso} :
  @Functor (Sets@{o so})^op Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{so sso}
       Powerset_obj@{o so}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_comap@{o so} f) _ _ _).
  - intros X Y f g H; exact (Powerset_comap_respects@{o so} f g H).
  - intros X; exact (@Powerset_comap_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_comap_comp@{o so} X Y Z f g).
Defined.

(* As with [Powerset_fmap_image] above: the two sides are the very same
   term, so the equality here is Leibniz (=) and not ≈, on the
   Functor/Bifunctor.v:42-45 precedent.  The file has five such same-term
   equalities in all, this being the second; the other three
   ([Powerset_Prop_fmap_image], [Powerset_Prop_Lift_obj] and
   [Powerset_Prop_Lift_fmap]) are in the last section and carry the same
   justification.  Every other statement about subsets in this file uses
   [≈]. *)
Lemma Powerset_op_fmap_preimage@{o so sso} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset_op@{o so sso}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_preimage@{o so} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The singleton transformation *)

(* The subset {a}, as a predicate: [λ x, a ≈ x]. *)
Definition Powerset_singleton_pred@{o so} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ x, @equiv _ (is_setoid X) a x) _).
  intros x x' Hxx'; split; intro H.
  - now transitivity x.
  - transitivity x'; [ exact H | now symmetry ].
Defined.

Definition Powerset_singleton_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (λ a, Powerset_singleton_pred@{o so} a) _).
  intros a a' Haa' x.
  (* [Haa'] arrives at the LIFTED relation of [Setoid_Lift X]; it is
     definitionally the relation of [X] itself, and re-ascribing it here
     keeps the rest of the proof at the level of the carriers. *)
  assert (Ha : @equiv _ (is_setoid X) a a') by exact Haa'.
  split; intro H.
  - exact (transitivity (symmetry Ha) H).
  - exact (transitivity Ha H).
Defined.

(* The naturality square, componentwise: the direct image of a singleton is
   the singleton of the image.  This is where the direct image earns its
   name — the existential over [S] collapses because [S] is a singleton. *)
Lemma Powerset_image_singleton@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_singleton_pred@{o so} (f a).
Proof.
  intro y; simpl; split.
  - intros [x [Hax Hfy]].
    transitivity (f x); [ exact (proper_morphism f _ _ Hax) | exact Hfy ].
  - intro Hfa; exists a; split; [ reflexivity | exact Hfa ].
Qed.

(* Riehl's Example 1.4.4(iii) FOR THE PROOF-RELEVANT CARRIER, in its honest
   cross-universe form: not [Id ⟹ Powerset] — which for this carrier is not
   typeable, since [Id] would have to be a functor into [Sets] one level
   up — but [Sets_Lift ⟹ Powerset], with [Sets_Lift] the carrier-preserving
   lift.  Riehl's statement in its own shape, [Id ⟹ P] with both sides
   endofunctors of one [Sets], is delivered over the truncated carrier as
   [Powerset_Prop_Singleton]. *)
Definition Powerset_Singleton@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso} Sets_Lift@{o so sso} Powerset@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Sets_Lift@{o so sso} Powerset@{o so sso}
       (fun X => @Powerset_singleton_map@{o so} X) _).
  intros X Y f a.
  exact (Powerset_image_singleton@{o so} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity: the direct image is not a relabelling *)

(* The witnesses in this section are chosen against three ways of proving
   nothing.

   (1) An INJECTIVE [f] cannot witness that the direct image does anything
       interesting: [Powerset_injective_reflects] below PROVES that along an
       injective map the direct image identifies no two distinct subsets.
       So the genuine witness must use a non-injective map, and it does.

   (2) A DEGENERATE CARRIER cannot witness anything either.  The empty and
       one-element setoids are avoided entirely below: every concrete
       witness in this file uses [Fin.t 2] or [Fin.t 3] (Witness 1 and 1b
       use both, Witness 2 only [Fin.t 2]), and each witness either proves,
       or is stated next to a lemma proving, that the relevant elements are
       distinct — so no conclusion rests on a collapse of the carrier.

   (3) A statement that would hold equally of the IDENTITY functor proves
       nothing about [fmap].  [Powerset_image_moves] below exhibits an [f]
       and an [S] with [fmap[Powerset] f S ≉ S], and
       [Powerset_direct_ne_inverse] separates the covariant action from the
       contravariant one on the same input. *)

(* Distinct points have distinct singletons, and equivalent points have
   equivalent ones: [Powerset_singleton_pred] is injective up to [≈].  This
   is what turns a statement about points into a statement about subsets. *)
Lemma Powerset_singleton_faithful@{o so} {X : SetoidObject@{o o}}
  (a b : carrier X) :
  Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
    ↔ @equiv _ (is_setoid X) a b.
Proof.
  split.
  - intro H.
    exact (symmetry (fst (H a) (reflexivity a))).
  - intros Hab x; simpl; split; intro H.
    + transitivity a; [ now symmetry | exact H ].
    + transitivity b; [ exact Hab | exact H ].
Qed.

(* THE DEGENERACY THEOREM.  Along an injective map the direct image reflects
   equivalence of subsets: nothing is merged.  This is the precise sense in
   which an injective witness is "just relabelling", and the reason the
   concrete witnesses below use a non-injective map. *)
Theorem Powerset_injective_reflects@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (Hinj : ∀ a b : carrier X, f a ≈ f b → @equiv _ (is_setoid X) a b)
  (S T : carrier (Powerset_obj@{o so} X))
  (H : Powerset_image@{o so} f S ≈ Powerset_image@{o so} f T) : S ≈ T.
Proof.
  intro x; split; intro Hx.
  - destruct (fst (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects T (Hinj x' x Hfx') Hx').
  - destruct (snd (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects S (Hinj x' x Hfx') Hx').
Qed.

(* THE MERGING THEOREM.  Conversely, the direct image merges the singletons
   {a} and {b} EXACTLY when [f a ≈ f b].  Read right-to-left it says the
   direct image collapses fibres; read left-to-right it says it collapses
   nothing else, so the identification on singletons tracks the fibres of
   [f] precisely.  [Powerset_not_injective_on_subsets] below draws out the
   right-to-left corollary in full, rather than leaving it to prose. *)
Theorem Powerset_merges_fibre@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)
  ↔ f a ≈ f b.
Proof.
  split.
  - intro H.
    apply (fst (Powerset_singleton_faithful@{o so} (f a) (f b))).
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)).
    { symmetry; exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
    { exact H. }
    exact (Powerset_image_singleton@{o so} f b).
  - intro H.
    transitivity (Powerset_singleton_pred@{o so} (f a)).
    { exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_singleton_pred@{o so} (f b)).
    { exact (snd (Powerset_singleton_faithful@{o so} (f a) (f b)) H). }
    symmetry.
    exact (Powerset_image_singleton@{o so} f b).
Qed.

(* The corollary that makes the merging theorem bite, machine-checked rather
   than left as prose: if [f] identifies two DISTINCT points, then
   [fmap[Powerset] f] identifies two distinct subsets — so it is not
   injective on subsets.  ("Not injective" is taken in the positive sense,
   [∃ a b, a ≉ b ∧ f a ≈ f b], which is the sense a witness supplies; the
   negative reading offers no constructive way to extract the pair.) *)
Corollary Powerset_not_injective_on_subsets@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X)
  (Hab : @equiv _ (is_setoid X) a b → False) (Hf : f a ≈ f b) :
  (Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
     → False)
  ∧ (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
       ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
Proof.
  split.
  - intro H.
    exact (Hab (fst (Powerset_singleton_faithful@{o so} a b) H)).
  - exact (snd (Powerset_merges_fibre@{o so} f a b) Hf).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Sanity: [FinSet]-sized computations *)

(* Small finite setoids, as objects of [Sets]: the standard [Fin.t n] under
   Leibniz equality (the discrete setoid [Fin_Setoid] of Lib/Setoid.v:89 —
   the same one Instance/FinSet.v:119 runs its hom-setoids over, per that
   file's header note at :23-24).  Only [n = 2] and [n = 3] are used, so no
   witness below rests on an empty or singleton carrier.

   A note on [=] versus [≈] in this section.  Morphism equivalence is still
   [≈] everywhere: every claim about subsets, images and preimages below is
   stated with [≈].  The [=] that appears is Coq's Leibniz equality between
   ELEMENTS of [Fin.t n], and on these carriers [≈] is [=] by construction —
   [Fin_Setoid]'s [equiv] field is [eq] (Lib/Setoid.v:89-91) — so writing
   [=] there names the same relation, not a stricter one. *)

Definition fin_setoid_object (n : nat) : SetoidObject :=
  {| carrier := Fin.t n ; is_setoid := Fin_Setoid |}.

(* Every function between discrete setoids is a setoid map: [≈] is [=] on
   both sides, so respectfulness is [f_equal]. *)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid_object m ~{Sets}~> fin_setoid_object n :=
  @Build_SetoidMorphism _ (is_setoid (fin_setoid_object m))
                        _ (is_setoid (fin_setoid_object n))
                        f (fun x y H => f_equal f H).

(* [fin32] collapses the first two elements of a three-element set and sends
   the third elsewhere: 0 ↦ 0, 1 ↦ 0, 2 ↦ 1.  It is neither injective (0 and
   1 collide) nor constant (2 goes elsewhere), so neither the merging below
   nor its non-triviality is an artefact of a degenerate map. *)
Definition fin32 (i : Fin.t 3) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) Fin.F1
    (fun j => Fin.caseS' j (fun _ => Fin.t 2) Fin.F1
                (fun _ => Fin.FS Fin.F1)).

Example fin32_at_0 : fin32 Fin.F1 = Fin.F1 := eq_refl.
Example fin32_at_1 : fin32 (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example fin32_at_2 : fin32 (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

(* The three elements of [Fin.t 3] used below are pairwise distinct, and so
   are the two elements of [Fin.t 2]: the carriers are not collapsing. *)
Lemma fin3_0_ne_1 : @Fin.F1 2 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

Lemma fin2_0_ne_1 : @Fin.F1 1 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

(* WITNESS 1 (merging along a non-injective map).  {0} and {1} are distinct
   subsets of the three-element set... *)
Lemma fin32_singletons_distinct :
  Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (fin3_0_ne_1 (fst (Powerset_singleton_faithful _ _) H)).
Qed.

(* ... but [fmap[Powerset] fin32] sends them to the same subset {0}. *)
Lemma fin32_images_merge :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)).
Proof.
  exact (snd (Powerset_merges_fibre (fin_map fin32) Fin.F1 (Fin.FS Fin.F1))
             eq_refl).
Qed.

(* And the merging is not because the action is constant: the third
   singleton has a DIFFERENT image, so [fmap[Powerset] fin32] takes at least
   two values on singletons.  Together with the previous lemma, and with the
   left-to-right half of [Powerset_merges_fibre], this says that the
   identification here tracks the fibres of [fin32] and nothing more. *)
Lemma fin32_third_image_distinct :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3)
           (Fin.FS (Fin.FS Fin.F1)))
  → False.
Proof.
  intro H.
  exact (fin2_0_ne_1
           (fst (Powerset_merges_fibre (fin_map fin32) Fin.F1
                   (Fin.FS (Fin.FS Fin.F1))) H)).
Qed.

(* The direct image of a two-element subset of [Fin.t 3] is computed as
   expected: {0,1} maps onto {0}, a PROPER subset of the two-element target
   (the second lemma), so the image is not everything either. *)
Definition fin3_sub01 : carrier (Powerset_obj (fin_setoid_object 3)).
Proof.
  unshelve refine {| morphism := fun i : Fin.t 3 =>
                       (i = Fin.F1) ∨ (i = Fin.FS Fin.F1) |}.
  intros x y ->; split; intro H; exact H.
Defined.

Lemma fin32_image_sub01 :
  fmap[Powerset] (fin_map fin32) fin3_sub01
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  intro y; split.
  - intros [i [Hi Hfi]].
    destruct Hi as [H0 | H1].
    + rewrite <- Hfi, H0; reflexivity.
    + rewrite <- Hfi, H1; reflexivity.
  - intro Hy.
    exists Fin.F1; split.
    + exact (Datatypes.inl eq_refl).
    + exact Hy.
Qed.

Lemma fin32_image_sub01_proper_subset :
  fmap[Powerset] (fin_map fin32) fin3_sub01 (Fin.FS Fin.F1) → False.
Proof.
  intro H.
  exact (fin2_0_ne_1 (fst (fin32_image_sub01 (Fin.FS Fin.F1)) H)).
Qed.

(* [fin3_sub01] really does have exactly two elements, and they are
   distinct: nothing below rests on it accidentally collapsing. *)
Lemma fin3_sub01_has_0 : fin3_sub01 Fin.F1.
Proof. exact (Datatypes.inl eq_refl). Qed.

Lemma fin3_sub01_has_1 : fin3_sub01 (Fin.FS Fin.F1).
Proof. exact (Datatypes.inr eq_refl). Qed.

Lemma fin3_sub01_lacks_2 : fin3_sub01 (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate. Qed.

(* Having two distinct elements, [fin3_sub01] is equivalent to no singleton
   at all.  This is what makes the inverse-image witness below substantive:
   the direct image of a singleton is always a singleton
   ([Powerset_image_singleton]), so no direct image of a singleton can equal
   this subset. *)
Lemma fin3_sub01_not_singleton (a : Fin.t 3) :
  fin3_sub01 ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) a → False.
Proof.
  intro H.
  assert (H0 : a = Fin.F1) by exact (fst (H Fin.F1) fin3_sub01_has_0).
  assert (H1 : a = Fin.FS Fin.F1)
    by exact (fst (H (Fin.FS Fin.F1)) fin3_sub01_has_1).
  exact (fin3_0_ne_1 (eq_trans (eq_sym H0) H1)).
Qed.

(* A three-way eliminator for [Fin.t 3], assembled from the standard
   library's [Fin.caseS'] and [Fin.case0] — the same two primitives
   Instance/FinSet.v uses, at :157-169 ([fin_split], via [Fin.caseS']) and
   :223 ([FinSet_Initial], via [Fin.case0]).  No [dependent destruction] is
   used anywhere in this file, and [Print Assumptions] reports every
   constant here closed under the global context. *)
Definition fin3_case (P : Fin.t 3 → Type)
  (H0 : P Fin.F1) (H1 : P (Fin.FS Fin.F1))
  (H2 : P (Fin.FS (Fin.FS Fin.F1))) : ∀ i : Fin.t 3, P i.
Proof.
  intro i.
  apply (Fin.caseS' i P H0); intro j.
  apply (Fin.caseS' j (fun j => P (Fin.FS j)) H1); intro k.
  apply (Fin.caseS' k (fun k => P (Fin.FS (Fin.FS k))) H2); intro l.
  exact (Fin.case0 (fun l => P (Fin.FS (Fin.FS (Fin.FS l)))) l).
Defined.

(* WITNESS 1b (the inverse image along the same non-injective, NON-ENDO map).
   Pulling the singleton {0} back along [fin32] GROWS it to the two-element
   {0,1} — the fibre of 0.  This is beyond anything the direct image can do
   to a singleton: [Powerset_image_singleton] says every direct image of a
   singleton IS a singleton, and [fin3_sub01_not_singleton] says this subset
   is not one.  The map here is not an endomorphism, so the two sides even
   live in different power sets, which the covariant action could not
   arrange from this starting point. *)
Lemma fin32_preimage_sng0 :
  fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 3)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1)
    ≈ fin3_sub01.
Proof.
  refine (fin3_case
            (fun i => fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                          ~{(Sets)^op}~> fin_setoid_object 3)
                        (Powerset_singleton_pred
                           (X:=fin_setoid_object 2) Fin.F1) i
                      ↔ fin3_sub01 i) _ _ _).
  - split; intro H.
    + exact (Datatypes.inl eq_refl).
    + exact eq_refl.
  - split; intro H.
    + exact (Datatypes.inr eq_refl).
    + exact eq_refl.
  - split; intro H.
    + discriminate H.
    + destruct H; discriminate.
Qed.

(* WITNESS 2 (the action is not the identity, and not the inverse image).
   [fin_const0] is the constant map [Fin.t 2 → Fin.t 2] at 0; both actions
   then land in the same setoid [Powerset_obj (fin_setoid_object 2)], so
   they can be compared directly. *)
Definition fin_const0 : Fin.t 2 → Fin.t 2 := fun _ => Fin.F1.

Lemma fin_const0_image :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  exact (Powerset_image_singleton (fin_map fin_const0) (Fin.FS Fin.F1)).
Qed.

(* The direct image MOVES the subset {1} to {0}; the identity functor's
   action would have left it where it was. *)
Lemma Powerset_image_moves :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  apply fin2_0_ne_1.
  apply (fst (Powerset_singleton_faithful
                (X:=fin_setoid_object 2) Fin.F1 (Fin.FS Fin.F1))).
  transitivity (fmap[Powerset] (fin_map fin_const0)
                  (Powerset_singleton_pred (X:=fin_setoid_object 2)
                     (Fin.FS Fin.F1))).
  { symmetry; exact fin_const0_image. }
  exact H.
Qed.

(* The inverse image of {1} along the same constant map is EMPTY, while its
   direct image contains 0.  So on this one input, in this one power set,
   the covariant action and the contravariant action of the same morphism
   disagree. *)
Lemma fin_const0_preimage_empty (y : Fin.t 2) :
  fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 2)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)) y
  → False.
Proof. intro H; exact (fin2_0_ne_1 (eq_sym H)). Qed.

Lemma fin_const0_image_inhabited :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
      Fin.F1.
Proof. exact (snd (fin_const0_image Fin.F1) (reflexivity _)). Qed.

Theorem Powerset_direct_ne_inverse :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                           ~{(Sets)^op}~> fin_setoid_object 2)
        (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
  → False.
Proof.
  intro H.
  exact (fin_const0_preimage_empty Fin.F1
           (fst (H Fin.F1) fin_const0_image_inhabited)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The second carrier: [Prop]-valued subsets, and a genuine endofunctor *)

(* Everything above is about the proof-relevant carrier, which lands one
   universe up and so is not an endofunctor.  This section builds the other
   carrier, at the SAME universe as the sets it is a power set of, and with
   it the two things the cross-universe carrier cannot supply: an
   endofunctor of [Sets], and Riehl's Example 1.4.4(iii) in its own shape,
   [Id ⟹ P].

   The move is the one the header's retraction describes.  A subset is not
   obliged to be valued where [≈] is valued; it is only obliged to RESPECT
   [≈].  So take subsets to be [Prop]-valued and truncate the direct image's
   existential impredicatively.  [Prop] then serves as the truth-value
   object at level [o] itself, and the whole power set stays put.

   Three prices are paid here, all of them visible in the types.

     (1) PROOF RELEVANCE.  [Powerset_squash (∃ x, S x ∧ f x ≈ y)] records
         only THAT some [x] witnesses membership, never which; the
         [Type@{o}]-valued carrier above records which.  This is the reason
         both carriers are shipped.  [Powerset_truncate] at the end of this
         section is the comparison between them, and it runs from the
         proof-relevant carrier to this one.  No map in the other direction
         is built here, and none is claimed either way.

     (2) [Set < o].  [Prop : Type@{Set+1}], so a [SetoidObject@{o o}] whose
         carrier is [Prop] forces [Set < o].  That is harmless in itself,
         but it does mean the [Fin]-based witnesses of the previous section
         cannot be reused verbatim: [fin_setoid_object] is pinned at
         [SetoidObject@{Set Set}] because [Fin_Setoid] (Lib/Setoid.v:89) is
         [Setoid@{Set Set}].  Hence the separate, universe-polymorphic
         [Powerset_Prop_fin_object] below, which is the only reason it
         exists.

     (3) [Powerset_Prop_truth]'s equivalence is [Prop]-valued (Coq's [/\] of
         the two implications), where [PropSetoid]'s is [Type]-valued
         ([↔] = [iffT]).  So the projections of an [≈] between two subsets
         are [proj1]/[proj2] in this section and [fst]/[snd] above.  The
         proofs below use [hnf in H] where a hypothesis whose type is a
         [Powerset_squash] arrives still wrapped in the constant that
         produced it.

   Nothing else changes: [≈] is still how morphisms and subsets are compared
   here (apart from the same-term [=] lemmas, which are flagged individually
   where they occur), no axiom is used, and no [funext]. *)

(* Propositional truncation, impredicatively.  [∀ Q : Prop, (A → Q) → Q] is
   a [Prop] whatever universe [A] lives in, which is exactly what keeps the
   power set at level [o]. *)
Definition Powerset_squash@{o} (A : Type@{o}) : Prop := ∀ Q : Prop, (A → Q) → Q.

Definition Powerset_squash_intro@{o} {A : Type@{o}} (a : A) :
  Powerset_squash@{o} A := fun Q k => k a.

(* The truth-value object at level [o]: [Prop] under mutual implication.
   Assembled in the same shape as [PropSetoid] (Classifier.v:144-154), one
   universe lower.  [Prop : Type@{Set+1}], which is where the [Set < o]
   constraint comes from. *)
Definition Powerset_Prop_truth_equiv@{o} : crelation@{o o} Prop :=
  λ P Q : Prop, (P → Q) /\ (Q → P).

Lemma Powerset_Prop_truth_equivalence@{o} :
  Equivalence@{o o} Powerset_Prop_truth_equiv@{o}.
Proof.
  unfold Powerset_Prop_truth_equiv; constructor.
  - intro P; split; intro H; exact H.
  - intros P Q [HPQ HQP]; split; assumption.
  - intros P Q R [HPQ HQP] [HQR HRQ]; split; intro H; auto.
Qed.

Definition Powerset_Prop_truth@{o} : SetoidObject@{o o} :=
  {| carrier   := Prop
   ; is_setoid := {| equiv        := Powerset_Prop_truth_equiv@{o}
                   ; setoid_equiv := Powerset_Prop_truth_equivalence@{o} |} |}.

(* A truncated subset of [X] is a [≈]-respecting [Prop]-valued predicate —
   that is, a [SetoidMorphism] into [Powerset_Prop_truth], compared
   pointwise by [SetoidMorphism_Setoid], exactly as [Powerset_obj] is
   compared.  No lift appears: domain and codomain are both at [o]. *)
Definition Powerset_Prop_obj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier   := SetoidMorphism@{o o o} X Powerset_Prop_truth@{o}
   ; is_setoid := @SetoidMorphism_Setoid@{o o o} X Powerset_Prop_truth@{o} |}.

(* The direct image, truncated: [y] belongs to [f S] when SOME [x ∈ S] has
   [f x ≈ y], with the "some" squashed. *)
Definition Powerset_Prop_image@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, Powerset_squash@{o}
               (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y)) _).
  intros y y' Hyy'; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - now transitivity y.
  - transitivity y'; [ exact Hfx | now symmetry ].
Defined.

(* Equivalent subsets have equivalent images. *)
Definition Powerset_Prop_map@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ S, Powerset_Prop_image@{o} f S) _).
  intros S T HST y; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hfx.
  - exact (proj1 (HST x) Hx).
  - exact (proj2 (HST x) Hx).
Defined.

(* [fmap_respects]. *)
Lemma Powerset_Prop_map_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} X Y) (H : f ≈ g) :
  Powerset_Prop_map@{o} f ≈ Powerset_Prop_map@{o} g.
Proof.
  intros S y; split; intros Hs Q k; hnf in Hs; apply Hs; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(* [fmap_id]: as for the proof-relevant carrier, the image of [S] along the
   identity is the [≈]-saturation of [S], which is [S] because subsets
   respect [≈]. *)
Lemma Powerset_Prop_map_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_map@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof.
  intros S y; split; intro H.
  - hnf in H; apply H; intros [x [Hx Hxy]].
    exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (Powerset_squash_intro@{o} (existT _ y (H, reflexivity y))).
Qed.

(* [fmap_comp]: the intermediate witness is [g x], and the truncation goes
   through because the goal is a [Prop] at every step. *)
Lemma Powerset_Prop_map_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y Z) (g : SetoidMorphism@{o o o} X Y) :
  Powerset_Prop_map@{o} (@setoid_morphism_compose@{o o o} X Y Z f g)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_map@{o} f) (Powerset_Prop_map@{o} g).
Proof.
  intros S z; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfg]]; apply k; exists (g x); split.
    + exact (Powerset_squash_intro@{o} (existT _ x (Hx, reflexivity (g x)))).
    + exact Hfg.
  - intros [y [Hy Hfz]]; hnf in Hy; apply Hy; intros [x [Hx Hgy]]; apply k;
      exists x; split; [ exact Hx | ].
    transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(* THE ENDOFUNCTOR.  Domain and codomain are the same category, at the same
   universes — which is the whole point of this section. *)
Definition Powerset_Prop@{o so} : @Functor Sets@{o so} Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{o so}
       Powerset_Prop_obj@{o} (@Powerset_Prop_map@{o}) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_map_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_map_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_map_comp@{o} X Y Z f g).
Defined.

(* As with [Powerset_fmap_image]: the two sides are the very same term, so
   the equality is Leibniz (=) rather than ≈, on the Functor/Bifunctor.v:42-45
   precedent. *)
Lemma Powerset_Prop_fmap_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop@{o so}] f S = Powerset_Prop_image@{o} f S.
Proof. reflexivity. Qed.

(* The truncated singleton {a}: [λ x, Powerset_squash (a ≈ x)]. *)
Definition Powerset_Prop_singleton_pred@{o} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, Powerset_squash@{o} (@equiv _ (is_setoid X) a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro Ha; apply k.
  - now transitivity x.
  - transitivity x'; [ exact Ha | now symmetry ].
Defined.

Definition Powerset_Prop_singleton_map@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} X (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X)
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (λ a, Powerset_Prop_singleton_pred@{o} a) _).
  intros a a' Haa' x; split; intros H Q k; hnf in H; apply H; intro Hx; apply k.
  - transitivity a; [ now symmetry | exact Hx ].
  - transitivity a'; [ exact Haa' | exact Hx ].
Defined.

(* The naturality square, componentwise: the direct image of a singleton is
   the singleton of the image, and truncation respects that because the
   existential over a singleton collapses. *)
Lemma Powerset_Prop_image_singleton@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (a : carrier X) :
  Powerset_Prop_image@{o} f (Powerset_Prop_singleton_pred@{o} a)
    ≈ Powerset_Prop_singleton_pred@{o} (f a).
Proof.
  intro y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hax Hfy]]; hnf in Hax; apply Hax; intro Ha; apply k.
    transitivity (f x); [ exact (proper_morphism f _ _ Ha) | exact Hfy ].
  - intro Hfa; apply k; exists a; split;
      [ exact (Powerset_squash_intro@{o} (reflexivity a)) | exact Hfa ].
Qed.

(* RIEHL EXAMPLE 1.4.4(iii), IN ITS OWN SHAPE.  Both sides are endofunctors
   of one and the same [Sets@{o so}]; the naturality square is the lemma
   immediately above, and is proved, not postulated. *)
Definition Powerset_Prop_Singleton@{o so} :
  @Transform Sets@{o so} Sets@{o so} (@Id Sets@{o so}) Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{o so}
       (@Id Sets@{o so}) Powerset_Prop@{o so}
       (fun X => @Powerset_Prop_singleton_map@{o} X) _).
  intros X Y f a.
  exact (Powerset_Prop_image_singleton@{o} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The blocked consumers, unblocked *)

(* [Theory/Monad.v:90] ([Context `{M : C ⟶ C}]) and
   [Construction/FAlg.v:114] ([Program Definition FAlg `(F : C ⟶ C)]) each
   require an endofunctor, so over [Powerset] neither of the two types below
   can be formed: substituting it reports "The term "Powerset" has type
   "Sets@{a b} ⟶ Sets@{b c}" while it is expected to have type
   "Sets@{d e} ⟶ Sets@{d e}"", with the same universe inconsistency as
   before.  Over [Powerset_Prop] both types elaborate, and naming them here
   puts that claim in the environment where the type checker settles it,
   instead of leaving it as a sentence in a comment.

   These are TYPES, not constructions.  No monad structure and no initial
   algebra is built anywhere in this file; #466 and #750 remain open.  What
   has changed is that they can now be stated over a carrier that lives in
   this module. *)

Definition Powerset_Prop_Monad_statement : Type := @Monad Sets Powerset_Prop.

Definition Powerset_Prop_FAlg : Category := FAlg Powerset_Prop.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity for the truncated carrier *)

(* Truncation is the one step that could plausibly have destroyed the
   content, by collapsing distinct subsets together.  It does not, and the
   next two results say so rather than leaving it to be assumed.

   Singletons are still faithful, up to truncation: equivalent singletons
   give a squashed proof that the points are equivalent.  That is the
   analogue of [Powerset_singleton_faithful] above, with the conclusion
   squashed because on this carrier the hypothesis is. *)
Lemma Powerset_Prop_singleton_faithful@{o} {X : SetoidObject@{o o}}
  (a b : carrier X)
  (H : Powerset_Prop_singleton_pred@{o} a ≈ Powerset_Prop_singleton_pred@{o} b) :
  Powerset_squash@{o} (@equiv _ (is_setoid X) a b).
Proof.
  intros Q k.
  assert (Hba : Powerset_squash@{o} (@equiv _ (is_setoid X) b a))
    by exact (proj1 (H a) (Powerset_squash_intro@{o} (reflexivity a))).
  apply Hba; intro Hb; apply k; now symmetry.
Qed.

(* The two-element discrete setoid, universe-polymorphic.  This duplicates
   [fin_setoid_object] for exactly one reason, given in the section header:
   that one is pinned at [SetoidObject@{Set Set}], and [Powerset_Prop_truth]
   forces [Set < o]. *)
Definition Powerset_Prop_fin_object@{o} (n : nat) : SetoidObject@{o o} :=
  {| carrier   := Fin.t n
   ; is_setoid :=
       {| equiv        := @eq (Fin.t n)
        ; setoid_equiv :=
            {| Equivalence_Reflexive  := @eq_refl (Fin.t n)
             ; Equivalence_Symmetric  := @eq_sym (Fin.t n)
             ; Equivalence_Transitive := @eq_trans (Fin.t n) |} |} |}.

(* Concretely, over a two-element carrier: the truncated power set does not
   collapse.  [fin2_0_ne_1] is reused from the previous section — it is a
   statement about [Fin.t 2] alone and carries no universe of its own. *)
Lemma Powerset_Prop_singletons_distinct@{o} :
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1
    ≈ Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2)
        (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (Powerset_Prop_singleton_faithful@{o} _ _ H False fin2_0_ne_1).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Relating the two carriers *)

(* Truncation is a map from the proof-relevant power set to the [Prop]-valued
   one, and it is natural.  The component sends a [Type@{o}]-valued subset
   [S] to [λ x, Powerset_squash (S x)]; that this respects [≈] at both levels
   is the whole of the proof. *)
Definition Powerset_truncate_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X)
                            (Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_Prop_obj@{o} X))
       (Setoid_Lift_instance@{o so} (is_setoid (Powerset_Prop_obj@{o} X)))
       (fun S => _) _).
  - unshelve refine
      (@Build_SetoidMorphism@{o o o}
         (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
         (λ x, Powerset_squash@{o} (S x)) _).
    intros x x' Hxx'; split; intros H Q k; apply H; intro Hs; apply k.
    + exact (fst (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
    + exact (snd (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
  - intros S T HST x; split; intros H Q k; hnf in H; apply H; intro Hs; apply k.
    + exact (fst (HST x) Hs).
    + exact (snd (HST x) Hs).
Defined.

(* The codomain functor of that transformation is [Sets_Lift ◯ Powerset_Prop],
   assembled directly rather than through the library's [Compose].  The
   reason is a universe one, and it is about [Compose] rather than about
   either factor: its signature is

     Compose@{u u0 u1 u2 u3} :
       ∀ {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}}
         {E : Category@{u u3 u3}}, D ⟶ E → C ⟶ D → C ⟶ E

   so the three categories may differ in their OBJECT universe but share one
   hom/proof universe [u3].  Here the two categories have different hom
   universes — [Sets@{o so} : Category@{so o o}] and
   [Sets@{so sso} : Category@{sso so so}] — so [Compose] would require
   [o = so].  Only the packaging is affected: [Powerset_Prop_Lift_obj] and
   [Powerset_Prop_Lift_fmap] below check, by [reflexivity], that this functor
   IS the composite on objects and on morphisms. *)
Definition Powerset_Prop_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       (fun X => Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X))
       (fun X Y f => @SetoidMorphism_Lift@{o so}
                       (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
                       (Powerset_Prop_map@{o} f)) _ _ _).
  - intros X Y f g H S; exact (Powerset_Prop_map_respects@{o} f g H S).
  - intros X S; exact (@Powerset_Prop_map_id@{o} X S).
  - intros X Y Z f g S; exact (@Powerset_Prop_map_comp@{o} X Y Z f g S).
Defined.

(* Same-term equalities, closed by [reflexivity], on the
   Functor/Bifunctor.v:42-45 precedent: [Powerset_Prop_Lift] is the lift of
   [Powerset_Prop], object-wise and morphism-wise. *)
Lemma Powerset_Prop_Lift_obj@{o so sso} (X : SetoidObject@{o o}) :
  Powerset_Prop_Lift@{o so sso} X = Setoid_Lift@{o so} (Powerset_Prop@{o so} X).
Proof. reflexivity. Qed.

Lemma Powerset_Prop_Lift_fmap@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop_Lift@{o so sso}] f
    = @SetoidMorphism_Lift@{o so} (Powerset_Prop_obj@{o} X)
        (Powerset_Prop_obj@{o} Y) (fmap[Powerset_Prop@{o so}] f).
Proof. reflexivity. Qed.

(* THE COMPARISON.  Truncating the proof-relevant power set commutes with
   taking direct images: squashing an image is the image of the squash.  One
   direction unwraps an inner squash into the ambient [Prop] goal, the other
   wraps a witness with [Powerset_squash_intro]; both stay inside [Prop]
   throughout, which is what makes the equivalence available at all. *)
Definition Powerset_truncate@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso}
    Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}
       (fun X => @Powerset_truncate_map@{o so} X) _).
  intros X Y f S y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfx]]; hnf in Hx; apply Hx; intro Hs; apply k;
      exists x; split; [ exact Hs | exact Hfx ].
  - intros [x [Hx Hfx]]; apply k; exists x; split;
      [ exact (Powerset_squash_intro@{o} Hx) | exact Hfx ].
Defined.
