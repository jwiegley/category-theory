Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(** * Sets is well-powered and co-well-powered, and at which universe *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Subobject

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.8, book p. 130 (PDF p. 139), calls a category well-powered when the
   subobjects of each object form a small set and co-well-powered when the
   quotient objects do.  Classically [Sets] is both: the subobjects of a
   set are its subsets, named by characteristic functions, and its quotient
   objects are named by kernel relations.  mathlib's
   [CategoryTheory.WellPowered] asks that [Subobject X] be [w]-small and
   names [w] = the hom universe as the common case.
   Structure/WellPowered.v carries the definitions: the per-object record
   [WellPoweredAt x] (a small index [wp_index], maps [wp_to] and [wp_from]
   both ways, and the exhaustiveness clause [wp_to_from]), and [WellPowered],
   which PINS the index at or below the hom universe.  This file is the
   [Sets] half of the witnesses; the [Grp] one is Instance/Grp/WellPowered.v.

   WHAT IS BUILT.

   (1) [Sets] is well-powered ONE UNIVERSE UP, with nothing assumed:
   [Sets_WellPoweredAt_up X] at every setoid [X].  The index is
   [sets_pred_index X], the ≈-respecting [Type@{o}]-valued predicates on the
   carrier.  [wp_to] sends a predicate to the sub-setoid of the elements
   satisfying it, included by the first projection; [wp_from] sends a
   subobject to "has a preimage", [fun b => { a & sub_mono u a ≈ b }], with
   the preimage carried as DATA.  The domain isomorphism of [wp_to_from]
   projects that preimage, and it respects ≈ because the mono is injective
   (Instance/Sets.v's [injectivity_is_monic]).  Readback, by [eq_refl]:
   the subobject a predicate names has [{ a : carrier X & `1 P a }] as its
   carrier ([Sets_WellPoweredAt_up_carrier]).

   (2) [Sets] is co-well-powered ONE UNIVERSE UP, with nothing assumed:
   [Sets_CoWellPoweredAt_up X], a [WellPoweredAt] in [Sets^op], whose
   subobjects are Theory/Subobject/Quotient.v's [QuotObj] on the nose.  The
   index is [sets_rel_index X], the [Type@{o}]-valued equivalence relations
   coarser than ≈.  Everything is Instance/Sets/QuotObj.v's: [wp_to] is
   [SetsQuotient_QuotObj], [wp_from] is the kernel relation
   [sets_coimage_rel] of a quotient's epi, and the codomain isomorphism uses
   the preimage [Sets_quot_epi_surjective] returns -- data, because [∃] is
   [sigT] in this library.  [wp_to_from] is closed through
   [quot_equiv_iff_iso], the covariant reading of ≈ on quotient objects.

   (3) [Sets] is well-powered AT THE PIN under [Untruncate]:
   [Sets_WellPowered_untruncate : Untruncate@{o} → WellPowered Sets@{o so}].
   The index at [X] is the hom-set [X ~> Ω] of Instance/Sets/Classifier/
   OneLevel.v's conditional classifier, and it reads back by [eq_refl] as
   [X ~{Sets}~> Powerset_Omega] ([Sets_WellPoweredAt_untruncate_index]):
   Prop-valued predicates, at the carrier universe [o].  The witness IS
   Structure/WellPowered.v's generic [wp_of_classifier], applied to
   [Sets_Classifier U] over Instance/Sets/Pullback.v's [Sets_HasPullbacks]:
   [wp_to] pulls the truth subobject back along a predicate, [wp_from] is
   [char], and [wp_to_from] is Structure/SubobjectClassifier.v's
   [classifier_pullback_roundtrip], which OneLevel.v's
   [sets_pullback_roundtrip] restates at [Sets].  [untruncate_of_IEM]
   (OneLevel.v) makes this hold under informative excluded middle as
   well.
   [Untruncate@{o} := ∀ P : Type@{o}, Powerset_squash P → P] is a
   HYPOTHESIS, not an axiom: nothing is declared, and Instance/Fun/Topos.v's
   header records that it has no in-tree inhabitant and that no
   impossibility of it is proved.

   (4) The §V.8 consequence at [Sets], under the same hypothesis:
   [Sets_wellpowered_intersection U X P HP] is an [IsIntersection] (Theory/
   Subobject/Lattice.v) of the LARGE family [{ m : SubObj X & P m }], for
   any ≈-closed [Type@{o}]-valued property [P] of subobjects.  It is stated
   directly against Instance/Sets/SubobjectLattice.v's
   [Sets_HasWidePullbacks] and Lattice.v's [sub_intersection]: the wide
   pullback is taken over the SMALL index [{ i : X ~> Ω & P (wp_to i) }],
   padded with [sub_top] so that [sub_intersection]'s chosen point [None]
   always exists; the lower bound transports [P] along [wp_to_from], and
   maximality holds because the small family is a subfamily of the large
   one.  [Sets_intersection_all_empty] reads it back at [P := unit], the
   class of ALL subobjects: the intersection has an empty carrier, because
   the empty subobject [sets_sub_bot] (Instance/Sets/SubobjectLattice.v's
   [Sets_zero_monic]) is a member.

   WHY THE PINNED WITNESS USES [Untruncate]: the routes without it,
   refused.  Each refusal below was taken by appending the one command to
   a copy of this whole file and compiling it; each has an accepted
   control beside it.  They refuse particular constructions; no
   impossibility is proved (see NOT DELIVERED).

     - The index of (1) sits at [o+1] and the pin asks for [o].  Offering
       [Sets_WellPoweredAt_up X] where [WellPowered@{so o o so so}
       Sets@{o so}] is expected is refused: "The term
       "Sets_WellPoweredAt_up X" has type "WellPoweredAt@{R1.2118 R1.2117
       R1.2117 o R1.2118} X" while it is expected to have type
       "WellPoweredAt@{o so so o so} X" (universe inconsistency: Cannot
       enforce o = so because o < so)".  Control: the same witness at
       [Sets_WellPoweredAt_up@{o so so}] is accepted.
     - A [Prop]-valued index sits at [o], but it cannot rebuild the domain
       of the subobject it names: the backward map needs an ELEMENT out of
       a truncated preimage.  With [inhabited]: "Incorrect elimination of
       "proj2_sig p" in the inductive type "inhabited": the return type
       has sort "Type" while it should be SProp or Prop."  With the
       impredicative [Powerset_squash] the classifier uses: "The term "q"
       has type "∃ a : A, m a ≈ b" while it is expected to have type "?Q"
       (unable to find a well-typed instantiation for "?Q": cannot ensure
       that "Type" is a subtype of "Prop")".  Inverting exactly that
       truncation is what [Untruncate] does, and it is spent once, in
       OneLevel.v's [sce_elim].  [PropEquiv] (Lib/Setoid/Propositional.v)
       does not help: it recovers a Type-valued ≈ from a Prop one, not an
       element from an existential.
     - The consequence (4) over the index of (1) is refused where the
       pinned index is accepted: [sub_intersection] at
       [Sets_HasWidePullbacks] with the family indexed by
       [option { i : wp_index (Sets_WellPoweredAt_up X) & … }] gives
       "unable to find a well-typed instantiation for "?A": cannot ensure
       that "Type@{max(o,R3.2141)}" is a subtype of "Type@{R3.2125}"",
       and the same term over [Sets_WellPoweredAt_untruncate U X] compiles.
       The wide-pullback index of [Sets] is the carrier universe; the
       well-powered index has to fit under it, which is the pin.

   STRENGTHS.  Every comparison of subobjects and quotient objects is ≈
   (an isomorphism of domains, resp. codomains, over [X]); there is no
   Leibniz uniqueness anywhere.  The two [eq_refl] readbacks are the
   carrier of a predicate's subobject and the index of the pinned witness.

   UNIVERSES, measured with [Set Printing Universes. About …] (stdlib
   bounds such as [Projections.u0] left out):

     sets_pred_index@{o so}  : SetoidObject@{o o} → Type@{o+1}
     sets_rel_index@{o so}   : SetoidObject@{o o} → Type@{o+1}
     Sets_WellPoweredAt_up@{o so u}   : ∀ X, WellPoweredAt@{u so so o u} X
                                        (* o < so, o < u *)
     Sets_CoWellPoweredAt_up@{o so u} : ∀ X, WellPoweredAt@{u so so o u} X
                                        (* in Sets^op; o < so, o < u *)
     Sets_WellPoweredAt_untruncate@{o so u} :
       Untruncate@{o} → ∀ X, WellPoweredAt@{o so so o u} X
                                        (* Set < o, o < so, o < u *)
     Sets_WellPowered_untruncate@{o so t} :
       Untruncate@{o} → WellPowered@{so o o so t} Sets@{o so}
                                        (* Set < o, o < so, o < t *)
     Sets_wellpowered_intersection@{o so u u0} : Untruncate@{o} → …
       IsIntersection@{so o so} (λ k : ∃ m : SubObj@{so o} X, P m, `1 k) w
                                        (* Set < o, o < so, o < u, o < u0 *)

   [WellPoweredAt]'s first slot is the index universe and its fourth the
   hom universe, so (1) and (2) have the index strictly above the homs and
   (3) has it equal to them.  [Set < o] in (3) and (4) comes from
   [Powerset_Omega]'s [Prop]-valued carrier; (1) and (2) carry no [Set]
   bound.  The first setoid slot [s] of the pinned witness is [so], where
   minimization put it inside the section: a top-level binder that names
   it apart gets "so = s" added back under [+].  The second, [t], is free
   above the homs, and [Sets_WellPowered_untruncate] names it.

   MEASUREMENTS.  27 constants ([.glob] heads matched by
   '^(def|prf|thm|ind|constr|proj|rec) ') and no [Program] obligation
   ([strings] on the .vo finds no [_obligation_] name); every one reports
   "Closed under the global context" under [Print Assumptions] by its
   fully qualified name.  13 [Defined] and 2 [Qed].  Flipping each
   [Defined] to [Qed] in a copy of the whole file, ten are load-bearing
   -- a later proof or readback reads their components back -- and three
   recompile green: [sets_pred_to_from], [sets_rel_to_from] and
   [Sets_wellpowered_intersection], kept transparent because ≈ on
   subobjects is an isomorphism and an intersection is an object, both
   data.  [sets_rel_of_quot] is built in tactic form rather than as an
   anonymous pair, and the two [eq_refl] readbacks sit outside the
   sections with no universe binder: both are Coq 8.19/8.20 precautions
   (the anonymous-pair trap recorded in Instance/Grp/Quotient.v's
   comment on [SubgroupGrp], and Theory/Size.v's note on [ObjEq]), taken
   before those toolchains were run; whether either is needed there was
   not measured.

   NOT DELIVERED.  [Sets] well-powered at the pin UNCONDITIONALLY: no
   construction is given and no impossibility is proved.  [Sets]
   co-well-powered at the pin, even under [Untruncate]: not attempted.  No
   witness at [Sets@{Set _}] for (3) or (4) ([Set < o] above).  The generic
   consequence over an arbitrary complete category is Structure/
   WellPowered.v's business, not this file's; (4) is its [Sets] instance
   stated directly over the wide pullbacks [Sets] already has.  No
   [Instance] is registered.  [Ab], [RMod R] and the other algebraic
   categories are not attempted here. *)

Section SetsWellPoweredUp.

Universe o so.
Constraint o < so.

(** ** Well-powered one universe up: subobjects as Type-valued predicates *)

(* The index at [X]: the ≈-respecting [Type@{o}]-valued predicates on the
   carrier.  It lives at [o+1]. *)
Definition sets_pred_index (X : SetoidObject@{o o}) :=
  { P : carrier X → Type@{o} & ∀ a b : carrier X, a ≈ b → P a → P b }.

(* The domain of the subobject a predicate names: the elements satisfying
   it, compared on the first component. *)
Definition sets_pred_setoid (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier := { a : carrier X & `1 P a } ;
       is_setoid := {| equiv := fun p q =>
                         @equiv _ (is_setoid X) (`1 p) (`1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; symmetry; exact H.
  - intros p q r H1 H2; etransitivity; [exact H1|exact H2].
Defined.

Definition sets_pred_incl (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  sets_pred_setoid X P ~{Sets@{o so}}~> X.
Proof.
  unshelve refine {| morphism := fun p => `1 p |}.
  intros p q H; exact H.
Defined.

Lemma sets_pred_incl_monic (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @Monic Sets@{o so} _ _ (sets_pred_incl X P).
Proof.
  apply (fst (injectivity_is_monic (sets_pred_incl X P))).
  intros p q H; exact H.
Qed.

Definition sets_sub_of_pred (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X (sets_pred_setoid X P) (sets_pred_incl X P)
    (sets_pred_incl_monic X P).

(* The predicate a subobject names: "is in the image", as DATA -- the
   preimage is carried, not truncated. *)
Definition sets_pred_of_sub (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) : sets_pred_index X.
Proof.
  exists (fun b => { a : carrier (sub_dom u) & sub_mono u a ≈ b }).
  intros b b' Hb [a Ha]; exists a; etransitivity; [exact Ha|exact Hb].
Defined.

(* The domain isomorphism.  Forward: project the carried preimage;
   it respects ≈ because the mono is injective. *)
Definition sets_pred_fwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sets_pred_setoid X (sets_pred_of_sub X u) ~{Sets@{o so}}~> sub_dom u.
Proof.
  pose proof (snd (injectivity_is_monic (sub_mono u)) (sub_is_monic u)) as inj.
  unshelve refine {| morphism := fun p => `1 (`2 p) |}.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply inj. rewrite Ha, Ha'. exact H.
Defined.

Definition sets_pred_bwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sub_dom u ~{Sets@{o so}}~> sets_pred_setoid X (sets_pred_of_sub X u).
Proof.
  unshelve refine {| morphism := fun a =>
      existT (fun b => { a' : carrier (sub_dom u) &
                         @equiv _ (is_setoid X) (sub_mono u a') b })
             (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid X) (sub_mono u a')
                                                     (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _ (@setoid_equiv _ (is_setoid X))
                        (sub_mono u a))) |}.
  intros a a' H; simpl. apply proper_morphism; exact H.
Defined.

Definition sets_pred_iso (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  @Isomorphism Sets@{o so} (sets_pred_setoid X (sets_pred_of_sub X u))
    (sub_dom u).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_pred_fwd X u) (sets_pred_bwd X u)
       _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition sets_pred_to_from (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) :
  sets_sub_of_pred X (sets_pred_of_sub X u) ≈ u.
Proof.
  exists (sets_pred_iso X u).
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition Sets_WellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  {| wp_index   := sets_pred_index X ;
     wp_to      := sets_sub_of_pred X ;
     wp_from    := sets_pred_of_sub X ;
     wp_to_from := sets_pred_to_from X |}.

(** ** Co-well-powered one universe up: quotients as coarser relations *)

(* The index at [X]: the [Type@{o}]-valued equivalence relations on the
   carrier coarser than its ≈.  It lives at [o+1]. *)
Definition sets_rel_index (X : SetoidObject@{o o}) :=
  { R : crelation@{o o} (carrier X) & (Equivalence R * SetoidCoarser R)%type }.

Definition sets_quot_of_rel (X : SetoidObject@{o o}) (R : sets_rel_index X) :
  @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X (`1 R) (fst (`2 R)) (snd (`2 R)).

(* The kernel relation of a quotient's epimorphism.  Written in tactic
   form: an anonymous pair whose expected type needs unfolding
   [sets_rel_index] down to the carrier is a known Coq 8.19/8.20 trap. *)
Definition sets_rel_of_quot (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) : sets_rel_index X.
Proof.
  exists (sets_coimage_rel (quot_epi q)).
  exact (sets_coimage_rel_Equivalence (quot_epi q),
         sets_coimage_rel_coarser (quot_epi q)).
Defined.

Definition sets_rel_fwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))
    ~{Sets@{o so}}~> quot_cod q.
Proof.
  unshelve refine {| morphism := fun a => quot_epi q a |}.
  intros a b H; exact H.
Defined.

(* Backward: the preimage [Sets_quot_epi_surjective] returns is DATA,
   because [∃] is [sigT] here. *)
Definition sets_rel_bwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod q
    ~{Sets@{o so}}~> quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q)).
Proof.
  unshelve refine {| morphism := fun b => `1 (Sets_quot_epi_surjective q b) |}.
  intros b b' H; simpl; unfold sets_coimage_rel.
  rewrite (`2 (Sets_quot_epi_surjective q b)),
          (`2 (Sets_quot_epi_surjective q b')).
  exact H.
Defined.

Definition sets_rel_iso (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  @Isomorphism Sets@{o so}
    (quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))) (quot_cod q).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_rel_fwd X q) (sets_rel_bwd X q)
       _ _).
  - intro b; simpl. exact (`2 (Sets_quot_epi_surjective q b)).
  - intro a; simpl; unfold sets_coimage_rel.
    exact (`2 (Sets_quot_epi_surjective q (quot_epi q a))).
Defined.

Definition sets_rel_to_from (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) :
  sets_quot_of_rel X (sets_rel_of_quot X q) ≈ q.
Proof.
  apply (snd (quot_equiv_iff_iso _ _)).
  exists (sets_rel_iso X q).
  intro a; simpl; reflexivity.
Defined.

Definition Sets_CoWellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt (Sets@{o so}^op) X :=
  {| wp_index   := sets_rel_index X ;
     wp_to      := sets_quot_of_rel X ;
     wp_from    := sets_rel_of_quot X ;
     wp_to_from := sets_rel_to_from X |}.

End SetsWellPoweredUp.

(* Readback: the subobject named by a predicate has the satisfying
   elements as its carrier, on the nose.  The two [eq_refl] readbacks of
   this file are stated outside any section and with no universe binder:
   Theory/Size.v's note on [ObjEq] records that Leibniz [eq] under a
   universe binder with a constraint clause is refused on Coq 8.19 and
   8.20, and the sections here declare constraints. *)
Example Sets_WellPoweredAt_up_carrier (X : SetoidObject)
  (P : sets_pred_index X) :
  carrier (sub_dom (wp_to (Sets_WellPoweredAt_up X) P))
    = { a : carrier X & `1 P a } := eq_refl.

(** ** Well-powered at the pin, under [Untruncate] *)

Section SetsWellPoweredPinned.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}).

(* Structure/WellPowered.v's generic [wp_of_classifier], at the
   conditional classifier [Sets_Classifier U] over [Sets_HasPullbacks]:
   the index is the hom-set [X ~> Ω], at the hom universe [o]. *)
Definition Sets_WellPoweredAt_untruncate (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  @wp_of_classifier Sets@{o so} Sets_Terminal@{so o} Sets_HasPullbacks@{so o}
    (Sets_Classifier@{o so} U) X.

End SetsWellPoweredPinned.

Example Sets_WellPoweredAt_untruncate_index (U : Untruncate)
  (X : SetoidObject) :
  wp_index (Sets_WellPoweredAt_untruncate U X)
    = (X ~{Sets}~> Powerset_Omega) := eq_refl.

Definition Sets_WellPowered_untruncate@{o so t | o < so, Set < o, o < t +}
  (U : Untruncate@{o}) : WellPowered@{so o o so t} Sets@{o so} :=
  fun X => Sets_WellPoweredAt_untruncate U X.

(** ** The intersection of a class of subobjects, at [Sets] *)

(* Mac Lane's "any set of subobjects", read as a ≈-closed property [P] of
   subobjects of [X]: the family [{ m : SubObj X & P m }] is LARGE (it sits
   at [so]), so [Sets_HasWidePullbacks], whose index lives at the carrier
   universe [o], cannot take it directly.  The pinned witness reindexes it
   over the SMALL index [{ i : X ~> Ω & P (wp_to i) }], padded with the top
   subobject so that the chosen point [None] of [sub_intersection] always
   exists. *)

Section SetsIntersection.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}) (X : SetoidObject@{o o}).
Context (P : @SubObj Sets@{o so} X → Type@{o}).
Context (HP : ∀ m m' : @SubObj Sets@{o so} X, m ≈ m' → P m → P m').

Definition sets_wp_family :
  option { i : wp_index (Sets_WellPoweredAt_untruncate U X)
         & P (wp_to (Sets_WellPoweredAt_untruncate U X) i) } →
  @SubObj Sets@{o so} X :=
  fun j => match j with
           | None => @sub_top Sets@{o so} X
           | Some p => wp_to (Sets_WellPoweredAt_untruncate U X) (`1 p)
           end.

Definition Sets_wellpowered_intersection :
  { w : @SubObj Sets@{o so} X &
    IsIntersection (fun k : { m : @SubObj Sets@{o so} X & P m } => `1 k) w }.
Proof using U HP.
  set (W := Sets_WellPoweredAt_untruncate U X).
  exists (@sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _
            None sets_wp_family).
  pose proof (@sub_intersection_IsIntersection Sets@{o so}
                Sets_HasWidePullbacks@{o so} X _ None sets_wp_family) as H.
  constructor.
  - intros [m pm].
    pose (p := HP m _ (symmetry (wp_to_from W m)) pm).
    apply (sub_le_trans _ (sets_wp_family (Some (wp_from W m; p)))).
    + exact (inter_le _ _ H (Some (wp_from W m; p))).
    + exact (sub_le_of_equiv _ _ (wp_to_from W m)).
  - intros v Hv.
    apply (inter_greatest _ _ H).
    intros [[i pi]|]; simpl.
    + exact (Hv (wp_to W i; pi)).
    + exact (sub_top_greatest v).
Defined.

End SetsIntersection.

(* The class of ALL subobjects: its intersection is empty, because the
   empty subobject is a member.  This reads the construction back at a
   case whose answer is known. *)
Definition sets_sub_bot@{o so | o < so +} (X : SetoidObject@{o o}) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X _ _ (Sets_zero_monic X).

Lemma Sets_intersection_all_empty@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) (X : SetoidObject@{o o})
  (a : carrier (sub_dom (`1 (Sets_wellpowered_intersection U X
                               (fun _ => Datatypes.unit)
                               (fun _ _ _ t => t))))) : False.
Proof.
  destruct (inter_le _ _
              (`2 (Sets_wellpowered_intersection U X
                     (fun _ => Datatypes.unit) (fun _ _ _ t => t)))
              (sets_sub_bot X; tt)) as [k _].
  exact (match k a with end).
Qed.
