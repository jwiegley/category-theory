Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.

Generalizable All Variables.

(** * The cross-universe subobject classifier of [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/subobject+classifier
   Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   A subobject classifier for a category C is an object Ω together with a
   point true : 1 ~> Ω such that every monomorphism m : A ~> B arises as the
   pullback of true along a unique characteristic map χ_m : B ~> Ω.  This
   file proves the classifier theorems for the setoid category [Sets] — as
   honest CROSS-UNIVERSE theorems, not as a [SubobjectClassifier Sets]
   instance at a single level: the canonical candidate provably cannot fit
   at one level (below), and no other route is available here.  (That NO
   small classifier can exist over predicative Type — setoids there form a
   ΠW-pretopos, and a classifier needs impredicativity — is standard but
   is folklore relative to this development: it is not proven in-tree, and
   this file does not claim it as a theorem.)

   WHY ONE LEVEL DOES NOT SUFFICE.  Morphism equivalence `≈` in this library
   is Type@{o}-valued (a [crelation]; see Lib/Setoid.v — equivalence proofs
   may carry computational content), so the characteristic predicate of a
   mono m : A ~> B in Sets@{o so}, namely λ b, ∃ a, m a ≈ b, is itself a
   Type@{o}-valued predicate on the carrier of B.  A truth-value object able
   to receive this predicate must have carrier Type@{o} (with equivalence
   iffT), and Type@{o} : Type@{o+1} — one universe up — so the resulting
   setoid is a SetoidObject@{so so}, an object of Sets@{so sso}, and NOT an
   obj[Sets@{o so}] (which is SetoidObject@{o o}).  Taking Prop as the
   carrier instead is not an escape: landing ∃ a, m a ≈ b in Prop would
   require truncating a Type-valued sigma, and the pullback property below
   must extract the witness back out of the truth value.  This is exactly
   the size obstruction recorded at the end of Instance/Sets.v (in the note
   on the reverse direction of epis-are-surjections); this file upgrades
   that remark to the theorems it gestures at.

   WHAT IS TRUE, AND WHERE EACH PIECE LIVES:

   - [PropSetoid]      the truth-value setoid: carrier Type@{o} under iffT,
                       a SetoidObject@{so so} (o < so) — one universe up.
   - [char_setoid]     the characteristic map of m : A ~> B, a morphism
                       Setoid_Lift B ~> PropSetoid of Sets@{so sso}, where
                       [Setoid_Lift] re-types a SetoidObject@{o o} at the
                       higher level (the library's records are not
                       cumulative, so the lift is by rebuilding).
   - [sets_char_pullback]  the full pullback square, via Stability.v's
                       apex-pinned [IsPullback] in Sets@{so sso}: the lift
                       of A, with the lift of m and the terminal map, IS the
                       pullback of true along char_setoid m.  The one-level
                       IsPullback form is not statable — its ambient
                       category would have to contain PropSetoid — but the
                       apex, legs and cone quantification all live honestly
                       one level up, so nothing is weakened beyond the
                       forced lifting.
   - [sets_char_subobject]  the one-level shadow: the pullback APEX (unlike
                       the truth-value object) is small — the sub-setoid
                       {b : B & ∃ a, m a ≈ b} is [Sets_Image m] of
                       Instance/Sets/Image.v — and (A, m) is equal to it in
                       the subobject setoid [SubObj_Setoid] of B, already in
                       Sets@{o so}.
   - [sets_char_unique]    uniqueness: any χ making the lifted square a
                       pullback agrees with char_setoid m up to iff on
                       components (the hom-setoid of Sets@{so sso}).

   No universe hacks are used: no impredicativity, no cumulativity, no
   disabling of universe checking.  The universe binders below are explicit,
   and each carries only the constraints the statements force (essentially
   o < so < sso). *)

(* ------------------------------------------------------------------------ *)
(** ** Lifting setoids one universe up *)

(* [SetoidObject] is a non-cumulative record, so a SetoidObject@{o o} is not
   itself a SetoidObject@{so so} even when o ≤ so; but its carrier and
   equivalence re-typecheck at the higher level, so the lift is a rebuild.
   The carrier and the relation are definitionally unchanged. *)
(* The lift is assembled from named, universe-annotated pieces.  Writing it
   as one nested record expression makes the elaborator unify the low- and
   high-level class heads first-order, which collapses the levels to o = so;
   ascribing each piece its high-level type separately (with the class heads
   η-expanded away, so conversion goes through δ on the definitional classes
   [Reflexive]/[Symmetric]/[Transitive]) keeps the honest o ≤ so. *)

Definition equiv_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  crelation@{so so} A := λ a b, @equiv A S a b.

Definition reflexive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Reflexive@{so so} (equiv_lift@{o so} S) :=
  λ a, @Equivalence_Reflexive _ _ (@setoid_equiv _ S) a.

Definition symmetric_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Symmetric@{so so} (equiv_lift@{o so} S) :=
  λ a b Hab, @Equivalence_Symmetric _ _ (@setoid_equiv _ S) a b Hab.

Definition transitive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Transitive@{so so} (equiv_lift@{o so} S) :=
  λ a b c Hab Hbc, @Equivalence_Transitive _ _ (@setoid_equiv _ S) a b c Hab Hbc.

Definition Setoid_Lift_instance@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Setoid@{so so} A :=
  {| equiv        := equiv_lift@{o so} S
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := reflexive_lift@{o so} S
        ; Equivalence_Symmetric  := symmetric_lift@{o so} S
        ; Equivalence_Transitive := transitive_lift@{o so} S |} |}.

Definition Setoid_Lift@{o so} (X : SetoidObject@{o o}) : SetoidObject@{so so} :=
  {| carrier   := carrier X
   ; is_setoid := Setoid_Lift_instance@{o so} (is_setoid X) |}.

(* A setoid morphism between level-o setoids re-typechecks between their
   lifts: carrier function and respectfulness are reused verbatim. *)
Definition SetoidMorphism_Lift@{o so} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Setoid_Lift@{o so} Y) :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
    (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
    (λ a, f a)
    (λ a b Hab, @proper_morphism _ _ _ _ f a b Hab).

(* ------------------------------------------------------------------------ *)
(** ** The truth-value object, one universe up *)

(* The setoid of truth values: carrier Type@{o} — the type of the library's
   Type-valued propositions at level o — under bi-implication [iffT] (which
   is what `↔` denotes in this library, cf. Lib/Foundation.v).  Its carrier
   forces o < so, which is exactly the classifier's size obstruction: this
   is a SetoidObject@{so so}, i.e. an object of Sets one universe up, and
   provably not an obj[Sets@{o so}].  Prop (with `iff`) would fit at level o
   size-wise, but could not receive the Type@{o}-valued characteristic
   predicate λ b, ∃ a, m a ≈ b without truncating away the witness that
   [sets_char_pullback] and [sets_char_unique] must recover; Type@{o} with
   iffT is the strongest formulation the universe checker accepts. *)

Definition PropSetoid_equiv@{o so} : crelation@{so so} Type@{o} :=
  λ P Q : Type@{o}, P ↔ Q.

Lemma PropSetoid_equivalence@{o so} :
  Equivalence@{so so} PropSetoid_equiv@{o so}.
Proof. unfold PropSetoid_equiv; equivalence. Qed.

Definition PropSetoid@{o so} : SetoidObject@{so so} :=
  {| carrier   := Type@{o}
   ; is_setoid := {| equiv        := PropSetoid_equiv@{o so}
                   ; setoid_equiv := PropSetoid_equivalence@{o so} |} |}.

(* The point true : 1 ~> Ω, selecting the (canonically) inhabited truth
   value [poly_unit].  Any inhabited type would do, up to iffT. *)
Definition sets_true@{o so} :
  SetoidMorphism@{so so so} unit_setoid_object@{so so} PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       poly_unit@{so} unit_setoid@{so so}
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ _, poly_unit@{o}) _).
  intros ? ? ?; split; intros ?; exact ttt.
Defined.

(* The terminal map: every setoid maps to the singleton. *)
Definition sets_to_unit@{so} {X : SetoidObject@{so so}} :
  SetoidMorphism@{so so so} X unit_setoid_object@{so so} :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (is_setoid X)
    poly_unit@{so} unit_setoid@{so so}
    (λ _, ttt) (λ _ _ _, eq_refl).

(* ------------------------------------------------------------------------ *)
(** ** The characteristic map *)

(* The characteristic map of m : A ~> B sends b to the truth value
   "b is in the image of m", i.e. the Type@{o}-valued ∃ a, m a ≈ b.  It is
   a morphism of Sets ONE UNIVERSE UP: its domain is the lift of B and its
   codomain is [PropSetoid].  Note that no monicity is needed for the map
   itself to be well-defined — [Monic] enters only in the classification
   theorems below. *)
Definition char_setoid@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} B) PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ b, ∃ a : carrier A, @equiv _ (is_setoid B) (m a) b) _).
  intros b b' Hbb'; split; intros [a Ha]; exists a.
  - transitivity b.
    + exact Ha.
    + exact Hbb'.
  - transitivity b'.
    + exact Ha.
    + now symmetry.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The classifying pullback square *)

(* The full subobject-classifier pullback property, at cross-universe
   strength: in Sets@{so sso} — one level above the mono's home Sets@{o so} —
   the square

        Setoid_Lift A ── sets_to_unit ──> 1
              |                           |
     SetoidMorphism_Lift m           sets_true
              v                           v
        Setoid_Lift B ── char_setoid m ─> PropSetoid

   is a pullback in the apex-pinned sense of Theory/Morphisms/Stability.v.
   The one-level [IsPullback] form is not statable: its ambient category
   would have to contain [PropSetoid], and no obj[Sets@{o so}] can (see the
   header).  Everything else — apex, legs, and the cones quantified over —
   lives honestly at the higher level, so beyond the forced lifting nothing
   is weakened.  Monicity of m enters exactly twice: to make the mediator
   well-defined on setoids, and to make it unique. *)
Theorem sets_char_pullback@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @IsPullback Sets@{so sso}
    (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
    (char_setoid@{o so} m) sets_true@{o so}
    (Setoid_Lift@{o so} A)
    (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}.
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  constructor.
  - (* the square commutes: for a : A, "m a is in the image of m" iff ⊤ *)
    intro a; split.
    + intros _; exact ttt.
    + intros _; exists a; reflexivity.
  - (* the universal property *)
    intros Q q1 q2 Hq.
    simpl in Hq.
    (* Each x : Q comes with the truth of "q1 x is in the image of m";
       extracting its witness defines the mediator.  Monicity makes the
       extraction respect ≈. *)
    given (u : SetoidMorphism@{so so so} Q (Setoid_Lift@{o so} A)). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier A) (Setoid_Lift_instance@{o so} (is_setoid A))
           (λ x, `1 (snd (Hq x) ttt)) _).
      intros x y Hxy.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      transitivity (q1 y).
      { now apply (proper_morphism q1). }
      symmetry.
      exact (`2 (snd (Hq y) ttt)).
    }
    unshelve refine {| unique_obj := u |}.
    + split.
      * intro x; simpl.
        exact (`2 (snd (Hq x) ttt)).
      * intro x; simpl.
        now destruct (q2 x).
    + intros v [Hv1 Hv2] x.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      symmetry.
      exact (Hv1 x).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Uniqueness of the characteristic map *)

(* Any χ making the (lifted) square a pullback agrees with [char_setoid m]
   componentwise up to iff — which is exactly morphism equivalence in the
   hom-setoid of Sets@{so sso}.  Forward direction: probe the universal
   property with the subobject {b' : B & χ b'} of truth-values-of-χ; its
   mediator into the apex recovers, for each b with χ b, a preimage under m.
   Backward direction: transport the commuting square's χ (m a) ↔ ⊤ along
   m a ≈ b using the properness of χ.  Monicity of m is not needed here. *)
Theorem sets_char_unique@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B)
  (chi : Setoid_Lift@{o so} B ~{Sets@{so sso}}~> PropSetoid@{o so})
  (H : @IsPullback Sets@{so sso}
         (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
         chi sets_true@{o so}
         (Setoid_Lift@{o so} A)
         (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}) :
  chi ≈[Sets@{so sso}] char_setoid@{o so} m.
Proof.
  intro b.
  split.
  - (* χ b holds → b is in the image of m *)
    intro t.
    given (Q : SetoidObject@{so so}). {
      unshelve refine
        {| carrier   := ∃ b' : carrier B, chi b'
         ; is_setoid :=
             {| equiv := λ p q, @equiv _ (is_setoid B) (`1 p) (`1 q) |} |}.
      constructor; repeat intro.
      - reflexivity.
      - now symmetry.
      - etransitivity; eauto.
    }
    given (q1 : Q ~{Sets@{so sso}}~> Setoid_Lift@{o so} B). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
           (λ p, `1 p) (λ p q Hpq, Hpq)).
    }
    assert (Hcone : chi ∘[Sets@{so sso}] q1
                      ≈ sets_true@{o so} ∘[Sets@{so sso}] sets_to_unit@{so}). {
      intro p; split.
      - intros _; exact ttt.
      - intros _; exact (`2 p).
    }
    pose proof (is_pullback_ump H Q q1 sets_to_unit@{so} Hcone) as U.
    exists (unique_obj U (b; t)).
    exact (fst (unique_property U) (b; t)).
  - (* b is in the image of m → χ b holds *)
    intros [a Ha].
    exact (fst (@proper_morphism _ _ _ _ chi (m a) b Ha)
               (snd (is_pullback_commutes H a) ttt)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The one-level shadow: the classified subobject *)

(* While the truth-value OBJECT is forced one universe up, the pullback APEX
   is not: the sub-setoid {b : B & ∃ a, m a ≈ b} — carrier-wise the preimage
   of true under [char_setoid m] — involves only level-o data, and
   Instance/Sets/Image.v already provides it as [Sets_Image m] together with
   its monic first projection.  So at the SAME level Sets@{o so}, the
   subobject (A, m) of B equals the image subobject in the subobject setoid
   of Theory/Subobject.v.  The domain isomorphism is a ↦ (m a; (a; _)) with
   inverse (b; (a; _)) ↦ a; monicity of m makes the inverse respect ≈.
   Ends in Defined: the equivalence transports an isomorphism. *)
Theorem sets_char_subobject@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @equiv _ (@SubObj_Setoid Sets@{o so} B)
    (@Build_SubObj Sets@{o so} B A m Hm)
    (@Build_SubObj Sets@{o so} B (Sets_Image m) (Sets_Image_mono m)
       (Sets_Image_mono_monic m)).
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  (* the inverse of the epi leg, available because m is monic *)
  given (h : Sets_Image m ~{Sets@{o so}}~> A). {
    unshelve refine {| morphism := λ p, `1 `2 p |}.
    intros p q Hpq.
    apply inj.
    transitivity (`1 p).
    { exact (`2 `2 p). }
    transitivity (`1 q).
    { exact Hpq. }
    symmetry.
    exact (`2 `2 q).
  }
  given (iso : A ≅[Sets@{o so}] Sets_Image m). {
    unshelve refine {| to := Sets_Image_epi m; from := h |}.
    - (* epi ∘ h ≈ id, compared on first components *)
      intro p.
      exact (`2 `2 p).
    - (* h ∘ epi ≈ id, on the nose *)
      intro a.
      reflexivity.
  }
  exists iso.
  exact (Sets_Image_comm m).
Defined.
