Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Funny.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * Strict equality of functors out of a funny tensor product

    [Instance/StrictCat.v] compares functors with [Functor_StrictEq_Setoid]
    (Theory/Functor.v): equal object maps, with morphism maps agreeing after
    transporting along the object equalities.  Every coherence law of the
    funny tensor product that lives over [StrictCat] therefore ends in the
    same kind of proof: two functors out of [C □ D] must be shown strictly
    equal.

    This file proves that master lemma once and for all ([Funny_strict_eq]):
    since every morphism of [C □ D] is a word in the generating steps
    [lstep]/[rstep], two functors out of [C □ D] are strictly equal as soon
    as they agree on objects and, after transport, on the generating steps.
    The word induction here is the single transport-heavy proof of the
    development; the seam helpers ([transport_id_hom], [transport_cod_comp],
    [transport_dom_comp], [transport_seam]) localize the transport
    bookkeeping so that downstream files never repeat it.

    As corollaries: the eta rule [Funny_eta] (every functor out of [C □ D]
    is recovered by [FunnyUP] from its restriction [toSep] to the generating
    steps), and the uniqueness half of the pushout universal property
    [Funny_UP_unique] (any functor agreeing with a [SepFunctorial] package
    on the generators is strictly equal to [FunnyUP] of the package).

    Precedent for the transport kit: [Compose_respects_stricteq] and the
    surrounding lemmas in Theory/Functor.v, and Instance/StrictCat/ToCat.v. *)

(** ** Seam helpers

    [transport] moves a morphism along an equality of its codomain and
    [transport_r] along an equality of its domain; note the orientation
    [transport_r B (p : a = b) : B b → B a], matching
    [Functor_StrictEq_Setoid].  Each helper is proved by path induction, so
    each holds definitionally once the equality is [eq_refl]. *)

Lemma transport_id_hom {E : Category} {a b : E} (p : a = b) :
  transport (fun z => a ~{E}~> z) p id
    ≈ transport_r (fun z => z ~{E}~> b) p id.
Proof. destruct p; simpl; reflexivity. Qed.

Lemma transport_cod_comp {E : Category} {x m w w' : E} (p : w = w')
  (u : m ~{E}~> w) (v : x ~{E}~> m) :
  transport (fun z => x ~{E}~> z) p (u ∘ v)
    = transport (fun z => m ~{E}~> z) p u ∘ v.
Proof. destruct p; reflexivity. Qed.

Lemma transport_dom_comp {E : Category} {x x' m w : E} (p : x = x')
  (u : m ~{E}~> w) (v : x' ~{E}~> m) :
  transport_r (fun z => z ~{E}~> w) p (u ∘ v)
    = u ∘ transport_r (fun z => z ~{E}~> m) p v.
Proof. destruct p; reflexivity. Qed.

(* Moving a transport across a composition seam: a domain-transport on the
   left factor equals a codomain-transport on the right factor. *)
Lemma transport_seam {E : Category} {x m m' w : E} (p : m = m')
  (u : m' ~{E}~> w) (v : x ~{E}~> m) :
  transport_r (fun z => z ~{E}~> w) p u ∘ v
    = u ∘ transport (fun z => x ~{E}~> z) p v.
Proof. destruct p; reflexivity. Qed.

(* ≈-congruence of the two transports, stated on hom-setoids directly so
   that [apply] needs no higher-order unification (cf. the instances
   [proper_transport_cod] and [proper_transport_dom] in Theory/Functor.v). *)
Lemma transport_cod_respects {E : Category} {x w w' : E} (p : w = w')
  {u v : x ~{E}~> w} :
  u ≈ v →
  transport (fun z => x ~{E}~> z) p u ≈ transport (fun z => x ~{E}~> z) p v.
Proof. intros; destruct p; assumption. Qed.

Lemma transport_dom_respects {E : Category} {x x' w : E} (p : x = x')
  {u v : x' ~{E}~> w} :
  u ≈ v →
  transport_r (fun z => z ~{E}~> w) p u
    ≈ transport_r (fun z => z ~{E}~> w) p v.
Proof. intros; destruct p; assumption. Qed.

(** ** Introduction form for [Functor_StrictEq_Setoid] *)

Definition Functor_StrictEq_intro {A B : Category} (F G : A ⟶ B)
  (eo : ∀ x : A, F x = G x)
  (em : ∀ (x y : A) (f : x ~{A}~> y),
      transport (fun z => F x ~{B}~> z) (eo y) (fmap[F] f)
        ≈ transport_r (fun z => z ~{B}~> G y) (eo x) (fmap[G] f)) :
  @equiv _ (@Functor_StrictEq_Setoid A B) F G := (eo; em).

(** ** The master lemma *)

Section FunnyStrictEq.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.
Context (H K : (C □ D) ⟶ E).
Context (eo : ∀ (c : C) (d : D), H (c, d) = K (c, d)).
Context (el : ∀ (c c' : C) (f : c ~{C}~> c') (d : D),
  transport (fun z => H (c, d) ~{E}~> z) (eo c' d)
            (@fmap (C □ D) E H (c, d) (c', d) (lstep f))
    ≈ transport_r (fun z => z ~{E}~> K (c', d)) (eo c d)
                  (@fmap (C □ D) E K (c, d) (c', d) (lstep f))).
Context (er : ∀ (c : C) (d d' : D) (g : d ~{D}~> d'),
  transport (fun z => H (c, d) ~{E}~> z) (eo c d')
            (@fmap (C □ D) E H (c, d) (c, d') (rstep g))
    ≈ transport_r (fun z => z ~{E}~> K (c, d')) (eo c d)
                  (@fmap (C □ D) E K (c, d) (c, d') (rstep g))).

(* The word induction: agreement on the generating steps extends to every
   word.  In the cons cases [fconsL f t ≡ t ∘ lstep f] holds definitionally
   ([fconsL_decomp]), so [fmap_comp] splits the word at the head; the seam
   helpers then walk both transports to the seam [(cb, da)] (resp.
   [(ca, db)]), where the induction hypothesis and [el] (resp. [er]) meet. *)
Lemma Funny_strict_eq_word {c1 : C} {d1 : D} {c2 : C} {d2 : D}
  (t : FunHom c1 d1 c2 d2) :
  transport (fun z => H (c1, d1) ~{E}~> z) (eo c2 d2)
            (@fmap (C □ D) E H (c1, d1) (c2, d2) t)
    ≈ transport_r (fun z => z ~{E}~> K (c2, d2)) (eo c1 d1)
                  (@fmap (C □ D) E K (c1, d1) (c2, d2) t).
Proof using C D E H K el eo er.
  induction t as [ c d | ca cb da f cc dc t IHt | ca da db g cc dc t IHt ].
  - (* fnil ≡ id *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_id (C □ D) E H (c, d)). }
    etransitivity.
    { apply transport_id_hom. }
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_id (C □ D) E K (c, d)).
  - (* fconsL f t ≡ t ∘ lstep f *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_comp (C □ D) E H (ca, da) (cb, da) (cc, dc) t (lstep f)). }
    rewrite transport_cod_comp.
    etransitivity.
    { apply compose_respects; [ exact IHt | reflexivity ]. }
    rewrite transport_seam.
    etransitivity.
    { apply compose_respects; [ reflexivity | exact (el ca cb f da) ]. }
    rewrite <- transport_dom_comp.
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_comp (C □ D) E K (ca, da) (cb, da) (cc, dc) t (lstep f)).
  - (* fconsR g t ≡ t ∘ rstep g *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_comp (C □ D) E H (ca, da) (ca, db) (cc, dc) t (rstep g)). }
    rewrite transport_cod_comp.
    etransitivity.
    { apply compose_respects; [ exact IHt | reflexivity ]. }
    rewrite transport_seam.
    etransitivity.
    { apply compose_respects; [ reflexivity | exact (er ca da db g) ]. }
    rewrite <- transport_dom_comp.
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_comp (C □ D) E K (ca, da) (ca, db) (cc, dc) t (rstep g)).
Qed.

(* In applications [eo] is typically [fun _ _ => eq_refl] (or a pair/unit
   destruct), making the transports in [el]/[er] vanish definitionally.  The
   object component needs the pair match because [prod] has no definitional
   eta. *)
Theorem Funny_strict_eq : @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H K.
Proof using C D E H K el eo er.
  refine (Functor_StrictEq_intro H K
            (fun x => match x as p return (H p = K p) with
                      | (c, d) => eo c d
                      end) _).
  intros [c1 d1] [c2 d2] t.
  exact (Funny_strict_eq_word t).
Qed.

End FunnyStrictEq.

(** ** Eta: a functor out of [C □ D] is determined by the generating steps *)

Corollary Funny_eta {C D E : Category} (H : (C □ D) ⟶ E) :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H (FunnyUP (toSep H)).
Proof.
  apply (Funny_strict_eq H (FunnyUP (toSep H)) (fun _ _ => eq_refl)).
  - intros c c' f d.
    symmetry.
    exact (id_left (@fmap (C □ D) E H (c, d) (c', d) (lstep f))).
  - intros c d d' g.
    symmetry.
    exact (id_left (@fmap (C □ D) E H (c, d) (c, d') (rstep g))).
Qed.

(** ** Uniqueness half of the pushout universal property *)

Corollary Funny_UP_unique {C D E : Category} {h : C → D → E}
  (S : SepFunctorial h) (H : (C □ D) ⟶ E)
  (eo : ∀ (c : C) (d : D), H (c, d) = h c d)
  (el : ∀ (c c' : C) (f : c ~{C}~> c') (d : D),
      transport (fun z => H (c, d) ~{E}~> z) (eo c' d)
                (@fmap (C □ D) E H (c, d) (c', d) (lstep f))
        ≈ transport_r (fun z => z ~{E}~> h c' d) (eo c d) (sf_lmap S f d))
  (er : ∀ (c : C) (d d' : D) (g : d ~{D}~> d'),
      transport (fun z => H (c, d) ~{E}~> z) (eo c d')
                (@fmap (C □ D) E H (c, d) (c, d') (rstep g))
        ≈ transport_r (fun z => z ~{E}~> h c d') (eo c d) (sf_rmap S c g)) :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H (FunnyUP S).
Proof.
  apply (Funny_strict_eq H (FunnyUP S) eo).
  - intros c c' f d.
    etransitivity; [ exact (el c c' f d) |].
    apply transport_dom_respects.
    symmetry.
    exact (FunnyUP_lstep S (d:=d) f).
  - intros c d d' g.
    etransitivity; [ exact (er c d d' g) |].
    apply transport_dom_respects.
    symmetry.
    exact (FunnyUP_rstep S (c:=c) g).
Qed.
