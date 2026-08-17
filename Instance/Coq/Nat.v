Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Theory.Lambek.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Adamek.Corollaries.

Generalizable All Variables.

(** * The natural numbers as the initial algebra of [NatF] over COQ *)

(* nLab:      https://ncatlab.org/nlab/show/natural+numbers+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   The polynomial endofunctor [NatF X := option X = 1 + X] on COQ
   (Theory/Adamek/Corollaries.v) has the type [nat] as its initial algebra.
   The structure map [nat_alg : 1 + nat ~> nat] is [O]/[S] ([None ↦ O],
   [Some k ↦ S k]), and initiality is exactly primitive recursion: for every
   [NatF]-algebra [β : 1 + Y ~> Y] there is a unique algebra map
   [nat ~> Y], namely the fold determined by [β].  Uniqueness is the induction
   that any algebra map into [(Y, β)] agrees with the fold.

   This exhibits [nat] as the least fixed point [μ NatF]; by Lambek's lemma
   (Theory/Lambek.v) the structure map is then an isomorphism
   [1 + nat ≅ nat], recorded below as [nat_lambek].  As in Instance/Coq/Lists.v
   the development stays within pointwise equality on COQ hom-sets and ordinary
   [nat] induction, so it carries no axioms (in particular no functional
   extensionality).

   Three readings of the same theorem are carried explicitly, because the
   sources state it in three different vocabularies:

     - Mac Lane's and Riehl's TRIPLES ⟨X, x₀, f⟩.  A [NatF]-algebra
       [α : 1 + X ~> X] is precisely a point together with an endomap, and the
       commuting square of an algebra map is precisely the pair of clauses
       [h x₀ ≈ x₀'] and [h ∘ f ≈ f' ∘ h].  [alg_of_triple]/[alg_pt]/[alg_step]
       and [alg_hom_clauses]/[clauses_alg_hom] are that dictionary, stated as
       lemmas rather than left as a remark, and [nat_recursion] restates
       initiality in the resulting clause form: a unique [h] with [h O = y₀]
       and [h (S n) = f (h n)].

     - Awodey's characterisation UP TO ISOMORPHISM.  [nat_initial_unique] shows
       that any initial algebra of [NatF] is isomorphic to [(nat, [O, S])] by an
       isomorphism *of algebras* — an isomorphism in [FAlg NatF], not merely a
       bijection of carriers, which [nat_initial_carrier_unique] then reads off.

     - Riehl's REPRESENTABILITY.  [Endos := FAlg Id[Coq]] is the category of
       sets with an endomorphism, [Endos_Forget] its forgetful functor to
       [Sets], and [nat_succ_represents] the natural isomorphism exhibiting
       [(nat, S)] as a representing object with universal element [O]
       ([nat_universal_element]).  [repr_initial] is the universal-element
       criterion for this functor: a representation of [Endos_Forget] makes the
       algebra built from the representing object and its universal element
       initial in [FAlg NatF].  [nat_initial_via_universal_element] is
       a second, independent construction of the same initial object through
       that criterion (its mediator is [nat_iter], not [nat_fold]; the two
       records are distinct terms), and [nat_initial_agree] checks by
       [reflexivity] that the two constructions name the same algebra. *)

(* Where the statement comes from, and what it is used for

   nLab:      https://ncatlab.org/nlab/show/natural+numbers+object
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              Springer GTM 5, 1998, §I.5, Exercise 8, p. 21
   Book:      Awodey, "Category Theory" (1st ed., Carnegie Mellon
              pre-print, September 2005), §10.5 and Exercise 10.6.1(c)
   Book:      Riehl, "Category Theory in Context" (2nd ed. numbering,
              per issue #252),
              Example 2.1.1 and Example 2.4.11
   Paper:     Lawvere, "An elementary theory of the category of sets",
              PNAS 52, 1964
   Paper:     Lambek, "A Fixpoint Theorem for Complete Categories",
              Mathematische Zeitschrift 103, 1968

   Mac Lane poses the result as an exercise in the chapter on monics, epis
   and zeros: in the category whose objects are triples ⟨X, e, t⟩ — a set,
   a point of it, and an endomap — and whose arrows are the maps commuting
   with both, the triple ⟨ℕ, 0, successor⟩ is initial (CWM §I.5, Ex 8).
   The same universal property is the natural numbers object, a notion
   Lawvere introduced in the setting of an elementary theory of the
   category of sets: arithmetic is fixed by a mapping property and not by
   any particular set-theoretic implementation (Lawvere 1964; nLab,
   "natural numbers object").  Awodey draws the consequence that the
   classical recursion theorem IS this initiality (§10.5), and asks in
   Exercise 10.6.1(c) for the same statement in its uniqueness form, that
   the property determines ℕ up to isomorphism.

   Riehl states the identical property twice from two different angles,
   which is why this file carries two proofs of it.  Example 2.1.1
   presents ⟨X, f, x₀⟩ as a discrete dynamical system and ⟨ℕ, succ, 0⟩ as
   the initial one; Example 2.4.11 re-derives the same fact from
   representability, observing that the category of such systems is the
   category of elements of the forgetful functor from sets-with-an-
   endomorphism to sets, that this functor is represented by (ℕ, succ)
   with universal element 0, and that a universal element is initial in
   the category of elements.  In this library that category of elements
   needs no separate construction: an object of [FAlg NatF] is a carrier
   with a point and an endomap, which is exactly a pair of an object of
   [Endos] and an element of its image under [Endos_Forget], and an
   arrow of [FAlg NatF] is exactly an arrow of [Endos] carrying one point
   to the other.  [repr_initial] therefore states the criterion directly
   over [FAlg NatF]; the deviation from Riehl is one of packaging, not of
   content.  The tree carries no [el(F)] for a [Sets]-valued functor to
   instantiate instead, though the header of Construction/Grothendieck.v
   notes that restricting the Grothendieck fibres to discrete categories
   would recover it.

   The computational reading is the reason the initiality matters here.
   Lambek (1968) observed that the structure map of an initial algebra is
   invertible, so [nat] is a fixed point of [1 + (-)]; the unique algebra
   map out of it is the fold, which Theory/Recursion.v names [cata] and
   whose defining square is the recursion equation.  Instance/Coq/Lists.v
   proves the structurally identical statement one parameter up, with
   [list A] initial for [ListF A X := 1 + A × X]; [NatF] is the [A := unit]
   reading of that functor up to [unit × X ≅ X].  Theory/Adamek.v
   constructs initial algebras in general as ω-colimits, but its
   [AdamekData] leg-agreement hypothesis has no concrete in-tree witness
   (see the header of Theory/Adamek/Corollaries.v), so — as with the list
   algebra — the initial [NatF]-algebra is established here directly
   rather than through that route. *)

(* Keep obligation handling explicit and predictable, as in
   Instance/Coq/Lists.v: this file builds functor, natural-transformation and
   F-algebra-hom records whose remaining fields are commuting squares, and we
   want every one surfaced as its own obligation rather than silently
   discharged. *)
#[local] Obligation Tactic := idtac.

(** ** Mac Lane's triples: algebras of [NatF] are points with an endomap *)

(* The point of an algebra: the image of the [None] summand. *)
Definition alg_pt {X : Type} (α : FAlgebra NatF X) : X := α None.

(* The endomap of an algebra: the restriction to the [Some] summand. *)
Definition alg_step {X : Type} (α : FAlgebra NatF X) : X ~{Coq}~> X :=
  fun x => α (Some x).

(* Conversely, a point and an endomap assemble into an algebra. *)
Definition alg_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X)
  : FAlgebra NatF X :=
  fun o => match o with
           | None   => x0
           | Some x => f x
           end.

(* The two directions are mutually inverse: the triple read off an assembled
   algebra is the original triple, and the algebra assembled from the triple
   read off an algebra is the original algebra. *)

Lemma alg_pt_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_pt (alg_of_triple x0 f) = x0.
Proof. reflexivity. Qed.

Lemma alg_step_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_step (alg_of_triple x0 f) ≈ f.
Proof. intro x; reflexivity. Qed.

Lemma alg_of_triple_eta {X : Type} (α : FAlgebra NatF X) :
  alg_of_triple (alg_pt α) (alg_step α) ≈ α.
Proof. intro o; destruct o as [x|]; reflexivity. Qed.

(* At the level of arrows, the commuting square of an algebra map is exactly
   Riehl's pair of clauses: the map carries point to point and intertwines the
   two endomaps. *)

Lemma alg_hom_clauses {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h ∘ α ≈ β ∘ fmap[NatF] h ->
  (h (alg_pt α) = alg_pt β) * (∀ x, h (alg_step α x) = alg_step β (h x)).
Proof.
  intro Hh; split.
  - exact (Hh None).
  - intro x; exact (Hh (Some x)).
Qed.

Lemma clauses_alg_hom {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h (alg_pt α) = alg_pt β ->
  (∀ x, h (alg_step α x) = alg_step β (h x)) ->
  h ∘ α ≈ β ∘ fmap[NatF] h.
Proof.
  intros H0 HS o; destruct o as [x|].
  - exact (HS x).
  - exact H0.
Qed.

(** ** The algebra (nat, [O, S]) and its initiality *)

(* The structure map of the natural-numbers algebra: [None] is [O] and
   [Some k] is [S k].  This is Mac Lane's triple ⟨ℕ, 0, successor⟩. *)
Definition nat_alg : FAlgebra NatF nat := alg_of_triple O S.

(* The catamorphism (fold) determined by an algebra [β : 1 + Y ~> Y].  This is
   primitive recursion, and it is the carrier of the unique algebra map out of
   [(nat, nat_alg)]. *)
Fixpoint nat_fold {Y : Type} (beta : FAlgebra NatF Y) (n : nat) : Y :=
  match n with
  | O   => alg_pt beta
  | S k => alg_step beta (nat_fold beta k)
  end.

(* Any [NatF]-algebra map [h : (nat, nat_alg) ~> (Y, β)] coincides with the
   fold determined by [β].  This is the uniqueness half of initiality, proven
   by induction on [n] using the commuting-square hypothesis [Hh] at the two
   relevant argument shapes. *)
Lemma hom_is_nat_fold {Y : Type} (beta : FAlgebra NatF Y)
      (h : nat ~{Coq}~> Y)
      (Hh : h ∘ nat_alg ≈ beta ∘ fmap[NatF] h)
      (n : nat) : h n = nat_fold beta n.
Proof.
  induction n as [|k IH].
  - exact (Hh None).
  - simpl.
    rewrite <- IH.
    exact (Hh (Some k)).
Qed.

(* The unique algebra map from [(nat, nat_alg)] to an arbitrary algebra [y],
   packaging the fold together with its commuting square. *)
Program Definition nat_alg_hom (y : FAlg NatF)
  : (nat; nat_alg) ~{FAlg NatF}~> y :=
  {| falg_hom := nat_fold (`2 y) |}.
Next Obligation.
  (* fold ∘ nat_alg ≈ β ∘ fmap fold, checked shape by shape *)
  intros y o; destruct o as [k|]; reflexivity.
Qed.

(* [nat] together with [nat_alg] is the initial [NatF]-algebra: it is the
   terminal object of the opposite of the algebra category. *)
Program Definition nat_initial : @Initial (FAlg NatF) := {|
  terminal_obj := (nat; nat_alg);
  one := fun y => nat_alg_hom y
|}.
Next Obligation.
  (* uniqueness: any two algebra maps out of [(nat, nat_alg)] agree, since each
     coincides with the fold determined by the target algebra *)
  intros x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro n; simpl.
  rewrite (hom_is_nat_fold (`2 x) hf Hf n).
  rewrite (hom_is_nat_fold (`2 x) hg Hg n).
  reflexivity.
Qed.

(* Initiality spelled out in Riehl's clause form (Example 2.1.1): for a set
   [Y] with a point [y0] and an endomap [f] there is exactly one
   [h : nat ~> Y] with [h O = y0] and [h ∘ S ≈ f ∘ h].  This is the same
   content as [nat_initial] with the algebra packaging unwound, and it is the
   shape in which the recursion theorem is usually met. *)
Corollary nat_recursion {Y : Type} (y0 : Y) (f : Y ~{Coq}~> Y) :
  ∃! h : nat ~{Coq}~> Y, (h O = y0) * (∀ n, h (S n) = f (h n)).
Proof.
  exists (nat_fold (alg_of_triple y0 f)).
  - split; [ reflexivity | intro n; reflexivity ].
  - intros v [Hz Hs] n.
    symmetry.
    exact (hom_is_nat_fold (alg_of_triple y0 f) v
             (clauses_alg_hom nat_alg (alg_of_triple y0 f) v Hz Hs) n).
Qed.

(** ** Lambek's lemma at [nat] *)

(* The initial structure map is invertible, so [nat] is a fixed point of
   [1 + (-)]: the isomorphism [option nat ≅ nat] whose forward direction is
   [nat_alg] itself. *)
Corollary nat_lambek : NatF nat ≅ nat.
Proof. exact (lambek NatF nat_initial). Qed.

(* The same isomorphism in the orientation [nat ≅ 1 + nat]. *)
Corollary nat_lambek_sym : nat ≅ NatF nat.
Proof. exact (iso_sym nat_lambek). Qed.

(** ** Awodey Ex 10.6.1(c): the characterisation up to isomorphism *)

(* Any initial algebra of [NatF] is isomorphic to [(nat, nat_alg)] BY AN
   ISOMORPHISM OF ALGEBRAS — the isomorphism lives in [FAlg NatF], so both its
   directions are algebra maps.  The argument is the generic one for initial
   objects, spelled out inline because Structure/Initial.v carries no
   uniqueness-up-to-isomorphism lemma to appeal to — only [initial_obj],
   [zero], [zero_unique] and [zero_comp]: the two mediators compose to
   endomorphisms of initial objects, which [zero_unique] forces to be
   identities. *)
Theorem nat_initial_unique (I : @Initial (FAlg NatF)) :
  @initial_obj (FAlg NatF) I ≅[FAlg NatF] (nat; nat_alg).
Proof.
  unshelve refine {| to   := @zero (FAlg NatF) I (nat; nat_alg)
                   ; from := @zero (FAlg NatF) nat_initial
                               (@initial_obj (FAlg NatF) I) |}.
  - exact (@zero_unique (FAlg NatF) nat_initial (nat; nat_alg) _ id).
  - exact (@zero_unique (FAlg NatF) I (@initial_obj (FAlg NatF) I) _ id).
Qed.

(* Reading off the carriers: the underlying type of any initial [NatF]-algebra
   is isomorphic to [nat] in COQ, by the carrier of the algebra isomorphism
   above (so the bijection does commute with the structure maps). *)
Corollary nat_initial_carrier_unique (I : @Initial (FAlg NatF)) :
  `1 (@initial_obj (FAlg NatF) I) ≅[Coq] nat.
Proof.
  pose proof (nat_initial_unique I) as iso.
  unshelve refine {| to   := falg_hom[to iso]
                   ; from := falg_hom[from iso] |}.
  - exact (iso_to_from iso).
  - exact (iso_from_to iso).
Qed.

(** ** Riehl Example 2.4.11: the representability reading *)

(* [Endos] is Riehl's category of sets with an endomorphism and maps commuting
   with them: an [Id]-algebra is an object with a map [X ~> X], and an
   [Id]-algebra map is a commuting square, with no point involved. *)
Definition Endos : Category := FAlg (Id[Coq]).

(* The forgetful functor to [Sets].  A COQ object is a bare type, so it is
   made a setoid by Leibniz equality ([eq_Setoid] of Lib/Setoid.v); this is
   the one place where the [Coq]-vs-[Sets] variance noted in the issue is
   paid for, and it costs nothing because [Coq]'s hom-setoid is already
   pointwise [eq]. *)
Program Definition Endos_Forget : Endos ⟶ Sets := {|
  fobj := fun x => {| carrier := ``x ; is_setoid := eq_Setoid ``x |};
  fmap := fun x y f => {| morphism := falg_hom[f] |}
|}.
Next Obligation. intros x y f a b Hab; now rewrite Hab. Qed.
Next Obligation. intros x y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros x a; reflexivity. Qed.
Next Obligation. intros x y z f g a; reflexivity. Qed.

(* The candidate representing object: the naturals with successor, no point. *)
Definition nat_succ : FAlgebra Id[Coq] nat := S.

Definition NatSucc : Endos := (nat; nat_succ).

#[local] Notation HomNS := (@Curried_Hom Endos NatSucc).

(* Iteration: the [n]-fold application of the endomap to the point. *)
Fixpoint nat_iter {X : Type} (x0 : X) (f : X ~{Coq}~> X) (n : nat) : X :=
  match n with
  | O   => x0
  | S k => f (nat_iter x0 f k)
  end.

(* Iteration is natural in the object of [Endos]: an endomorphism-preserving
   map carries the iterate of a point to the iterate of its image. *)
Lemma nat_iter_natural {y z : Endos} (g : y ~{Endos}~> z) (y0 : ``y) (n : nat) :
  falg_hom[g] (nat_iter y0 (`2 y) n) = nat_iter (falg_hom[g] y0) (`2 z) n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 z) (falg_hom[g] (nat_iter y0 (`2 y) k))).
    + exact (@falg_commutes _ _ _ _ _ _ g (nat_iter y0 (`2 y) k)).
    + f_equal; exact IH.
Qed.

(* Every endomorphism-preserving map out of [(nat, S)] is the iterate of its
   own value at zero.  This is the injectivity half of the representation. *)
Lemma nat_iter_eval {y : Endos} (h : NatSucc ~{Endos}~> y) (n : nat) :
  nat_iter (falg_hom[h] O) (`2 y) n = falg_hom[h] n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 y) (falg_hom[h] k)).
    + f_equal; exact IH.
    + symmetry; exact (@falg_commutes _ _ _ _ _ _ h k).
Qed.

(* Φ: evaluate an endomorphism-preserving map at zero. *)
Program Definition nat_eval_at_zero (y : Endos)
  : HomNS y ~{Sets}~> Endos_Forget y :=
  {| morphism := fun h => falg_hom[h] O |}.
Next Obligation. intros y h k Hhk; exact (Hhk O). Qed.

(* Ψ: send a point to the iterate along the endomap, which is automatically an
   endomorphism-preserving map because [nat_iter x0 f (S n)] is [f] applied to
   [nat_iter x0 f n] by definition. *)
Program Definition nat_iterate (y : Endos)
  : Endos_Forget y ~{Sets}~> HomNS y :=
  {| morphism := fun y0 => {| falg_hom := nat_iter y0 (`2 y) |} |}.
Next Obligation. intros y y0 n; reflexivity. Qed.

Program Definition nat_eval_transform : HomNS ⟹ Endos_Forget :=
  Build_Transform' nat_eval_at_zero _.
Next Obligation. intros y z g h; reflexivity. Qed.

Program Definition nat_iterate_transform : Endos_Forget ⟹ HomNS :=
  Build_Transform' nat_iterate _.
Next Obligation. intros y z g y0 n; exact (nat_iter_natural g y0 n). Qed.

(* The representation: [Hom((nat, S), ─) ≅ Endos_Forget] in [[Endos, Sets]].
   Evaluation at zero and iteration are mutually inverse, naturally in the
   object of [Endos]. *)
Program Definition nat_succ_represents
  : HomNS ≅[[Endos, Sets]] Endos_Forget :=
  {| to := nat_eval_transform; from := nat_iterate_transform |}.
Next Obligation. intros y y0; reflexivity. Qed.
Next Obligation. intros y h n; exact (nat_iter_eval h n). Qed.

#[export] Program Instance nat_succ_Representable
  : Representable Endos_Forget := {|
  repr_obj := NatSucc;
  represented := nat_succ_represents
|}.

(* The universal element of the representation, in the sense of the Yoneda
   lemma: the image of the identity under the representing isomorphism.  It is
   zero, on the nose. *)
Lemma nat_universal_element :
  transform (to nat_succ_represents) NatSucc (id{Endos}) = O.
Proof. reflexivity. Qed.

(** ** The universal-element criterion *)

(* Riehl's Proposition 2.4.8, stated for this functor: a representation of
   [Endos_Forget] makes the algebra built from the representing object and the
   universal element initial in [FAlg NatF].  Objects of [FAlg NatF] ARE pairs
   of an object of [Endos] and an element of its image under [Endos_Forget],
   and arrows of [FAlg NatF] ARE the arrows of [Endos] carrying one such
   element to the other (that is [alg_hom_clauses]/[clauses_alg_hom] above), so
   this is exactly the statement that a universal element is initial in the
   category of elements — with the category of elements presented concretely as
   [FAlg NatF] rather than built as a general construction.

   ERRATUM (#303).  The clause that used to close that sentence, "which the
   tree does not carry", was true when written (commit 30c01af0, 2026-08-05)
   and went stale four days later: [Construction/Elements.v] landed the general
   category of elements on 2026-08-09 (f2177328), and
   Theory/Universal/Element/Elements.v now states Riehl 2.4.8 — a universal
   element is an initial object of it — over that general construction.  What
   is still NOT built is the comparison [Elements Endos_Forget ≃ FAlg NatF], so
   [repr_initial] below is neither re-derived nor made redundant by it; the two
   remain independent statements. *)

Section UniversalElement.

Context (Repr : Representable Endos_Forget).

(* The representing object and the representing natural isomorphism.  These
   are spelled as abbreviations rather than as further section variables so
   that the [Sets] universe instance is the one fixed by [Endos_Forget]. *)
Notation RObj := (@repr_obj _ _ Repr).
Notation RIso := (@represented _ _ Repr).

(* The universal element: the image of the identity. *)
Definition repr_element : ``RObj := transform (to RIso) RObj (id{Endos}).

(* The algebra of the representing object pointed at its universal element. *)
Definition repr_alg : FAlg NatF :=
  (``RObj ; alg_of_triple repr_element (`2 RObj)).

(* The Yoneda computation: the representing isomorphism sends an arrow to the
   image of the universal element under it.  This is naturality evaluated at
   the identity, followed by the right unit law inside the setoid map. *)
Lemma repr_eval {y : Endos} (h : RObj ~{Endos}~> y) :
  falg_hom[h] repr_element = transform (to RIso) y h.
Proof.
  transitivity (transform (to RIso) y (h ∘ id{Endos})).
  - exact (naturality (to RIso) RObj y h (id{Endos})).
  - apply (@proper_morphism _ _ _ _ (transform (to RIso) y)).
    apply id_right.
Qed.

(* Each [NatF]-algebra gives an object of [Endos] by forgetting the point. *)
Definition endo_of (y : FAlg NatF) : Endos :=
  (``y ; (alg_step (`2 y) : FAlgebra Id[Coq] ``y)).

(* The mediating arrow: the inverse of the representation applied to the point
   of the target algebra. *)
Definition repr_med (y : FAlg NatF) : RObj ~{Endos}~> endo_of y :=
  transform (from RIso) (endo_of y) (alg_pt (`2 y)).

(* It carries the universal element to the point of the target. *)
Lemma repr_med_pt (y : FAlg NatF) :
  falg_hom[repr_med y] repr_element = alg_pt (`2 y).
Proof.
  transitivity (transform (to RIso) (endo_of y) (repr_med y)).
  - exact (repr_eval (repr_med y)).
  - exact (iso_to_from RIso (endo_of y) (alg_pt (`2 y))).
Qed.

(* Hence it is an algebra map out of [repr_alg], by the triple dictionary: the
   point clause is [repr_med_pt] and the step clause is its [Endos] square. *)
Program Definition repr_alg_hom (y : FAlg NatF)
  : repr_alg ~{FAlg NatF}~> y :=
  {| falg_hom := falg_hom[repr_med y] |}.
Next Obligation.
  intro y.
  apply clauses_alg_hom.
  - exact (repr_med_pt y).
  - exact (@falg_commutes _ _ _ _ _ _ (repr_med y)).
Qed.

(* Conversely every algebra map out of [repr_alg] is an [Endos] arrow, by the
   step clause of the same dictionary. *)
Program Definition endo_of_alg_hom {y : FAlg NatF}
        (f : repr_alg ~{FAlg NatF}~> y) : RObj ~{Endos}~> endo_of y :=
  {| falg_hom := falg_hom[f] |}.
Next Obligation.
  intros y f.
  exact (snd (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(* An arrow out of the representing object is determined by its image under
   the representation, since that is an isomorphism at every object. *)
Lemma repr_hom_determined {y : Endos} (k l : RObj ~{Endos}~> y)
      (H : transform (to RIso) y k = transform (to RIso) y l) : k ≈ l.
Proof.
  transitivity (transform (from RIso) y (transform (to RIso) y k)).
  - symmetry; exact (iso_from_to RIso y k).
  - transitivity (transform (from RIso) y (transform (to RIso) y l)).
    + apply (@proper_morphism _ _ _ _ (transform (from RIso) y)); exact H.
    + exact (iso_from_to RIso y l).
Qed.

(* Every algebra map out of [repr_alg] sends the universal element to the
   point of the target: that is the point clause of its commuting square,
   transported along [repr_eval]. *)
Lemma repr_alg_hom_pt {y : FAlg NatF} (f : repr_alg ~{FAlg NatF}~> y) :
  transform (to RIso) (endo_of y) (endo_of_alg_hom f) = alg_pt (`2 y).
Proof.
  transitivity (falg_hom[endo_of_alg_hom f] repr_element).
  - symmetry; exact (repr_eval (endo_of_alg_hom f)).
  - exact (fst (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(* ... so any two of them agree. *)
Lemma repr_alg_hom_unique {y : FAlg NatF}
      (f g : repr_alg ~{FAlg NatF}~> y) : f ≈ g.
Proof.
  refine (repr_hom_determined (endo_of_alg_hom f) (endo_of_alg_hom g) _).
  transitivity (alg_pt (`2 y)).
  - exact (repr_alg_hom_pt f).
  - symmetry; exact (repr_alg_hom_pt g).
Qed.

(* The criterion itself. *)
Program Definition repr_initial : @Initial (FAlg NatF) := {|
  terminal_obj := repr_alg;
  one := fun y => repr_alg_hom y
|}.
Next Obligation. intros y f g; exact (repr_alg_hom_unique f g). Qed.

End UniversalElement.

(* [nat_initial] as an instance of the criterion rather than as a standalone
   proof: feeding the representation [nat_succ_represents] to [repr_initial]
   produces an initial [NatF]-algebra, and it is literally the same algebra —
   the universal element is [O] and the endomap is [S], so the structure map is
   [nat_alg] by conversion. *)
Definition nat_initial_via_universal_element : @Initial (FAlg NatF) :=
  repr_initial nat_succ_Representable.

Lemma nat_initial_agree :
  @initial_obj (FAlg NatF) nat_initial_via_universal_element
    = @initial_obj (FAlg NatF) nat_initial.
Proof. reflexivity. Qed.
