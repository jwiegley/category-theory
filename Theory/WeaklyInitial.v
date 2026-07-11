Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * From a weakly initial family to a genuine initial object *)

(* nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   This file records the object-level input of Freyd's General Adjoint
   Functor Theorem: the passage from a *weakly* initial family to an actual
   initial object.  A family [wif_obj : wif_index -> C] is weakly initial
   when every object [c] is hit by some member, i.e. [wif_cover c] exhibits
   an index [i] and an arrow [wif_obj i ~> c] (existence, with no
   uniqueness).  The classical construction (Freyd, Mac Lane CWM V.6) forms
   the product [P] of the family — itself a single weakly initial object —
   and then carves out the joint equalizer of *all* endomorphisms of [P];
   that equalizer is genuinely initial.

   STATUS / hypothesis form.  The construction consumes exactly two limits
   over caller-chosen index [Type]s and a supply of binary equalizers:

     - [P]  : the product of the family [wif_obj] over [wif_index]
              (an indexed product = limit of a discrete diagram);
     - [Pe] : the product, over the hom-type of endomorphisms of that
              product object, of that object with itself — this is the
              [Type]-indexed limit whose universal cone lets a single
              parallel pair [P ~> Pe] "capture all endos" at once, so the
              wide equalizer of the endomorphism family reduces to one
              *binary* equalizer supplied by [E];
     - [E]  : binary equalizers for parallel pairs.

   Both products are passed as explicit hypotheses rather than harvested
   from a [Complete] / [HasIndexedProducts] instance.  This is deliberate
   (Risk (b)): the endomorphism-indexed product ranges over the hom-type
   [iprod .. ~> iprod ..], which sits at the hom universe [h]; routing it
   through a class that quantifies over every index [Type] would over-commit
   the ambient universes, whereas the explicit form leaves the smallness of
   the index (hence the relevant universe constraints) in the caller's
   hands.  Supplying [Pe] separately from [P] strengthens the hypotheses
   (an honest, leaner input) and never weakens the conclusion, which remains
   a full [Initial C]. *)

(* A weakly initial family: an index [Type], a family of objects, and for
   every object [c] a *choice* of covering member together with an arrow
   into [c].  No uniqueness of the covering arrow is required — that is what
   makes the family only *weakly* initial. *)
Record WeaklyInitialFamily (C : Category) := {
  wif_index : Type;
  wif_obj : wif_index -> C;
  wif_cover (c : C) : { i : wif_index & wif_obj i ~> c }
}.

Arguments wif_index {C} _.
Arguments wif_obj {C} _ _.
Arguments wif_cover {C} _ _.

(* The product [P] of a weakly initial family, together with equalizers and
   the endomorphism-indexed product [Pe] over the product object, yields a
   genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial (a single
   object now).  The projections of [Pe] separate all endomorphisms of
   [P0]: there is a map [m : P0 ~> Pe] with [proj u ∘ m ≈ u] for every endo
   [u], and a map [d : P0 ~> Pe] with [proj u ∘ d ≈ id] for every [u].  The
   binary equalizer [e : I ~> P0] of [m] and [d] then satisfies
   [u ∘ e ≈ e] for *every* endomorphism [u] of [P0], and is monic.  This
   [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e], the weakly initial map post-
       composed with the equalizer inclusion;
     - uniqueness: given [f g : I ~> c], take the (binary) equalizer
       [k : K ~> I] of [f] and [g]; weak initiality gives [s : P0 ~> K], so
       [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi, and
       [f ∘ k ≈ g ∘ k] forces [f ≈ g]. *)
Theorem initial_from_weakly_initial `(W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W)))
  (Pe : Limit (DiscreteCat_Functor
                 (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                  => iprod (wif_obj W) P)))
  (E : HasEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object and fold it into [Pe]'s index. *)
  set (P0 := iprod (wif_obj W) P) in *.
  set (Endo := fun _ : (P0 ~> P0) => P0) in *.

  (* Weak initiality of [P0]: a chosen map into every object. *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (* The tupling of all endomorphisms, and of the constant identity family,
     through the endomorphism-indexed product [Pe]. *)
  destruct (iprod_ump Endo Pe P0 (fun u => u)) as [m Hm0 _].
  destruct (iprod_ump Endo Pe P0 (fun _ => id[P0])) as [d Hd0 _].
  (* beta-normalized reads of the two universal families *)
  assert (Hm : ∀ u : P0 ~> P0, iprod_proj Endo Pe u ∘ m ≈ u)
    by exact Hm0.
  assert (Hd : ∀ u : P0 ~> P0, iprod_proj Endo Pe u ∘ d ≈ id[P0])
    by exact Hd0.

  (* The binary equalizer of the two tuplings. *)
  destruct (@equalizer C E P0 (iprod Endo Pe) m d) as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizer inclusion. *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    assert (Hu : iprod_proj Endo Pe u ∘ (m ∘ e)
                   ≈ iprod_proj Endo Pe u ∘ (d ∘ e)).
    { rewrite (fork_eq Eeq); reflexivity. }
    rewrite !comp_assoc in Hu.
    rewrite (Hm u) in Hu.
    rewrite (Hd u) in Hu.
    transitivity (id[P0] ∘ e).
    + exact Hu.
    + apply id_left. }

  (* The equalizer inclusion is monic. *)
  pose proof (equalizer_monic m d Eeq) as Me.
  destruct Me as [mon].

  (* Assemble the initial object as a terminal object of [C^op]. *)
  unshelve refine (@Build_Terminal (C^op) I _ _).
  - (* existence: [I ~> x] via weak initiality post-composed with [e] *)
    intro x.
    exact (wmap x ∘ e).
  - (* uniqueness: any two [f g : I ~> x] agree *)
    intros x f g.
    (* read the goal in [C]: [f], [g] are [C]-morphisms [I ~> x] *)
    change (unop f ≈ unop g).
    (* the binary equalizer of the competing pair *)
    destruct (@equalizer C E I x f g) as [K [k Ek]].
    (* weak initiality supplies a map [P0 ~> K] *)
    pose (s := wmap K).
    (* [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then cancels it, exhibiting [s ∘ e] as a section of [k]. *)
    assert (Habs : (e ∘ (k ∘ s)) ∘ e ≈ e ∘ id[I]).
    { transitivity e.
      - exact (endo_absorb (e ∘ (k ∘ s))).
      - symmetry; apply id_right. }
    assert (Hk : (k ∘ s) ∘ e ≈ id[I]).
    { apply (mon _ ((k ∘ s) ∘ e) (id[I])).
      transitivity ((e ∘ (k ∘ s)) ∘ e).
      - apply comp_assoc.
      - exact Habs. }
    (* hence [k ∘ (s ∘ e) ≈ id]: [k] is a split epimorphism *)
    assert (Hkr : k ∘ (s ∘ e) ≈ id[I]).
    { transitivity ((k ∘ s) ∘ e).
      - apply comp_assoc.
      - exact Hk. }
    (* [k] equalizes [f] and [g] and is (split) epic, so [f ≈ g] *)
    transitivity (unop f ∘ (k ∘ (s ∘ e))).
    + transitivity (unop f ∘ id[I]).
      * symmetry; apply id_right.
      * apply compose_respects; [ reflexivity | symmetry; exact Hkr ].
    + transitivity (unop g ∘ (k ∘ (s ∘ e))).
      * transitivity ((unop f ∘ k) ∘ (s ∘ e)).
        -- apply comp_assoc.
        -- transitivity ((unop g ∘ k) ∘ (s ∘ e)).
           ++ apply compose_respects; [ exact (fork_eq Ek) | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.
