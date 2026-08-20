Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Freyd's initial-object construction, through the wide-equalizer API *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   [Theory/WeaklyInitial.v] proves [initial_from_weakly_initial]: a weakly
   initial family, a product of it, an endomorphism-indexed POWER of that
   product, and a supply of BINARY equalizers together yield a genuine
   initial object (Freyd; Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.6).  The power is there for one reason,
   which that file states in terms: it is the device by which "the wide
   equalizer of the endomorphism family reduces to one *binary*
   equalizer".  With wide equalizers available the device is unnecessary,
   and this file says so — [initial_from_weakly_initial_wide] equalizes
   ALL endomorphisms of the product directly, which is the form Freyd's
   argument is usually presented in.

   WHAT THIS FILE IS AND IS NOT.  It is ADDITIVE.  [Theory/WeaklyInitial.v]
   is untouched: [initial_from_weakly_initial] keeps its statement, its
   proof and its universe constraints, and [Adjunction/GAFT.v],
   [Adjunction/SAFT.v] and the two GAFT example files keep consuming it
   unchanged.  Nothing here is claimed to supersede it, and the two are not
   related by any passage — neither theorem is derived from the other.

   THE TRADE, STATED PLAINLY.  The wide form drops one hypothesis (the
   power [Pe]) and needs no separate binary-equalizer supply, since the
   two-element family [fun b : bool => if b then f else g] is a wide family
   like any other.  What it costs is the shape of the remaining hypothesis:
   [HasWideEqualizers] is a CLASS whose index [Type] is a universe
   parameter, and the endomorphism family forces that parameter to sit at
   or above the ambient hom universe.  [Theory/WeaklyInitial.v] avoids
   exactly this by passing both limits as explicit hypotheses, on the
   stated ground that a class quantifying over index [Type]s would
   over-commit the ambient universes; that reasoning is not withdrawn here.
   A caller who wants the leaner input keeps the original theorem, and a
   caller who has wide equalizers uses this one.

   WHERE THE PROOF ACTUALLY GETS SHORTER.  In the original, absorption of
   endomorphisms ([endo_absorb]) is four rewrites through the two tuplings
   [m] and [d] and their defining families.  Here it is one instance of the
   wide fork condition at [u] and [id], followed by [id_left]: the wide
   equalizer's defining equation IS "every endomorphism agrees with the
   identity after [e]".  Monicity of the equalizing map, which supplies the
   uniqueness half, comes from [wide_equalizer_monic] exactly as it came
   from [equalizer_monic].  The endgame — a weakly initial map into the
   equalizer of a competing pair, exhibited as a section, then cancellation
   — is the original's, transcribed.

   UNIVERSES, measured (reproduce with [Set Printing Universes. About
   initial_from_weakly_initial. About initial_from_weakly_initial_wide.]).
   Both theorems are over [C : Category@{u2 Set Set}] — the pin at [Set]
   is the DONOR's, inherited from [Terminal] and the equalizer supply, and
   is not introduced here.  The binder COUNT is the same — both are
   [@{u u0 u1 u2}], so there is no extra binder: the wide form replaces the
   power's binder with the class's index binder, which is itself
   unconstrained, appearing free in [HasWideEqualizers@{u1 u2 Set} C].  The
   constraint-block difference runs the other way: the DONOR carries two
   extra stdlib bounds ([u0 <= eq.u0], [u0 <= Logic_lemmas.equality.u0])
   from the power's discrete diagram, which the wide form drops.

   NOT DELIVERED.  No [HasWideEqualizers] instance, so this theorem has no
   in-tree application and is a conditional exactly as its donor is; in
   particular [Adjunction/GAFT.v] is NOT rerouted through it.  No wide
   analogue of [Structure/Limit/Product.v]'s indexed products (the product
   [P] is still an ordinary discrete-diagram limit).  No claim that the two
   theorems have the same universe constraints — they do not, and the
   difference is the donor's two extra bounds described above. *)

(* A weakly initial family, a product of it, and a supply of wide
   equalizers yield a genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial.  Take the
   wide equalizer [e : I ~> P0] of the family of ALL endomorphisms of [P0],
   indexed by the hom-type itself.  Its fork condition instantiated at an
   endomorphism [u] and at [id] says [u ∘ e ≈ id ∘ e], i.e. [e] absorbs
   every endomorphism; and [e] is monic.  This [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e];
     - uniqueness: given [f g : I ~> c], take the wide equalizer [k : K ~> I]
       of the two-element family {f, g}; weak initiality gives [s : P0 ~> K],
       so [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e];
       monicity of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi,
       and [f ∘ k ≈ g ∘ k] forces [f ≈ g]. *)
Theorem initial_from_weakly_initial_wide `(W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W)))
  (E : HasWideEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object. *)
  set (P0 := iprod (wif_obj W) P) in *.

  (* Weak initiality of [P0]: a chosen map into every object. *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (* The wide equalizer of the family of ALL endomorphisms of [P0].  The
     index type is the hom-type [P0 ~> P0] and the family is the identity
     assignment, so "the i-th member" IS the endomorphism [i]. *)
  destruct (@wide_equalizer C E (P0 ~> P0) P0 P0 (fun u => u))
    as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizing map.  This is
     one instance of the wide fork condition — at [u] and at [id] — where
     the original needed the two tuplings through the power. *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    transitivity (id[P0] ∘ e).
    - exact (wfork_eq Eeq u id[P0]).
    - apply id_left. }

  (* The equalizing map is monic. *)
  pose proof (wide_equalizer_monic (fun u : P0 ~> P0 => u) Eeq) as Me.
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
    (* the wide equalizer of the two-element family {f, g}; no separate
       binary-equalizer supply is needed *)
    destruct (@wide_equalizer C E bool I x
                (fun b : bool => if b then unop f else unop g))
      as [K [k Ek]].
    assert (Hfg : unop f ∘ k ≈ unop g ∘ k)
      by exact (wfork_eq Ek true false).
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
           ++ apply compose_respects; [ exact Hfg | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.
