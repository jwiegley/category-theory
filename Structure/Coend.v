Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.

Generalizable All Variables.

(** * Coends: ergonomic covariant accessors *)

(* nLab:      https://ncatlab.org/nlab/show/coend
   Wikipedia: https://en.wikipedia.org/wiki/Coend

   The COEND of a functor of mixed variance `F : C^op ∏ C ⟶ D`, written
   `∫^c F(c,c)`, is the UNIVERSAL (initial) COWEDGE: an object `coend_obj : D`
   together with injections `coend_inj_x : F (x, x) ~> coend_obj`, one per
   object `x : C`, satisfying the covariant (co)dinaturality condition and
   through which every other cowedge factors uniquely. It is the dinatural
   analogue of a colimit, dual to the END of Structure/End.

   In this library a coend is DEFINED as an end in the opposite categories,

     Coend F := @End (C^op) (D^op) (F^op)          (Structure/End.v)

   so its underlying datum is a `Wedge F^op` (equivalently a `Cowedge F`, see
   Structure/Wedge) whose legs `F (x, x) ~{D}~> coend_obj` are the reversed
   wedge legs and whose universal property runs OUT of the coend. Reasoning
   directly with that opposite-category packaging forces every morphism to be
   read reversed, which is awkward downstream.

   This file supplies a thin convenience layer, in the exact spirit of
   Structure/Pushout (a covariant reader over the dualized `Pullback`): the
   accessors `coend_obj` and `coend_inj`, the covariant cowedge condition
   `coend_cowedge`, the universal property `coend_ump`, the mediator
   `coend_med` (with its computation and uniqueness rules), and a smart
   constructor `Build_Coend` assembling a coend from covariant cowedge data.
   Each accessor is an op-read of the corresponding `End`/`Wedge` accessor
   (`end_wedge`, `wedge_map`, `ump_wedges`, `ump_ends`) with the morphisms
   inverted, so downstream code can reason entirely in `C` and `D`. Nothing
   here alters Structure/End.

   The covariant cowedge condition, for `f : x ~> y`, both sides
   `F (y, x) ~> coend_obj`:

     coend_inj_x ∘ bimap[F] (op f) id ≈ coend_inj_y ∘ bimap[F] id f

   This is the dual of the wedge condition of Structure/Wedge: the leg at `x`
   precomposed with the contravariant action `F(f, 1)` agrees with the leg at
   `y` precomposed with the covariant action `F(1, f)`. Because `Coend`,
   `F^op`, `op` and the reversed hom-sets are all involutive on the nose, the
   op-reads below are the underlying `End`/`Wedge` data up to one `symmetry`,
   with no coherence obligations of their own. *)

(* The coend calculus, its history, and the existential reading

   nLab:  https://ncatlab.org/nlab/show/coend
   Book:  Loregian, "(Co)end Calculus", London Math. Soc. Lecture Note
          Series 468, Cambridge University Press 2021
   Paper: Yoneda, "On Ext and exact sequences", J. Fac. Sci. Univ. Tokyo
          Sec. I, 8 (1960) 507–576
   Book:  Mac Lane, "Categories for the Working Mathematician", Springer
          1971 (2nd ed. 1998), chapter IX
   Paper: Day, "On closed categories of functors", Midwest Category
          Seminar IV, Springer LNM 137 (1970) 1–38

   A coend integrates a functor of mixed variance over its diagonal into
   a single object of the target, and it does so where an ordinary
   colimit cannot.  A colimit glues a covariant diagram; [coend_obj] is
   instead the universal object receiving the injections [coend_inj]
   that COEQUALIZE the two functorial actions of `F`.  Concretely it is
   the coequalizer

     ∐_{f : c → c'} F(c', c) ⇉ ∐_c F(c, c) → ∫^c F(c, c)

   forcing the contravariant action `F(f, 1)` and the covariant action
   `F(1, f)` to agree (nLab, "coend"); this is [coend_cowedge] read as a
   quotient rather than as a family of equations.  Many canonical
   constructions are inherently of mixed variance, and it is these, not
   covariant diagrams, that a coend is built to express.

   The notation and the calculus accumulated in layers.  Yoneda
   introduced the integral sign for ends and coends in §4 of his 1960
   dissertation, though under a convention reversed from the modern one:
   he named the coend "integration" and the end "cointegration" (Yoneda
   1960; nLab, "end").  Mac Lane gave the textbook account — chapter IX
   of "Categories for the Working Mathematician" defines dinatural
   transformations and presents ends and coends as universal (co)wedges,
   the presentation this file inherits through Structure/Wedge and
   Structure/End (Mac Lane 1971).  Mac Lane also used a coend to render a
   construction in algebraic topology as a tensor product of functors,
   `F ⊗_C G ≅ ∫^c F c ⊗ G c`, with `C` cast in the role of the ring
   (reported in Loregian's survey).  Loregian later supplied the first
   book-length treatment and described the technique as a "secret weapon"
   of working category theorists (Loregian 2021).

   The utility is the calculus itself: a compact algebra of integral
   manipulations that replaces long diagram chases.  Its basic reduction
   is the co-Yoneda, or "ninja Yoneda", lemma — every functor is a coend
   of representables, `∫^{c'} C(c', c) · F c' ≅ F c` — proven in Sets in
   Theory/Coend/Yoneda.v; its second rule is the Fubini interchange
   `∫^{(c,d)} H ≅ ∫^c ∫^d H` (Theory/Coend/Fubini.v).  Over these run the
   applications: Day convolution, which makes a functor category
   monoidal by `(F * G) c ≅ ∫^{a,b} C(a ⊗ b, c) · F a · G b`
   (Day 1970; Construction/Day.v); profunctor composition
   `(Q ∘ P)(c, e) ≅ ∫^d P(c, d) × Q(d, e)` (Theory/Profunctor.v,
   Construction/Profunctor/Compose.v); the pointwise left Kan extension
   `∫^c D(K c, d) · F c`, the coend presentation of the extension that
   Theory/Kan/Extension.v instead builds through an adjunction; and the
   geometric realization of a simplicial set as a single coend (nLab,
   "coend").

   Computationally a coend is an existential type.  An element of
   `∫^c F(c, c)` is a pair `(c, a)` with `a : F(c, c)` — a hidden object
   together with a value — taken modulo the dinaturality gluing that
   identifies `(c, F(f, 1) b)` with `(c', F(1, f) b)`; dually an end is
   a polymorphic `∀ c. …` carrying a naturality side-condition
   (Milewski, "Category Theory for Programmers", §26).  This is the
   shape of the concrete coend in Instance/Sets/Coend.v, where an
   injection at a witness is quotiented by exactly that relation, and it
   is why existential and parametric encodings stand in for coends in
   profunctor-optics libraries (Clarke et al., "Profunctor Optics, a
   Categorical Update", arXiv 2020). *)

Section Coend.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.

(** The coend object `∫^c F(c,c)` of `D`: the apex of the underlying end
    wedge, read as an object of `D` (objects of `D^op` are objects of `D`). *)
Definition coend_obj (E : Coend F) : D :=
  @Wedge_to_obj (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E).

(** The injection `coend_inj_x : F (x, x) ~> coend_obj`: the underlying wedge
    leg `wedge_obj ~{D^op}~> F^op (x, x)`, read reversed in `D`. *)
Definition coend_inj (E : Coend F) {x : C} :
  F (x, x) ~{D}~> coend_obj E :=
  @wedge_map (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E) x.

(** The covariant cowedge (co-dinaturality) condition, obtained from the
    underlying wedge condition of `end_wedge` by one `symmetry`. For
    `f : x ~> y` both composites run `F (y, x) ~> coend_obj`. *)
Lemma coend_cowedge (E : Coend F) {x y : C} (f : x ~{C}~> y) :
  @coend_inj E x ∘ bimap[F] (op f) id ≈ @coend_inj E y ∘ bimap[F] id f.
Proof.
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op)
           (@end_wedge (C^op) (D^op) (F^op) E) y x (op f)).
Qed.

(** Covariant cowedge data on a candidate apex `w`: a family of legs
    `i x : F (x, x) ~> w` satisfying the cowedge condition. This packages the
    hypotheses of the coend's universal property and of the smart constructor
    below. *)
Definition Cowedge_cond (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) : Type :=
  ∀ (x y : C) (f : x ~{C}~> y),
    i x ∘ bimap[F] (op f) id ≈ i y ∘ bimap[F] id f.

(** Covariant cowedge data assembles into an underlying `Wedge F^op`
    (equivalently a `Cowedge F`). The wedge condition is the covariant
    `cond` read back through `F^op` by one `symmetry`; this is the inverse of
    the reading performed in [coend_cowedge]. *)
Definition covariant_cowedge (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  @Wedge (C^op) (D^op) (F^op).
Proof.
  unshelve refine (@Build_Wedge (C^op) (D^op) (F^op) w (fun x => i x) _).
  intros x y f.
  symmetry.
  exact (cond y x f).
Defined.

(** The coend universal property, stated covariantly: every cowedge
    `(w, i)` over `F` factors through the coend by a unique mediator
    `u : coend_obj ~> w` recovering each leg, `u ∘ coend_inj_x ≈ i x`. This is
    the end UMP `ump_ends` read on the cowedge `covariant_cowedge w i cond`. *)
Lemma coend_ump (E : Coend F)
  (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  ∃! u : coend_obj E ~{D}~> w, ∀ x : C, u ∘ coend_inj E ≈ i x.
Proof.
  exact (@ump_ends (C^op) (D^op) (F^op) E (covariant_cowedge w i cond)).
Qed.

(** The mediating morphism out of a coend into any cowedge. *)
Definition coend_med (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  coend_obj E ~{D}~> w :=
  unique_obj (coend_ump E w i cond).

(** The mediator recovers each leg of the target cowedge. *)
Lemma coend_med_inj (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) (x : C) :
  coend_med E w i cond ∘ coend_inj E ≈ i x.
Proof.
  unfold coend_med.
  exact (unique_property (coend_ump E w i cond) x).
Qed.

(** Any morphism factoring the injections through the same legs equals the
    mediator. *)
Lemma coend_med_unique (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (v : coend_obj E ~{D}~> w) :
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> coend_med E w i cond ≈ v.
Proof.
  intro Hv.
  unfold coend_med.
  exact (uniqueness (coend_ump E w i cond) v Hv).
Qed.

(** Two mediators out of a coend that agree on every injection are equal.
    This lets one prove `u ≈ v` without exhibiting `coend_med` explicitly. *)
Lemma coend_med_eq (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (u v : coend_obj E ~{D}~> w) :
  (∀ x : C, u ∘ coend_inj E ≈ i x) ->
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (coend_med E w i cond).
  - symmetry.
    now apply coend_med_unique.
  - now apply coend_med_unique.
Qed.

(** A `Build_Coend`-style smart constructor: a coend is assembled from
    covariant cowedge data `(w, i, cond)` together with its covariant
    universal property `ump`. The underlying end wedge is
    `covariant_cowedge w i cond`; the end UMP `ump_ends` is discharged by
    reading each competing `Wedge F^op` back into covariant cowedge data and
    applying `ump`. *)
Definition Build_Coend (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (ump : ∀ (w' : D) (i' : ∀ x : C, F (x, x) ~{D}~> w')
           (cond' : Cowedge_cond w' i'),
           ∃! u : w ~{D}~> w', ∀ x : C, u ∘ i x ≈ i' x) :
  Coend F.
Proof.
  unshelve refine
    (@Build_End (C^op) (D^op) (F^op) (covariant_cowedge w i cond) _).
  intros W.
  refine (ump (@Wedge_to_obj (C^op) (D^op) (F^op) W)
              (fun x => @wedge_map (C^op) (D^op) (F^op) W x)
              (fun x y f => _)).
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op) W y x (op f)).
Defined.

End Coend.

Arguments coend_obj {C D F} E.
Arguments coend_inj {C D F} E {x}.
Arguments Cowedge_cond {C D} F w i.
Arguments coend_cowedge {C D F} E {x y} f.
Arguments coend_ump {C D F} E w i cond.
Arguments coend_med {C D F} E w i cond.
Arguments Build_Coend {C D F} w i cond ump.
