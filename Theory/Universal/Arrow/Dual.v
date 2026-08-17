Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Opposite.

Generalizable All Variables.

(* NOTATION GUARD.  Three scopes declare the token `_ ^op` at the same level:
   category_scope (Construction/Opposite.v, [Opposite]), functor_scope
   (Functor/Opposite.v, [Opposite_Functor]) and adjunction_scope
   (Adjunction/Opposite.v, [Opposite_Adjunction]).  The last two files each
   [Open] their own scope as a side effect of being imported, so by the end of
   the [Require] block above the winning interpretation of `X^op` is the
   ADJUNCTION one.

   BE PRECISE ABOUT WHICH HALF OF THIS IS FORCED -- an earlier revision of
   this block was not, and claimed the [Open Scope] below is required.  It is
   NOT, in this file: [Bind Scope category_scope with Category]
   (Theory/Category.v) rescues every occurrence of `C^op` here, all of which
   sit in argument or ascription positions, and deleting the [Open Scope] line
   leaves the file compiling clean (measured).  The hazard is real in general
   -- a bare [Definition d := C^op.] after this Require block does fail, with
   `C` reported as expected to have type `?F ⊣ ?U` -- but this file contains
   no such occurrence.  So the [Open Scope] is DEFENSIVE, kept because it is
   cheap, exported, and useful to downstream importers who may write the bare
   form.

   What IS forced is the other half: `F^op` is rejected under either scope
   order ([Fail Definition fop := F^op.] succeeds with the guard in place), so
   every opposite FUNCTOR below is written [Opposite_Functor F] by name.  (The
   same family of hazard is recorded for Instance/Rng/Mod.v.) *)
Open Scope category_scope.

(** * Couniversal arrows *)

(* nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   A couniversal arrow from a functor F : D ⟶ C to an object c : C -- Mac
   Lane's "universal arrow from F to c" (CWM 2nd ed., §III.1, p. 58) -- is a
   pair (a, ε) consisting of an object a : D and a morphism ε : F a ~> c, such
   that for every object d : D and every morphism h : F d ~> c there exists a
   unique g : d ~> a satisfying h ≈ ε ∘ fmap[F] g.  Equivalently, (a, ε) is a
   TERMINAL object of the comma category F ↓ =(c).

   That last sentence is not new here: it is the one Theory/Universal/Arrow.v
   already writes down in its own header -- "The dual notion, a universal
   arrow from F to c, is a terminal object of F ↓ =(c)" -- as a remark, with
   nothing in the tree carrying it.  This file carries it.

   Where a universal arrow is the pointwise form of a LEFT adjoint, with the
   arrows serving as the components of the unit, a couniversal arrow is the
   pointwise form of a RIGHT adjoint, with the arrows serving as the
   components of the counit.  That is the content of
   [RightAdjointFunctorFromCouniversalArrows] and
   [AdjunctionFromCouniversalArrows] below: a couniversal arrow to every
   c : C assembles into a right adjoint of F. *)

(* Why the dual is cheap here, and what it costs

   nLab:  https://ncatlab.org/nlab/show/opposite+category
   Paper: Mac Lane, "Duality for groups", Bull. Amer. Math. Soc. 56, 1950

   The couniversal notion is introduced as the formal dual and its theory
   left to the duality principle, and this file honours that: the
   definition is an INSTANTIATION of the primal class at the opposite
   categories,

       CouniversalArrow c F := @UniversalArrow (C^op) (D^op) c (F^op),

   after which every result of Theory/Universal/Arrow.v is available by
   instantiation rather than by a second proof.  What the file adds is the
   covariant reading, so that a consumer never types `op`: [coarrow_obj],
   [coarrow] and [ump_couniversal_arrows] are DEFINITIONAL op-reads,
   supplied by [:=] with no tactic at all, because `x ~{C^op}~> y` is
   literally `y ~{C}~> x` (Construction/Opposite.v), the object and
   morphism maps of `F^op` are literally those of `F`
   (Functor/Opposite.v), and composition in `C^op` is composition in `C`
   with its arguments exchanged.  The same device carries
   Comonad/Core.v over [Comonad := @Monad (C^op) (W^op)] and
   Structure/End.v:58 over [Coend F := @End (C^op) (D^op) (F^op)] -- the
   definition lives in End.v, not in Structure/Coend.v, which is the calculus
   built on it.  This file applies the device again, and those two are the
   models it follows.

   The duality is not free everywhere, and the file measures rather than
   assumes.  Two boundaries are recorded.

   FIRST, the terminal-object reading is a THEOREM, not the definition.
   `@Initial (=(c) ↓ F^op)` computed in the opposite categories is NOT
   convertible with `@Terminal (F ↓ =(c))`: [Comma] stores its two
   indices as an ordered pair, so the first has objects over `1 ∏ D^op`
   and the second over `D ∏ 1`, and the product of categories is not
   symmetric on the nose.  [couniversal_arrow_terminal] and
   [couniversal_arrow_of_terminal] therefore convert in both directions
   through the universal mapping property, and Test/ProbeCouniversal.v
   pins the negative side.  This is the same accounting
   Structure/Initial.v makes for [initial_unique], where transporting
   the terminal statement would cost more than the direct argument.

   The bridge's round-trip behaviour is ASYMMETRIC, and both halves are
   recorded here rather than left for a reader to discover.  In one
   direction it is better than the file claims elsewhere: for an
   ARBITRARY [U], both [coarrow_obj] and [coarrow] survive
   [couniversal_arrow_of_terminal (couniversal_arrow_terminal U)] by
   [eq_refl] -- more general than Examples.v's [product_terminal_round],
   which records only the arrow and only at the product.  In the other
   direction it does not reduce at all: [couniversal_arrow_of_terminal]
   destructs its argument, so on a variable [T] the object component of
   [couniversal_arrow_terminal (couniversal_arrow_of_terminal T)] is
   stuck.  Neither statement is packaged as an isomorphism, and the
   "not a bijection" note in the WHAT IS NOT DELIVERED block below is
   about the ENCODING passage, not about this bridge.

   The mismatch is located precisely, and it is NOT the terminal/initial
   axis: [terminal_is_initial_op] below records by [eq_refl] that
   `@Terminal (F ↓ =(c))` IS `@Initial ((F ↓ =(c))^op)`, the house idiom
   costing nothing.  What differs is WHICH comma category, and
   Construction/Comma.v's [Cocomma] -- which the issue proposes as the
   route -- does not close the gap either: [Cocomma F =(c)] is neither
   the comma the op-side [arrow_initial] inhabits nor
   `(F ↓ =(c))^op` on the nose (both measured, both pinned in the probe
   file).  Hence the bridge is built, not asserted.

   SECOND, the adjunction assembles by duality but its counit does not
   REDUCE to the couniversal arrow.  [Opposite_Adjunction]
   (Adjunction/Opposite.v) turns the opposite-side left adjoint into the
   covariant right adjoint with `(C^op)^op = C` and `(F^op)^op = F`
   holding by [reflexivity], so [RightAdjointFunctorFromCouniversalArrows]
   is a `C ⟶ D` on the nose and its object action is [coarrow_obj] by
   [eq_refl] ([right_adjoint_obj]).  The counit, however, arrives as
   `coarrow ∘ fmap[F] id`, so [counit_couniversal] closes only up to `≈`
   -- one [fmap_id] and one [id_right] away from [eq_refl], and the
   residue is in the transpose, not in the [abstract]-opaque obligations
   of [AdjunctionFromUniversalArrows].

   The witnesses live in Theory/Universal/Arrow/Dual/Examples.v, kept
   separate so that consumers of the theory -- Mac Lane §IV.1 Theorem 2
   is the scheduled one -- do not inherit a dependency on
   Structure/Cartesian.v. *)

(* WHAT IS DELIVERED

   Both encodings, mirroring the primal file field for field:
   [CouniversalArrow], packaging the property with the object projected
   out, and [ACouniversalArrow], with the object a : D a parameter.  For
   each: the covariant accessors, the couniversal mapping property and
   its converse, the full mediator calculus ([cua_med] / [acua_med] with
   commutes / unique / id / comp), the canonical isomorphism of
   couniversal objects, and Awodey's Proposition 1.10 dualized
   ([couniversal_arrow_unique], [acouniversal_arrow_unique]).  Mac Lane's
   terminal-object reading in both directions.  The right adjoint and the
   adjunction, with the counit identified.  And -- an addition rather than
   a mirror, the primal file relating its two encodings nowhere -- the
   passage between the two encodings, both ways, each keeping the arrow
   and the object by [eq_refl].

   WHAT IS NOT DELIVERED

   * NO NOTATION.  The primal `c ⟿ F` is declared INSIDE
     [Section UniversalArrow] and so does not survive its [End]; there is
     no exported spelling to mirror, and inventing one is out of scope.

   * NO CONVERSE.  Mac Lane §IV.1 Theorem 2 -- that the counit of an
     adjunction is a couniversal arrow at every object, the converse of
     [AdjunctionFromCouniversalArrows] -- is deliberately left to the
     issue that owns it (#347), which is why the artifacts here sit at
     this path for it to import.

   * NO REPRESENTABILITY FACE.  Structure/UniversalProperty/Universal/
     Arrow.v identifies an [AUniversalArrow] with a hom-set isomorphism
     via Yoneda ([UniversalArrowIsUniversalProperty]); no dual of that is
     built here, and none is needed by the assembly.

   * THE ENCODING PASSAGE IS NOT A BIJECTION.  Its two round trips are
     recorded on the ARROW and the OBJECT only; nothing is claimed about
     the uniqueness data, and no setoid isomorphism is stated. *)

Section CouniversalArrow.

Context {C : Category}.
Context {D : Category}.

(** ** The comma-packaged encoding *)

(* A couniversal arrow from F to c.  Definitionally a [UniversalArrow] in the
   opposite categories; every accessor below reads it back covariantly. *)
Definition CouniversalArrow (c : C) (F : D ⟶ C) : Type :=
  @UniversalArrow (C^op) (D^op) c (Opposite_Functor F).

(* Mirrors [Existing Class Comonad] in Comonad/Core.v: typeclass resolution
   keys on the head constant of a goal and does not unfold this definition, so
   without the declaration a couniversal arrow in scope would not be found for
   the implicit arguments of the accessors below.  Goals headed by
   [UniversalArrow] are untouched, the two heads being distinct. *)
Existing Class CouniversalArrow.

Section Accessors.

Context {c : C}.
Context {F : D ⟶ C}.
Context (U : CouniversalArrow c F).

(* The couniversal object a : D.  Objects of `D^op` ARE objects of `D`, so
   this is [arrow_obj] with no transport. *)
Definition coarrow_obj : D := @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U.

(* The couniversal morphism ε : F a ~> c.  Its op-side type is
   `c ~{C^op}~> (F^op) a`, which is literally `F a ~{C}~> c`; the covariant
   ascription below is accepted by conversion alone. *)
Definition coarrow : F coarrow_obj ~{C}~> c :=
  @arrow (C^op) (D^op) c (Opposite_Functor F) U.

End Accessors.

(* No [Arguments] command is needed -- or would survive: [Arguments] inside a
   [Section] is discharged at its [End].  Both accessors take c and F
   implicitly already, from the implicit [Context] binders of [Accessors], and
   that survives; likewise for every [{c}]/[{F}] below. *)

(* The couniversal mapping property: any h : F d ~> c factors as
   h ≈ coarrow ∘ fmap[F] g through a unique g : d ~> coarrow_obj.  This is
   [ump_universal_arrows] read in the opposite categories -- the op-side
   composite `fmap[F^op] g ∘[C^op] arrow` IS `coarrow ∘[C] fmap[F] g` -- and
   so is supplied by [:=], with no proof step of its own. *)
Definition ump_couniversal_arrows {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) {d : D} (h : F d ~{C}~> c) :
  ∃! g : d ~{D}~> coarrow_obj U, h ≈ coarrow U ∘ fmap[F] g :=
  @ump_universal_arrows (C^op) (D^op) c (Opposite_Functor F) U d h.

(* Conversely, the couniversal mapping property reconstructs the couniversal
   arrow.  Again a definitional op-read of [universal_arrow_from_UMP]. *)
Definition couniversal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D)
  (ε : F d ~{C}~> c)
  (u : ∀ (d' : D) (f : F d' ~{C}~> c), ∃! g : d' ~{D}~> d, f ≈ ε ∘ fmap[F] g)
  : CouniversalArrow c F :=
  @universal_arrow_from_UMP (C^op) (D^op) c (Opposite_Functor F) d ε u.

(** ** The terminal-object reading (Mac Lane §III.1 Definition 3) *)

(* Mac Lane defines a couniversal arrow from F to c as a TERMINAL object of
   the comma category F ↓ =(c), and that reading is delivered here as a pair
   of conversions rather than as the definition, for the reason the header
   gives: the opposite-side comma category indexes its objects by `1 ∏ D^op`
   where this one indexes by `D ∏ 1`, and [Product] of categories is not
   symmetric on the nose.  Test/ProbeCouniversal.v pins that boundary.

   The two constructions below are the exact duals of [arrow_initial] and
   [universal_arrow_from_UMP], run through the couniversal mapping property. *)

(* Locating the mismatch: it is NOT the terminal/initial axis.  `Initial K`
   is notation for `@Terminal (K^op)` (Structure/Initial.v) and
   `(K^op)^op = K` holds by conversion (Construction/Opposite.v), so the
   terminal object of F ↓ =(c) IS an initial object of its opposite, for
   free.  What the op-instantiation cannot supply is the COMMA CATEGORY.
   Convertibility of types, not an equation between morphisms. *)
Corollary terminal_is_initial_op {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : @Initial ((F ↓ =(c))^op).
Proof. exact T. Defined.

Definition couniversal_arrow_terminal {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) : @Terminal (F ↓ =(c)).
Proof.
  unshelve eapply Build_Terminal.
  - (* the terminal object is the couniversal pair (a, ε) *)
    exact (((coarrow_obj U, ttt); coarrow U)).
  - (* the unique arrow into it is the UMP mediator *)
    intros [[d u] h]; simpl in *.
    exists (unique_obj (ump_couniversal_arrows U h), ttt).
    simpl.
    (* [simpl] has already reduced fmap[=(c)] ttt to id[c] *)
    rewrite id_left.
    symmetry.
    exact (unique_property (ump_couniversal_arrows U h)).
  - (* two arrows into it agree: the D-components by UMP uniqueness, the
       1-components because `1` has exactly one arrow *)
    intros [[d u] h] [[f1 f2] Hf] [[g1 g2] Hg]; simpl in *.
    rewrite ?fmap_id, ?id_left in Hf, Hg.
    split.
    + rewrite <- (uniqueness (ump_couniversal_arrows U h) f1 (symmetry Hf)).
      exact (uniqueness (ump_couniversal_arrows U h) g1 (symmetry Hg)).
    + now destruct f2, g2.
Defined.

(* The transported structure chooses the couniversal object on the nose --
   what makes [couniversal_arrow_terminal] a transport rather than a bare
   existence claim, in the idiom of [Terminal_iso_obj] (Structure/Initial.v).
   Convertibility of OBJECTS, not an equation between morphisms. *)
Corollary couniversal_arrow_terminal_obj {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) :
  `1 (@terminal_obj _ (couniversal_arrow_terminal U)) = (coarrow_obj U, ttt).
Proof. reflexivity. Qed.

(* ... and back: a terminal object of F ↓ =(c) is a couniversal arrow. *)
Definition couniversal_arrow_of_terminal {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : CouniversalArrow c F.
Proof.
  destruct T as [t one one_unique].
  destruct t as [[a u] ε]; simpl in *.
  unshelve eapply (couniversal_arrow_from_UMP c F a ε).
  intros d' f.
  (* every factorization of f through ε satisfies the comma square, whose
     =(c)-leg computes to id[c].  Kept as a bare square proof rather than as a
     packaged comma morphism so that the pairs below are literal sigmas: the
     [fst `1] projections of an opaque hypothesis would not reduce. *)
  assert (sq : ∀ v : d' ~{D}~> a, f ≈ ε ∘ fmap[F] v →
                 ε ∘ fmap[F] v ≈ id{C} ∘ f).
  { intros v Hv.
    rewrite id_left.
    now symmetry. }
  destruct (one (((d', ttt); f))) as [[g1 g2] Hg]; simpl in Hg.
  rewrite id_left in Hg.
  unshelve eexists g1.
  - now symmetry.
  - intros v Hv.
    exact (fst (one_unique (((d', ttt); f))
                           ((g1, ttt); sq g1 (symmetry Hg))
                           ((v, ttt); sq v Hv))).
Defined.

(** ** Uniqueness up to a unique isomorphism *)

(* The duals of the mediator calculus added to Theory/Universal/Arrow.v for
   Awodey's Proposition 1.10.  Each is the primal statement read in the
   opposite categories, so each is supplied by [:=] or by a one-line [exact];
   note that the ARGUMENT ORDER swaps, since the op-side mediator
   `arrow_obj U1 ~{D^op}~> arrow_obj U2` is covariantly a morphism
   `coarrow_obj U2 ~> coarrow_obj U1`. *)

Section CouniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

(* The canonical mediating morphism: the unique factorization of the FIRST
   couniversal arrow through the SECOND (dual to the primal orientation). *)
Definition cua_med (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ~{D}~> coarrow_obj U2 :=
  @ua_med (C^op) (D^op) c (Opposite_Functor F) U2 U1.

Lemma cua_med_commutes (U1 U2 : CouniversalArrow c F) :
  coarrow U2 ∘ fmap[F] (cua_med U1 U2) ≈ coarrow U1.
Proof. exact (@ua_med_commutes (C^op) (D^op) c (Opposite_Functor F) U2 U1). Qed.

(* Any morphism commuting with the two couniversal arrows IS the mediator. *)
Lemma cua_med_unique (U1 U2 : CouniversalArrow c F)
      (g : coarrow_obj U1 ~{D}~> coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] g ≈ coarrow U1 → cua_med U1 U2 ≈ g.
Proof.
  exact (@ua_med_unique (C^op) (D^op) c (Opposite_Functor F) U2 U1 g).
Qed.

Lemma cua_med_id (U1 : CouniversalArrow c F) : cua_med U1 U1 ≈ id.
Proof. exact (@ua_med_id (C^op) (D^op) c (Opposite_Functor F) U1). Qed.

Lemma cua_med_comp (U1 U2 U3 : CouniversalArrow c F) :
  cua_med U2 U3 ∘ cua_med U1 U2 ≈ cua_med U1 U3.
Proof. exact (@ua_med_comp (C^op) (D^op) c (Opposite_Functor F) U3 U2 U1). Qed.

(* The two mediators are mutually inverse, so the couniversal objects are
   isomorphic.  [Isomorphism_Opposite] reads the op-side isomorphism back
   into `(D^op)^op`, which IS `D`; it exchanges [to] and [from], which is
   exactly what makes the [to] component come out as [cua_med U1 U2]. *)
Definition couniversal_arrow_iso (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ≅ coarrow_obj U2 :=
  @Isomorphism_Opposite (D^op) _ _
    (@universal_arrow_iso (C^op) (D^op) c (Opposite_Functor F) U1 U2).

Corollary couniversal_arrow_iso_to (U1 U2 : CouniversalArrow c F) :
  to (couniversal_arrow_iso U1 U2) ≈ cua_med U1 U2.
Proof. reflexivity. Qed.

Corollary couniversal_arrow_iso_from (U1 U2 : CouniversalArrow c F) :
  from (couniversal_arrow_iso U1 U2) ≈ cua_med U2 U1.
Proof. reflexivity. Qed.

Lemma couniversal_arrow_iso_unique (U1 U2 : CouniversalArrow c F)
      (v : coarrow_obj U1 ≅ coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] (to v) ≈ coarrow U1 →
  couniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply cua_med_unique.
Qed.

(* Awodey's Proposition 1.10, dualized: exactly one isomorphism of the
   couniversal objects carries the second couniversal arrow to the first. *)
Program Definition couniversal_arrow_unique
        (U1 U2 : CouniversalArrow c F) :
  Unique (fun i : coarrow_obj U1 ≅ coarrow_obj U2 =>
            coarrow U2 ∘ fmap[F] (to i) ≈ coarrow U1) := {|
  unique_obj      := couniversal_arrow_iso U1 U2;
  unique_property := cua_med_commutes U1 U2
|}.
Next Obligation. exact (couniversal_arrow_iso_unique U1 U2 v X). Qed.

End CouniversalArrowUnique.

(** ** From couniversal arrows to a right adjoint *)

Context (F : @Functor D C).

(* A couniversal arrow from F to every object c : C assembles into a right
   adjoint of F.  The object map sends c to its couniversal object, and the
   morphism map sends f : x ~> y to the unique factorization of f ∘ coarrow
   through coarrow_obj y.  Both are read off [Opposite_Functor] applied to the
   primal assembly, so `C ⟶ D` is the type on the nose -- no comparison
   functor and no transport. *)
Definition RightAdjointFunctorFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) : @Functor C D :=
  Opposite_Functor
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H).

(* The object action is [coarrow_obj] by convertibility -- what makes the
   op-route usable rather than merely type-correct. *)
Corollary right_adjoint_obj (H : forall c : C, CouniversalArrow c F) (c : C) :
  fobj[RightAdjointFunctorFromCouniversalArrows H] c = coarrow_obj (H c).
Proof. reflexivity. Qed.

(* The induced functor is genuinely right adjoint to F, with the couniversal
   arrows serving as the components of the counit.  [Opposite_Adjunction]
   supplies the whole proof: `(C^op)^op = C` and `(F^op)^op = F` both hold by
   [reflexivity], so the dual of the opposite-side adjunction lands at
   `F ⊣ RightAdjointFunctorFromCouniversalArrows H` with nothing to
   transport. *)
Definition AdjunctionFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) :
  F ⊣ RightAdjointFunctorFromCouniversalArrows H :=
  Opposite_Adjunction
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H)
    (Opposite_Functor F)
    (@AdjunctionFromUniversalArrows (C^op) (D^op) (Opposite_Functor F) H).

(* The counit of that adjunction is the couniversal arrow.  Only up to `≈`:
   the transpose delivers `coarrow ∘ fmap[F] id`, which is one [fmap_id] and
   one [id_right] short of [eq_refl].  See the header's second boundary; the
   negative half is pinned in Test/ProbeCouniversal.v. *)
Lemma counit_couniversal (H : forall c : C, CouniversalArrow c F) (c : C) :
  @counit C D F (RightAdjointFunctorFromCouniversalArrows H)
          (AdjunctionFromCouniversalArrows H) c ≈ coarrow (H c).
Proof.
  unfold counit; simpl.
  rewrite fmap_id.
  apply id_right.
Qed.

(** ** The direct encoding *)

(* The same notion stated directly, with the couniversal object a : D given as
   a parameter rather than projected out.  Definitionally [AUniversalArrow] in
   the opposite categories, exactly as [CouniversalArrow] is [UniversalArrow]
   there. *)
Definition ACouniversalArrow (c : C) (G : D ⟶ C) (a : D) : Type :=
  @AUniversalArrow (C^op) (D^op) c (Opposite_Functor G) a.

Existing Class ACouniversalArrow.

(* The couniversal morphism ε : F a ~> c, covariantly. *)
Definition couniversal_arrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : G a ~{C}~> c :=
  @universal_arrow (C^op) (D^op) c (Opposite_Functor G) a U.

(* ... and its universal property, in the orientation the primal field has
   ([fmap ∘ arrow ≈ f] there, [arrow ∘ fmap ≈ f] here). *)
Definition couniversal_arrow_couniversal {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) {d : D} {f : G d ~{C}~> c} :
  Unique (fun g : d ~{D}~> a => couniversal_arrow U ∘ fmap[G] g ≈ f) :=
  @universal_arrow_universal (C^op) (D^op) c (Opposite_Functor G) a U d f.

(* Two couniversal arrows at the same object are equivalent when their
   underlying morphisms agree; the op-read of [AUniversalArrowEquiv]. *)
#[export] Instance ACouniversalArrowEquiv (c : C) (G : D ⟶ C) (a : D) :
  Setoid (ACouniversalArrow c G a) :=
  @AUniversalArrowEquiv (C^op) (D^op) c (Opposite_Functor G) a.

Section ACouniversalArrowUnique.

Context {c : C}.
Context {G : D ⟶ C}.

Definition acua_med {a b : D} (U1 : ACouniversalArrow c G a)
           (U2 : ACouniversalArrow c G b) : a ~{D}~> b :=
  @aua_med (C^op) (D^op) c (Opposite_Functor G) b a U2 U1.

Lemma acua_med_commutes {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) :
  couniversal_arrow U2 ∘ fmap[G] (acua_med U1 U2) ≈ couniversal_arrow U1.
Proof.
  exact (@aua_med_commutes (C^op) (D^op) c (Opposite_Functor G) b a U2 U1).
Qed.

Lemma acua_med_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (g : a ~{D}~> b) :
  couniversal_arrow U2 ∘ fmap[G] g ≈ couniversal_arrow U1 → acua_med U1 U2 ≈ g.
Proof.
  exact (@aua_med_unique (C^op) (D^op) c (Opposite_Functor G) b a U2 U1 g).
Qed.

Lemma acua_med_id {a : D} (U1 : ACouniversalArrow c G a) : acua_med U1 U1 ≈ id.
Proof. exact (@aua_med_id (C^op) (D^op) c (Opposite_Functor G) a U1). Qed.

Lemma acua_med_comp {a b e : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (U3 : ACouniversalArrow c G e) :
  acua_med U2 U3 ∘ acua_med U1 U2 ≈ acua_med U1 U3.
Proof.
  exact (@aua_med_comp (C^op) (D^op) c (Opposite_Functor G) e b a U3 U2 U1).
Qed.

Definition acouniversal_arrow_iso {a b : D} (U1 : ACouniversalArrow c G a)
        (U2 : ACouniversalArrow c G b) : a ≅ b :=
  @Isomorphism_Opposite (D^op) _ _
    (@auniversal_arrow_iso (C^op) (D^op) c (Opposite_Functor G) a b U1 U2).

Lemma acouniversal_arrow_iso_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (v : a ≅ b) :
  couniversal_arrow U2 ∘ fmap[G] (to v) ≈ couniversal_arrow U1 →
  acouniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply acua_med_unique.
Qed.

Program Definition acouniversal_arrow_unique {a b : D}
        (U1 : ACouniversalArrow c G a) (U2 : ACouniversalArrow c G b) :
  Unique (fun i : a ≅ b =>
            couniversal_arrow U2 ∘ fmap[G] (to i) ≈ couniversal_arrow U1) := {|
  unique_obj      := acouniversal_arrow_iso U1 U2;
  unique_property := acua_med_commutes U1 U2
|}.
Next Obligation. exact (acouniversal_arrow_iso_unique U1 U2 v X). Qed.

End ACouniversalArrowUnique.

(** ** The two encodings agree *)

(* Theory/Universal/Arrow.v carries both encodings but never relates them;
   here the passage is cheap in both directions, so it is supplied.  Note the
   orientations of the two universal properties differ by a [symmetry]
   ([h ≈ ε ∘ fmap g] in the comma-packaged form, [ε ∘ fmap g ≈ f] in the
   direct one), which is the whole content of the two proofs. *)

Definition ACouniversalArrow_of_CouniversalArrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) : ACouniversalArrow c G (coarrow_obj U).
Proof.
  unshelve econstructor.
  - exact (coarrow U).
  - intros d f.
    unshelve eexists (unique_obj (ump_couniversal_arrows U f)).
    + symmetry; exact (unique_property (ump_couniversal_arrows U f)).
    + intros v Hv.
      exact (uniqueness (ump_couniversal_arrows U f) v (symmetry Hv)).
Defined.

Definition CouniversalArrow_of_ACouniversalArrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : CouniversalArrow c G.
Proof.
  unshelve eapply (couniversal_arrow_from_UMP c G a (couniversal_arrow U)).
  intros d' f.
  unshelve eexists (unique_obj (@couniversal_arrow_couniversal c G a U d' f)).
  - symmetry.
    exact (unique_property (@couniversal_arrow_couniversal c G a U d' f)).
  - intros v Hv.
    exact (uniqueness (@couniversal_arrow_couniversal c G a U d' f) v
             (symmetry Hv)).
Defined.

(* The passage keeps the arrow on the nose in one direction ... *)
Corollary ACouniversalArrow_of_CouniversalArrow_arrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) :
  couniversal_arrow (ACouniversalArrow_of_CouniversalArrow U) = coarrow U.
Proof. reflexivity. Qed.

(* ... and in the other. *)
Corollary CouniversalArrow_of_ACouniversalArrow_arrow {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow (CouniversalArrow_of_ACouniversalArrow U) = couniversal_arrow U.
Proof. reflexivity. Qed.

Corollary CouniversalArrow_of_ACouniversalArrow_obj {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow_obj (CouniversalArrow_of_ACouniversalArrow U) = a.
Proof. reflexivity. Qed.

End CouniversalArrow.

Arguments CouniversalArrow {C D} c F.
Arguments ACouniversalArrow {C D} c G a.
