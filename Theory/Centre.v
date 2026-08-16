Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * The centre of a category *)

(* nLab:      https://ncatlab.org/nlab/show/center+of+a+category
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.5 Exercise 8 (printed p. 45)          [maclane:II.5:ex8]
   Book:      Riehl, "Category Theory in Context", §1.7 Exercise 1.7.iv
              (printed p. 51)                           [riehl:1.7:exiv]

   The CENTRE of a category C is the collection of natural transformations
   from the identity functor to itself,

       Z(C)  :=  End(Id[C])  =  (Id[C] ⟹ Id[C]),

   under vertical composition.  Mac Lane's Exercise 8 and Riehl's Exercise
   1.7.iv ask for the same thing: show that these form a COMMUTATIVE monoid.
   Mac Lane sets it in the same exercise list as the Eckmann–Hilton argument
   (§II.5 Exercise 5, proved in this tree as Theory/EckmannHilton.v), and
   this file is that exercise, together with the packaging that explains why
   the two sit in the same list.

   The commutativity is a one-line consequence of naturality, and the line
   is worth writing out because it is easy to mistake for something deeper.
   Let α, β : Id ⟹ Id and fix an object x.  The component `β x` is itself a
   morphism `x ~> x`, so it is a legal argument for α's naturality square,
   and that square reads

       fmap[Id] (β x) ∘ α x  ≈  α x ∘ fmap[Id] (β x).

   Since `fmap[Id]` is the identity on morphisms — definitionally so in this
   library, `Id`'s field being `fun _ _ f => f` (Theory/Functor.v:248) — the
   square IS

       β x ∘ α x  ≈  α x ∘ β x,

   which is commutativity at x.  No unit is needed, no padding, no
   interchange law: the naturality of one centre element AT the component of
   another is already the statement.  That is [centre_commutes_at] below,
   and [centre_commutative] is its componentwise packaging in the hom-setoid
   of `[C, C]`.

   Note what the argument does NOT need.  It never uses β's naturality, only
   α's; it never uses `fmap_comp` or `fmap_id`; and it holds in every
   category whatsoever, with no completeness, size, or local smallness
   hypothesis.  The centre is therefore always defined and always
   commutative, though it may well be trivial ([centre_Sets_trivial] below
   shows that it is trivial for `Sets`). *)

(* Why this is the arity-zero shadow of Eckmann–Hilton

   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/center+of+a+category
   Paper: Eckmann, Hilton, "Group-like structures in general categories I",
          Mathematische Annalen 145, 1962

   Read one level up.  A category C is a one-object bicategory's worth of
   structure sitting inside Cat: `[C, C]` is a hom-category of Cat, its
   objects (functors) are 1-cells and its morphisms (natural
   transformations) are 2-cells, and Id[C] is the identity 1-cell.  The
   2-cells on an identity 1-cell are exactly the position at which the
   Eckmann–Hilton collapse bites: vertical and horizontal composition
   normally have DIFFERENT units — Theory/TwoCategory.v (:167-171) makes
   that point explicitly, and it is why a 2-category does not degenerate —
   but on an identity 1-cell the two units coincide, the argument applies,
   and the monoid of such 2-cells is forced to be commutative.

   In this tree the collapse was already visible concretely before it was
   stated in general.  Instance/Cat/TwoCategory.v's [NatBase_centre]
   (~:422-436) exhibits the 2-cells on the identity functor of the delooping
   of (ℕ, +): every natural number gives one, and their vertical and
   horizontal composites both compute to addition BY [eq_refl]
   ([NatBase_centre_vcomp], [NatBase_centre_hcomp]).  That file's comment
   names the present exercise as what it is illustrating.  This file
   supplies the general theorem those examples instantiate.

   The same one-object reading is what makes the centre a monoid in the
   sense the library already has: Construction/Deloop.v's [hom_monoid C a]
   turns the endomorphism hom-setoid of any object of any category into a
   [MonObject], every monoid law being a category law by projection.  Taking
   C := `[C, C]` and a := Id[C] gives the centre with no new proof
   obligations at all — [centre_monoid] below is literally that application,
   and the three data fields of the resulting monoid (carrier, unit,
   operation) are the transformation setoid, [nat_id] and [nat_compose],
   each recorded by [eq_refl].  What this file must supply on its own is the
   one thing [hom_monoid] cannot know: commutativity.

   HONESTY ABOUT THE EH ROUTE.  The exercise's traditional packaging
   presents the centre as an Eckmann–Hilton situation and reads
   commutativity off the general argument.  That packaging is delivered
   below ([centre_commutative_EH]), and it is a genuine invocation of
   Theory/EckmannHilton.v's [eh_comm] with all seven hypotheses discharged.
   It is NOT, however, an independent derivation of commutativity, and this
   file says so in two machine-checked ways rather than in prose:

   (1) The second operation is not an independent operation.  At the
       identity functor the Godement (horizontal) composite has the SAME
       components as the vertical one — [centre_hcompose_is_vcomp] records
       `transform[nat_hcompose α β] x = transform[nat_compose α β] x` by
       [eq_refl], and both whiskerings against Id are the identity on
       components ([centre_whisker_left], [centre_whisker_right]).  So the
       "two operations" the argument wants are one operation and that same
       operation with its arguments swapped.

   (2) The interchange hypothesis already contains the conclusion.
       [centre_interchange_forces_commutative] derives commutativity from
       interchange by instantiating two of its four arguments at the unit
       and cancelling with the unit laws — no padding argument, no
       [eh_units] step, no appeal to Theory/EckmannHilton.v at all.  So no
       proof of interchange for these operations can be weaker than
       commutativity, and indeed [centre_interchange]'s proof below consumes
       [centre_commutes_at] literally.

   The EH route is therefore a CONSISTENCY EXHIBIT: it shows that the centre
   genuinely is an Eckmann–Hilton situation and that the abstract engine
   applies to it, which is the mathematical content of putting the two
   exercises next to each other.  It is not a second, independent proof.
   Theory/EckmannHilton.v's own header anticipates exactly this ("there they
   genuinely share a unit, which is precisely the special position that
   makes the collapse bite"); this file is that engine's third consumer,
   after Structure/Semiadditive.v (which uses [eh_ops], [eh_comm] and
   [eh_assoc] for its two convolutions) and Instance/Top/LoopSpace.v (which
   uses the packaged [eckmann_hilton]).  Instance/Cat/TwoCategory.v does NOT
   import it: its [NatBase_centre] examples exhibit the collapse by
   computation rather than by invoking the theorem. *)

(* THREE DIFFERENT THINGS ARE CALLED A CENTRE.  All three are in this tree,
   and they are of three different KINDS.  Naming them together once is
   cheaper than disambiguating them repeatedly downstream.

   - THIS centre: the natural endotransformations of the identity functor,
     `Id[C] ⟹ Id[C]`, under vertical composition.  A commutative MONOID.
     Defined for an arbitrary category, no extra structure required.
     Mac Lane §II.5 Exercise 8; Riehl Exercise 1.7.iv.

   - The PREMONOIDAL centre: the central MORPHISMS of a binoidal category —
     those whose two whiskerings commute with everything — assembled into a
     wide subcategory.  A CATEGORY, namely `Centre C` of
     Structure/Binoidal/Central.v:256 (built from [CentralSub], :232), given
     a monoidal structure in Structure/Premonoidal/Centre.v.  Requires a
     binoidal/premonoidal ambient structure.

   - The DRINFELD (monoidal) centre: objects of a monoidal category equipped
     with a half-braiding, with intertwiners as morphisms.  A BRAIDED
     MONOIDAL CATEGORY, `Drinfeld` of Structure/Monoidal/Drinfeld.v:138,
     with [Drinfeld_Braided] and the forgetful [Drinfeld_Forget].  Requires
     a monoidal ambient structure.

   The bare name [Centre] is DELIBERATELY NOT taken here: it already belongs
   to Structure/Binoidal/Central.v, and a second [Centre] in Theory/ would
   make any file importing both ambiguous.  The names below are all
   lower-case and prefixed ([centre_setoid], [centre_monoid],
   [centre_commutative]).

   REMARKS ON CONCRETE CENTRES, not computed here.  For `Sets` the centre is
   trivial, and that IS proved below ([centre_Sets_trivial]) — the argument
   is the standard one, probe naturality with the map out of a singleton
   that picks a point.  For Grp and Ab the answer is more interesting, and
   it is NOT computed in this tree.  The expected answer for FINITELY
   GENERATED abelian groups is the multiplicative monoid (ℤ, ·), each
   integer n acting on every group by the n-fold sum — a family that is
   natural because every homomorphism preserves sums — via the route of
   Riehl's Proposition 1.4.6, per the issue catalog; pinning it down
   (rather than merely exhibiting the family) needs machinery this tree
   does not have.
   These two sentences are a REMARK, not a claim about anything proved here,
   and nothing below depends on them. *)

(** ** The centre as a setoid and as a monoid *)

Section Centre.

Context {C : Category}.

(* The carrier: the hom-setoid of the functor category `[C, C]` at the
   identity functor.  This is the categorical home of the centre — the
   objects of `[C, C]` are functors and its morphisms are natural
   transformations (Instance/Fun.v), so `Id[C] ~{[C, C]}~> Id[C]` is
   `Id[C] ⟹ Id[C]` and the setoid is [Transform_Setoid], comparing two
   transformations componentwise. *)
Definition centre_setoid : SetoidObject := {|
  carrier   := @hom ([C, C]) Id[C] Id[C];
  is_setoid := @homset ([C, C]) Id[C] Id[C]
|}.

(* The monoid structure needs no proof: it is Construction/Deloop.v's
   endomorphism monoid of the object Id[C] of the category `[C, C]`.  The
   associativity and unit laws are taken by PROJECTION from `[C, C]`'s own
   [comp_assoc], [id_left] and [id_right] — the fields Instance/Fun.v's
   [Fun] discharges — and not from that file's standalone restatements
   [nat_comp_assoc], [nat_id_left], [nat_id_right], which are separate
   corollaries.  (The last two are used below, for the EH route's unit
   hypotheses, where they are what is wanted; [nat_comp_assoc] is not
   consumed in this file.) *)
Definition centre_monoid : MonObject := hom_monoid ([C, C]) Id[C].

(* The three data fields, definitionally.  [Set Primitive Projections] gives
   record eta, so the carrier equation is an equation of records. *)

Example centre_monoid_setoid : mon_setoid centre_monoid = centre_setoid
  := eq_refl.

Example centre_monoid_carrier :
  carrier centre_monoid = (Id[C] ⟹ Id[C]) := eq_refl.

Example centre_monoid_unit :
  @mon_unit centre_monoid = @nat_id C C Id[C] := eq_refl.

Example centre_monoid_op :
  @mon_op centre_monoid = @nat_compose C C Id[C] Id[C] Id[C] := eq_refl.

(** ** Commutativity, directly from naturality *)

(* The whole content of the exercise, at a single object.  Read α's
   naturality square at the morphism `transform[β] x : x ~> x`; because
   `fmap[Id]` is definitionally the identity on morphisms, the square is
   already the commutation.  Only α's naturality is used. *)
Lemma centre_commutes_at (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[α] x ∘ transform[β] x ≈ transform[β] x ∘ transform[α] x.
Proof.
  symmetry.
  exact (naturality[α] x x (transform[β] x)).
Qed.

(* The centre is a COMMUTATIVE monoid: vertical composition of natural
   endotransformations of the identity functor is commutative.  This is the
   pinned constant of Mac Lane §II.5 Exercise 8 / Riehl Exercise 1.7.iv. *)
Theorem centre_commutative (α β : Id[C] ⟹ Id[C]) :
  nat_compose α β ≈[Fun] nat_compose β α.
Proof.
  intro x.
  exact (centre_commutes_at α β x).
Qed.

(* The same statement read through the monoid packaging, so that a consumer
   holding [centre_monoid] can quote commutativity in the monoid's own
   vocabulary. *)
Corollary centre_monoid_commutative (α β : carrier centre_monoid) :
  mon_op α β ≈ mon_op β α.
Proof. exact (centre_commutative α β). Qed.

End Centre.

(** ** The Eckmann–Hilton packaging *)

(* The traditional route: exhibit two unital operations that interchange and
   invoke Theory/EckmannHilton.v.  Everything in this section is honest
   about being a consistency exhibit rather than an independent derivation;
   see the header, and see [centre_interchange_forces_commutative] at the
   end of the section for the machine-checked form of that claim. *)

Section CentreEH.

Context {C : Category}.

(* The first operation is vertical composition.  The second is the SAME
   composition with its arguments swapped — which, by
   [centre_vcomp_op_is_hcompose] below, is exactly the Godement horizontal
   composite in the other order, the two agreeing on components at the
   identity functor. *)

Definition centre_vcomp (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose α β.

Definition centre_vcomp_op (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose β α.

(* Components, definitionally: `f` composes in the given order, `g` in the
   opposite one. *)

Example centre_vcomp_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp α β] x = transform[α] x ∘ transform[β] x := eq_refl.

Example centre_vcomp_op_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[β] x ∘ transform[α] x
  := eq_refl.

(** *** The second operation IS the horizontal composite, componentwise *)

(* [nat_hcompose ε η : J ◯ F ⟹ K ◯ G] lands at `Id ◯ Id`, not at `Id`, so
   the two transformations do not have the same TYPE and no equation between
   them can be written without a transport.  Componentwise they need none:
   `(Id ◯ Id) x` reduces to `x`, so both components inhabit `x ~> x` and the
   identification is [eq_refl].  This is stated componentwise deliberately;
   no isomorphism [nat_ρ]/[nat_λ] is inserted and none is claimed. *)

Example centre_hcompose_is_vcomp (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[nat_hcompose α β] x = transform[nat_compose α β] x := eq_refl.

Example centre_vcomp_op_is_hcompose (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[nat_hcompose β α] x := eq_refl.

(* Both whiskerings against the identity functor are the identity on
   components, which is the other half of the same observation. *)

Example centre_whisker_left (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[Id[C] ⊳ α] x = transform[α] x := eq_refl.

Example centre_whisker_right (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[α ⊲ Id[C]] x = transform[α] x := eq_refl.

(** *** The seven hypotheses of [eh_comm] *)

(* Respectfulness: both operations are [nat_compose] up to argument order,
   so both are [nat_compose_respects] (the second with its two arguments
   exchanged). *)

Definition centre_vcomp_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp.
Proof. repeat intro; now apply nat_compose_respects. Qed.

Definition centre_vcomp_op_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp_op.
Proof. repeat intro; now apply nat_compose_respects. Qed.

(* The four unit laws.  Both operations take [nat_id] as a two-sided unit —
   this is the coincidence of units that makes the Eckmann–Hilton argument
   applicable at all, and here it is not an accident of the construction but
   the fact that both operations ARE vertical composition.  The laws are
   Instance/Fun.v's [nat_id_left] and [nat_id_right], used crosswise for the
   opposite-order operation. *)

Definition centre_vcomp_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp nat_id α ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

Definition centre_vcomp_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp α nat_id ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op nat_id α ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op α nat_id ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

(* The interchange law, in the orientation Theory/EckmannHilton.v states it:
   `f (g a b) (g c d) ≈ g (f a c) (f b d)`.

   Componentwise the goal is `(b ∘ a) ∘ (d ∘ c) ≈ (b ∘ d) ∘ (a ∘ c)`;
   reassociating both sides to `b ∘ (_ ∘ _) ∘ c` leaves exactly
   `a ∘ d ≈ d ∘ a`, and there is nothing to appeal to for that but the
   naturality square — i.e. [centre_commutes_at], which the proof therefore
   uses LITERALLY.  This is the disclosure the header promises: the
   interchange hypothesis of the EH route is not cheaper than its
   conclusion. *)
Lemma centre_interchange (a b c d : Id[C] ⟹ Id[C]) :
  centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
    ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d).
Proof.
  intro x.
  simpl.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity].
  exact (centre_commutes_at a d x).
Qed.

(** *** Commutativity via [eh_comm] *)

(* All seven hypotheses discharged, the abstract argument applied.  The
   conclusion is [centre_commutative] again, reached the long way. *)
Theorem centre_commutative_EH (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp β α.
Proof.
  exact (eh_comm centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(* [eh_ops] — the Eckmann–Hilton conclusion that the two operations
   COINCIDE — degenerates here into commutativity a second time, since the
   second operation is the first with its arguments swapped.  Recording it
   makes the degeneration visible instead of leaving it implicit. *)
Corollary centre_EH_ops (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp_op α β.
Proof.
  exact (eh_ops centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(* Likewise [eh_units]: the two units coincide.  Here they were literally
   the same transformation to begin with, so the general theorem's first
   conclusion is [reflexivity] at this instance — another measurement of how
   degenerate the EH situation is at the centre. *)
Corollary centre_EH_units : (nat_id : Id[C] ⟹ Id[C]) ≈[Fun] nat_id.
Proof.
  exact (eh_units centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange).
Qed.

(** *** Why the EH route cannot be independent *)

(* The claim, machine-checked.  Take the interchange law as a HYPOTHESIS —
   not the proved [centre_interchange], but any statement of that shape —
   and instantiate its second and third arguments at [nat_id].  The unit
   laws then collapse it directly to commutativity, with no padding
   argument, no [eh_units] step, and no appeal to Theory/EckmannHilton.v.
   So interchange for these two operations is not a weaker input than the
   conclusion it is supposed to produce, and the EH packaging above is a
   consistency exhibit rather than a second proof. *)
Theorem centre_interchange_forces_commutative
  (inter : ∀ a b c d : Id[C] ⟹ Id[C],
      centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
        ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d))
  (α δ : Id[C] ⟹ Id[C]) :
  centre_vcomp α δ ≈[Fun] centre_vcomp δ α.
Proof.
  (* Instantiate at (α, 1, 1, δ), writing 1 for [nat_id]:

       f (g α 1) (g 1 δ)  ≈  g (f α 1) (f 1 δ).

     Componentwise that is `(1 ∘ α x) ∘ (δ x ∘ 1) ≈ (1 ∘ δ x) ∘ (α x ∘ 1)`,
     and cancelling the four units leaves `α x ∘ δ x ≈ δ x ∘ α x`, which is
     the goal.  Only [id_left] and [id_right] are spent. *)
  specialize (inter α nat_id nat_id δ).
  intro x.
  specialize (inter x).
  simpl in *.
  rewrite !id_left, !id_right in inter.
  exact inter.
Qed.

End CentreEH.

(** ** The centre of Sets is trivial *)

(* Mac Lane asks for the centre of Set.  The probe is the standard one: a
   point of a setoid X is the same thing as a morphism into X from the
   singleton, and naturality of α at that morphism pins α's component at X
   to the identity.

   Concretely, for `x : carrier X` let `pick x : 1 ~> X` be the constant map.
   Naturality of α at `pick x`, evaluated at the sole element `ttt`, reads

       pick x (α_1 ttt)  ≈  α_X (pick x ttt),

   whose left side is `x` (the map is constant) and whose right side is
   `α_X x`.  Note that the value of `α` at the singleton is never inspected:
   it is absorbed by the constancy of the probe, which is why the argument
   needs no decidability, no choice, and no extensionality. *)

(* The singleton setoid used as the probe's domain is the carrier of
   [Sets_Terminal] (Instance/Sets.v:253), [poly_unit] under `=`.

   UNIVERSE ANNOTATION, and why it is not decoration.  `Sets@{o so}` has
   carriers at `o` and objects at `so` (Instance/Sets.v:193).  Written
   without the annotations below, universe minimization instantiates the
   probe's carrier as `poly_unit@{Set}` and, through the object type, pins
   `o := Set` — so the theorems would speak only of setoids whose carriers
   live in `Set`.  Naming `o` and `so` and writing `poly_unit@{o}` keeps
   both free, and the statements then apply to `Sets` at every level. *)
Program Definition centre_Sets_point@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) :
  ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) ~{Sets@{o so}}~> X := {|
  morphism := fun _ => x
|}.

(* The probe's underlying function is given literally, so it computes; the
   [Program] wrapper touches only the respectfulness certificate.  Recorded
   because [centre_Sets_trivial] below relies on the reduction. *)
Example centre_Sets_point_computes@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) (u : poly_unit@{o}) : centre_Sets_point x u = x := eq_refl.

(* Pointwise form: every centre element of `Sets` acts as the identity on
   every point of every setoid. *)
Theorem centre_Sets_trivial@{o so} (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}])
  (X : obj[Sets@{o so}]) (x : carrier X) : transform[α] X x ≈ x.
Proof.
  symmetry.
  exact (naturality[α] ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) X
           (centre_Sets_point x) ttt).
Qed.

(* Packaged form: every centre element of `Sets` IS the identity
   transformation, in the hom-setoid of `[Sets, Sets]`. *)
Corollary centre_Sets_trivial_nat@{o so}
  (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Sets_trivial.
Qed.

(* Hence the centre of `Sets` is a singleton: it is the trivial monoid. *)
Corollary centre_Sets_subsingleton@{o so}
  (α β : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] β.
Proof.
  transitivity (@nat_id Sets@{o so} Sets@{o so} Id[Sets@{o so}]).
  - apply centre_Sets_trivial_nat.
  - symmetry; apply centre_Sets_trivial_nat.
Qed.

(** ** The centre of Coq is trivial *)

(* The same probe over Instance/Coq.v, where the hom-setoid is pointwise
   Leibniz equality (Instance/Coq.v:123), so the conclusion is an equation
   rather than an `≈`.  It costs nothing beyond changing the probe's
   codomain, and it is included because it is the reading a programmer
   expects: a polymorphic function `forall a, a -> a` is the identity. *)

Theorem centre_Coq_trivial (α : Id[Coq] ⟹ Id[Coq])
  (X : obj[Coq]) (x : X) : transform[α] X x = x.
Proof.
  symmetry.
  exact (naturality[α] poly_unit X (fun _ => x) ttt).
Qed.

Corollary centre_Coq_trivial_nat (α : Id[Coq] ⟹ Id[Coq]) :
  α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Coq_trivial.
Qed.
