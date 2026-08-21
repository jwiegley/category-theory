Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * [Sets] is cocomplete *)

(* nLab:      https://ncatlab.org/nlab/show/cocomplete+category
   nLab:      https://ncatlab.org/nlab/show/colimit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   Mac Lane, "Categories for the Working Mathematician" 2nd ed., Springer
   GTM 5 1998, §III.3 (pp. 67-68), where the colimit of a diagram of sets
   is the disjoint union of the [F d] with the images of the connecting
   maps identified; and §V.1 Exercise 8, "Set is cocomplete", which asks
   for the GENERAL statement -- all small colimits -- and not only the
   union of an increasing chain.  Riehl, "Category Theory in Context",
   Dover 2016, §3.1 Example 3.1.26 is the same computation.

   [Cocomplete C] is [∀ (D : Category) (F : D ⟶ C), Colimit F]
   (Structure/Complete.v:119) and [Colimit F] is [Limit (F^op)]
   (Structure/Limit.v:158): an oracle assigning a chosen colimit to every
   diagram.  This file inhabits it at [Sets], as the mirror of
   Instance/Sets/Complete.v.  Five in-tree notes across four files record
   the absence this answers -- Instance/Sets/Complete.v:106 ("[Cocomplete
   Sets] is NOT provided"), Instance/Sets/Coequalizer.v:62 and :144,
   Instance/Sets/Quotient.v:157, and Instance/Sets/Products.v:236, whose
   "cocompleteness is not addressed at all, here or anywhere else in the
   tree" is the flattest of the five -- and it sits in the very file that
   supplies [Sets_icoprod_obj], this construction's own donor.  None of
   those files is edited here: the notes are left UNCORRECTED, and every
   one of them is now STALE.  An earlier draft of this paragraph counted
   THREE and said the notes "still stand as written" -- wrong twice over,
   missing Products.v:236 and Coequalizer.v:144, and phrasing staleness in
   words that read as continued truth.

   THE CONSTRUCTION

   The colimit of [F : D ⟶ Sets] is the indexed coproduct of the diagram's
   objects, quotiented by the equivalence relation that the connecting
   maps generate.  Three named pieces:

     [Sets_colim_sum]   is [Sets_icoprod_obj (fun d : D => F d)], the sigma
                        setoid of Instance/Sets/Products.v -- an element is
                        a pair [(d; x)] with [x] an element of [F d];

     [colim_rel]        is the inductive relation on that carrier with two
                        generating clauses, [cr_point] (the fibre
                        equivalence: [x ≈ y] in [F d] relates [(d; x)] and
                        [(d; y)]) and [cr_glue] (the diagram glue: [(d; x)]
                        is related to [(d'; fmap[F] f x)] for every
                        [f : d ~> d']), closed under [cr_sym] and
                        [cr_trans], with reflexivity DERIVED as
                        [colim_rel_refl] rather than taken as a fifth
                        constructor -- so the induction has four cases,
                        exactly the shape of [coend_eq] in
                        Instance/Sets/Coend.v;

     [Sets_colim_obj]   is [SetsQuotient] (Instance/Sets/Quotient.v) of the
                        first by the second: SAME CARRIER, coarser [≈].

   The leg at [d] is [Sets_colim_inj d], the injection [x ↦ (d; x)].  The
   mediator out of a competing cocone [N] is [Sets_colim_med N], which
   sends [(d; x)] to [N]'s own leg at [d] applied to [x]; that this
   respects [colim_rel] is [Sets_colim_med_respects], by induction on the
   relation, the [cr_glue] case being [N]'s cone coherence read at the
   point [x] and symmetrised.  Commuting is [reflexivity] and uniqueness
   is the symmetry of the competing map's commuting equations -- the same
   two closing moves as Instance/Sets/Complete.v.

   READING THE OBLIGATIONS THROUGH THE DUALITY

   Because [Colimit F] is [Limit (F^op)], the record built below is a
   [Cone (F^op)], i.e. a [Cocone F] (Structure/Cone.v).  Its coherence
   field at [f : d ~{D^op}~> d'] -- that is, at [f : d' ~{D}~> d] -- reads
   [ι_d ∘ fmap[F] f ≈ ι_{d'}] in [Sets], which runs opposite to the
   covariant direction [cr_glue] is stated in; the obligation is therefore
   discharged by [cr_sym] of a [cr_glue], and not by [cr_glue] itself.
   The universal property likewise unfolds so that the mediator runs OUT
   of the apex, [Sets_colim_obj ~{Sets}~> vertex_obj[N]].

   NO DUALITY SHORTCUT FROM [Sets_Complete] -- MEASURED, NOT ASSUMED

   [Sets_Complete] (Instance/Sets/Complete.v:193) supplies a [Limit F] for
   every [F : D ⟶ Sets].  A colimit of [F] is a limit of [F^op], and
   [F^op] is a diagram into [Sets^op]; no instantiation of [Sets_Complete]
   has that type.  Elaborating
   [Sets_Complete (Opposite D) (Opposite_Functor F)] is rejected with
   "The term "F^op" has type "D^op ⟶ Sets^op" while it is expected to have
   type "D^op ⟶ Sets"", against the positive control
   [Sets_Complete D F : Limit F], which is accepted.  What would produce
   the colimit is [Complete (Sets^op)], and that IS [Cocomplete Sets]
   again, so the duality is not a route.  No [Fail] probe is kept in this
   file; all three refutations are pinned in Test/ProbeCocomplete329.v.

   A probe-hygiene point, since the same trap awaits anyone rewriting that
   measurement: written as [Sets_Complete (D^op) (F^op)] it fails for the
   WRONG reason.  Functor/Opposite.v opens [functor_scope], in which
   [_ ^op] is [Opposite_Functor], so [D^op] parses as [Opposite_Functor D]
   and the error is "The term "D" has type "Category" while it is expected
   to have type "?C ⟶ ?D"" -- a notation clash and not the mathematics.
   The measurement above spells [Opposite] and [Opposite_Functor] by name.
   This is the notation guard Instance/Rng/Mod.v records.

   HOW THIS IS *NOT* PROVED, STATED PLAINLY

   It is NOT routed through "a category with all small coproducts and
   coequalizers is cocomplete".  That theorem is in this development in
   neither variance: on the limit side Instance/Sets/Complete.v:44-59
   already records its absence, and dually no constant here or elsewhere
   derives [Cocomplete] from [HasIndexedCoproducts] and [HasCoequalizers].
   In particular [Sets_HasCoequalizers] (Instance/Sets/Coequalizer.v:293)
   is NOT consumed.  What is consumed is the layer beneath it: the two
   objects [Sets_icoprod_obj] and [SetsQuotient].  Both halves of the
   informal recipe are therefore genuine donors, but the coequalizer is
   not one of them, and Instance/Sets/Coequalizer.v:66's forecast that its
   hand-built object "is what a later [Cocomplete Sets] would itself need"
   is not what happened.

   Two further constants are present but OFF the path to
   [Sets_Cocomplete]: [Sets_colim_coarser] and [Sets_colim_inj_donors],
   the leg written as the donor composite
   [sets_quot_proj ∘ Sets_icoprod_inj].  They are kept because they make
   the coproduct-then-quotient provenance machine-checked rather than
   merely described -- [Sets_colim_inj_is_donor_composite] equates them
   with the leg actually used, at [eq_refl] -- and because of the universe
   measurement recorded next.

   SMALLNESS AND UNIVERSES, FROM THE CONSTRAINT BLOCKS

   [About Sets_Cocomplete] under [Set Printing Universes] prints

     Sets_Cocomplete@{uc ud uo uso} : Cocomplete@{uc ud uo uso}
     (* uc ud uo uso |= uc < uso   ud <= uc   ud <= uo   uc = uo   ... *)

   Writing [Sets@{o so}] as Instance/Sets.v:193 does, [uo] is [o] -- the
   universe of the CARRIERS of [Sets]' objects, and of its homs -- and
   [uso] is [so], where [obj[Sets]] itself lives.  [Cocomplete@{a b c d}]
   applies to [C : Category@{d c c}] and quantifies over
   [D : Category@{b c c}], so [c] is D's hom universe, forced equal to
   [Sets]' by the type of [Cocomplete] itself, and [b] is D's OBJECT
   universe.  The block records [ud <= uo]: the diagram category's objects
   sit at or BELOW [Sets]' carrier universe and are NOT identified with
   it.  That inequality is the smallness side condition, and it is exactly
   what the construction needs -- the sigma [{ d : D & F d }] and the
   inductive [colim_rel] both quantify over the objects and the arrows of
   [D], so they fit as a [Sets] carrier when both sit at or below [o].
   This is the universe-polymorphic stand-in for "D small relative to C"
   that Structure/Complete.v:27-34 describes.

   TWO MEASURED FINDINGS ABOUT THAT BLOCK.

   (1) The four universe binders are written out deliberately.  Left to
   minimization, [Definition Sets_Cocomplete : @Cocomplete Sets :=
   fun D F => Sets_Colimit F] elaborates to
   [Sets_Cocomplete@{u u0} : Cocomplete@{u u u u0}], which sets [ud := uo]
   and so refuses a diagram category whose objects sit strictly below
   [Sets]' carriers.  The identification is minimization and not a
   constraint: the annotated form above is accepted, and instantiating it
   under a declared [Constraint pd < po] is accepted too.  The mirror
   [Sets_Complete@{u u0} : Complete@{u u u u0}] carries the identification,
   but that is minimization there as well -- the same annotation on its
   body was accepted in a scratch session -- so nothing here says that
   limits are inherently tighter than colimits, and
   Instance/Sets/Complete.v is not edited.

   (2) The identification would return if the leg were the donor
   composite.  [Sets_icoprod_inj@{u u0}] (Instance/Sets/Products.v:352)
   carries only two universe binders and types its family as
   [A → SetoidObject@{u u}] with [A : Type@{u}], identifying the index
   type's universe with the setoid carrier universe, whereas
   [Sets_icoprod_obj@{u u0 u1 u2}] keeps them apart under [u <= u0].
   Measured in the file as it stands: [Sets_colim_inj_donors] carries
   [u = u0] where the direct [Sets_colim_inj] carries [u <= u0].  Measured
   on an earlier revision, in which the donor composite WAS the leg: that
   identification propagates, giving [Sets_Colimit] and hence
   [Sets_Cocomplete] the pin [ud = uo].  The second half is a
   counterfactual about a revision that is not in tree, so it cannot be
   rechecked from this file alone; only the first half can.  The donor's
   restriction belongs to Instance/Sets/Products.v, is NOT repaired here,
   and is NOT claimed unavoidable.

   STRENGTHS, MEASURED STRICT-FIRST

   Holding at [eq_refl] (each an [Example] below, each a Leibniz equality
   and not an [≈]):

     [Sets_colim_carrier_is_coproduct]  the apex carrier IS the coproduct
                                        carrier -- the quotient leaves it
                                        alone;
     [Sets_colim_equiv_is_rel]          the apex's [≈] IS [colim_rel];
     [Sets_colim_inj_at]                the leg IS the sigma injection;
     [Sets_colim_inj_is_donor_composite] leg = donor composite;
     [Sets_colim_triangle]              the factorization triangle
                                        POINTWISE, one grade above the [≈]
                                        the universal property asks for;
     [Sets_Colimit_cocone]              the produced colimit's chosen cone
                                        IS [Sets_colim_cocone].

   REFUTED, and kept in two kinds.  Conversion negatives: [Sets_colim_obj]
   is not [Sets_colim_sum] ("cannot unify" -- the two share a carrier,
   which is the positive control, and differ in [is_setoid]); and the
   triangle as a Leibniz equality of WHOLE morphisms,
   [Sets_colim_med N ∘ Sets_colim_inj d = vertex_map[N]], is rejected,
   the composite rebuilding a [proper_morphism] certificate, while the
   pointwise form is the [Example] above.  Typing negative: the
   [Sets_Complete] instantiation quoted earlier.  None of the three is
   pinned in this file; all three are pinned in the probe.  (An earlier
   draft shipped only two: the whole-morphism triangle was measured here
   and guarded nowhere.)

   WHAT THIS UNLOCKS

   [Cocomplete] is a hypothesis of [adamek_cocomplete]
   (Theory/Adamek/Corollaries.v:61), of [creates_colimits_Cocomplete]
   (Structure/Limit/Creation.v:439) and of
   [Cocomplete_equivalence_invariant] (Instance/Proset/Limit.v:643).  Keep
   those two roles apart: [adamek_cocomplete] TAKES a [Cocomplete] but its
   own type is [@Initial (FAlg F)], so it is not in the list that follows.
   The constants whose TYPE is [@Cocomplete _] are exactly THREE --
   [creates_colimits_Cocomplete], [Cocomplete_equivalence_invariant] and
   [Proset_Cocomplete_of_all_joins] (Instance/Proset/Limit.v:603) -- and
   every one takes a hypothesis, a [Cocomplete] or a family of joins.  So
   this is the first hypothesis-free inhabitant.  (An earlier draft of
   this paragraph listed [adamek_cocomplete] among the four "constants
   whose type is [@Cocomplete _]"; that was a conflation of taking the
   class with having it as a type.)  It does NOT make [adamek_cocomplete]
   unconditional: that corollary still wants an [AdamekData], and
   Theory/Adamek/Corollaries.v:83-84 records that no [AdamekData] witness
   is constructed anywhere in the tree.

   NON-VACUITY, AT ONE SHAPE -- READ THE SCOPE

   A colimit construction that identified every point would compile and
   satisfy the universal property vacuously, so the quotient is shown not
   to collapse.  **This is a witness at one shape, not a general
   non-collapse theorem**, and nothing below is claimed for any other
   diagram.

   The shape is [TwoDisc := DiscreteCat bool], whose hom type IS index
   equality ([two_disc_hom_is_eq], by [eq_refl]) -- so [cr_glue] can only
   relate an index to itself and has nothing to glue across the two
   objects, which is what makes this the sharp case.  The diagram
   [TwoPoints] puts a singleton over each object.  Then
   **[two_fibres_not_collapsed]**: the point of the fibre over [true] and
   the point of the fibre over [false] are NOT related by [colim_rel].
   [two_fibres_not_equal_in_colimit] restates it through the apex's own
   [≈], the same statement by [Sets_colim_equiv_is_rel].

   The proof is by mapping OUT, through [colim_rel_separates] at the
   cocone [TwoSep] whose leg at [b] is constant at [b] in the discrete
   setoid on [bool], landing on [discriminate].  No induction on
   [colim_rel] could have produced a negative.

   Three degeneracies are excluded by proof rather than by assertion.
   The shape has two distinct objects, so "the two fibres" names two
   things ([two_disc_objects_distinct]).  Both fibres are inhabited, and
   the theorem is stated at named inhabitants
   ([two_fibre_point_true]/[two_fibre_point_false]), each of which
   typechecks only because its fibre has an element -- so the statement is
   not vacuously true of no elements.  And the empty-shape reading, where
   the apex has no elements at all ([empty_shape_colim_empty]), is
   labelled in the file as a DEGENERATE CONTROL and deliberately does not
   stand alone: it separates for a reason unrelated to the glue.

   The complementary half -- that the quotient MERGES something the
   coproduct keeps apart -- cannot be shown at a discrete shape, there
   being no connecting maps, and is therefore not here.  It is
   Instance/Sets/Chain.v's [omega_stages_merged] together with
   [omega_stages_apart_in_coproduct], at the ω-shape.

   What the two witnesses JOINTLY establish is that NEITHER endpoint
   describes [colim_rel] uniformly: the ω pair refutes "always the
   coproduct's own relation", the discrete witness refutes "always
   total".  That is a statement about the FAMILY.  They do NOT show the
   relation strictly inside the interval at any one shape -- and at the
   two shapes exhibited here it is in fact AT an endpoint.  Measured, not
   shipped, since adding theorems is not what a correction is for: at
   [OmegaPoints] every fibre is a singleton and any two stages are
   ordered, so [colim_rel] is TOTAL; at [TwoPoints] the only homs are
   identities, so [cr_glue] never crosses an index and [colim_rel]
   coincides with the coproduct's own [≈].  An earlier draft said the two
   files "place [colim_rel] strictly between the coproduct's own relation
   and the total one -- each at its own shape".  The hedge does not save
   it: no in-tree theorem supports "strictly between", and the claim is
   refutable at both witnesses.

   WHAT IS NOT DELIVERED, SCOPED TO THIS FILE

   * No identification with any other colimit-shaped construction in
     [Sets]: no comparison with [Sets_HasCoequalizers]
     (Instance/Sets/Coequalizer.v), with [Sets_HasIndexedCoproducts]
     (Instance/Sets/Products.v) as the discrete-shape instance, with
     Instance/Sets/Pushout.v, or with [SetsCoend]
     (Instance/Sets/Coend.v), whose relation this one's shape follows.

   * No normal form for [colim_rel], hence no decision procedure, and in
     particular no theorem that two elements are related exactly when
     their images agree at a common later stage.

   * No functoriality of the colimit in [F], no preservation statement,
     and no [Complete (Sets^op)] (which would be this same statement read
     the other way round, and is not restated).

   * No ω-chain reading here.  Instance/Sets/Chain.v instantiates this
     constant at [Omega] and at Construction/Chain.v's [Chain], and proves
     the SUFFICIENT half of "the colimit is the union"; its own header
     records that the necessary half is not proved, and why.  Nothing in
     this file depends on that one.

   STATUS: axiom-free.  All 44 constants of this module -- 32 named, 8
   [Program] obligations and the 4 eliminators generated for [colim_rel]
   -- report "Closed under the global context", enumerated by
   [Print Module] per the docs/AXIOMS.md methodology. *)

#[local] Obligation Tactic := idtac.

Section SetsColimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(** ** The indexed coproduct of the diagram's objects *)

Definition Sets_colim_sum : obj[Sets] := Sets_icoprod_obj (fun d : D => F d).

(** ** The relation generated by the connecting maps *)

Inductive colim_rel :
  carrier Sets_colim_sum -> carrier Sets_colim_sum -> Type :=
  | cr_point : forall (d : D) (x y : F d), x ≈ y ->
      colim_rel (existT _ d x) (existT _ d y)
  | cr_glue  : forall (d d' : D) (f : d ~{D}~> d') (x : F d),
      colim_rel (existT _ d x) (existT _ d' (fmap[F] f x))
  | cr_sym   : forall p q, colim_rel p q -> colim_rel q p
  | cr_trans : forall p q r, colim_rel p q -> colim_rel q r -> colim_rel p r.

Lemma colim_rel_refl (p : carrier Sets_colim_sum) : colim_rel p p.
Proof. destruct p as [d x]; apply cr_point; reflexivity. Qed.

Definition colim_rel_Equivalence : Equivalence colim_rel.
Proof.
  constructor.
  - exact colim_rel_refl.
  - exact cr_sym.
  - exact cr_trans.
Defined.

(** ** The colimit apex: the coproduct quotiented by that relation *)

Definition Sets_colim_obj : obj[Sets] :=
  SetsQuotient Sets_colim_sum colim_rel colim_rel_Equivalence.

Lemma Sets_colim_coarser : SetoidCoarser colim_rel.
Proof.
  intros [d x] [d' y] [e Hxy]; simpl in *.
  destruct e; simpl in *.
  now apply cr_point.
Qed.

Program Definition Sets_colim_inj (d : D) :
  F d ~{Sets}~> Sets_colim_obj := {|
  morphism := fun x => existT _ d x
|}.
Next Obligation. intros d x y Hxy; apply cr_point; exact Hxy. Qed.

Definition Sets_colim_inj_donors (d : D) : F d ~{Sets}~> Sets_colim_obj :=
  sets_quot_proj Sets_colim_sum colim_rel colim_rel_Equivalence
    Sets_colim_coarser ∘ Sets_icoprod_inj (fun d : D => F d) d.

Example Sets_colim_inj_is_donor_composite (d : D) (x : F d) :
  Sets_colim_inj d x = Sets_colim_inj_donors d x.
Proof. reflexivity. Qed.

(** ** What the apex is, by conversion *)

(* The quotient leaves the carrier alone, so the colimit carrier IS the
   coproduct carrier -- the [eq_refl] exception to the `≈` discipline that
   Instance/Sets/Quotient.v's [sets_quot_carrier] records generically. *)
Example Sets_colim_carrier_is_coproduct :
  carrier Sets_colim_obj = Sets_icoprod_carrier (fun d : D => F d).
Proof. reflexivity. Qed.

(* ... and the apex's own `≈` IS the generated relation. *)
Example Sets_colim_equiv_is_rel (p q : carrier Sets_colim_sum) :
  @equiv _ Sets_colim_obj p q = colim_rel p q.
Proof. reflexivity. Qed.

(* The leg at [d] is the [d]th coproduct injection on elements. *)
Example Sets_colim_inj_at (d : D) (x : F d) :
  Sets_colim_inj d x = existT _ d x.
Proof. reflexivity. Qed.

(** ** The colimit cocone *)

Program Definition Sets_colim_cocone : Cocone F := {|
  vertex_obj := Sets_colim_obj;
  coneFrom   := {| vertex_map := Sets_colim_inj |}
|}.
Next Obligation.
  intros d d' f x.
  exact (cr_sym _ _ (cr_glue d' d f x)).
Qed.

(** ** The mediator into a competing cocone *)

Definition Sets_colim_med_fun (N : Cocone F)
  (p : carrier Sets_colim_sum) : carrier (vertex_obj[N]) :=
  match p with
  | existT _ d x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x
  end.

Lemma Sets_colim_med_respects (N : Cocone F)
  (p q : carrier Sets_colim_sum) (H : colim_rel p q) :
  Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q.
Proof.
  induction H as [d x y Hxy | d d' f x | p q H IH | p q r H1 IH1 H2 IH2].
  - now apply proper_morphism.
  - symmetry.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d' d f x).
  - now symmetry.
  - now transitivity (Sets_colim_med_fun N q).
Qed.

Program Definition Sets_colim_med (N : Cocone F) :
  Sets_colim_obj ~{Sets}~> vertex_obj[N] := {|
  morphism := Sets_colim_med_fun N
|}.
Next Obligation.
  intros N p q Hpq; exact (Sets_colim_med_respects N p q Hpq).
Qed.

(* The factorization triangle holds at LEIBNIZ equality, one grade above the
   `≈` the universal property asks for: the mediator's value on the [d]th
   injection IS the competing cocone's leg at [d], by conversion. *)
Example Sets_colim_triangle (N : Cocone F) (d : D) (x : F d) :
  Sets_colim_med N (Sets_colim_inj d x)
    = @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x.
Proof. reflexivity. Qed.

(* Mapping OUT is how the quotient is shown not to collapse: no induction on
   [colim_rel] can yield a negative, but a cocone that separates two points
   proves they are unrelated.  It is spent at the end of this file, on
   [two_fibres_not_collapsed]. *)
Lemma colim_rel_separates (N : Cocone F) (p q : carrier Sets_colim_sum) :
  (Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q -> False) ->
  colim_rel p q -> False.
Proof. intros Hne Hpq; exact (Hne (Sets_colim_med_respects N p q Hpq)). Qed.

(** ** The colimit *)

Program Definition Sets_Colimit : Colimit F := {|
  limit_cone := Sets_colim_cocone;
  ump_limits := fun N => {| unique_obj := Sets_colim_med N |}
|}.
Next Obligation. intros N d x; reflexivity. Qed.
Next Obligation.
  intros N v Hv p; destruct p as [d x]; symmetry; exact (Hv d x).
Qed.

(* The chosen cocone of the produced colimit is the one built above, by
   conversion.  (Its apex is then [Sets_colim_obj] by the same conversion;
   that reading is stated separately, in Instance/Sets/Chain.v, as
   [Sets_omega_apex].) *)
Example Sets_Colimit_cocone :
  @limit_cone _ _ _ Sets_Colimit = Sets_colim_cocone.
Proof. reflexivity. Qed.

End SetsColimit.

(* [Sets] is cocomplete: every diagram of every shape has a colimit.  The
   universe binders are written out rather than left to minimization; see the
   header for what that buys and what it does not. *)
Definition Sets_Cocomplete@{uc ud uo uso} :
  @Cocomplete@{uc ud uo uso} Sets@{uo uso} := fun D F => Sets_Colimit F.

(** * Non-vacuity, at the two-object discrete shape *)

(* Everything below is about ONE shape and ONE diagram.  It is a witness,
   not a general non-collapse theorem, and the header says so. *)

Section TwoDiscreteWitness.

(* The two-object discrete shape.  Its hom type IS index equality, by
   conversion, which is precisely why [cr_glue] has nothing to glue across
   the two objects: a morphism can only relate an index to itself. *)
Definition TwoDisc : Category := DiscreteCat bool.

Example two_disc_hom_is_eq (b b' : bool) :
  (b ~{TwoDisc}~> b') = (b = b').
Proof. reflexivity. Qed.

(* ... and the shape really does have two objects, so "the two fibres"
   below names two things and not one. *)
Lemma two_disc_objects_distinct : (true : TwoDisc) = (false : TwoDisc) -> False.
Proof. discriminate. Qed.

(* The diagram: a singleton setoid over each of the two objects.  Both
   fibres are INHABITED, by [ttt], so the separation proved below is a
   statement about actual elements and not vacuously true. *)
Program Definition TwoPoints : TwoDisc ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.
(* Measured: [fmap_respects] never surfaces as an obligation here, the
   arrow action being constant; the two that do are [fmap_id] and
   [fmap_comp]. *)
Next Obligation. intros x; reflexivity. Qed.
Next Obligation. intros x y z f g; symmetry; apply id_left. Qed.

(* The separating cocone: the leg at [b] is constant at [b] in the
   discrete setoid on [bool].  Respectfulness is free (the map ignores its
   argument) and the cocone coherence is available because a morphism of
   [TwoDisc] IS an equality of its two indices. *)
Program Definition two_sep_leg (b : bool) :
  TwoPoints b ~{Sets}~> bool_setoid_object := {|
  morphism := fun _ => b
|}.
(* Measured: [proper_morphism] never surfaces as an obligation here
   either, the map being constant, so none is written out. *)

Program Definition TwoSep : Cocone TwoPoints := {|
  vertex_obj := bool_setoid_object;
  coneFrom   := {| vertex_map := two_sep_leg |}
|}.
Next Obligation. intros b b' e x; exact (eq_sym e). Qed.

(* The two fibres are INHABITED, and these are the points the separation
   below is stated at -- so the theorem is about actual elements, not
   vacuously true.  Naming them makes that machine-checked rather than a
   remark: each definition typechecks only because the fibre it names has
   an element. *)
Definition two_fibre_point_true : carrier (TwoPoints true) := ttt.
Definition two_fibre_point_false : carrier (TwoPoints false) := ttt.

(* THE WITNESS.  The point of the fibre over [true] and the point of the
   fibre over [false] are NOT identified by the generated relation, so
   [colim_rel] does not collapse this colimit.  Proved by mapping OUT
   through [colim_rel_separates] -- no induction on [colim_rel] could
   yield a negative -- and landing on [discriminate]. *)
Theorem two_fibres_not_collapsed :
  colim_rel TwoPoints
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof.
  apply (colim_rel_separates TwoPoints TwoSep).
  discriminate.
Qed.

(* Read through the apex's own `≈` rather than through [colim_rel], which
   is the same statement by [Sets_colim_equiv_is_rel]. *)
Corollary two_fibres_not_equal_in_colimit :
  @equiv _ (Sets_colim_obj TwoPoints)
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof. exact two_fibres_not_collapsed. Qed.

(* DEGENERATE CONTROL, and labelled as one: over the EMPTY shape the apex
   has no elements at all, so it separates for a reason that has nothing
   to do with the glue.  This is why it does not stand alone. *)
Lemma empty_shape_colim_empty (F : DiscreteCat False ⟶ Sets)
  (p : carrier (Sets_colim_obj F)) : False.
Proof. destruct p as [d x]; destruct d. Qed.

End TwoDiscreteWitness.
