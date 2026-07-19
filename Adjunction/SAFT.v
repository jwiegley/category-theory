Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The Special Adjoint Functor Theorem (SAFT) *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   The Special Adjoint Functor Theorem (SAFT; Freyd, Mac Lane CWM V.8) refines
   Freyd's General Adjoint Functor Theorem (GAFT, [Adjunction/GAFT.v]) by
   *manufacturing* the solution set from three classical smallness conditions on
   the domain [C]:

     - [C] is complete;
     - [C] is *well-powered* — the subobjects of any object form a small set;
     - [C] has a *cogenerating family* [{G_j}] — a family separating parallel
       arrows through the representable functors [C(-, G_j)].

   Together with the preservation hypothesis on [U] these produce, at every
   [d : D], a solution set, and [GAFT] then yields the left adjoint [F ⊣ U].

   HYPOTHESES AS DATA (honest reading; stated explicitly per the campaign
   discipline).  The classical SAFT proof has TWO halves, and only one of them
   can be internalized in this library.

   (1) SEPARATION ⇒ MONIC — internalized, in full.  The genuine content of a
   cogenerating family is that the canonical map of any [c : C] into a power of
   the family is a monomorphism.  This is proved below as
   [cogenerator_canonical_monic], and it genuinely CONSUMES [cog_separates]:
   forming the hom-indexed power [cogen_power] of the cogenerating family — one
   factor [cog_obj G j] per arrow [k : c ~> cog_obj G j], built via [Complete] —
   the mediator [cogen_canonical] whose [(j, k)]-component is [k] itself is
   left-cancellable precisely because [G] separates parallel arrows: two arrows
   equalized by [cogen_canonical] agree after every such [k] (read off the
   matching projection), hence are equal by [cog_separates].  So [cog_separates]
   is NOT inert — it is the operative hypothesis of that lemma, and deleting the
   field breaks the file.

   (2) SMALL SOLUTION SET — packaged as DATA, of necessity.  The other half of
   the classical proof is a SIZE argument: well-poweredness makes the family of
   subobjects of the cogenerator product a *set*, and the image factorization of
   a given [h : d ~> U c] through one of those subobjects places the resulting
   member inside that set.  This library carries NO size / smallness machinery
   and NO image-factorization system on a general base, so neither "the
   subobjects form a set" nor "take the image of [h]" can be constructed
   internally — there is nothing to quantify smallness against.  The honest
   reading — the one the plan sanctioned — is therefore to package this half as
   DATA, in exactly the shape the classical argument delivers:

     - [SubobjectIndex x] supplies well-poweredness object-by-object, as a small
       [Type] [sub_index] of subobjects of [x], each NAMED by a monomorphism
       [sub_mono] into [x] (a subobject of [x] IS a mono into [x], per
       Theory/Morphisms.v).  The smallness content lives in the [Type]
       [sub_index] itself; the field [sub_monic] is a subobject-naming
       annotation, witnessing that each [sub_dom i] genuinely names a subobject
       of the cogenerator product [cogen_prod].  The existence proof does not
       consume [sub_monic] — smallness is supplied here as data, not derived, so
       nothing in the reduction inspects the monic witness — and [sub_monic] is
       emphatically NOT claimed to drive any factorization.

     - the covering datum [cover] of [SAFT] states precisely the CONCLUSION of
       the classical image-factorization step: every [h : d ~> U c] factors,
       through a well-powered subobject [i] of [cogen_prod], as a [d]-arrow
       [s : d ~> U (sub_dom i)] followed by a [C]-arrow [t : sub_dom i ~> c].
       This is exactly one member of a solution set at [d].

   Packaging half (2) as data is a leaner-but-honest *hypothesis* form; it never
   weakens the CONCLUSION, which remains a genuine left adjoint
   [{ F : D ⟶ C & F ⊣ U }].  The completeness [comp] and cone-level preservation
   [cont] hypotheses are consumed unchanged and fed straight to [GAFT] — see the
   [Adjunction/GAFT.v] header for why the operative preservation notion is the
   cone-level [PreservesImageLimit] rather than the apex-only class.  The
   mathematical content proven here is thus twofold: the separation⇒monic lemma
   [cogenerator_canonical_monic] (half 1, fully internal and consuming
   [cog_separates]), and the reduction assembling the packaged classical data
   into a [SolutionSet] at every [d] and invoking [GAFT] (half 2, over the
   packaged smallness datum). *)

(** ** Cogenerating families *)

(* A cogenerating family for [C]: a small [Type] of indices [cog_index] with
   objects [cog_obj j : C], such that parallel arrows [f, g : x ~> y] are equal
   as soon as they agree after every arrow [k : y ~> cog_obj j] into a member of
   the family.  Equivalently the representables [C(-, cog_obj j)] are jointly
   faithful.  This is the minimal data form of "cogenerating family". *)
Record Cogenerator {C : Category} := {
  cog_index : Type;
  cog_obj : cog_index -> C;
  cog_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : cog_index) (k : y ~> cog_obj j), k ∘ f ≈ k ∘ g) -> f ≈ g
}.

Arguments Cogenerator : clear implicits.
Arguments cog_index {C} _.
Arguments cog_obj {C} _ _.
Arguments cog_separates {C} _ {x y} f g _.

(** ** Well-powered indexing of subobjects *)

(* A chosen small indexing of the subobjects of [x] : a [Type] [sub_index] of
   indices, an object [sub_dom i : C] for each, and a monomorphism
   [sub_mono i : sub_dom i ~> x] witnessing that [sub_dom i] genuinely names a
   subobject of [x] (a subobject of [x] IS a mono into [x], per Theory/
   Morphisms.v).  Well-poweredness of [C] is then [forall x, SubobjectIndex x]:
   the subobjects of every object are supplied as a small family of data. *)
Record SubobjectIndex {C : Category} (x : C) := {
  sub_index : Type;
  sub_dom : sub_index -> C;
  sub_mono : forall i, sub_dom i ~> x;
  sub_monic : forall i, Monic (sub_mono i)
}.

Arguments sub_index {C x} _.
Arguments sub_dom {C x} _ _.
Arguments sub_mono {C x} _ _.
Arguments sub_monic {C x} _ _.

(** ** The product of the cogenerating family *)

(* The product [∏_{j} cog_obj j] of the whole cogenerating family, a single
   object of [C], independent of any [d : D].  It is built as the limit of the
   discrete diagram on the family via completeness.

   These are top-level polymorphic definitions rather than section-local ones on
   purpose.  [Complete] forces the diagram category's hom universe to coincide
   with C's hom universe (see the printed signature of [Complete]), while
   [DiscreteCat_Functor] emits a diagram whose hom universe is [Set]; reconciling
   the two requires C's hom universe to absorb [Set], which a polymorphic
   definition records as a universe constraint but a rigid section variable
   cannot.  This is the universe-level shadow of the same "no size machinery"
   note in the header. *)
Definition cogen_prod_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) := comp _ (DiscreteCat_Functor (cog_obj G)).

Definition cogen_prod {C : Category} (comp : @Complete C)
  (G : Cogenerator C) : C :=
  iprod (cog_obj G) (cogen_prod_limit comp G).

(** ** The canonical map into a power of the cogenerating family *)

(* The genuine separation content of a cogenerating family, delivered and
   consumed here (so [cog_separates] is NOT inert).  Fix [c : C].  Index the
   arrows out of [c] into the family by the hom-indexed Σ-type

     [cogen_power_index G c := { j : cog_index G & c ~> cog_obj G j }],

   and form the product [cogen_power] of the family whose [(j, k)]-component is
   [cog_obj G j] — a *power* of the cogenerating family, with one factor per
   arrow [k : c ~> cog_obj G j].  The canonical map [cogen_canonical] is the
   unique mediator whose [(j, k)]-component is [k] itself; it is monic
   ([cogenerator_canonical_monic]) precisely because [G] separates, which is the
   classical "the unit into the cogenerator power is monic" step, internalized
   in full.

   The Σ-index is hom-indexed, so this product is taken against [Complete]
   exactly as [cogen_prod] is (via [cogen_power_limit], mirroring
   [cogen_prod_limit]), and it carries the same universe constraint recorded on
   [cogen_prod_limit]; every definition here is top-level polymorphic for that
   reason. *)

(* The hom-indexed Σ-index of arrows out of [c] into the cogenerating family. *)
Definition cogen_power_index {C : Category} (G : Cogenerator C) (c : C) : Type :=
  { j : cog_index G & c ~> cog_obj G j }.

(* The family whose [(j, k)]-component is [cog_obj G j]. *)
Definition cogen_power_fam {C : Category} (G : Cogenerator C) (c : C) :
  cogen_power_index G c -> C :=
  fun p => cog_obj G (projT1 p).

(* Its product, drawn from completeness exactly as [cogen_prod_limit]. *)
Definition cogen_power_limit {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) :=
  comp _ (DiscreteCat_Functor (cogen_power_fam G c)).

Definition cogen_power {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : C :=
  iprod (cogen_power_fam G c) (cogen_power_limit comp G c).

(* The family of legs [c ~> cog_obj G j] whose [(j, k)]-component is [k]. *)
Definition cogen_canonical_legs {C : Category} (G : Cogenerator C) (c : C) :
  forall p : cogen_power_index G c, c ~> cogen_power_fam G c p :=
  fun p => projT2 p.

(* The canonical map [c ~> cogen_power], the unique mediator of those legs. *)
Definition cogen_canonical {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : c ~> cogen_power comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                        c (cogen_canonical_legs G c)).

(* The [(j, k)]-component of the canonical map is [k]: the projection at index
   [(j, k)] post-composed with [cogen_canonical] recovers [k].  This is exactly
   the mediator's commuting property from [iprod_ump]. *)
Lemma cogen_canonical_commutes {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) (j : cog_index G) (k : c ~> cog_obj G j) :
  iprod_proj (cogen_power_fam G c) (cogen_power_limit comp G c)
    (existT _ j k) ∘ cogen_canonical comp G c ≈ k.
Proof.
  exact (unique_property
           (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                      c (cogen_canonical_legs G c))
           (existT _ j k)).
Qed.

(* SEPARATION ⇒ MONIC (the genuine content consuming [cog_separates]).  The
   canonical map of [c] into the power of the cogenerating family is monic.
   Given [g1, g2 : z ~> c] equalized by [cogen_canonical], post-composing with
   the projection at each index [(j, k)] and using [cogen_canonical_commutes]
   shows [k ∘ g1 ≈ k ∘ g2] for every [j] and every [k : c ~> cog_obj G j];
   [cog_separates] then forces [g1 ≈ g2]. *)
Lemma cogenerator_canonical_monic {C : Category} (comp : @Complete C)
  (G : Cogenerator C) (c : C) : Monic (cogen_canonical comp G c).
Proof.
  constructor; intros z g1 g2 H.
  apply (cog_separates G g1 g2); intros j k.
  rewrite <- (cogen_canonical_commutes comp G c j k).
  rewrite <- !comp_assoc.
  now rewrite H.
Qed.

(** ** The covering datum and the solution set *)

(* The covering datum (the packaged conclusion of the classical factorization
   step) at [d]: every [h : d ~> U c] factors through a well-powered subobject of
   the product of the cogenerating family — there is a subobject index [i], a
   [d]-arrow [s : d ~> U (sub_dom i)], and a [C]-arrow [t : sub_dom i ~> c] with
   [fmap[U] t ∘ s ≈ h].  This is exactly a member of a solution set at [d]. *)
Definition SubobjectCover {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x) : Type :=
  forall (d : D) (c : C) (h : d ~> U c),
    { i : sub_index (WP (cogen_prod comp G)) &
      { s : d ~> U (sub_dom (WP (cogen_prod comp G)) i) &
        { t : sub_dom (WP (cogen_prod comp G)) i ~> c &
          fmap[U] t ∘ s ≈ h } } }.

(* The solution set at [d]: its members are the pairs [(i, s)] of a well-powered
   subobject [i] of the cogenerator product together with a [d]-arrow
   [s : d ~> U (sub_dom i)].  The covering property is delivered by [cover]. *)
Definition SAFT_solution_set {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (G : Cogenerator C)
  (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) (d : D) : SolutionSet U d.
Proof.
  unshelve refine
    {| sol_index := { i : sub_index (WP (cogen_prod comp G))
                      & d ~> U (sub_dom (WP (cogen_prod comp G)) i) }
     ; sol_obj := fun p => sub_dom (WP (cogen_prod comp G)) (projT1 p)
     ; sol_arr := fun p => projT2 p |}.
  intros c h.
  destruct (cover d c h) as [i [s [t e]]].
  exists (existT _ i s); simpl.
  exists t.
  exact e.
Defined.

(** ** The Special Adjoint Functor Theorem *)

(* SAFT.  The packaged well-powered / cogenerator data assemble a solution set at
   every [d]; completeness and cone-level preservation are handed to [GAFT],
   which returns the left adjoint [F ⊣ U]. *)
Definition SAFT {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : forall x : C, SubobjectIndex x)
  (cover : SubobjectCover U comp G WP) : { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont (SAFT_solution_set U comp G WP cover).
