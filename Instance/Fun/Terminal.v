Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Pointwise terminal object and indexed products in a functor category *)

(* nLab:      https://ncatlab.org/nlab/show/functor+category
   nLab:      https://ncatlab.org/nlab/show/terminal+object
   nLab:      https://ncatlab.org/nlab/show/product
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Book:      Mac Lane, CWM 2nd ed., §III.5 Exercise 5, p. 74
              ([maclane:III.5:ex5]): if D has (finite) products, so does
              the functor category [C, D], computed pointwise.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH

     [Functor_Category_Terminal T : @Terminal ([C, D])] for any
     [T : @Terminal D] -- the constant functor at 1, with the unique
     natural transformation into it.  This is the nullary half of the
     exercise.

     [Fun_HasIndexedProducts HP : @HasIndexedProducts ([C, D])] for any
     [HP : @HasIndexedProducts D] -- pointwise indexed products at an
     ARBITRARY index [Type], not merely a finite one.  This is the
     substantial half.

   Everything is stated FIRST at the elementary, apex-pinned level and only
   then packaged.  [Fun_iprod]/[Fun_iprod_proj]/[Fun_IsIndexedProduct] are
   the elementary datum -- an object of [C, D], a family of natural
   transformations out of it, and [Structure/Limit/Product.v]'s
   [IsIndexedProduct] record for that family -- and
   [Fun_HasIndexedProducts] is [Build_HasIndexedProducts] applied to
   exactly those three.  No [Limit], no [Cone] and no [DiscreteCat] occurs
   anywhere in this file; see NOT DELIVERED for the measured reason.

   HOW THE TWO HALVES FIT TOGETHER.  They are one phenomenon:
   [Fun_empty_iprod_terminal] exhibits the terminal functor as the
   pointwise indexed product over an empty index, canonically.  It is an
   ISOMORPHISM in [C, D] and nothing stronger, because the empty
   [indexed_product] of D is whatever [HasIndexedProducts D] chose and
   nothing forces that choice to be [terminal_obj].  The enabling piece is
   [terminal_empty_IsIndexedProduct], stated over an arbitrary [A] with an
   [A -> False] rather than over a named empty type, so that no index
   universe is pinned.

   WHERE EACH HYPOTHESIS IS SPENT

     [Terminal D] supplies the object ([Constant_Terminal_Functor]) and,
     through [one_unique], the obligations of the [Terminal] record.  An
     earlier revision of this sentence said "exactly twice ... Nothing
     else uses it", which is FALSE: it is consumed again by
     [terminal_empty_IsIndexedProduct], [Fun_empty_iprod_terminal],
     [Two_Sets_Terminal] and [two_pick].

     [HasIndexedProducts D] supplies the object, the projections and the
     universal property -- all three fields of Structure/Limit/Product.v's
     class -- and its UMP is also applied directly in places.  What ONE
     derived lemma carries is the ROUTING: every functor law of
     [Fun_iprod] and every naturality square below is "compose with the
     projections and compute" through [iprod_jointly_monic], two
     morphisms into an indexed product that agree after every projection
     being equal.  Note that lemma takes [IsIndexedProduct], not the
     class.  (An earlier revision said the class was spent in that one
     lemma alone; that was false.)

     [iprod_jointly_monic] is NOT new, and an earlier revision of this
     header claimed it was on the strength of a search for the NAME
     [jointly_monic] -- the exact trap this tree's own conventions warn
     against.  Structure/Bicartesian/Matrix.v:356 already has
     [iprod_ext], the same statement for indexed products with
     essentially the same proof, plus the dual [icoprod_ext].  What is
     true, and is the honest reason for restating it, is that
     [iprod_ext]'s type carries a spurious [IsIndexedCoproduct] argument
     inherited from its section, so it cannot be applied here without
     supplying a coproduct that has nothing to do with the statement.
     The natural home for a hypothesis-free version is
     Structure/Limit/Product.v; it is declared here because this issue's
     deliverable is this file.

   PRIOR ART -- CITED, NOT DUPLICATED

     The BINARY case is [Functor_Category_Cartesian]
     (Instance/Fun/Cartesian.v:111).  It is not re-proved and not
     subsumed; it is COMPARED, see below.

     The general pointwise-limits fact is stated in PROSE in at least
     three places, and this file does not present it as new:
     Structure/Cartesian/Product.v:32-35 ("the general fact that limits
     in a functor category [J, D] are computed pointwise whenever D has
     them"), Instance/Fun.v:27-28 and :101-104, and
     Instance/Fun/Cartesian.v:17-19, which quotes the nLab for it.  What
     was absent was any Coq statement of it beyond the binary product:
     re-verified on this commit, no [Terminal] instance existed for ANY
     functor category (sweep of every declaration whose name or type
     mentions [Terminal]), and no pointwise indexed products existed
     anywhere -- [HasIndexedProducts] had exactly one instance,
     [Sets_HasIndexedProducts] (Instance/Sets/Products.v:302), plus the
     [C^op] repackaging in Structure/Limit/Coproduct.v.

     [Functor/Diagonal.v]'s [Diagonal] already carries a constant functor
     as its object action, and [Constant_Functor] is NOT defined as
     [fobj[Diagonal C] d].  Both actions agree ON THE NOSE
     ([constant_functor_diagonal_obj], [constant_functor_diagonal_fmap],
     both [eq_refl]); the two RECORDS do not
     ([constant_functor_is_diagonal], a pinned conversion negative --
     [Diagonal] is a [Program Instance], so its three law fields are
     opaque obligation constants).  The reason for not routing through it
     is a UNIVERSE measurement, not taste; see below.

   THE BINARY COMPARISON, MEASURED RATHER THAN ASSUMED

     [Fun_bool_iprod_iso] relates the pointwise indexed product at a
     two-element index to [Functor_Category_Cartesian]'s pointwise binary
     product.  The strength is an ISOMORPHISM in [C, D] and NOT [eq_refl]:
     [bool_iprod_is_binary_product] is a pinned conversion negative, with
     [ctl_bool_iprod_obj] the passing control at the same arguments.  The
     obstruction is not presentational -- [HasIndexedProducts D] and
     [Cartesian D] choose their objects independently, and nothing relates
     the two choices -- so an isomorphism is the strongest available
     statement.  It carries its leg equations
     ([Fun_bool_iprod_iso_commutes] and [Fun_bool_iprod_iso_inv_commutes],
     both leg families rather than one); a bare [≅] would be the weak form.

     The comparison is affordable because the enabling piece is generic:
     [cartesian_bool_IsIndexedProduct] proves that in ANY cartesian
     category the binary product is an indexed product over [bool], with
     [exl]/[exr] as the two projections.  Instantiated at
     [Functor_Category_Cartesian] it gives a second [IsIndexedProduct] of
     the same family, and [iprod_unique_iso]
     (Structure/Limit/Product/Finite.v:545) does the rest.  Its own
     constraint block is character-for-character [IsIndexedProduct]'s, so
     it adds no universe content.

   STRICTNESS, MEASURED STRICT-FIRST

     Holding at [eq_refl]: the terminal functor's object action, its arrow
     action, and the component of its unique arrow ([fun_terminal_obj],
     [fun_terminal_fmap], [fun_terminal_one_component]); the pointwise
     product's object action and the components of its projections
     ([fun_iprod_obj_computes], [fun_iprod_proj_component]); the mediator
     extracted from the packaged class IS [fun_iprod_tuple]
     ([fun_iprod_class_mediator]); and both actions of [Constant_Functor]
     against [Diagonal].

     REFUTED, each pinned as a [Fail] with a passing control alongside:
     the pointwise indexed product at a [bool] index is not the pointwise
     binary product, and [Constant_Functor d] is not the [Diagonal]
     record.  Both are genuine CONVERSION failures ("cannot unify"), read
     off the stripped commands rather than inferred.

   UNIVERSES -- BLOCKS READ IN FULL, DONORS TESTED SEPARATELY

     Four donors were each rejected at a section declaring
     [Constraint uh < up] against passing controls at the same levels, so
     the following are guarded rather than merely read off a printed
     binder.  [Terminal@{u u0}], [HasIndexedProducts], [IsIndexedProduct]
     and [Cartesian] each take their category as [Category@{o h h}]:
     every one of them identifies hom with proof.  [Fun] does more --
     [Fun@{...} : Category@{u u0 u0} -> Category@{u1 u2 u2} ->
     Category@{u3 u4 u4}] with [u0 = u2] -- so it identifies hom with
     proof in BOTH arguments AND the two hom levels with each other.

     [Constant_Functor@{co ch cp dro dh dp}] identifies NOTHING: its block
     is the five bounds [ch <= cp], [ch <= dh], [ch <= dp], [cp <= dp],
     [dh <= dp], which is [Functor]'s own block character for character.
     [Constant_Terminal_Functor@{co ch cp dro dh}] takes D at
     [Category@{dro dh dh}] -- [Terminal]'s doing -- while C's hom and
     proof stay APART ([ch <= cp]).  Both are hand-written record literals
     with explicit universe binders precisely to keep that: written as
     [Program Definition]s in an unannotated [Section] they minimize to
     [C : Category@{u u0 u0}], and the annotated form is then rejected
     because [Program] introduces an obligation universe that no [@{...}]
     list can bind.

     ROUTING THROUGH [Diagonal] WOULD COST THAT, AND THAT IS MEASURED:
     [fobj[@Diagonal D C] d] is REJECTED at [C : Category@{co ch cp}] with
     [ch < cp] ("Cannot enforce cp = dh"), against two passing controls,
     because [Diagonal]'s type mentions [C, D] and so inherits [Fun]'s
     identification even when only a bare constant functor is wanted.

     [Functor_Category_Terminal@{u u0 u1 u2 u3 u4}] is over
     [C : Category@{u2 u4 u4}] and [D : Category@{u3 u4 u4}] -- both
     identified, and both hom levels the SAME level [u4].  That is [Fun]'s
     doing and it lives in the BINDER: the constraint block is six bounds
     ([u4 < u], [u2 <= u0], [u2 <= u1], [u3 <= u0], [u4 <= u0],
     [u4 <= u1]) with NO equation in it, so reading the block alone would
     miss the identification entirely.

     [Fun_iprod@{u u0 u1 u2 u3 u4 u5 u6}] is over [C : Category@{u u0 u0}]
     and [D : Category@{u1 u2 u2}] -- the two hom levels stay DISTINCT
     ([u0 <= u2], a bound, not an equation), and the INDEX universe [u5]
     is only bounded ([u5 <= u3], [u5 <= u4]), never identified.  D's
     hom = proof is [HasIndexedProducts]'s doing.  C's is NOT
     donor-forced: [Functor] keeps them apart, as [Constant_Functor]
     above demonstrates, so it is the unannotated [Context {C : Category}]
     of the section, the minimization family recorded for
     [Build_Quiver_Standard_Eq].  It is repairable in principle and is NOT
     claimed unavoidable; a full lift was not attempted, and it costs a
     consumer nothing at the packaged level, where [Fun] identifies the
     two anyway.  The file's only EQUATION is [Fun]'s [u0 = u2], and it is
     carried by EIGHT constants, not one: [Fun_IsIndexedProduct]
     together with [fun_terminal_obj], [fun_terminal_fmap],
     [fun_terminal_one_component], [fun_iprod_tuple],
     [constant_functor_diagonal_obj], [constant_functor_diagonal_fmap]
     and [ctl_bool_iprod_obj] -- every constant whose statement is at
     [C, D].  It is the SAME equation each time, so the conclusion is
     unchanged, but an earlier revision of this sentence named one
     constant and read as a count, in a file that elsewhere insists a
     universe block be read IN FULL.
     [iprod_jointly_monic@{u u0 u1 u2}] leaves its index universe bounded
     ([u <= u1]) and never identified.

     THE WITNESSES CARRY A [Set], AND IT IS THE SHAPE'S:
     [Two_Sets_HasIndexedProducts] elaborates at
     [Fun@{u0 Set u1 Set u u0 u1}] -- [Instance/Two.v] declares
     [TwoHom : ... -> Set], and [Fun] identifies the shape's hom level
     with the target's, so [Sets] is cut to [Sets@{Set u1}], carriers in
     [Set].  That is the price of using [_2] as the shape, not a property
     of the general theorems, which carry no [Set] at all.

   NON-VACUITY

     Terminal half: [two_pick true] and [two_pick false] are two provably
     DISTINCT natural transformations INTO a functor of [_2, Sets]
     ([two_pick_distinct]), while [two_sets_one_unique] has arrows OUT of
     any functor into the terminal one unique.  So the category is not
     collapsed and terminality is a real, asymmetric constraint rather
     than a consequence of every hom-setoid being a singleton -- the
     Bool argument Structure/Terminal.v's own header cites.

     Indexed half: over [_2, Sets] the pointwise product of the constant
     [bool]-indexed family has carrier [forall _ : bool, bool] by
     [eq_refl], contains two provably inequivalent elements
     ([two_bool_prod_separates]), and its projections compute.  The
     universal property is EXERCISED, not merely stated: [two_pick_med]
     is the mediator the class produces for the competing family
     [two_pick], it satisfies the triangle ([two_pick_med_commutes]), and
     it COMPUTES -- [two_pick_med_true] and [two_pick_med_false] are
     [eq_refl].

   STATUS.  72/72 constants report "Closed under the global context",
   counted over [Print Module] so that the eighteen [Program] obligations --
   invisible to a [.glob] sweep, and queried by fully-qualified name --
   are included.

   REGISTRATION.  [Functor_Category_Terminal] is an [#[export] Instance],
   matching [Functor_Category_Cartesian], whose premise has the identical
   shape.  [Fun_HasIndexedProducts] is deliberately a plain [Definition],
   and the reason is an UNTESTED PRECAUTION rather than a measurement,
   which this sentence now says: the only other inhabitant of that class,
   [Sets_HasIndexedProducts], is a leaf, and registering a
   premise-carrying one could let resolution unify an unknown category
   with [Fun ?C ?D] and recurse.  That argument does NOT distinguish its
   own neighbours -- [Functor_Category_Cartesian] and this file's
   [Functor_Category_Terminal] are both premise-carrying [#[export]]
   instances with [Fun]-headed conclusions -- and no divergence has been
   exhibited either way.  Flipping it is a one-word change if a consumer
   wants it.

   WHAT IS NOT DELIVERED

     No [Limit]-shaped corollary, and the reason is measured here rather
     than inherited.  [Cone@{u0 u1 u2 u3 u4 u5}] is INNOCENT -- it takes
     [J : Category@{u0 u1 u2}] and [C : Category@{u3 u4 u5}], all six
     apart.  [IsALimit] and [Limit] are not: both are over
     [J : Category@{u0 u1 u1}] and [C : Category@{u2 u1 u1}], identifying
     the shape's hom and proof with the ambient's.  [DiscreteCat_Functor]
     (Instance/Discrete.v:52) is unannotated and instantiates
     [DiscreteCat@{u Set Set}] while leaving C's hom free.  It takes BOTH
     to bite: [Limit (DiscreteCat_Functor f)] elaborates only at
     [C : Category@{u1 Set Set}], measured on this commit.  So the [Set]
     pin is not the functor's alone.  Read the [Cone] half NARROWLY: the
     RECORD is innocent, but that licenses no claim that [IsALimit] and
     [Limit] are the only other donors, and they are not --
     [cone_leg] (Structure/Limit/Preservation.v:108) and [IsLimitCone]
     (:166) identify the shape's hom and proof with the ambient's in
     exactly the same way, so CONE VOCABULARY is among the donors even
     though the record is not.  Structure/Limit/Initial.v's own header
     already warns that an [ACone] control rules out only [ACone]/[Cone];
     an earlier revision of this section ran that control and drew the
     broader conclusion anyway.
     [DiscreteCat] itself is properly annotated [@{o h p}].

     No general "limits in [C, D] are pointwise" theorem -- only the
     nullary and the arbitrary-index-product shapes.  No colimits, no
     equalizers, no pullbacks, no exponentials.  No [Cartesian] or
     [Complete] instance is derived for [C, D] from these.  No
     functoriality or naturality of [Fun_iprod] in the family or the
     index.  No proof that [HasIndexedProducts D] alone yields
     [Terminal D] (that needs a chosen empty index type, which would pin
     an index universe; [terminal_empty_IsIndexedProduct] takes the
     emptiness as a hypothesis instead).  No preservation statement --
     nothing says the evaluation functors [C, D] -> D preserve these
     products, though they visibly do by construction.  And the general
     left fold of [Structure/Limit/Product/Finite.v] is consumed
     ([iprod_unique_iso]) but not extended. *)

(** ** Joint monicity of a family of product projections *)

(* Two morphisms into an indexed product that agree after every projection
   are equal.  This is the only place [HasIndexedProducts D] is spent below:
   every functor law and every naturality square of the pointwise product is
   "compose with the projections and compute" through it.  It is stated for
   the elementary [IsIndexedProduct] record, so it applies equally to a
   product harvested from the class. *)
Lemma iprod_jointly_monic {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a)
  (HP : IsIndexedProduct f p proj)
  {c : C} (u v : c ~> p) :
  (∀ a : A, proj a ∘ u ≈ proj a ∘ v) → u ≈ v.
Proof.
  intros Heq.
  pose proof (iprod_desc HP (fun a => proj a ∘ u)) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U).
    intros a; reflexivity.
  - apply (uniqueness U).
    intros a; symmetry; apply Heq.
Qed.

(** ** The constant functor, and the terminal functor *)

(* The constant functor at [d]: every object goes to [d], every morphism to
   [id].  Written as an explicit record literal, rather than as a [Program
   Definition] in a [Section], so that its universe binders can be spelled
   out and C's hom and proof universes stay apart; see the header. *)
Definition Constant_Functor@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

(* The terminal object of [C, D]: the constant functor at 1.  D's hom and
   proof universes are identified here, and that is [Terminal]'s doing. *)
Definition Constant_Terminal_Functor@{co ch cp dro dh}
  {C : Category@{co ch cp}} {D : Category@{dro dh dh}}
  (T : @Terminal D) : C ⟶ D :=
  Constant_Functor@{co ch cp dro dh dh} (@terminal_obj D T).

(* Mac Lane §III.5 Ex 5, nullary case.  The unique arrow [F ⟹ 1] has the
   unique arrow of D at every component; all three obligations -- the two
   naturality orientations and uniqueness -- are [one_unique]. *)
#[export]
Program Instance Functor_Category_Terminal {C D : Category}
  (T : @Terminal D) : @Terminal ([C, D]) := {|
  terminal_obj := Constant_Terminal_Functor T;
  one := fun F => {| transform := fun _ => one |}
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(** ** Pointwise indexed products *)

Section FunIndexedProducts.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context {A : Type}.
Context (F : A → (C ⟶ D)).

Definition fun_iprod_fam (c : C) : A → D := fun a => fobj[F a] c.

Definition fun_iprod_obj (c : C) : D := indexed_product (fun_iprod_fam c).

Definition fun_iprod_pr (c : C) (a : A) : fun_iprod_obj c ~> F a c :=
  indexed_product_proj (fun_iprod_fam c) a.

Definition fun_iprod_ump (c : C) :
  IsIndexedProduct (fun_iprod_fam c) (fun_iprod_obj c) (fun_iprod_pr c) :=
  indexed_product_ump (fun_iprod_fam c).

(* The arrow action: the unique map into the product at [c'] induced by the
   family whose [a]th leg is [fmap[F a] g] after the [a]th projection. *)
Definition fun_iprod_fmap {c c' : C} (g : c ~> c') :
  fun_iprod_obj c ~> fun_iprod_obj c' :=
  unique_obj (iprod_desc (fun_iprod_ump c')
                (fun a => fmap[F a] g ∘ fun_iprod_pr c a)).

Lemma fun_iprod_fmap_commutes {c c' : C} (g : c ~> c') (a : A) :
  fun_iprod_pr c' a ∘ fun_iprod_fmap g
    ≈ fmap[F a] g ∘ fun_iprod_pr c a.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c')
              (fun a => fmap[F a] g ∘ fun_iprod_pr c a)) a).
Qed.

(* The pointwise product as a functor.  Each of the three laws is proved by
   composing with the projections and appealing to [iprod_jointly_monic]. *)
Program Definition Fun_iprod : C ⟶ D := {|
  fobj := fun_iprod_obj;
  fmap := fun c c' g => fun_iprod_fmap g
|}.
Next Obligation.
  proper.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (fun_iprod_fmap_commutes x0 a).
  rewrite (fun_iprod_fmap_commutes y0 a).
  now rewrite X.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump x)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (@id C x) a).
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump z)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (f ∘ g) a).
  rewrite fmap_comp.
  rewrite (comp_assoc (fun_iprod_pr z a)
             (fun_iprod_fmap f) (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr y a)
                (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes g a).
  rewrite (comp_assoc (fmap[F a] f) (fmap[F a] g) (fun_iprod_pr x a)).
  reflexivity.
Qed.

(* The [a]th projection is a natural transformation: its naturality square
   IS the defining equation of the arrow action. *)
Program Definition Fun_iprod_proj (a : A) : Fun_iprod ⟹ F a := {|
  transform := fun c => fun_iprod_pr c a
|}.
Next Obligation. symmetry; apply fun_iprod_fmap_commutes. Qed.
Next Obligation. apply fun_iprod_fmap_commutes. Qed.

Definition fun_iprod_tuple_at (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) (c : C) :
  Q c ~> fun_iprod_obj c :=
  unique_obj (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)).

Lemma fun_iprod_tuple_commutes (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a)
  (c : C) (a : A) :
  fun_iprod_pr c a ∘ fun_iprod_tuple_at Q pi c ≈ transform (pi a) c.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)) a).
Qed.

(* The mediating transformation.  Its naturality is where the naturality of
   the competing family [pi] is spent, and nowhere else. *)
Program Definition fun_iprod_tuple (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) :
  Q ⟹ Fun_iprod := {|
  transform := fun c => fun_iprod_tuple_at Q pi c
|}.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.
Next Obligation.
  symmetry.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.

(* The elementary universal property, in [C, D].  Existence is
   [fun_iprod_tuple]; the triangle and the uniqueness clause are the
   corresponding facts in D, taken at each object. *)
Program Definition Fun_IsIndexedProduct :
  @IsIndexedProduct ([C, D]) A F Fun_iprod Fun_iprod_proj := {|
  iprod_desc := fun Q pi => {| unique_obj := fun_iprod_tuple Q pi |}
|}.
Next Obligation. apply fun_iprod_tuple_commutes. Qed.
Next Obligation.
  apply (uniqueness
           (iprod_desc (fun_iprod_ump x) (fun a => transform (pi a) x))).
  intros a.
  apply X.
Qed.

End FunIndexedProducts.

(* Mac Lane §III.5 Ex 5, the substantial case, packaged with the class's own
   constructor from exactly the elementary datum above.  Deliberately a plain
   [Definition] rather than an [Instance]; see the header. *)
Definition Fun_HasIndexedProducts {C D : Category}
  (HP : @HasIndexedProducts D) : @HasIndexedProducts ([C, D]) :=
  @Build_HasIndexedProducts ([C, D])
    (fun A F => @Fun_iprod C D HP A F)
    (fun A F a => @Fun_iprod_proj C D HP A F a)
    (fun A F => @Fun_IsIndexedProduct C D HP A F).

(** ** The binary case: a product is an indexed product over [bool] *)

Definition bool_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition cartesian_bool_proj {C : Category} (CP : @Cartesian C) (x y : C)
  (b : bool) : @product_obj C CP x y ~> bool_fam x y b :=
  match b with
  | true  => exl
  | false => exr
  end.

Program Definition cartesian_bool_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (bool_fam x y) (@product_obj C CP x y)
    (cartesian_bool_proj CP x y) := {|
  iprod_desc := fun c pi => {| unique_obj := pi true △ pi false |}
|}.
Next Obligation.
  destruct a; simpl.
  - apply exl_fork.
  - apply exr_fork.
Qed.
Next Obligation.
  symmetry.
  apply ump_products.
  split.
  - exact (X true).
  - exact (X false).
Qed.

(** The pointwise indexed product at a two-element index, compared with the
    pointwise binary product of Instance/Fun/Cartesian.v. *)

Definition Fun_bool_iprod_iso {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) :
  @Isomorphism ([C, D])
    (Fun_iprod HP (@bool_fam ([C, D]) F G))
    (@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G) :=
  iprod_unique_iso (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G))
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G).

Definition Fun_bool_iprod_iso_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b
    ∘ to (Fun_bool_iprod_iso HP CD F G)
    ≈ Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b :=
  iprod_compare_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G) b.

Definition Fun_bool_iprod_iso_inv_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  @compose ([C, D]) _ _ _
      (Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b)
      (from (Fun_bool_iprod_iso HP CD F G))
    ≈ cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b :=
  iprod_compare_inv_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G)) b.

(** ** What computes, and what does not *)

Section Strictness.

Context {C : Category}.
Context {D : Category}.
Context (T : @Terminal D).
Context (HP : @HasIndexedProducts D).

Example fun_terminal_obj (c : C) :
  fobj[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] c
    = @terminal_obj D T := eq_refl.

Example fun_terminal_fmap (c c' : C) (f : c ~> c') :
  fmap[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] f
    = @id D (@terminal_obj D T) := eq_refl.

Example fun_terminal_one_component (F : C ⟶ D) (c : C) :
  transform (@one ([C, D]) (Functor_Category_Terminal T) F) c
    = @one D T (F c) := eq_refl.

Example fun_iprod_obj_computes {A : Type} (F : A → (C ⟶ D)) (c : C) :
  fobj[Fun_iprod HP F] c = indexed_product (fun a => fobj[F a] c) := eq_refl.

Example fun_iprod_proj_component {A : Type} (F : A → (C ⟶ D))
  (a : A) (c : C) :
  transform (Fun_iprod_proj HP F a) c
    = indexed_product_proj (fun a => fobj[F a] c) a := eq_refl.

End Strictness.

Section StrictnessNegatives.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context (CD : @Cartesian D).
Context (F G : C ⟶ D) (c : C).

(* CONTROL: the object action of the pointwise indexed product is the
   indexed product of the pointwise family, on the nose. *)
Example ctl_bool_iprod_obj :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = indexed_product (fun b : bool => fobj[@bool_fam ([C, D]) F G b] c)
  := eq_refl.

(* NEGATIVE (conversion): it is NOT the pointwise binary product.  The two
   are related by [Fun_bool_iprod_iso] and by nothing stronger, because
   [HasIndexedProducts D] and [Cartesian D] choose their objects
   independently. *)
Fail Example bool_iprod_is_binary_product :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = fobj[@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G] c
  := eq_refl.

(* The mediator extracted from the class IS [fun_iprod_tuple], on the nose. *)
Example fun_iprod_class_mediator {A : Type} (Fm : A → (C ⟶ D))
  (Q : C ⟶ D) (pi : ∀ a, Q ⟹ Fm a) :
  unique_obj (iprod_desc (Fun_IsIndexedProduct HP Fm) pi)
    = fun_iprod_tuple HP Fm Q pi := eq_refl.

End StrictnessNegatives.

(** ** Relation to the diagonal functor *)

Section DiagonalComparison.

Context {C : Category}.
Context {D : Category}.
Context (d : D) (c : C).

(* Object and arrow actions agree with [Functor/Diagonal.v]'s constant
   functor ON THE NOSE. *)
Example constant_functor_diagonal_obj :
  fobj[@Constant_Functor C D d] c = fobj[fobj[@Diagonal D C] d] c := eq_refl.

Example constant_functor_diagonal_fmap (f : c ~> c) :
  fmap[@Constant_Functor C D d] f = fmap[fobj[@Diagonal D C] d] f := eq_refl.

(* NEGATIVE (conversion): the two functor RECORDS are not the same term.
   [Diagonal] is a [Program Instance], so its three law fields are opaque
   obligation constants, while [Constant_Functor] supplies them as explicit
   terms. *)
Fail Example constant_functor_is_diagonal :
  @Constant_Functor C D d = fobj[@Diagonal D C] d := eq_refl.

End DiagonalComparison.

(** ** Witnesses over [_2, Sets] *)

Definition FunBoolSet : SetoidObject := {|
  carrier   := bool
; is_setoid := eq_Setoid bool
|}.

Definition Two_Bool : _2 ⟶ Sets := @Constant_Functor _2 Sets FunBoolSet.

Definition Two_Sets_Terminal : @Terminal ([_2, Sets]) :=
  Functor_Category_Terminal Sets_Terminal.

Example two_sets_terminal_obj (o : _2) :
  fobj[@terminal_obj ([_2, Sets]) Two_Sets_Terminal] o
    = @terminal_obj Sets Sets_Terminal := eq_refl.

Program Definition two_pick (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ Two_Bool := {|
  transform := fun _ => {| morphism := fun _ => b |}
|}.

(* Non-degeneracy of the terminal object: arrows OUT of the terminal functor
   are unique, arrows INTO a functor are not.  So [_2, Sets] is not
   collapsed, and terminality is a real constraint rather than a
   consequence of every hom-setoid being a singleton. *)
Theorem two_pick_distinct : two_pick true ≈ two_pick false → False.
Proof.
  intros Heq.
  exact (match Heq TwoX ttt with eq_refl => I end).
Qed.

Theorem two_sets_one_unique (F : _2 ⟶ Sets)
  (u v : F ~{[_2, Sets]}~> @terminal_obj ([_2, Sets]) Two_Sets_Terminal) :
  u ≈ v.
Proof. exact (@one_unique ([_2, Sets]) Two_Sets_Terminal F u v). Qed.

Definition Two_Sets_HasIndexedProducts : @HasIndexedProducts ([_2, Sets]) :=
  Fun_HasIndexedProducts Sets_HasIndexedProducts.

Definition two_bool_fam : bool → (_2 ⟶ Sets) := fun _ => Two_Bool.

Definition two_bool_prod : _2 ⟶ Sets :=
  @indexed_product ([_2, Sets]) Two_Sets_HasIndexedProducts bool two_bool_fam.

Example two_bool_prod_carrier :
  carrier (fobj[two_bool_prod] TwoX) = (∀ _ : bool, bool) := eq_refl.

Definition two_all_true : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => true.

Definition two_all_false : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => false.

(* The pointwise product does not collapse: it has at least two elements. *)
Theorem two_bool_prod_separates : two_all_true ≈ two_all_false → False.
Proof.
  intros Heq.
  exact (match Heq true with eq_refl => I end).
Qed.

(* Its projections compute. *)
Example two_bool_proj_computes (b : bool) :
  transform
    (@indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
       bool two_bool_fam b) TwoX two_all_true = true := eq_refl.

(* The universal property is exercised, and its mediator COMPUTES.  The
   competing family is [two_pick], whose component at [b] picks [b]; the
   induced map into the product therefore sends [ttt] to the identity
   function on [bool]. *)
Definition two_pick_family (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ two_bool_fam b :=
  two_pick b.

Definition two_pick_med :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ~{[_2, Sets]}~> two_bool_prod :=
  unique_obj
    (iprod_desc
       (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
          bool two_bool_fam)
       two_pick_family).

Example two_pick_med_true :
  transform two_pick_med TwoX ttt true = true := eq_refl.

Example two_pick_med_false :
  transform two_pick_med TwoX ttt false = false := eq_refl.

Theorem two_pick_med_commutes (b : bool) :
  @indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
    bool two_bool_fam b ∘ two_pick_med ≈ two_pick_family b.
Proof.
  exact (unique_property
           (iprod_desc
              (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
                 bool two_bool_fam)
              two_pick_family) b).
Qed.

(** ** The nullary case: the terminal functor as an empty pointwise product *)

Program Definition terminal_empty_IsIndexedProduct {C : Category}
  (T : @Terminal C) {A : Type} (Hempty : A → False) (f : A → C)
  (proj : ∀ a : A, @terminal_obj C T ~> f a) :
  IsIndexedProduct f (@terminal_obj C T) proj := {|
  iprod_desc := fun c pi => {| unique_obj := one |}
|}.
Next Obligation. destruct (Hempty a). Qed.
Next Obligation. apply one_unique. Qed.

(* Over an empty index the pointwise indexed product IS the terminal functor,
   canonically.  This is an isomorphism and nothing stronger: the empty
   [indexed_product] of [D] is whatever [HasIndexedProducts D] chose, and
   nothing forces that choice to be [terminal_obj]. *)
Definition Fun_empty_iprod_terminal {C D : Category}
  (HP : @HasIndexedProducts D) (T : @Terminal D)
  {A : Type} (Hempty : A → False) (F : A → (C ⟶ D)) :
  @Isomorphism ([C, D])
    (Fun_iprod HP F)
    (@terminal_obj ([C, D]) (Functor_Category_Terminal T)) :=
  @iprod_unique_iso ([C, D]) A F _ _ _ _
    (Fun_IsIndexedProduct HP F)
    (terminal_empty_IsIndexedProduct
       (Functor_Category_Terminal T) Hempty F
       (fun a => False_rect _ (Hempty a))).
