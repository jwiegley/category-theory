Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Structure.Limit.Product.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** * Indexed products of modules

    The product ∏_{i∈I} V_i of an arbitrary family of R-modules, with every
    operation pointwise, and its universal property — in the two clauses,
    and assembled into Structure/Limit/Product.v's [IsIndexedProduct].
    Written for Instance/FdVect/NoRightAdjoint.v (#433), which needs the
    countable power F^ℕ as an object of [RMod (field_ring F)]; nothing here
    is specific to fields or to ℕ.

    BEFORE THIS FILE the tree had no indexed product or coproduct in any
    algebraic category: Instance/Mod/Coproduct.v's [RMod_Biproduct] and
    Instance/Ab/Coproduct.v's coproduct are binary, and the tree's
    [HasIndexedProducts] inhabitants — Sets' (Instance/Sets/Products.v:302),
    Cat's and StrictCat's (Instance/Cat/Limit.v:293, :521), functor
    categories' and [[_2, Sets]]'s (Instance/Fun/Terminal.v:520, :713) and
    [_1]'s (Structure/Limit/Power/Adjunction.v:1611) — include no algebraic
    category; measured by `grep -rn 'Instance .*HasIndexedProducts\|
    Definition .*HasIndexedProducts' --include='*.v'`.

    WHAT IS HERE.  Over [Context {R : RingObject} {I : Type} (V : I →
    RModObject R)]: the carrier [modprod_setoid] (the dependent function
    space [∀ i, carrier (V i)] under pointwise [≈]), the commutative monoid
    [modprod_cmon], the abelian group [modprod_ab], the module [ProdMod],
    the projections [prod_proj i : RModHom ProdMod (V i)], the mediator
    [prod_tuple f : RModHom Z ProdMod] out of a family [f : ∀ i, RModHom Z
    (V i)], the two clauses of the universal property, [prod_tuple_proj]
    ([prod_proj i ∘ prod_tuple f ≈ f i], stated as a composite in [RMod R])
    and [prod_tuple_unique] (any [u] with the same projections is [≈
    prod_tuple f]) — both [reflexivity] pointwise, because the projections
    compute: [prod_proj_component] reads [cmon_map (rm_hom (prod_proj i)) f
    = f i] by [eq_refl] — and their assembly [ProdMod_IsIndexedProduct :
    IsIndexedProduct V ProdMod prod_proj], whose mediator IS [prod_tuple]
    ([prod_iprod_mediator], by [eq_refl]).

    NOT DELIVERED.  The [HasIndexedProducts (RMod R)] instance itself — not
    attempted: #433 needs only the one product, and Instance/Sets/Products.v
    (its header, "the class quantifies its index by a bare [Type]") records
    the universe negotiation the class demands, which is left for the issue
    that needs the class; indexed COPRODUCTS ⊕_I (finite support needs a
    decidable index or a free construction; none is built); the
    identification of the binary case with Instance/Mod/Coproduct.v's
    [RMod_Biproduct].

    MEASURED.  11 `.glob` heads (9 `def`, 2 `prf`) and 20 [Program]
    obligations, all 31 "Closed under the global context", zero `Axioms:`
    lines; the 20 obligations are the respectfulness and law proofs of the
    six [Program Definition]s, every one closed by hand under
    [Obligation Tactic := idtac] with `Qed` — twenty-two `Qed` in all, and
    ONE `Defined`, [ProdMod_IsIndexedProduct], LOAD-BEARING (flipped to
    `Qed` in a copy of the whole file, [prod_iprod_mediator] stops).
    Universes ([About] under `Set Printing Universes`): no [Set] anywhere;
    the data ([modprod_setoid], [modprod_cmon], [modprod_ab], [ProdMod])
    carry no equation and — apart from [modprod_setoid], which carries no
    strict constraint at all — one strict constraint, the module carrier
    level below the product's (`u6 < u11` for the monoid and the group,
    `u6 < u13` for the module); [prod_proj], [prod_tuple] and
    [prod_proj_component] carry [RModHom]'s identification of the three
    module-internal levels (`u5 = u6 = u7`) and `u6 < u8`; the four heads
    stated inside [RMod R] — [prod_tuple_proj], [prod_tuple_unique],
    [ProdMod_IsIndexedProduct], [prod_iprod_mediator] — inherit that
    category's identification of the module levels with the ring's (`u =
    u3 = u5 = u6 = u7`, `u1 = u4`), two strict constraints (`u < u8`,
    `u < u9`) and the stdlib caps `Basics.compose` and `ID` (the readback
    adds `Setoid.u`).  Closure 43 files excluding self (Structure/Limit/
    Product.v 7 at the margin, Instance/Mod.v 6, the other six `Require`s
    0; none of the eight is droppable); zero name collisions across the
    tree for the eleven names (`grep -rlw --include='*.v'`; the first
    draft's [prod_setoid] became [modprod_setoid] because
    Lib/Datatypes.v:139 owns [prod_setoid]).  The `make print-assumptions`
    gate carries the eleven heads. *)

#[local] Obligation Tactic := idtac.

Section ProdMod.

Context {R : RingObject}.
Context {I : Type}.
Context (V : I → RModObject R).

(* The carrier is the dependent function space, with pointwise [≈]. *)
Program Definition modprod_setoid : SetoidObject := {|
  carrier := ∀ i : I, carrier (cmon_setoid (V i));
  is_setoid := {| equiv := fun f g => ∀ i, f i ≈ g i |}
|}.
Next Obligation.
  intros; constructor.
  - intros f i; reflexivity.
  - intros f g H i; now symmetry.
  - intros f g h H1 H2 i; now transitivity (g i).
Qed.

Program Definition modprod_cmon : CMonObject := {|
  cmon_setoid := modprod_setoid;
  cmon_zero   := fun i => cmon_zero (V i);
  cmon_plus   := fun f g i => cmon_plus (V i) (f i) (g i)
|}.
Next Obligation. intros f f' Hf g g' Hg i; now rewrite (Hf i), (Hg i). Qed.
Next Obligation. intros f g h i; apply cmon_plus_assoc. Qed.
Next Obligation. intros f g i; apply cmon_plus_comm. Qed.
Next Obligation. intros f i; apply cmon_plus_zero_l. Qed.

Program Definition modprod_ab : AbObject := {|
  ab_cmon := modprod_cmon;
  ab_neg  := fun f i => ab_neg (V i) (f i)
|}.
Next Obligation. intros f g H i; now rewrite (H i). Qed.
Next Obligation. intros f i; apply ab_neg_left. Qed.

(* The product module: all operations pointwise. *)
Program Definition ProdMod : RModObject R := {|
  rm_ab   := modprod_ab;
  rm_smul := fun r f i => rm_smul (V i) r (f i)
|}.
Next Obligation. intros r s Hrs f g Hfg i; now rewrite Hrs, (Hfg i). Qed.
Next Obligation. intros r f g i; apply rm_smul_distr_l. Qed.
Next Obligation. intros r s f i; apply rm_smul_distr_r. Qed.
Next Obligation. intros r s f i; apply rm_smul_assoc. Qed.
Next Obligation. intros f i; apply rm_smul_one. Qed.

(* The projections. *)
Program Definition prod_proj (i : I) : RModHom ProdMod (V i) := {|
  rm_hom := {| cmon_map := {| morphism := fun f => f i |} |}
|}.
Next Obligation. intros i f g H; exact (H i). Qed.
Next Obligation. intros i; reflexivity. Qed.
Next Obligation. intros i f g; reflexivity. Qed.
Next Obligation. intros i r f; reflexivity. Qed.

(* The mediating map out of a family of maps. *)
Program Definition prod_tuple {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) :
  RModHom Z ProdMod := {|
  rm_hom := {|
    cmon_map := {| morphism := fun z i => cmon_map (rm_hom (f i)) z |}
  |}
|}.
Next Obligation. intros Z f z z' H i; now rewrite H. Qed.
Next Obligation. intros Z f i; apply (cmon_map_zero (rm_hom (f i))). Qed.
Next Obligation. intros Z f a b i; apply (cmon_map_plus (rm_hom (f i))). Qed.
Next Obligation. intros Z f r z i; apply (rm_map_smul (f i)). Qed.

(* The universal property, in the two clauses [IsIndexedProduct] asks for;
   both are [reflexivity] pointwise. *)
Lemma prod_tuple_proj {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) (i : I) :
  @compose (RMod R) Z ProdMod (V i) (prod_proj i) (prod_tuple f) ≈ f i.
Proof. intro z; reflexivity. Qed.

Lemma prod_tuple_unique {Z : RModObject R} (f : ∀ i, RModHom Z (V i))
  (u : RModHom Z ProdMod)
  (H : ∀ i, @compose (RMod R) Z ProdMod (V i) (prod_proj i) u ≈ f i) :
  u ≈ prod_tuple f.
Proof. intros z i; exact (H i z). Qed.

(* The projections compute. *)
Example prod_proj_component (i : I) (f : carrier (cmon_setoid ProdMod)) :
  cmon_map (rm_hom (prod_proj i)) f = f i := eq_refl.

(* The two clauses assembled into the tree's own record: [ProdMod] with its
   projections is an indexed product in [RMod R]. *)
Definition ProdMod_IsIndexedProduct :
  @IsIndexedProduct (RMod R) I V ProdMod prod_proj.
Proof.
  constructor; intros Z pi.
  exists (prod_tuple pi).
  - exact (prod_tuple_proj pi).
  - intros u Hu; symmetry; exact (prod_tuple_unique pi u Hu).
Defined.

(* The record's mediator IS [prod_tuple]. *)
Example prod_iprod_mediator {Z : RModObject R} (pi : ∀ i, RModHom Z (V i)) :
  unique_obj (iprod_desc ProdMod_IsIndexedProduct pi) = prod_tuple pi
  := eq_refl.

End ProdMod.
