Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Tensor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Presentation.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Selective comonoid supplies on coloured PROPs *)

(* nLab:      https://ncatlab.org/nlab/show/comonoid
   nLab:      https://ncatlab.org/nlab/show/copy-discard+category
   Reference: Fong & Spivak, "Supplying bells and whistles in symmetric
              monoidal categories" (arXiv:1908.02633)
   Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
              string diagrams", MSCS 29(7):938-971, 2019 (arXiv:1709.00322)

   A SUPPLY of commutative comonoids in a symmetric monoidal category
   (Fong-Spivak) equips every object with a comonoid structure,
   coherently with the tensor.  In a coloured PROP objects are colour
   words, so the natural datum is PER-COLOUR: a SELECTIVE supply
   assigns a commutative comonoid to the single-colour wire [wire c]
   of every colour [c] that a boolean predicate [copyable] marks as
   duplicable.  All other colours are LINEAR: their wires need not
   (and in the free/presented instances provably do not — see
   Construction/ColouredPROP/Linear.v and Supply/Instance.v) support
   any copy or delete operation.

   Design decisions, recorded:

   - The class carries the SINGLE per-colour primitive [supply_wire];
     the supply on a composite boundary [cs] is DERIVED by tensoring
     wire comonoids ([supply_list] below), using the packaged tensor
     and unit comonoids of Theory/Algebra/Comonoid/Tensor.v.  No
     boundary-level comonoid axiom is ever assumed.

   - Copyability is a [bool] predicate, not a [Type]-valued class:
     boolean equations enjoy UNCONDITIONAL proof irrelevance
     ([UIP_dec Bool.bool_dec]), so the derived-evidence bookkeeping of
     [supply_list] never depends on the choice of copyability proof
     ([all_copyable_irrelevant]).

   - As with [cd_comonoid] in Structure/Monoidal/CopyDiscard.v, the
     class is deliberately NOT declared an [Existing Instance]-style
     supplier of comonoids: which objects are copyable is semantic
     information, and instance resolution must not silently pick a
     supply.

   ** The MP/MB mediation

   A [ColouredPROP] carries two [Monoidal] structures on the same
   category — the strict path [MPc P] and the braided/symmetric path
   [MBc P] (Construction/ColouredPROP/Interp.v) — equal by the
   propositional field [cprop_monoidal_coherence].  Comonoids live on
   the symmetric side (their cocommutativity needs the braid), while
   the object correspondence [cprop_tensor_app]/[cprop_unit_nil] is
   stated on the strict side.  [ctensor_app_b] and [cunit_nil_b]
   below transport the correspondence across the coherence equality —
   the one new coherence-elimination site of this file, extending the
   doctrine of Interp.v.  At the free and presented instances the
   coherence field is [eq_refl], so both definitions REDUCE to the
   strict-side fields; Supply/Instance.v pins this with [eq_refl]
   [Example]s. *)

Section Supply.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** The coloured-PROP-object [⟦cs⟧c], as in
    [Construction/ColouredPROP.v] (whose notation is section-local
    there and must be re-declared per file). *)
Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(** ** MP/MB mediation *)

(** Tensor-on-objects is concatenation, transported to the
    braided/symmetric monoidal path where the comonoids live. *)
Definition ctensor_app_b (cs ds : list Colour) :
  ((⟦cs⟧c ⨂[MBc P] ⟦ds⟧c)%object = ⟦cs ++ ds⟧c) :=
  match cprop_monoidal_coherence P in _ = M
        return ((⟦cs⟧c ⨂[M] ⟦ds⟧c)%object = ⟦cs ++ ds⟧c)
  with eq_refl => cprop_tensor_app cs ds end.

(** The unit object is the empty word, on the braided/symmetric
    monoidal path. *)
Definition cunit_nil_b : @I P (MBc P) = ⟦[]⟧c :=
  match cprop_monoidal_coherence P in _ = M
        return (@I P M = ⟦[]⟧c)
  with eq_refl => cprop_unit_nil end.

(** Transparent congruence of [⨂[MBc P]] on object equalities (the
    [MBc]-side sibling of Interp.v's [ctensor_obj_eq]; kept as nested
    [match]es so that it computes to [eq_refl] on [eq_refl]s). *)
Definition ctensor2_b {x x' y y' : P} (e : x = x') (e' : y = y') :
  ((x ⨂[MBc P] y)%object = (x' ⨂[MBc P] y')%object) :=
  match e in _ = u return ((x ⨂[MBc P] y)%object = (u ⨂[MBc P] y')%object) with
  | eq_refl =>
      match e' in _ = v
            return ((x ⨂[MBc P] y)%object = (x ⨂[MBc P] v)%object) with
      | eq_refl => eq_refl
      end
  end.

(** ** Copyability evidence *)

Context (copyable : Colour -> bool).

(** Every colour of the word is copyable.  A boolean equation, so the
    evidence is proof-irrelevant without any axioms. *)
Definition all_copyable (cs : list Colour) : Prop :=
  forallb copyable cs = true.

Definition all_copyable_nil : all_copyable [] := eq_refl.

Lemma all_copyable_single (c : Colour) (H : copyable c = true) :
  all_copyable [c].
Proof.
  unfold all_copyable; simpl.
  rewrite H; reflexivity.
Qed.

Lemma all_copyable_app (cs ds : list Colour) :
  all_copyable cs -> all_copyable ds -> all_copyable (cs ++ ds).
Proof.
  unfold all_copyable; intros Hcs Hds.
  rewrite forallb_app, Hcs, Hds; reflexivity.
Qed.

Lemma all_copyable_app_l (cs ds : list Colour) :
  all_copyable (cs ++ ds) -> all_copyable cs.
Proof.
  unfold all_copyable; intros H.
  rewrite forallb_app in H.
  exact (proj1 (andb_prop _ _ H)).
Qed.

Lemma all_copyable_app_r (cs ds : list Colour) :
  all_copyable (cs ++ ds) -> all_copyable ds.
Proof.
  unfold all_copyable; intros H.
  rewrite forallb_app in H.
  exact (proj2 (andb_prop _ _ H)).
Qed.

(** Unconditional proof irrelevance of copyability evidence — the
    payoff of [bool]-valued copyability (no colour decidability
    needed). *)
Lemma all_copyable_irrelevant (cs : list Colour)
  (H1 H2 : all_copyable cs) : H1 = H2.
Proof. exact (UIP_dec Bool.bool_dec H1 H2). Qed.

(** ** The class: a per-colour selective supply

    The single primitive: every copyable colour's wire carries a
    commutative comonoid.  Everything else — the boundary supply, its
    copy/discard accessors — is derived below.

    Deliberately NOT wired into instance resolution (the [cd_comonoid]
    doctrine of Structure/Monoidal/CopyDiscard.v): a supply is chosen,
    not inferred. *)
Class SelectiveSupply : Type := {
  supply_wire (c : Colour) :
    copyable c = true ->
    @CommutativeComonoid (@cprop_cat Colour P) (@cprop_symmetric Colour P)
      (wire c)
}.

(** ** The derived boundary supply *)

(** Leibniz transport of a commutative-comonoid structure along an
    object equality.  Transparent, so that at instances where the
    equality computes to [eq_refl] the transport vanishes. *)
Definition ccomonoid_transport {X Y : P} (e : X = Y) :
  @CommutativeComonoid P (@cprop_symmetric Colour P) X ->
  @CommutativeComonoid P (@cprop_symmetric Colour P) Y :=
  match e in _ = Z
        return @CommutativeComonoid P (@cprop_symmetric Colour P) X ->
               @CommutativeComonoid P (@cprop_symmetric Colour P) Z
  with eq_refl => fun M => M end.

(** The supply on a boundary word, derived from the wire supplies:
    the empty word carries the (transported) unit comonoid, and a
    cons peels one wire comonoid off and tensors it onto the supply
    of the tail via the packaged tensor comonoid of
    Theory/Algebra/Comonoid/Tensor.v.  Note [wire c ≡ ⟦[c]⟧c] and
    [[c] ++ cs' ≡ c :: cs'] definitionally, so the only transports
    are the two mediation equalities. *)
Fixpoint supply_list `{SS : SelectiveSupply} (cs : list Colour) :
  all_copyable cs ->
  @CommutativeComonoid P (@cprop_symmetric Colour P) ⟦cs⟧c :=
  match cs return all_copyable cs ->
                  @CommutativeComonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
  with
  | [] => fun _ =>
      ccomonoid_transport cunit_nil_b
        (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))
  | c :: cs' => fun H =>
      ccomonoid_transport (ctensor_app_b [c] cs')
        (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
           (supply_wire c (proj1 (andb_prop _ _ H)))
           (supply_list cs' (proj2 (andb_prop _ _ H))))
  end.

(** Copy and discard on a fully copyable boundary. *)
Definition scopy `{SS : SelectiveSupply} (cs : list Colour)
  (H : all_copyable cs) :
  ⟦cs⟧c ~{P}~> (⟦cs⟧c ⨂[MBc P] ⟦cs⟧c)%object :=
  ccomon_delta (supply_list cs H).

Definition sdiscard `{SS : SelectiveSupply} (cs : list Colour)
  (H : all_copyable cs) :
  ⟦cs⟧c ~{P}~> @I P (MBc P) :=
  ccomon_epsilon (supply_list cs H).

(** The derived supply does not depend on the copyability evidence —
    Leibniz equality, not merely [≈]. *)
Lemma supply_list_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  supply_list cs H1 = supply_list cs H2.
Proof.
  rewrite (all_copyable_irrelevant cs H1 H2); reflexivity.
Qed.

Lemma scopy_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  scopy cs H1 = scopy cs H2.
Proof.
  unfold scopy; rewrite (supply_list_irr cs H1 H2); reflexivity.
Qed.

Lemma sdiscard_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  sdiscard cs H1 = sdiscard cs H2.
Proof.
  unfold sdiscard; rewrite (supply_list_irr cs H1 H2); reflexivity.
Qed.

End Supply.

Arguments ctensor_app_b {Colour} P cs ds : assert.
Arguments cunit_nil_b {Colour} P : assert.
Arguments ctensor2_b {Colour} P {x x' y y'} e e' : assert.
Arguments all_copyable {Colour} copyable cs : assert.
Arguments all_copyable_nil {Colour} copyable : assert.
Arguments all_copyable_single {Colour} copyable c H : assert.
Arguments all_copyable_app {Colour} copyable cs ds _ _ : assert.
Arguments all_copyable_app_l {Colour} copyable cs ds _ : assert.
Arguments all_copyable_app_r {Colour} copyable cs ds _ : assert.
Arguments all_copyable_irrelevant {Colour} copyable cs H1 H2 : assert.
Arguments SelectiveSupply {Colour} P copyable : assert.
Arguments supply_wire {Colour P copyable SelectiveSupply} c _ : assert.
Arguments ccomonoid_transport {Colour} P {X Y} e _ : assert.
Arguments supply_list {Colour P copyable SS} cs H : assert.
Arguments scopy {Colour P copyable SS} cs H : assert.
Arguments sdiscard {Colour P copyable SS} cs H : assert.
Arguments supply_list_irr {Colour P copyable SS} cs H1 H2 : assert.
Arguments scopy_irr {Colour P copyable SS} cs H1 H2 : assert.
Arguments sdiscard_irr {Colour P copyable SS} cs H1 H2 : assert.

(* ------------------------------------------------------------------ *)

(** ** Machine-checked sanity: the mediation is definitional at both
       delivered instances

    At the free ([FreeColouredPROP]) and the presented
    ([CPresentedColouredPROP]) coloured PROPs the coherence field is
    [eq_refl] over ONE shared [Monoidal] record, so both mediating
    equalities compute to [eq_refl].  Each [Example] holds by a closed
    [eq_refl] proof term; any regression in the shared-record wiring
    of Instance.v/Presentation.v is caught here (and again, at the
    supplied instance, by the [Example]s of Supply/Instance.v). *)

Example ctensor_app_b_free_is_refl {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (cs ds : list Colour) :
  ctensor_app_b (FreeColouredPROP S Cdec) cs ds = eq_refl := eq_refl.

Example cunit_nil_b_free_is_refl {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  cunit_nil_b (FreeColouredPROP S Cdec) = eq_refl := eq_refl.

Example ctensor_app_b_presented_is_refl {Colour : Type} (E : CSMT Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (cs ds : list Colour) :
  ctensor_app_b (CPresentedColouredPROP E Cdec) cs ds = eq_refl := eq_refl.

Example cunit_nil_b_presented_is_refl {Colour : Type} (E : CSMT Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  cunit_nil_b (CPresentedColouredPROP E Cdec) = eq_refl := eq_refl.

(* ------------------------------------------------------------------ *)

(** ** Toward the Fong–Spivak coherence theorems

    The remainder of the file proves that the DERIVED boundary supply
    satisfies the supply-coherence squares of Fong–Spivak (the
    [scfa_tensor_*] shapes of Hypergraph.v, the [cd_tensor_*] fields
    of CopyDiscard.v): the comultiplication/counit of [supply_list
    (cs ++ ds)] is the canonical tensor delta/epsilon of the parts'
    supplies, mediated by the [ctensor_app_b] cast.  Because the
    boundary supply is derived rather than axiomatized, these are
    THEOREMS ([supply_app_delta]/[supply_app_epsilon] below).

    The proof layers:

    1.  variable-equality transporters between [Monoidal] records
        ([tmon_unitl_cast]/[tmon_assoc_cast]), which carry the
        morphism-level strictness of [MPc P] (Interp.v's
        [cstrict_*_cast]) over to [MBc P] exactly the way Interp.v's
        [BraidTransport] kit carries the braid the other way: the
        lemma eliminates a VARIABLE equality and the instantiation
        merely passes [cprop_monoidal_coherence];

    2.  raw coherences of the canonical tensor-comonoid morphisms in
        an arbitrary symmetric monoidal category (no comonoid laws —
        pure naturality and interchange, so the induction can
        substitute an inductive hypothesis for an inner
        comultiplication);

    3.  cast-aligned [_general] forms at [P] (the Interp.v K-kit
        style): every boundary equality is quantified, destructible
        ones are destructed, and the unitor-/associator-shaped
        residues are aligned by [obj_uip] — hence the [ObjDecEq]
        hypothesis — and discharged through layers 1–2. *)

(** Transport a left-unitor-shaped object equality along an equality
    of [Monoidal] records. *)
Definition tmon_unitl_obj {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x : C)
  (e : ((@I C M1) ⨂[M1] x)%object = x) :
  ((@I C M2) ⨂[M2] x)%object = x :=
  match E in _ = m return (((@I C m) ⨂[m] x)%object = x) with
  | eq_refl => e
  end.

Lemma tmon_unitl_cast {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x : C)
  (e : ((@I C M1) ⨂[M1] x)%object = x) :
  to (@unit_left C M1 x) ≈ id_cast e →
  to (@unit_left C M2 x) ≈ id_cast (tmon_unitl_obj E x e).
Proof.
  destruct E.
  intro He.
  exact He.
Qed.

(** Transport an associator-shaped object equality. *)
Definition tmon_assoc_obj {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x y z : C)
  (e : ((x ⨂[M1] y) ⨂[M1] z)%object = (x ⨂[M1] (y ⨂[M1] z))%object) :
  ((x ⨂[M2] y) ⨂[M2] z)%object = (x ⨂[M2] (y ⨂[M2] z))%object :=
  match E in _ = m
        return (((x ⨂[m] y) ⨂[m] z)%object = (x ⨂[m] (y ⨂[m] z))%object)
  with
  | eq_refl => e
  end.

Lemma tmon_assoc_cast {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x y z : C)
  (e : ((x ⨂[M1] y) ⨂[M1] z)%object = (x ⨂[M1] (y ⨂[M1] z))%object) :
  to (@tensor_assoc C M1 x y z) ≈ id_cast e →
  to (@tensor_assoc C M2 x y z) ≈ id_cast (tmon_assoc_obj E x y z e).
Proof.
  destruct E.
  intro He.
  exact He.
Qed.

(** If the [to] direction of an isomorphism is a cast, its [from]
    direction is the cast along the symmetric equality. *)
Lemma iso_from_id_cast {C : Category} {x y : C} (i : x ≅ y) (e : x = y) :
  to i ≈ id_cast e → from i ≈ id_cast (eq_sym e).
Proof.
  intro H.
  rewrite <- (id_right (from i)).
  rewrite <- (id_cast_inv_r e).
  rewrite comp_assoc.
  rewrite <- H.
  rewrite iso_from_to.
  apply id_left.
Qed.

(* ------------------------------------------------------------------ *)

(** ** Raw coherences of the canonical tensor-comonoid morphisms

    Three general symmetric-monoidal facts about the canonical
    morphisms of Structure/Monoidal/Hypergraph.v, for RAW
    comultiplications and counits:

    - [tensor_delta_unit_l_raw]: the canonical tensor delta of the
      unit comonoid's [λ⁻¹] with [dy] is [dy] conjugated by unitors
      ([swap_inner_unit_left] plus naturality of [λ]);
    - [tensor_delta_assoc_raw]: the two iterations of the canonical
      tensor delta agree across the associator — [swap_inner_assoc]
      (the associativity hexagon of the squaring functor,
      Braided/Proofs.v) at diagonal arguments, plus naturality of the
      associator;
    - [tensor_epsilon_assoc_raw]: the same for the canonical epsilon
      (triangle coherence plus Kelly's [unit_identity]). *)

Section TensorComonoidCoherence.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Lemma tensor_delta_unit_l_raw {y : C} (dy : y ~> (y ⨂ y)%object) :
  (to (@unit_left C _ y) ⨂ to (@unit_left C _ y))
    ∘ (mid_swap_inv I y ∘ ((@unit_left C _ I)⁻¹ ⨂ dy))
    ≈ dy ∘ to (@unit_left C _ y).
Proof.
  rewrite mid_swap_inv_swap_inner.
  assert (E : ((@unit_left C _ I)⁻¹ ⨂ dy)
                ≈ ((@unit_left C _ I)⁻¹ ⨂ id[(y ⨂ y)%object])
                    ∘ (id[I] ⨂ dy)).
  { rewrite <- bimap_comp.
    now rewrite id_right, id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left.
  symmetry.
  apply to_unit_left_natural.
Qed.

Lemma tensor_delta_assoc_raw {x y z : C}
  (dx : x ~> (x ⨂ x)%object) (dy : y ~> (y ⨂ y)%object)
  (dz : z ~> (z ⨂ z)%object) :
  (to (@tensor_assoc C _ x y z) ⨂ to (@tensor_assoc C _ x y z))
    ∘ (mid_swap_inv ((x ⨂ y)%object) z
         ∘ ((mid_swap_inv x y ∘ (dx ⨂ dy)) ⨂ dz))
    ≈ (mid_swap_inv x ((y ⨂ z)%object)
         ∘ (dx ⨂ (mid_swap_inv y z ∘ (dy ⨂ dz))))
        ∘ to (@tensor_assoc C _ x y z).
Proof.
  rewrite !mid_swap_inv_swap_inner.
  assert (EL : ((swap_inner x x y y ∘ (dx ⨂ dy)) ⨂ dz)
                 ≈ (swap_inner x x y y ⨂ id[(z ⨂ z)%object])
                     ∘ ((dx ⨂ dy) ⨂ dz)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  assert (ER : (dx ⨂ (swap_inner y y z z ∘ (dy ⨂ dz)))
                 ≈ (id[(x ⨂ x)%object] ⨂ swap_inner y y z z)
                     ∘ (dx ⨂ (dy ⨂ dz))).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite EL, ER; clear EL ER.
  rewrite <- !comp_assoc.
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  symmetry.
  apply swap_inner_assoc.
Qed.

Lemma tensor_epsilon_assoc_raw {x y z : C}
  (ex : x ~> I) (ey : y ~> I) (ez : z ~> I) :
  to (@unit_left C _ I) ∘ ((to (@unit_left C _ I) ∘ (ex ⨂ ey)) ⨂ ez)
    ≈ (to (@unit_left C _ I)
         ∘ (ex ⨂ (to (@unit_left C _ I) ∘ (ey ⨂ ez))))
        ∘ to (@tensor_assoc C _ x y z).
Proof.
  assert (EL : ((to (@unit_left C _ I) ∘ (ex ⨂ ey)) ⨂ ez)
                 ≈ (to (@unit_left C _ I) ⨂ id[I]) ∘ ((ex ⨂ ey) ⨂ ez)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  assert (ER : (ex ⨂ (to (@unit_left C _ I) ∘ (ey ⨂ ez)))
                 ≈ (id[I] ⨂ to (@unit_left C _ I)) ∘ (ex ⨂ (ey ⨂ ez))).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite EL, ER; clear EL ER.
  rewrite <- !comp_assoc.
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  rewrite unit_identity.
  reflexivity.
Qed.

End TensorComonoidCoherence.

(* ------------------------------------------------------------------ *)

(** ** The cast kit at [MBc P] *)

Section SupplyCastKit.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** A tensor of casts at [MBc P] is the cast along the paired
    equality [ctensor2_b]. *)
Lemma cbimap_cast_b {x x' y y' : P} (e : x = x') (e' : y = y') :
  (id_cast e ⨂[MBc P] id_cast e') ≈ id_cast (ctensor2_b P e e').
Proof.
  destruct e, e'.
  exact (@bimap_id_id P P P (@tensor P (MBc P)) x y).
Qed.

(** *** Strictness of [MBc P], through the transporters

    The strict path's comparison facts (Interp.v's [cstrict_*_cast]
    at [MPc P]) transported to the symmetric path along
    [cprop_monoidal_coherence].  Only the left unitor and the
    associator are needed by the supply theorems. *)

Definition cunitl_obj_b (x : P) :
  ((@I P (MBc P)) ⨂[MBc P] x)%object = x :=
  tmon_unitl_obj (@cprop_monoidal_coherence Colour P) x
    (@strict_unit_left_obj P (@cprop_strict Colour P) x).

Lemma cunitl_cast_b (x : P) :
  to (@unit_left P (MBc P) x) ≈ id_cast (cunitl_obj_b x).
Proof.
  apply (tmon_unitl_cast (@cprop_monoidal_coherence Colour P) x
           (@strict_unit_left_obj P (@cprop_strict Colour P) x)).
  symmetry.
  apply (cstrict_unitl_cast P x).
Qed.

Lemma cunitl_cast_from_b (x : P) :
  from (@unit_left P (MBc P) x) ≈ id_cast (eq_sym (cunitl_obj_b x)).
Proof.
  apply iso_from_id_cast.
  apply cunitl_cast_b.
Qed.

Definition cassoc_obj_b (x y z : P) :
  ((x ⨂[MBc P] y) ⨂[MBc P] z)%object
  = (x ⨂[MBc P] (y ⨂[MBc P] z))%object :=
  tmon_assoc_obj (@cprop_monoidal_coherence Colour P) x y z
    (@strict_assoc_obj P (@cprop_strict Colour P) x y z).

Lemma cassoc_cast_b (x y z : P) :
  to (@tensor_assoc P (MBc P) x y z) ≈ id_cast (cassoc_obj_b x y z).
Proof.
  apply (tmon_assoc_cast (@cprop_monoidal_coherence Colour P) x y z
           (@strict_assoc_obj P (@cprop_strict Colour P) x y z)).
  symmetry.
  apply (cstrict_assoc_cast P x y z).
Qed.

Lemma cassoc_cast_from_b (x y z : P) :
  from (@tensor_assoc P (MBc P) x y z)
    ≈ id_cast (eq_sym (cassoc_obj_b x y z)).
Proof.
  apply iso_from_id_cast.
  apply cassoc_cast_b.
Qed.

(** *** Projections of transported comonoids

    The delta of a transported comonoid is the [hom_cast] of the
    delta (along the equality and its [ctensor2_b] pairing); the
    epsilon likewise, with the codomain [I] untouched. *)

Lemma ccomonoid_transport_delta {X Y : P} (e : X = Y)
  (M : @CommutativeComonoid P (@cprop_symmetric Colour P) X) :
  ccomon_delta (ccomonoid_transport P e M)
  = hom_cast e (ctensor2_b P e e) (ccomon_delta M).
Proof.
  destruct e.
  reflexivity.
Qed.

Lemma ccomonoid_transport_epsilon {X Y : P} (e : X = Y)
  (M : @CommutativeComonoid P (@cprop_symmetric Colour P) X) :
  ccomon_epsilon (ccomonoid_transport P e M)
  = hom_cast e eq_refl (ccomon_epsilon M).
Proof.
  destruct e.
  reflexivity.
Qed.

(** *** The canonical morphisms, respelled through [ccomon_*]

    Definitional unfoldings of [canonical_tensor_delta]/[epsilon]
    (Hypergraph.v) into the raw shapes the supply theorems chase. *)

Lemma canonical_tensor_delta_ccomon {X Y : P}
  (MX : @CommutativeComonoid P (@cprop_symmetric Colour P) X)
  (MY : @CommutativeComonoid P (@cprop_symmetric Colour P) Y) :
  @canonical_tensor_delta P (@cprop_symmetric Colour P) X Y MX MY
  = @mid_swap_inv P (@cprop_symmetric Colour P) X Y
      ∘ (ccomon_delta MX ⨂[MBc P] ccomon_delta MY).
Proof.
  reflexivity.
Qed.

Lemma canonical_tensor_epsilon_ccomon {X Y : P}
  (MX : @CommutativeComonoid P (@cprop_symmetric Colour P) X)
  (MY : @CommutativeComonoid P (@cprop_symmetric Colour P) Y) :
  @canonical_tensor_epsilon P (@cprop_symmetric Colour P) X Y MX MY
  = to (@unit_left P (MBc P) (@I P (MBc P)))
      ∘ (ccomon_epsilon MX ⨂[MBc P] ccomon_epsilon MY).
Proof.
  reflexivity.
Qed.

End SupplyCastKit.

Arguments cbimap_cast_b {Colour} P {x x' y y'} e e' : assert.
Arguments cunitl_obj_b {Colour} P x : assert.
Arguments cunitl_cast_b {Colour} P x : assert.
Arguments cunitl_cast_from_b {Colour} P x : assert.
Arguments cassoc_obj_b {Colour} P x y z : assert.
Arguments cassoc_cast_b {Colour} P x y z : assert.
Arguments cassoc_cast_from_b {Colour} P x y z : assert.
Arguments ccomonoid_transport_delta {Colour} P {X Y} e M : assert.
Arguments ccomonoid_transport_epsilon {Colour} P {X Y} e M : assert.
Arguments canonical_tensor_delta_ccomon {Colour} P {X Y} MX MY : assert.
Arguments canonical_tensor_epsilon_ccomon {Colour} P {X Y} MX MY : assert.

(* ------------------------------------------------------------------ *)

(** ** The Fong–Spivak coherence theorems *)

Section SupplyCoherence.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).
Context {OD : @ObjDecEq P}.

Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(** *** The cast-aligned [_general] forms

    Interp.v K-kit style: quantify every boundary equality, destruct
    the destructible ones, align the unitor-/associator-shaped
    residues by [obj_uip], and discharge through the [MBc]-strictness
    bridges and the raw coherences. *)

(** Unit absorption for the canonical delta: casting the canonical
    tensor delta of (the transported unit comonoid's delta) with [dy]
    along a unitor-shaped equality is [dy] itself. *)
Lemma supply_delta_unit_general {n y : P}
  (u : @I P (MBc P) = n)
  (U2 : ((@I P (MBc P)) ⨂[MBc P] (@I P (MBc P)))%object
        = (n ⨂[MBc P] n)%object)
  (dy : y ~{P}~> (y ⨂[MBc P] y)%object)
  (e : (n ⨂[MBc P] y)%object = y)
  (E2 : ((n ⨂[MBc P] y) ⨂[MBc P] (n ⨂[MBc P] y))%object
        = (y ⨂[MBc P] y)%object) :
  hom_cast e E2
    (@mid_swap_inv P (@cprop_symmetric Colour P) n y
       ∘ (hom_cast u U2 (from (@unit_left P (MBc P) (@I P (MBc P))))
          ⨂[MBc P] dy))
    ≈ dy.
Proof using OD P.
  destruct u.
  rewrite (obj_uip U2 eq_refl).
  rewrite hom_cast_refl.
  rewrite (obj_uip e (cunitl_obj_b P y)).
  rewrite (obj_uip E2 (ctensor2_b P (cunitl_obj_b P y) (cunitl_obj_b P y))).
  rewrite hom_cast_decompose.
  rewrite <- (cbimap_cast_b P).
  rewrite <- !(cunitl_cast_b P).
  rewrite <- (cunitl_cast_from_b P).
  rewrite (tensor_delta_unit_l_raw (S := @cprop_symmetric Colour P) dy).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(** Unit absorption for the canonical epsilon. *)
Lemma supply_epsilon_unit_general {n y : P}
  (u : @I P (MBc P) = n)
  (ey : y ~{P}~> @I P (MBc P))
  (e : (n ⨂[MBc P] y)%object = y) :
  hom_cast e eq_refl
    (to (@unit_left P (MBc P) (@I P (MBc P)))
       ∘ (hom_cast u eq_refl id[@I P (MBc P)] ⨂[MBc P] ey))
    ≈ ey.
Proof using OD P.
  destruct u.
  rewrite hom_cast_refl.
  rewrite (obj_uip e (cunitl_obj_b P y)).
  rewrite hom_cast_decompose.
  rewrite id_cast_refl, id_left.
  rewrite <- (cunitl_cast_from_b P).
  rewrite <- to_unit_left_natural.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(** Associativity for the canonical delta: the two cast-mediated
    iterations of the canonical tensor delta agree. *)
Lemma supply_delta_assoc_general {x y z v w s : P}
  (dx : x ~{P}~> (x ⨂[MBc P] x)%object)
  (dy : y ~{P}~> (y ⨂[MBc P] y)%object)
  (dz : z ~{P}~> (z ⨂[MBc P] z)%object)
  (eyz : (y ⨂[MBc P] z)%object = v)
  (Eyz : ((y ⨂[MBc P] z) ⨂[MBc P] (y ⨂[MBc P] z))%object
         = (v ⨂[MBc P] v)%object)
  (exv : (x ⨂[MBc P] v)%object = s)
  (Exv : ((x ⨂[MBc P] v) ⨂[MBc P] (x ⨂[MBc P] v))%object
         = (s ⨂[MBc P] s)%object)
  (exy : (x ⨂[MBc P] y)%object = w)
  (Exy : ((x ⨂[MBc P] y) ⨂[MBc P] (x ⨂[MBc P] y))%object
         = (w ⨂[MBc P] w)%object)
  (ewz : (w ⨂[MBc P] z)%object = s)
  (Ewz : ((w ⨂[MBc P] z) ⨂[MBc P] (w ⨂[MBc P] z))%object
         = (s ⨂[MBc P] s)%object) :
  hom_cast exv Exv
    (@mid_swap_inv P (@cprop_symmetric Colour P) x v
       ∘ (dx ⨂[MBc P]
          hom_cast eyz Eyz
            (@mid_swap_inv P (@cprop_symmetric Colour P) y z
               ∘ (dy ⨂[MBc P] dz))))
    ≈ hom_cast ewz Ewz
        (@mid_swap_inv P (@cprop_symmetric Colour P) w z
           ∘ (hom_cast exy Exy
                (@mid_swap_inv P (@cprop_symmetric Colour P) x y
                   ∘ (dx ⨂[MBc P] dy))
              ⨂[MBc P] dz)).
Proof using OD P.
  destruct eyz.
  rewrite (obj_uip Eyz eq_refl).
  rewrite hom_cast_refl.
  destruct exy.
  rewrite (obj_uip Exy eq_refl).
  rewrite hom_cast_refl.
  destruct ewz.
  rewrite (obj_uip Ewz eq_refl).
  rewrite hom_cast_refl.
  rewrite (obj_uip exv (eq_sym (cassoc_obj_b P x y z))).
  rewrite (obj_uip Exv (ctensor2_b P (eq_sym (cassoc_obj_b P x y z))
                                     (eq_sym (cassoc_obj_b P x y z)))).
  rewrite hom_cast_decompose.
  rewrite <- (cbimap_cast_b P).
  rewrite <- !(cassoc_cast_from_b P).
  rewrite (id_cast_irr (eq_sym (eq_sym (cassoc_obj_b P x y z)))
                       (cassoc_obj_b P x y z)).
  rewrite <- (cassoc_cast_b P).
  rewrite <- comp_assoc.
  rewrite <- (tensor_delta_assoc_raw (S := @cprop_symmetric Colour P)
                dx dy dz).
  rewrite (comp_assoc
             (from (@tensor_assoc P (MBc P) x y z)
                ⨂[MBc P] from (@tensor_assoc P (MBc P) x y z))
             (to (@tensor_assoc P (MBc P) x y z)
                ⨂[MBc P] to (@tensor_assoc P (MBc P) x y z))).
  rewrite <- bimap_comp.
  rewrite !iso_from_to.
  rewrite bimap_id_id.
  apply id_left.
Qed.

(** Associativity for the canonical epsilon. *)
Lemma supply_epsilon_assoc_general {x y z v w s : P}
  (ex : x ~{P}~> @I P (MBc P))
  (ey : y ~{P}~> @I P (MBc P))
  (ez : z ~{P}~> @I P (MBc P))
  (eyz : (y ⨂[MBc P] z)%object = v)
  (exv : (x ⨂[MBc P] v)%object = s)
  (exy : (x ⨂[MBc P] y)%object = w)
  (ewz : (w ⨂[MBc P] z)%object = s) :
  hom_cast exv eq_refl
    (to (@unit_left P (MBc P) (@I P (MBc P)))
       ∘ (ex ⨂[MBc P]
          hom_cast eyz eq_refl
            (to (@unit_left P (MBc P) (@I P (MBc P)))
               ∘ (ey ⨂[MBc P] ez))))
    ≈ hom_cast ewz eq_refl
        (to (@unit_left P (MBc P) (@I P (MBc P)))
           ∘ (hom_cast exy eq_refl
                (to (@unit_left P (MBc P) (@I P (MBc P)))
                   ∘ (ex ⨂[MBc P] ey))
              ⨂[MBc P] ez)).
Proof using OD P.
  destruct eyz.
  rewrite hom_cast_refl.
  destruct exy.
  rewrite hom_cast_refl.
  destruct ewz.
  rewrite hom_cast_refl.
  rewrite (obj_uip exv (eq_sym (cassoc_obj_b P x y z))).
  rewrite hom_cast_decompose.
  rewrite id_cast_refl, id_left.
  rewrite (id_cast_irr (eq_sym (eq_sym (cassoc_obj_b P x y z)))
                       (cassoc_obj_b P x y z)).
  rewrite <- (cassoc_cast_b P).
  symmetry.
  apply (tensor_epsilon_assoc_raw (S := @cprop_symmetric Colour P)
           ex ey ez).
Qed.

(** *** Computed projections of the derived supply *)

Context (copyable : Colour -> bool).
Context {SS : SelectiveSupply P copyable}.

(** Per-colour copyability evidence is unique, like [all_copyable]'s. *)
Lemma copyable_irrelevant (c : Colour) (p q : copyable c = true) : p = q.
Proof.
  apply (UIP_dec Bool.bool_dec).
Qed.

(** Each equation unfolds one [supply_list] constructor case and
    computes the transported projection through
    [ccomonoid_transport_delta]/[epsilon]; the residue is
    definitional. *)

Lemma supply_list_delta_nil (H : all_copyable copyable []) :
  ccomon_delta (supply_list [] H)
  = hom_cast (cunit_nil_b P)
      (ctensor2_b P (cunit_nil_b P) (cunit_nil_b P))
      (from (@unit_left P (MBc P) (@I P (MBc P)))).
Proof.
  exact (ccomonoid_transport_delta P (cunit_nil_b P)
           (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))).
Qed.

Lemma supply_list_epsilon_nil (H : all_copyable copyable []) :
  ccomon_epsilon (supply_list [] H)
  = hom_cast (cunit_nil_b P) eq_refl id[@I P (MBc P)].
Proof.
  exact (ccomonoid_transport_epsilon P (cunit_nil_b P)
           (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))).
Qed.

Lemma supply_list_delta_cons (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l)) :
  ccomon_delta (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l)
      (ctensor2_b P (ctensor_app_b P [c] l) (ctensor_app_b P [c] l))
      (@mid_swap_inv P (@cprop_symmetric Colour P) (@wire Colour P c) ⟦l⟧c
         ∘ (ccomon_delta (supply_wire c (proj1 (andb_prop _ _ H)))
            ⨂[MBc P]
            ccomon_delta (supply_list l (proj2 (andb_prop _ _ H))))).
Proof.
  exact (ccomonoid_transport_delta P (ctensor_app_b P [c] l)
           (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
              (supply_wire c (proj1 (andb_prop _ _ H)))
              (supply_list l (proj2 (andb_prop _ _ H))))).
Qed.

Lemma supply_list_epsilon_cons (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l)) :
  ccomon_epsilon (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l) eq_refl
      (to (@unit_left P (MBc P) (@I P (MBc P)))
         ∘ (ccomon_epsilon (supply_wire c (proj1 (andb_prop _ _ H)))
            ⨂[MBc P]
            ccomon_epsilon (supply_list l (proj2 (andb_prop _ _ H))))).
Proof.
  exact (ccomonoid_transport_epsilon P (ctensor_app_b P [c] l)
           (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
              (supply_wire c (proj1 (andb_prop _ _ H)))
              (supply_list l (proj2 (andb_prop _ _ H))))).
Qed.

(** The same projections at ARBITRARY split evidence: since
    copyability evidence is unique ([copyable_irrelevant] /
    [all_copyable_irrelevant]), the head-wire and tail evidence in the
    unfolding may be chosen freely.  These are the forms the coherence
    theorems consume — they let the induction thread ONE uniform
    evidence spelling through both sides of the square. *)

Lemma supply_list_delta_cons_any (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l))
  (p : copyable c = true) (q : all_copyable copyable l) :
  ccomon_delta (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l)
      (ctensor2_b P (ctensor_app_b P [c] l) (ctensor_app_b P [c] l))
      (@mid_swap_inv P (@cprop_symmetric Colour P) (@wire Colour P c) ⟦l⟧c
         ∘ (ccomon_delta (supply_wire c p)
            ⨂[MBc P] ccomon_delta (supply_list l q))).
Proof.
  rewrite (copyable_irrelevant c p (proj1 (andb_prop _ _ H))).
  rewrite (all_copyable_irrelevant copyable l q (proj2 (andb_prop _ _ H))).
  exact (supply_list_delta_cons c l H).
Qed.

Lemma supply_list_epsilon_cons_any (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l))
  (p : copyable c = true) (q : all_copyable copyable l) :
  ccomon_epsilon (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l) eq_refl
      (to (@unit_left P (MBc P) (@I P (MBc P)))
         ∘ (ccomon_epsilon (supply_wire c p)
            ⨂[MBc P] ccomon_epsilon (supply_list l q))).
Proof.
  rewrite (copyable_irrelevant c p (proj1 (andb_prop _ _ H))).
  rewrite (all_copyable_irrelevant copyable l q (proj2 (andb_prop _ _ H))).
  exact (supply_list_epsilon_cons c l H).
Qed.

(** *** The coherence theorems

    The comultiplication (resp. counit) of the derived supply on a
    concatenated boundary [cs ++ ds] is the canonical tensor delta
    (resp. epsilon) of the supplies of the parts, mediated by the
    [ctensor_app_b] cast — the Fong–Spivak supply-coherence squares
    (the [scfa_tensor_*] shapes of Hypergraph.v, the [cd_tensor_*]
    fields of CopyDiscard.v), PROVED for the derived boundary supply
    rather than assumed. *)

Theorem supply_app_delta (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (Hcd : all_copyable copyable (cs ++ ds)) :
  ccomon_delta (supply_list (cs ++ ds) Hcd)
    ≈ hom_cast (ctensor_app_b P cs ds)
        (ctensor2_b P (ctensor_app_b P cs ds) (ctensor_app_b P cs ds))
        (canonical_tensor_delta (supply_list cs Hc) (supply_list ds Hd)).
Proof using OD P SS copyable.
  revert Hc Hcd.
  induction cs as [| c cs' IH]; intros Hc Hcd.
  - (* [[] ++ ds ≡ ds]: align the evidence, expose the transported
       unit comonoid, and absorb it. *)
    rewrite (all_copyable_irrelevant copyable _ Hcd Hd).
    rewrite (canonical_tensor_delta_ccomon P).
    rewrite supply_list_delta_nil.
    symmetry.
    apply supply_delta_unit_general.
  - (* [(c :: cs') ++ ds ≡ c :: (cs' ++ ds)]: unfold one cons on each
       side at a UNIFORM choice of evidence (the [_any] projections),
       substitute the inductive hypothesis for the tail, and close by
       cast-aligned associativity. *)
    change ((c :: cs') ++ ds) with (c :: cs' ++ ds).
    rewrite (supply_list_delta_cons_any c (cs' ++ ds) Hcd
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite (IH (proj2 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite !(canonical_tensor_delta_ccomon P).
    rewrite (supply_list_delta_cons_any c cs' Hc
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hc))).
    apply supply_delta_assoc_general.
Qed.

Theorem supply_app_epsilon (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (Hcd : all_copyable copyable (cs ++ ds)) :
  ccomon_epsilon (supply_list (cs ++ ds) Hcd)
    ≈ hom_cast (ctensor_app_b P cs ds) eq_refl
        (canonical_tensor_epsilon (supply_list cs Hc) (supply_list ds Hd)).
Proof using OD P SS copyable.
  revert Hc Hcd.
  induction cs as [| c cs' IH]; intros Hc Hcd.
  - rewrite (all_copyable_irrelevant copyable _ Hcd Hd).
    rewrite (canonical_tensor_epsilon_ccomon P).
    rewrite supply_list_epsilon_nil.
    symmetry.
    apply supply_epsilon_unit_general.
  - change ((c :: cs') ++ ds) with (c :: cs' ++ ds).
    rewrite (supply_list_epsilon_cons_any c (cs' ++ ds) Hcd
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite (IH (proj2 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite !(canonical_tensor_epsilon_ccomon P).
    rewrite (supply_list_epsilon_cons_any c cs' Hc
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hc))).
    apply supply_epsilon_assoc_general.
Qed.

End SupplyCoherence.

Arguments copyable_irrelevant {Colour} copyable c p q : assert.
Arguments supply_list_delta_nil {Colour P copyable SS} H : assert.
Arguments supply_list_epsilon_nil {Colour P copyable SS} H : assert.
Arguments supply_list_delta_cons {Colour P copyable SS} c l H : assert.
Arguments supply_list_epsilon_cons {Colour P copyable SS} c l H : assert.
Arguments supply_list_delta_cons_any {Colour P copyable SS} c l H p q
  : assert.
Arguments supply_list_epsilon_cons_any {Colour P copyable SS} c l H p q
  : assert.
Arguments supply_app_delta {Colour P OD copyable SS} cs ds Hc Hd Hcd : assert.
Arguments supply_app_epsilon {Colour P OD copyable SS} cs ds Hc Hd Hcd
  : assert.
