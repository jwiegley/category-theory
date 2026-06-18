(* ========================================================================= *)
(* Regression suite for issue #138.                                          *)
(*                                                                           *)
(* This file locks in the resolution of issue #138.  It checks that:        *)
(*                                                                           *)
(*   - [StrictCat] is the STRICT category of categories: its homset          *)
(*     equivalence is [Functor_StrictEq_Setoid] (strict equality of          *)
(*     functors), not the weak nat-iso equivalence [Functor_Setoid] used by  *)
(*     the weak category [Cat].                                              *)
(*                                                                           *)
(*   - The underlying-graph [Forgetful] functor and the [Free] ⊣ [Forgetful] *)
(*     adjunction live OVER [StrictCat], not over the weak [Cat].  They       *)
(*     cannot be defined over [Cat] because they do not respect natural      *)
(*     isomorphism: a category's underlying quiver is not invariant under     *)
(*     the weak equivalence that [Cat]'s [Functor_Setoid] identifies.        *)
(*                                                                           *)
(*   - The comparison functor [StrictCat_to_Cat] witnesses that strict        *)
(*     equality of functors implies natural isomorphism (strict-eq ⟹         *)
(*     natural-iso), exhibiting [StrictCat] as a refinement of [Cat].        *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Free.Quiver.
Generalizable All Variables.

(* ===== BLOCK A138 — forgetful behaviour ===== *)

(* The underlying-graph (Forgetful) functor is the motivating example of issue
   #138.  It is defined over [StrictCat], NOT the weak [Cat], precisely because
   it does NOT respect natural isomorphism: two categories can be equivalent
   (naturally isomorphic functors witnessing an equivalence) while their
   underlying quivers are genuinely different, so a functor sending a category
   to its underlying quiver cannot be well-defined up to the weak equivalence
   that [Cat]'s [Functor_Setoid] identifies.  It is well-defined up to the
   STRICT equality of [StrictCat]'s [Functor_StrictEq_Setoid]. *)

(* Forgetful is well-typed with the claimed signature. *)
Check (Forgetful : StrictCat ⟶ QuiverCategory).

(* Computational behaviour: underlying nodes are the category's objects. *)
Example A138_nodes (C : Category) : @nodes (Forgetful C) = obj[C] := eq_refl.

(* Underlying edges are the hom-sets. *)
Example A138_edges (C : Category) (x y : C) :
  @edges (Forgetful C) x y = (x ~> y) := eq_refl.

(* The edge-map of the functor's fmap is the functor's fmap. *)
Example A138_fedgemap (C D : Category) (F : C ⟶ D) (x y : C) (f : x ~> y) :
  @fedgemap _ _ (fmap[Forgetful] F) x y f = fmap[F] f := eq_refl.

(* The underlying constructions on objects and morphisms are well-typed. *)
Check (QuiverOfCat : Category -> Quiver).
Check (@QuiverHomomorphismOfFunctor
        : ∀ (C D : Category), (C ⟶ D) ->
            QuiverHomomorphism (QuiverOfCat C) (QuiverOfCat D)).

(* The composite Forgetful ◯ FreeCatFunctor is an endofunctor on QuiverCategory. *)
Check (Forgetful ◯ FreeCatFunctor : QuiverCategory ⟶ QuiverCategory).

(* A negative check.  [Forgetful] is fixed as [StrictCat ⟶ Quiv], so ascribing
   it the type [Cat ⟶ Quiv] is a genuine type error — the domain category differs
   ("has type StrictCat ⟶ QuiverCategory while it is expected to have type
   Cat ⟶ QuiverCategory").  These [Fail] commands lock in that [Forgetful] is NOT
   a functor over the weak [Cat].  Note this only checks the type mismatch; it
   does not itself exercise the deeper reason no such functor can be *built* over
   [Cat] (its [fmap_respects] would have to turn a natural isomorphism [F x ≅ G x]
   into a strict equality [F x = G x] of quiver nodes — see [Instance.Cat]). *)
Fail Check (Forgetful : Cat ⟶ QuiverCategory).
Fail Definition A138_forgetful_over_Cat : Cat ⟶ QuiverCategory := Forgetful.

(* ===== BLOCK B138 — free ⊣ forgetful adjunction ===== *)

Check (FreeCatFunctor : QuiverCategory ⟶ StrictCat).

Check (FreeForgetfulAdjunction : FreeCatFunctor ⊣ Forgetful).

(* A concrete worked quiver: one node, one loop.
   NB: bare [unit] in edge position resolves to the adjunction-unit notation, so
   we must qualify the Coq type as [Datatypes.unit]. *)
Definition B138_loop : Quiver :=
  Build_Quiver_Standard_Eq Datatypes.unit (fun _ _ => Datatypes.unit).

Check (FreeOnQuiver B138_loop : Category).
Check (FreeCatFunctor B138_loop : Category).

(* The nodes of the free category on the loop quiver are exactly the quiver's
   nodes (here [unit]). *)
Example B138_free_loop_nodes :
  obj[FreeOnQuiver B138_loop] = Datatypes.unit := eq_refl.

(* The composite endofunctor on StrictCat *)
Check (FreeCatFunctor ◯ Forgetful : StrictCat ⟶ StrictCat).

(* ===== BLOCK C138 — StrictCat strict laws ===== *)

(* The defining property of issue #138's fix: StrictCat's hom-equivalence IS the
   strict equality [Functor_StrictEq_Setoid] (not the weak nat-iso
   [Functor_Setoid] of [Cat]).  This pins it directly, so reverting StrictCat to
   the weak setoid fails HERE, in the test body — not merely transitively
   through some downstream consumer. *)
Example C138_homset_is_strict (A B : Category) :
  @homset StrictCat A B = @Functor_StrictEq_Setoid A B := eq_refl.

(* The strict identity law, exercised through StrictCat's OWN category structure
   (its [id], [compose], [homset] and [id_left]), rather than only via the
   free-standing [fun_strict_equiv_*] lemmas. *)
Example C138_strictcat_id_left (A B : Category) (F : A ⟶ B) :
  @equiv _ (@homset StrictCat A B)
         (@compose StrictCat _ _ _ (@id StrictCat B) F) F :=
  @id_left StrictCat A B F.

(* The three strict category laws, stated with the EXPLICIT strict setoid
   and discharged by the existing lemmas. *)
Example C138_id_left {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F := fun_strict_equiv_id_left F.

Example C138_id_right {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ Id) F := fun_strict_equiv_id_right F.

Example C138_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ (G ◯ H)) ((F ◯ G) ◯ H) :=
  fun_strict_equiv_comp_assoc F G H.

(* Strict equality is genuinely an equivalence usable on concrete witnesses. *)

(* Reflexivity of a functor under the strict setoid. *)
Example C138_strict_refl {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid F F.
Proof.
  reflexivity.
Qed.

(* Id ◯ (Id ◯ F) relates to F under strict equality, using transitivity. *)
Example C138_nested_id {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ (Id ◯ F)) F.
Proof.
  transitivity (Id ◯ F).
  - exact (fun_strict_equiv_id_left (Id ◯ F)).
  - exact (fun_strict_equiv_id_left F).
Qed.

(* Strict equality refines weak (nat-iso) equality. *)
Example C138_strict_refines_weak {A B} (F : A ⟶ B) :
  @equiv _ Functor_Setoid (Id ◯ F) F :=
  strict_equiv_implies_fun_equiv (Id ◯ F) F (fun_strict_equiv_id_left F).

(* ===== BLOCK D138 — comparison functor ===== *)

Check (StrictCat_to_Cat : StrictCat ⟶ Cat).

Example D138_obj (C : Category) : StrictCat_to_Cat C = C := eq_refl.

Example D138_map {C D} (F : C ⟶ D) : fmap[StrictCat_to_Cat] F = F := eq_refl.

(* The per-object isomorphism the comparison uses is [iso_of_eq] of the object
   equality, which at a reflexivity proof is the identity iso (its [to] and
   [from] are [id]).  These two examples pin [iso_of_eq]'s behaviour directly.
   That [strict_equiv_implies_fun_equiv] builds its natural-iso family as
   [fun x => iso_of_eq (eq_on_obj x)] is true by construction (see ToCat.v); it
   is not separately machine-checked here because that lemma is opaque ([Qed]),
   so its body does not reduce for an [eq_refl] comparison. *)
Example D138_iso_of_eq_refl_to (C : Category) (x : C) :
  to (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_iso_of_eq_refl_from (C : Category) (x : C) :
  from (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_strict_to_weak {C D} (F G : C ⟶ D)
  (H : @equiv _ Functor_StrictEq_Setoid F G) : @equiv _ Functor_Setoid F G
  := strict_equiv_implies_fun_equiv F G H.

(* Concrete instance: re-derive a strict equality witness locally (id_left),
   then push it through the comparison functor to obtain a weak (nat-iso)
   equality in Cat. *)

Definition D138_idleft_strict {C D} (F : C ⟶ D)
  : @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F
  := fun_strict_equiv_id_left F.

Definition D138_idleft_weak {C D} (F : C ⟶ D)
  : @equiv _ Functor_Setoid (Id ◯ F) F
  := strict_equiv_implies_fun_equiv (Id ◯ F) F (D138_idleft_strict F).
