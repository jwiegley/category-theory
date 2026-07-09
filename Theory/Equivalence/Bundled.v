Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   The bundled notion of equivalence of categories.  Where
   [EquivalenceOfCategories F] (Theory/Equivalence.v) is a structure carried
   by a *given* functor F, the bundle [C ≃ D] defined here packages the
   functor together with that structure — a sigma type, in the same split,
   choice-carrying house style as the unbundled classes — so that "C and D
   are equivalent" becomes a single proof-relevant statement about the two
   categories themselves.

   Being equivalent is reflexive ([Equivalence_refl], the identity functor
   quasi-inverted by itself), symmetric ([Equivalence_sym], the
   quasi-inverse with the two cells swapped — [EquivalenceOfCategories_sym]
   of Theory/Equivalence.v), and transitive ([Equivalence_trans], carried
   by the composite functor).  The composite's witness,
   [EquivalenceOfCategories_Compose] below, is proved at the unbundled
   level: the composite of two equivalences is quasi-inverted by the
   composite of the quasi-inverses in the opposite order, its two cells
   obtained by reassociating with [fun_equiv_comp_assoc] and cancelling
   the inner counit/unit cell.

   Naming and hygiene: nothing here is called bare "Equivalence" (that
   name belongs to the standard library's class of equivalence relations);
   the [≃] notation is guarded in [category_theory_scope]; and, as
   everywhere in this development, nothing is registered for instance
   resolution — a quasi-inverse is a choice, so all constructions below
   are plain Definitions, passed explicitly at use sites. *)

Definition CategoryEquivalence (C D : Category) : Type :=
  ∃ F : C ⟶ D, EquivalenceOfCategories F.

Notation "C ≃ D" := (CategoryEquivalence C%category D%category)
  (at level 91) : category_theory_scope.

(* Covariant accessors: the underlying functor, its equivalence structure,
   and the chosen quasi-inverse. *)

Definition equivalence_functor {C D : Category} (E : C ≃ D) : C ⟶ D :=
  `1 E.

Definition equivalence_witness {C D : Category} (E : C ≃ D) :
  EquivalenceOfCategories (`1 E) :=
  `2 E.

Definition equivalence_quasi_inverse {C D : Category} (E : C ≃ D) :
  D ⟶ C :=
  @quasi_inverse C D (`1 E) (`2 E).

(* Composition of equivalences, at the unbundled level.  The composite
   G ◯ F is quasi-inverted by F′ ◯ G′ (primes denoting the chosen
   quasi-inverses): each cell collapses by reassociation followed by the
   corresponding cell of the inner equivalence, then of the outer one. *)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.
Context (HF : @EquivalenceOfCategories C D F).
Context (HG : @EquivalenceOfCategories D E G).

Local Notation F' := (@quasi_inverse C D F HF).
Local Notation G' := (@quasi_inverse D E G HG).

Lemma EquivalenceOfCategories_Compose_counit :
  (G ◯ F) ◯ (F' ◯ G') ≈ Id[E].
Proof.
  rewrite <- (fun_equiv_comp_assoc G F (F' ◯ G')).
  rewrite (fun_equiv_comp_assoc F F' G').
  (* the inner counit cell F ◯ F′ ≈ Id[D] cancels the middle *)
  rewrite (@equivalence_counit C D F HF).
  rewrite (fun_equiv_id_left G').
  exact (@equivalence_counit D E G HG).
Qed.

Lemma EquivalenceOfCategories_Compose_unit :
  Id[C] ≈ (F' ◯ G') ◯ (G ◯ F).
Proof.
  rewrite <- (fun_equiv_comp_assoc F' G' (G ◯ F)).
  rewrite (fun_equiv_comp_assoc G' G F).
  (* the inner unit cell Id[D] ≈ G′ ◯ G cancels the middle *)
  rewrite <- (@equivalence_unit D E G HG).
  rewrite (fun_equiv_id_left F).
  exact (@equivalence_unit C D F HF).
Qed.

Definition EquivalenceOfCategories_Compose :
  EquivalenceOfCategories (G ◯ F) :=
  @Build_EquivalenceOfCategories C E (G ◯ F) (F' ◯ G')
    EquivalenceOfCategories_Compose_counit
    EquivalenceOfCategories_Compose_unit.

End Compose.

(* Equivalence of categories is reflexive, symmetric and transitive.
   These are data-carrying Definitions at the bundled level, not instances
   of the standard library's Reflexive/Symmetric/Transitive classes: the
   bundle is Type-valued and choice-carrying, and must never be conjured
   by resolution. *)

Definition Equivalence_refl (C : Category) : C ≃ C :=
  (Id[C]; @EquivalenceOfCategories_Id C).

Definition Equivalence_sym {C D : Category} (E : C ≃ D) : D ≃ C :=
  (@quasi_inverse C D (`1 E) (`2 E);
   @EquivalenceOfCategories_sym C D (`1 E) (`2 E)).

Definition Equivalence_trans {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) : C ≃ E :=
  (`1 E2 ◯ `1 E1; EquivalenceOfCategories_Compose (`2 E1) (`2 E2)).

(* Two sanity corollaries, definitional on the functor components: symmetry
   is involutive on the underlying data, and the functor carried by a
   composite is the composite of the carried functors. *)

Corollary Equivalence_sym_involutive {C D : Category} (E : C ≃ D) :
  `1 (Equivalence_sym (Equivalence_sym E)) ≈ `1 E.
Proof. reflexivity. Qed.

Corollary Equivalence_trans_functor {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) :
  `1 (Equivalence_trans E1 E2) ≈ `1 E2 ◯ `1 E1.
Proof. reflexivity. Qed.
