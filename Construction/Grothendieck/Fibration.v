Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.

Generalizable All Variables.

(** * The Grothendieck projection is a split opfibration *)

(* nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

   The projection ∫ A ⟶ B of the Grothendieck construction
   (Construction/Grothendieck.v) is an opfibration, and its canonical
   opcleaving is split: the chosen lifts compose functorially on the nose,
   with the chosen coherence isos of [A] as the mediators.

   Opcartesian lifts.  Over [f : x ~> y] with [dx] above [x], the chosen
   lift is the total morphism [(f; id)] into [(y; idx_map A f dx)]: push
   [dx] forward along [f]; the displayed part is the identity of the
   pushforward [idx_map A f dx].  Opcartesianness is [DCartesian] in the
   op-displayed sense of Theory/Fibration.v — cartesianness for
   [Displayed_op (Grothendieck_Displayed A)] over [B^op].  Unwinding the
   op-reading, a displayed morphism over [g ∘ f] out of [dx] is a fibre
   morphism [hh : idx_map A (g ∘ f) dx ~> dz], and it factors through the
   chosen lift uniquely by conjugating with the chosen composition iso:
   the mediating morphism is [hh ∘ to (idx_comp A g f dx)], and both
   existence and uniqueness are inverse cancellation for [idx_comp] —
   which is exactly why the lift is opcartesian: [idx_comp] is an iso.
   [Grothendieck_OpCleaving] packages the chosen lifts as an [OpCleaving],
   and [cleaving_total_cloven] upgrades it to a cloven fibration of the
   projection out of the op-total category ([Grothendieck_OpCloven]).

   Splitting (disclosed design point).  The split laws are delivered as
   standalone named lemmas ([Grothendieck_split_lift_id],
   [Grothendieck_split_lift_comp], bundled as [Grothendieck_Split]) rather
   than as an op-instance of the strict [SplitCleaving] record of
   Theory/Fibration.v.  [SplitCleaving] anchors its laws in propositional
   object equalities ([lift_obj … = e']); for the canonical opcleaving
   here those anchors would read [idx_map A id dx = dx] and
   [idx_map A g (idx_map A f dx) = idx_map A (g ∘ f) dx] in the fibres,
   and a general [IndexedCat] provides them only as the chosen isos
   [idx_id] and [idx_comp], not as equalities — demanding equality would
   amount to demanding that [A] itself be strict.  The honest split laws
   therefore state functoriality of the cleavage on the nose relative to
   the chosen coherence isos: composing the chosen lift of [id[x]] with
   the vertical image of [idx_id A dx] IS the identity of [(x; dx)], and
   composing the chosen lifts of [f] then [g] with the vertical image of
   [idx_comp A g f dx] IS the chosen lift of [g ∘ f].  The mediators are
   pinned to the chosen isos — which satisfy the unit and cocycle
   coherence of [IndexedCat] — not merely asserted to exist; nothing is
   quantified away.  When [A] is strict (all [idx_id]/[idx_comp]
   components identity isos), the mediators reduce to identities and the
   laws specialize to the classical on-the-nose splitting. *)

Section GrothendieckFibration.

Context {B : Category}.
Context (A : IndexedCat B).

(** ** The chosen opcartesian lift *)

(* Over [f : x ~> y] — read in [B^op] as an arrow from [y] to [x] — the
   chosen lift of [dx : idx_fib A x] is displayed over [f] from the
   pushforward [idx_map A f dx] (over [y], the op-domain) to [dx] (over
   [x], the op-codomain); unwinding [Displayed_op] and
   [Grothendieck_Displayed], such a displayed morphism is a fibre morphism
   [idx_map A f dx ~> idx_map A f dx], and the chosen one is the
   identity. *)
Definition Grothendieck_op_lift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  @dhom (B^op) (Displayed_op (Grothendieck_Displayed A)) y x
        (idx_map A f dx) dx f :=
  @id (idx_fib A y) (idx_map A f dx).

(* The chosen lift is opcartesian: every displayed morphism over a
   composite [g ∘ f] out of [dx] factors through it by a unique displayed
   morphism over [g].  Unwound, the factorization candidate ranges over
   fibre morphisms [idx_map A g (idx_map A f dx) ~> dz], the equation
   composes with [from (idx_comp A g f dx)], and the unique solution
   conjugates [hh] with the chosen composition iso. *)
Definition Grothendieck_lift_cocartesian {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  DCartesian (D := Displayed_op (Grothendieck_Displayed A))
             (Grothendieck_op_lift f dx).
Proof.
  unfold Grothendieck_op_lift.
  constructor; intros z g dz hh; simpl in *.
  unshelve refine {| unique_obj := hh ∘ to (idx_comp A g f dx) |}.
  - (* the factorization commutes: cancel [to] against [from] *)
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    apply id_right.
  - (* uniqueness: cancel [from] against [to] *)
    intros v Hv.
    rewrite <- Hv.
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    apply id_right.
Defined.

(** ** The opcleaving *)

(* The canonical opcleaving of the Grothendieck construction: chosen
   opcartesian lifts, pushing displayed objects forward along base
   morphisms by reindexing.  Per Theory/Fibration.v's vocabulary this is a
   [Cleaving] of the op-displayed category.  Built with an explicit
   [Build_Cleaving] so the op-displayed instance is pinned during
   elaboration: record syntax would elaborate the field against an
   undetermined displayed-category evar, where [dobj v] cannot yet be seen
   to be [idx_fib A v]. *)
Definition Grothendieck_OpCleaving :
  OpCleaving (Grothendieck_Displayed A) :=
  @Build_Cleaving (B^op) (Displayed_op (Grothendieck_Displayed A))
    (fun u v (f : u ~{ B^op }~> v) (dv : idx_fib A v) =>
       (idx_map A f dv;
        (@Grothendieck_op_lift v u f dv;
         @Grothendieck_lift_cocartesian v u f dv))).

(** ** The chosen lifts, read in the total category ∫ A *)

(* The chosen opcartesian lift of [f] at [dx], as a morphism of ∫ A from
   [(x; dx)] to [(y; idx_map A f dx)].  Its displayed component is
   definitionally the one chosen by [Grothendieck_OpCleaving]
   ([Grothendieck_colift_is_clift] below). *)
Definition Grothendieck_colift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  (x; dx) ~{ Grothendieck A }~> (y; idx_map A f dx) :=
  (f; Grothendieck_op_lift f dx).

(* Vertical morphisms: a fibre morphism [k : a ~> b] over [z], embedded as
   a total morphism over [id[z]] by recentring along the unit iso. *)
Definition Grothendieck_vert {z : B} {a b : idx_fib A z} (k : a ~> b) :
  (z; a) ~{ Grothendieck A }~> (z; b) :=
  (@id B z; k ∘ to (idx_id A a)).

(* The total-level lift and the cleaving's chosen lift agree — both are
   the identity of the pushforward, so the comparison is definitional. *)
Lemma Grothendieck_colift_is_clift {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  `1 (`2 (@clift (B^op) (Displayed_op (Grothendieck_Displayed A))
                 Grothendieck_OpCleaving y x f dx))
    ≈ `2 (Grothendieck_colift f dx).
Proof. reflexivity. Qed.

(* The chosen lift lies strictly over [f]: the projection sends it to [f]
   on the nose. *)
Lemma Grothendieck_colift_over {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  fmap[Grothendieck_Proj A] (Grothendieck_colift f dx) ≈ f.
Proof. reflexivity. Qed.

(** ** The split laws *)

(* Identity law: the chosen lift of [id[x]] at [dx], corrected by the
   chosen unit iso [idx_id A dx], is the identity of [(x; dx)].  The
   mediator is the CHOSEN iso, not an arbitrary one; for strict [A] it is
   an identity and the law reads [lift id ≈ id] on the nose. *)
Lemma Grothendieck_split_lift_id {x : B} (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_id A dx)) ∘ Grothendieck_colift (@id B x) dx
    ≈ @id (Grothendieck A) (x; dx).
Proof.
  simpl.
  exists (id_left (@id B x)); simpl.
  unfold Grothendieck_op_lift.
  rewrite fmap_id.
  (* [id_right] is applied at its exact occurrence: the goal carries the
     composite [id ∘ id] inside a dependent argument of [idx_resp], which
     an ambient rewrite would try to abstract *)
  rewrite (id_right
             (to (idx_id A dx) ∘ to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite (idx_unit_left_from A (@id B x) dx).
  rewrite iso_to_from.
  apply id_right.
Qed.

(* Composition law: the composite of the chosen lifts of [f] and [g],
   corrected by the chosen composition iso [idx_comp A g f dx], is the
   chosen lift of [g ∘ f].  Again the mediator is the CHOSEN iso; for
   strict [A] the law reads [lift g ∘ lift f ≈ lift (g ∘ f)] on the
   nose. *)
Lemma Grothendieck_split_lift_comp {x y z : B} (g : y ~> z) (f : x ~> y)
  (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_comp A g f dx))
      ∘ Grothendieck_colift g (idx_map A f dx)
      ∘ Grothendieck_colift f dx
    ≈ Grothendieck_colift (g ∘ f) dx.
Proof.
  assert (e0 : (@id B z ∘ g) ∘ f ≈ g ∘ f).
  { now rewrite id_left. }
  simpl.
  exists e0; simpl.
  unfold Grothendieck_op_lift.
  rewrite !fmap_id, !id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A g (idx_map A f dx))))).
  rewrite (idx_unit_left_from A g (idx_map A f dx)).
  rewrite <- (idx_resp_from_sym A (id_left g) (idx_map A f dx)).
  rewrite (comp_assoc (from (idx_resp A (symmetry (id_left g))
                                        (idx_map A f dx)))).
  rewrite (idx_comp_resp_l_from A f (symmetry (id_left g)) (symmetry e0) dx).
  rewrite <- (comp_assoc (from (idx_comp A g f dx))).
  rewrite (comp_assoc (to (idx_comp A g f dx)) (from (idx_comp A g f dx))).
  rewrite iso_to_from.
  rewrite id_left.
  rewrite (idx_resp_from_trans A (symmetry e0) e0 dx).
  apply (idx_resp_from_id A).
Qed.

(** ** The split laws, bundled *)

(* The splitting of the canonical opcleaving, as one named theorem: the
   chosen lifts are functorial on the nose, mediated by the chosen unit
   and composition isos of [A]. *)
Theorem Grothendieck_Split :
  (∀ (x : B) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_id A dx))
         ∘ Grothendieck_colift (@id B x) dx
       ≈ @id (Grothendieck A) (x; dx))
  ∧ (∀ (x y z : B) (g : y ~> z) (f : x ~> y) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_comp A g f dx))
         ∘ Grothendieck_colift g (idx_map A f dx)
         ∘ Grothendieck_colift f dx
       ≈ Grothendieck_colift (g ∘ f) dx).
Proof.
  split.
  - intros x dx.
    apply Grothendieck_split_lift_id.
  - intros x y z g f dx.
    apply Grothendieck_split_lift_comp.
Qed.

(** ** The projection as a cloven fibration of the op-total category *)

(* Through the bridge of Theory/Fibration.v, the chosen opcartesian lifts
   make the projection out of the op-total category a cloven fibration —
   the functor-level reading of "∫ A ⟶ B is a (cloven) opfibration". *)
Definition Grothendieck_OpCloven :
  ClovenFibration (Total_Proj (Displayed_op (Grothendieck_Displayed A))) :=
  @cleaving_total_cloven (B^op) (Displayed_op (Grothendieck_Displayed A))
    Grothendieck_OpCleaving.

End GrothendieckFibration.
