Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * Closed sets, and the complementation duality *)

(* Book:      Riehl, "Category Theory in Context", Example 1.3.14(iv) and
              Example 1.4.4(v)
   nLab:      https://ncatlab.org/nlab/show/closed+subset
   nLab:      https://ncatlab.org/nlab/show/frame
   Wikipedia: https://en.wikipedia.org/wiki/Closed_set

   Riehl's Example 1.3.14(iv) reads the poset of open subsets of a space as
   a category — a thin category, one arrow `U ~> V` exactly when `U ⊆ V` —
   and Example 1.4.4(v) observes that complementation is an isomorphism
   between that category and the OPPOSITE of the poset of closed subsets:
   taking complements reverses inclusions.  This file supplies both, plus
   the functorial form: the opens of a space are contravariantly functorial
   in the space (preimage), the closed sets likewise, and complementation
   is a natural isomorphism between the two presheaves on [Top].

      Opens X          thin category of the opens of X, ordered by ⊆
      Closeds X        thin category of the closed sets of X
      Opens X ≅ (Closeds X)^op            complementation, objectwise
      OpensF, ClosedsF : Top^op ⟶ Sets    preimage presheaves
      OpensF ≅ ClosedsF                   complementation, naturally *)

(* Design: closed sets constructively, and why the order is what it is

   nLab: https://ncatlab.org/nlab/show/excluded+middle
   nLab: https://ncatlab.org/nlab/show/double+negation

   Two decisions here need stating plainly, because in both cases the
   classical formulation would silently import excluded middle.

   1. A CLOSED SET CARRIES ITS COMPLEMENTING OPEN AS DATA.  Classically one
      says "C is closed when its complement is open", and extracts the open
      from the existential when needed.  Constructively that extraction is
      an appeal to choice (from `∃ U, IsOpen U ∧ ...` one cannot in general
      produce `U`), so [ClosedSet] below bundles the complementing open as
      a field, with [closed_agree] recording that the closed predicate IS
      the negation of that open.  The record is therefore not "a predicate
      that happens to be closed" but "a predicate together with a witness
      of its closedness" — the same move the library makes wherever a
      classical existential would otherwise need choice, as with the chosen
      pullbacks of Theory/Subobject/Functor.v or the chosen lifts of
      Theory/Fibration.v's [Cleaving].

   2. THE ORDER IS REVERSE INCLUSION OF THE COMPLEMENTING OPENS, AND THE
      SETOID IS THEIR MUTUAL INCLUSION.  Complementation turns inclusion of
      opens into inclusion of closed predicates constructively: from
      `U ⊆ U'` one gets `¬U' ⊆ ¬U` by composition.  The converse does NOT
      hold — recovering `U ⊆ U'` from `¬U' ⊆ ¬U` needs `¬¬`-stability, i.e.
      excluded middle — so ordering closed sets by inclusion of their
      closed predicates would break the duality in one direction.  Ordering
      them by reverse inclusion of the complementing opens keeps the
      duality exact, implies inclusion of the closed predicates (lemma
      [closed_order_implies_inclusion]), and agrees with it classically.

      The same reasoning fixes the setoid: two closed sets are identified
      when their complementing OPENS agree pointwise.  That implies their
      closed predicates agree ([closed_equiv_implies_pred_equiv]) but is
      not implied by it, for the same `¬¬` reason.  Comparing the closed
      predicates instead would make [closed_interior] — "read off the
      complementing open" — not respect `≈`, and the natural isomorphism
      at the end of this file would have no inverse.  Riehl's statement is
      classical; what is proved below is its constructive rendering, and
      this paragraph is the disclosure of the difference.

      The disclosure has a CONSEQUENCE that must be stated just as
      plainly (the audit of the first commit insisted, correctly): with
      this setoid, [ClosedSets X] is [OpenSets X] carrying an extra field
      the equivalence never inspects, both round trips of the duality
      copy the compared component verbatim, and the natural isomorphism
      at the end of the file is, extensionally, the identity dressed as
      complementation.  The constructive CONTENT of the duality therefore
      lives in the one-directional lemmas
      ([closed_order_implies_inclusion], [closed_equiv_implies_pred_equiv])
      and in the closing section, which prices the classical reading
      exactly: a predicate-comparing setoid is EQUIVALENT to
      double-negation elimination ([pred_comparison_forces_DNE]), and
      under that explicit hypothesis the two-sided classical
      correspondence is recovered
      ([closed_inclusion_implies_order_classical],
      [closed_pred_equiv_implies_equiv_classical]). *)

(** ** Opens and closed sets of a space *)

(* An open of X, as an object: the predicate together with its openness. *)
Definition OpenSet (X : TopSpace) : Type := { U : X → Type & IsOpen X U }.

(* A closed set of X: the closed predicate, its complementing open (as
   data, per design note 1), and the agreement between the two. *)
Record ClosedSet (X : TopSpace) := {
  closed_pred : X → Type;                       (* the closed predicate *)
  closed_compl : X → Type;                      (* its complementing open *)
  closed_compl_open : IsOpen X closed_compl;    (* which is indeed open *)

  (* the closed predicate is the negation of the complementing open *)
  closed_agree : ∀ x : X, closed_pred x ↔ ¬ (closed_compl x)
}.

Arguments closed_pred {X} _ _.
Arguments closed_compl {X} _ _.
Arguments closed_compl_open {X} _.
Arguments closed_agree {X} _ _.

(* Complementation, object by object.  An open becomes the closed set whose
   predicate is its negation and whose complementing open is the open
   itself; the agreement field is then the identity equivalence. *)
Definition open_complement {X : TopSpace} (U : OpenSet X) : ClosedSet X := {|
  closed_pred       := fun x => ¬ (`1 U x);
  closed_compl      := `1 U;
  closed_compl_open := `2 U;
  closed_agree      := fun x => (fun h => h, fun h => h)
|}.

(* ... and back: a closed set already carries its complementing open. *)
Definition closed_interior {X : TopSpace} (C : ClosedSet X) : OpenSet X :=
  (closed_compl C; closed_compl_open C).

(* The chosen order on closed sets implies inclusion of the closed
   predicates — the direction that survives without excluded middle. *)
Lemma closed_order_implies_inclusion {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl D x → closed_compl C x) →
  ∀ x : X, closed_pred C x → closed_pred D x.
Proof.
  intros Hincl x Hc.
  exact (snd (closed_agree D x) (fun hd => fst (closed_agree C x) Hc (Hincl x hd))).
Qed.

(* Likewise for the setoid: agreement of complementing opens implies
   agreement of the closed predicates. *)
Lemma closed_equiv_implies_pred_equiv {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl C x ↔ closed_compl D x) →
  ∀ x : X, closed_pred C x ↔ closed_pred D x.
Proof.
  intros Heq x; split.
  - exact (closed_order_implies_inclusion C D (fun y h => snd (Heq y) h) x).
  - exact (closed_order_implies_inclusion D C (fun y h => fst (Heq y) h) x).
Qed.

(** ** The two thin categories *)

(* The opens of X as a thin category: objects the opens, a unique arrow
   `U ~> V` when `U ⊆ V`.  As in Instance/Proset.v the hom-setoid is
   trivial, since any two parallel arrows are the same arrow. *)
Program Definition Opens (X : TopSpace) : Category := {|
  obj     := OpenSet X;
  hom     := fun U V => ∀ x : X, `1 U x → `1 V x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun U x u => u;
  compose := fun U V W g f x u => g x (f x u)
|}.

(* The closed sets of X as a thin category, ordered by REVERSE inclusion of
   the complementing opens (design note 2).  By
   [closed_order_implies_inclusion] an arrow `C ~> D` does entail
   `C ⊆ D` on the closed predicates. *)
Program Definition Closeds (X : TopSpace) : Category := {|
  obj     := ClosedSet X;
  hom     := fun C D => ∀ x : X, closed_compl D x → closed_compl C x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun C x u => u;
  compose := fun C D E g f x u => f x (g x u)
|}.

(** ** Complementation as an isomorphism of categories *)

(* Forward: an open goes to its complement.  An inclusion `U ⊆ V` is
   literally the arrow required in `(Closeds X)^op`, namely the inclusion
   of the complementing opens. *)
Program Definition OpenCompl (X : TopSpace) : Opens X ⟶ (Closeds X)^op := {|
  fobj := fun U => open_complement U;
  fmap := fun U V g => g
|}.

(* Backward: a closed set goes to its complementing open. *)
Program Definition ClosedCompl (X : TopSpace) : (Closeds X)^op ⟶ Opens X := {|
  fobj := fun C => closed_interior C;
  fmap := fun C D g => g
|}.

(* Riehl, CTiC Example 1.4.4(v), constructively: the opens of X and the
   opposite of its closed sets are isomorphic categories.  Both round trips
   are the identity on the complementing opens, which is exactly what the
   chosen order compares — note that the closed predicate of a
   round-tripped closed set is the negation of its complementing open,
   equivalent to the original predicate by [closed_agree] but not literally
   it.  Both naturality conditions hold trivially, the categories being
   thin. *)
Program Definition Opens_Closeds_iso (X : TopSpace) :
  Opens X ≅[Cat] (Closeds X)^op := {|
  to   := OpenCompl X;
  from := ClosedCompl X
|}.
Next Obligation.
  unshelve eexists.
  - intro C; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.
Next Obligation.
  unshelve eexists.
  - intro U; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.

(** ** The two presheaves on Top *)

(* Preimage of an open along a continuous map is open — that IS continuity,
   and it is what makes the opens contravariantly functorial. *)
Definition open_preimage {X Y : TopSpace} (g : Y ~{Top}~> X) (U : OpenSet X) :
  OpenSet Y :=
  (fun y => `1 U (g y); continuity g (`1 U) (`2 U)).

(* Preimage of a closed set: both components are pulled back, the
   complementing open stays open by continuity, and the agreement field
   transports pointwise. *)
Definition closed_preimage {X Y : TopSpace} (g : Y ~{Top}~> X)
           (C : ClosedSet X) : ClosedSet Y := {|
  closed_pred       := fun y => closed_pred C (g y);
  closed_compl      := fun y => closed_compl C (g y);
  closed_compl_open := continuity g (closed_compl C) (closed_compl_open C);
  closed_agree      := fun y => closed_agree C (g y)
|}.

(* The setoid of opens of X, as an object of [Sets]: two opens are
   identified when their predicates agree pointwise (up to the library's
   Type-valued `↔`). *)
Definition OpenSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := OpenSet X
          ; is_setoid := {| equiv := fun U V => ∀ x : X, `1 U x ↔ `1 V x |} |}.
  constructor.
  - intros U x; split; exact (fun h => h).
  - intros U V H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros U V W H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(* The setoid of closed sets of X, compared through their complementing
   opens (design note 2). *)
Definition ClosedSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := ClosedSet X
          ; is_setoid := {| equiv := fun C D => ∀ x : X,
                              closed_compl C x ↔ closed_compl D x |} |}.
  constructor.
  - intros C x; split; exact (fun h => h).
  - intros C D H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros C D E H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(* From here on the obligations are discharged explicitly rather than by the
   library's default [cat_simpl], because every one of them is a pointwise
   equivalence of predicates and the automation has no reason to prefer one
   direction of an [iffT] to the other. *)
Local Obligation Tactic := idtac.

(* The presheaf of opens: contravariant on [Top], acting by preimage. *)
Program Definition OpensF : Top^op ⟶ Sets := {|
  fobj := fun X => OpenSets X;
  fmap := fun X Y f => {| morphism := open_preimage (unop f) |}
|}.
Next Obligation.
  (* the preimage map respects `≈` of opens *)
  intros X Y f U V H y; exact (H (unop f y)).
Qed.
Next Obligation.
  (* fmap respects `≈` of morphisms: equivalent maps have, pointwise,
     equivalent preimages, because an open respects the carrier's `≈` *)
  intros X Y f g Hfg U y; split.
  - exact (open_proper X (`1 U) (`2 U) (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (`1 U) (`2 U) (unop g y) (unop f y)
             (symmetry (Hfg y))).
Qed.
Next Obligation.
  (* the preimage along the identity is the identity *)
  intros X U y; split; exact (fun h => h).
Qed.
Next Obligation.
  (* preimages compose contravariantly, definitionally *)
  intros X Y Z f g U y; split; exact (fun h => h).
Qed.

(* The presheaf of closed sets, likewise.  Everything happens on the
   complementing open, which is exactly the component the setoid compares. *)
Program Definition ClosedsF : Top^op ⟶ Sets := {|
  fobj := fun X => ClosedSets X;
  fmap := fun X Y f => {| morphism := closed_preimage (unop f) |}
|}.
Next Obligation.
  intros X Y f C D H y; exact (H (unop f y)).
Qed.
Next Obligation.
  intros X Y f g Hfg C y; split.
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop g y) (unop f y) (symmetry (Hfg y))).
Qed.
Next Obligation.
  intros X C y; split; exact (fun h => h).
Qed.
Next Obligation.
  intros X Y Z f g C y; split; exact (fun h => h).
Qed.

(** ** Complementation is natural *)

(* The two components, at each space.  Complementation respects `≈`
   because the setoid on closed sets compares exactly the complementing
   open, which the forward map copies verbatim; the inverse respects `≈`
   for the same reason, and this is where design note 2 is cashed in — with
   the closed predicates as the setoid there would be no inverse. *)
Program Definition complement_at (X : TopSpace) :
  OpenSets X ~{Sets}~> ClosedSets X := {|
  morphism := @open_complement X
|}.
Next Obligation. intros X U V H x; exact (H x). Qed.

Program Definition interior_at (X : TopSpace) :
  ClosedSets X ~{Sets}~> OpenSets X := {|
  morphism := @closed_interior X
|}.
Next Obligation. intros X C D H x; exact (H x). Qed.

(* Naturality is the statement that the preimage of a complement is the
   complement of the preimage — which here holds definitionally, both
   sides carrying the complementing open `fun y => U (g y)`. *)
Program Definition complement_transform : OpensF ⟹ ClosedsF := {|
  transform := complement_at
|}.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.

Program Definition interior_transform : ClosedsF ⟹ OpensF := {|
  transform := interior_at
|}.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.

(* The natural isomorphism `OpensF ≅ ClosedsF` in `[Top^op, Sets]`: Riehl's
   Example 1.4.4(v) in its functorial form.  Both round trips are the
   identity pointwise — one because [closed_interior] just reads off the
   complementing open that [open_complement] stored, the other because a
   closed set is determined, for the chosen setoid, by that same open. *)
Program Definition complement_natural : OpensF ≅[Fun] ClosedsF := {|
  to   := complement_transform;
  from := interior_transform
|}.
Next Obligation. intros X C y; split; exact (fun h => h). Qed.
Next Obligation. intros X U y; split; exact (fun h => h). Qed.

(* ------------------------------------------------------------------------ *)
(** ** The exact price of the classical reading *)

(* Design note 2 chose to compare closed sets through their complementing
   opens and disclosed what that choice buys and what it costs.  This
   closing section (its first theorem supplied by the audit of the first
   commit) makes the cost precise rather than rhetorical.

   If agreement of the closed PREDICATES implied agreement of the
   complementing opens — the respectfulness a predicate-comparing setoid
   would need — then double negation would be eliminable at every Type.
   The probe is the one-point space with the constant predicates `P` and
   `¬¬P`: their negations are equivalent outright, so the hypothetical
   implication hands back `P ↔ ¬¬P` at the point. *)
Theorem pred_comparison_forces_DNE :
  (∀ (X : TopSpace) (C D : ClosedSet X),
      (∀ x : X, closed_pred C x ↔ closed_pred D x) →
      (∀ x : X, closed_compl C x ↔ closed_compl D x)) →
  ∀ P : Type, ¬ ¬ P → P.
Proof.
  intros Hconv P.
  pose (CP := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => P); open_const Point_Top P)).
  pose (CN := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => (¬ ¬ P : Type));
                 open_const Point_Top (¬ ¬ P : Type))).
  assert (Hpred : ∀ x : Point_Top, closed_pred CP x ↔ closed_pred CN x).
  { intro x; split.
    - intros np nnp; exact (nnp np).
    - intros nnnp p; exact (nnnp (fun np => np p)). }
  exact (snd (Hconv Point_Top CP CN Hpred ttt)).
Qed.

(* Under double-negation elimination as an EXPLICIT HYPOTHESIS — taken as a
   hypothesis and never as an axiom, the same discipline the library
   applies to UIP and to choice — the two constructively one-directional
   implications become equivalences, and Riehl's classical statement is
   recovered in full. *)
Section Classical.

Hypothesis DNE : ∀ P : Type, ¬ ¬ P → P.

Lemma closed_inclusion_implies_order_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x → closed_pred D x) →
  (∀ x : X, closed_compl D x → closed_compl C x).
Proof using DNE.
  intros Hincl x Hd.
  apply (DNE (closed_compl C x)).
  intro Hnc.
  exact (fst (closed_agree D x) (Hincl x (snd (closed_agree C x) Hnc)) Hd).
Qed.

Lemma closed_pred_equiv_implies_equiv_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x ↔ closed_pred D x) →
  (∀ x : X, closed_compl C x ↔ closed_compl D x).
Proof using DNE.
  intros H x; split.
  - intro Hc; exact (closed_inclusion_implies_order_classical D C
                       (fun y => snd (H y)) x Hc).
  - intro Hd; exact (closed_inclusion_implies_order_classical C D
                       (fun y => fst (H y)) x Hd).
Qed.

End Classical.
