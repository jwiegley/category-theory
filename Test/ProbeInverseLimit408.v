Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.
Require Import Category.Instance.Sets.InverseLimit.

Generalizable All Variables.
Open Scope category_scope.

(** * Refutation probe for Instance/Sets/InverseLimit.v *)

(* Each refutation command below was verified by stripping its [Fail] in a
   copy of the WHOLE file and compiling that copy alone, then reading the
   error in full -- a preamble-plus-command scratch drops the enclosing
   [Section]'s [Context] and its local universe declarations and then
   refuses for a reason unrelated to the claim.  The four negatives are of
   THREE kinds, told apart by the error TEXT and not by label:

     CONVERSION  ends "cannot unify", no universe clause  (1, 2)
     TYPING      a plain has-type mismatch, neither of those  (3)
     FORMABILITY ends "universe inconsistency: Cannot enforce ..."  (4)

   Every constant a negative names is also named by a passing command
   outside every [Fail], so a rename breaks the probe rather than turning
   a guard vacuously green. *)

(** ** Instrument: a [Fail] that fails for a scope-free reason *)

Fail Check probe408_no_such_constant.

(** ** Guard block: every constant the negatives name, outside every Fail *)

Check @tower_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @tower_iso.
Check @Sets_tower_limit.
Check @Sets_tower_limit_iso_cone_limit.
Check @inverse_limit.
Check @Cochain.
Check @Chain.
Check @Omega.
Check @Diagonal.
Check @cochain_inverse_limit.
Check @stream_to_tower.
Check @StreamTower.
Check @tower_compat.
Check @tower_compat_all.
Check @tower_proj.

(** ** (1) CONVERSION: the two presentations are not one object *)

(* The tower object carries compatibility at the STEPS; [Sets_limit_obj]
   carries it at every arrow.  They are isomorphic ([tower_iso]) and not
   convertible. *)
Fail Definition neg_tower_is_limit_obj (F : Omega^op ⟶ Sets) :
  tower_obj F = Sets_limit_obj F := eq_refl.

(* The control: the isomorphism the file actually delivers. *)
Check (fun F : Omega^op ⟶ Sets => tower_iso F).

(** ** (2) CONVERSION: nor is the tower object the cone set *)

Fail Definition neg_tower_is_cone_apex (F : Omega^op ⟶ Sets) :
  tower_obj F = cone_apex F := eq_refl.

Check (fun F : Omega^op ⟶ Sets => Sets_tower_limit_iso_cone_limit F).

(** ** (3) TYPING: the shape is [Omega^op], and a covariant diagram is not one *)

(* A plain has-type mismatch: no [cannot unify], no universe clause. *)
Fail Definition neg_wrong_variance (X : obj[Sets]) : obj[Sets] :=
  inverse_limit (Diagonal Omega X).

(* The control: the OPPOSITE shape is what [inverse_limit] consumes, and
   it is exactly the constant tower of the library file's section (G). *)
Check (fun X : obj[Sets] => inverse_limit (Diagonal (Omega^op) X)).

(** ** (4) FORMABILITY: [Cochain]'s [Set] pin, and it is the donor's *)

Section CochainPin.

Universes co ch.
Constraint Set < ch.

(* [Cochain@{u u0}] is declared over [C : Category@{u0 Set Set}] -- hom AND
   proof pinned to the literal [Set] -- so it is refused at a [Sets] whose
   hom-and-proof level is declared strictly above [Set]. *)
Fail Definition neg_cochain_above_Set
  (G : Sets@{ch co} ⟶ Sets@{ch co}) : Omega^op ⟶ Sets@{ch co} := Cochain G.

(* Controls accepted at those very levels: the category itself, a functor
   both ways, [Omega], and -- the discriminating one -- [Chain], declared
   one line above [Cochain] in the same file and FREE of any [Set]. *)
Check Sets@{ch co}.
Check (Sets@{ch co} ⟶ Sets@{ch co}).
Check Omega@{ch co co}.
Check (fun (T : @Terminal (Opposite Sets@{ch co}))
           (G : Sets@{ch co} ⟶ Sets@{ch co}) => @Chain Sets@{ch co} T G).

End CochainPin.
