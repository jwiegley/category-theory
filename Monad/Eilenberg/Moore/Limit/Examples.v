Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Eilenberg.Moore.Limit.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * A hypothesis-free instantiation of created limits *)

(* Monad/Eilenberg/Moore/Limit.v proves that [EM_Forget T] strictly creates
   every limit for every monad T on every category.  That is a conditional
   statement about an arbitrary monad; this file discharges every
   hypothesis at once, over objects the library already builds: the
   identity monad on [Coq] (Monad/Strong.v), the empty diagram
   ([From_0], Instance/Zero.v), and the terminal object of [Coq]
   downstairs (Instance/Coq.v).  What comes out is the created terminal
   algebra, and its carrier is the apex of the limit downstairs by
   [eq_refl] — creation on the nose.  (Nothing here reduces: the equality
   holds by projection, not by evaluation, for the reason in the next
   paragraph.)

   Two small points of usage.  [Terminal_Limit]
   (Structure/Limit/Terminal.v:33) is an [↔], which in this library is
   [iffT] (Lib/Foundation.v), so its halves are taken with [fst] and [snd]
   rather than [proj1]/[proj2].  And it is [Qed]-opaque, so the strictness
   equality below is stated against [vertex_obj[Lbelow]] — the apex of the
   limit actually produced — rather than against [unit]. *)

Definition IdC : Coq ⟶ Coq := Id[Coq].

Definition Kempty : 0 ⟶ @EilenbergMoore Coq IdC (@Id_Monad Coq) :=
  From_0 _.

(* The terminal object of [Coq], read as the limit of the empty diagram. *)

Definition Lbelow : Limit (EM_Forget IdC ◯ Kempty) :=
  snd (Terminal_Limit Coq (EM_Forget IdC ◯ Kempty)) Coq_Terminal.

(* The created lift, and the fact that it is limiting. *)

Definition created_terminal_algebra :
  IsALimit Kempty (em_apex IdC Kempty Lbelow) :=
  em_created IdC Kempty Lbelow.

(* The carrier of the created algebra is the apex of the limit downstairs,
   definitionally: [EM_Forget]'s object map is the first projection. *)

Definition created_carrier :
  `1 (em_apex IdC Kempty Lbelow) = vertex_obj[Lbelow] := eq_refl.

(* Terminality upstairs, read back through the empty-diagram theorem. *)

Definition created_terminal :
  @Terminal (@EilenbergMoore Coq IdC (@Id_Monad Coq)) :=
  fst (Terminal_Limit _ Kempty)
    {| limit_cone := em_cone IdC Kempty Lbelow
     ; ump_limits := @ump_limit _ _ _ _ (em_created IdC Kempty Lbelow) |}.
