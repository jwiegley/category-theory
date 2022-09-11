Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IListVec.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

Definition helper {f} :
  (let '(dom, cod) := tys[@f] in objD dom objs ~> objD cod objs)
    → objD (fst (tys[@f])) objs ~> objD (snd (tys[@f])) objs.
Proof. destruct (tys[@f]); auto. Defined.

Definition Pos_to_fin (n : nat) (p : positive) : Fin.t (S n) :=
  Pos.peano_rect (λ _, ∀ n, Fin.t (S n))
    (λ n,     Fin.F1)
    (λ _ H n, match n with
              | O => Fin.F1
              | S n' => Fin.FS (H n')
              end) p n.

Fixpoint sobjD {n} (x : SObj) : Obj n :=
  match x with
  | SOb x     => Ob (Pos_to_fin n x)
  | SPair x y => Pair (sobjD x) (sobjD y)
  end.

Import EqNotations.

Definition pos_obj (f : Fin.t (S num_arrs)) dom :
  option (∃ cod, objD dom objs ~> objD cod objs) :=
  match eq_dec (fst (tys[@f])) dom with
  | left H =>
      Some (snd (tys[@f]);
            rew [fun x => objD x objs ~> _] H in helper (ith arrs f))
  | _ => None
  end.

Fixpoint stermD_work dom (e : STerm) :
  option (∃ cod, objD dom objs ~> objD cod objs) :=
  match e with
  | SIdent => Some (dom; id)
  | SMorph a => pos_obj (Pos_to_fin num_arrs a) dom
  | SFork f g =>
    match stermD_work dom f with
    | Some (fcod; f) =>
      match stermD_work dom g with
      | Some (gcod; g) => Some (Pair fcod gcod; f △ g)
      | _ => None
      end
    | _ => None
    end
  | SExl =>
      match dom with
      | Pair x y => Some (x; exl)
      | _ => None
      end
  | SExr =>
      match dom with
      | Pair x y => Some (y; exr)
      | _ => None
      end
  | SComp f g =>
    match stermD_work dom g with
    | Some (mid; g) =>
      match stermD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition stermD dom cod (e : STerm) :
  option (objD dom objs ~> objD cod objs) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objD dom objs ~> objD y objs] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint sexprD (e : SExpr) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    let d := sobjD x in
    let c := sobjD y in
    match stermD d c f, stermD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | SAnd p q       => sexprD p ∧ sexprD q
  | SOr p q        => sexprD p + sexprD q
  | SImpl p q      => sexprD p → sexprD q
  end.

End Denote.

Module DenoteExamples.

Import VectorNotations.

Section DenoteExamples.

Context (C : Category).
Context `{H : @Cartesian C}.
Variables x y z w : C.
Variable f : z ~> w.
Variable g : y ~> z.
Variable h : x ~> y.
Variable i : x ~> z.

#[local] Instance sample_env : Env := {|
  cat := C;
  cart := H;
  num_objs := 4%nat;
  objs := [w; x; z; y; y];
  num_arrs := 4%nat;
  tys :=
    [(sobjD (SOb (Pos.succ (Pos.succ 1))), sobjD (SOb 1));
    (sobjD (SOb (Pos.succ 1)), sobjD (SOb (Pos.succ (Pos.succ 1))));
    (sobjD (SOb (Pos.succ 1)),
     sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1)))));
    (sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1)))),
     sobjD (SOb (Pos.succ (Pos.succ 1))));
    (sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1)))),
     sobjD (SOb (Pos.succ (Pos.succ 1))))];
  arrs :=
    icons (sobjD (SOb (Pos.succ (Pos.succ 1))), sobjD (SOb 1)) f
      (icons
         (sobjD (SOb (Pos.succ 1)),
          sobjD (SOb (Pos.succ (Pos.succ 1)))) i
         (icons
            (sobjD (SOb (Pos.succ 1)),
             sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1))))) h
            (icons
               (sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1)))),
                sobjD (SOb (Pos.succ (Pos.succ 1)))) g
               (icons
                  (sobjD (SOb (Pos.succ (Pos.succ (Pos.succ 1)))),
                   sobjD (SOb (Pos.succ (Pos.succ 1)))) g inil))))
|}.

Example stermD_SIdent_Some :
  stermD (sobjD (SOb 1%positive)) (sobjD (SOb 1%positive)) SIdent = Some id.
Proof. reflexivity. Qed.

Example stermD_SExl_Some :
  stermD (sobjD (SPair (SOb 1%positive) (SOb 2%positive)))
    (sobjD (SOb 1%positive)) SExl
    = Some exl.
Proof. reflexivity. Qed.

Example stermD_SExr_Some :
  stermD (sobjD (SPair (SOb 1%positive) (SOb 2%positive)))
    (sobjD (SOb 2%positive)) SExr
    = Some exr.
Proof. reflexivity. Qed.

Example stermD_SFork_Some :
  stermD
    (sobjD (SOb 2%positive))
    (sobjD (SPair (SOb 4%positive) (SOb 3%positive)))
    (SFork (SMorph 3%positive) (SMorph 2%positive))
    = Some (h △ i).
Proof. reflexivity. Qed.

End DenoteExamples.

End DenoteExamples.
