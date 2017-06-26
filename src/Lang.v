Require Import Coq.PArith.BinPos.

Require Import Cat.
Require Import Functor.

Definition catI : Set := positive.

Inductive obj_expr : Set :=
| ORef : positive -> obj_expr
| OFun : positive -> obj_expr -> obj_expr
.

Inductive mor_expr : Set :=
| MRef : positive -> mor_expr
| MIdentity : obj_expr -> mor_expr
| MCompose : mor_expr -> mor_expr -> mor_expr
| MFun : positive -> list obj_expr -> list mor_expr -> mor_expr
.

Section denote.

Context {cats : catI -> Category}.
(** TODO: This only captures unary functors *)
Context {funcD : positive -> option { ij : catI * catI & cats (fst ij) ⟶ cats (snd ij) } }.
Context {objGet : positive -> option { i : catI & @obj (cats i) } }.

Fixpoint objD (e : obj_expr) (c : catI) : option (obj[cats c]) :=
  match e with
  | ORef r =>
    match objGet r with
    | Some (existT _ ci val) =>
      match Pos.eq_dec ci c with
      | left pf => match pf with
                   | eq_refl => Some val
                   end
      | right _ => None
      end
    | _ => None
    end
  | OFun r e =>
    match funcD r with
    | Some (existT _ ij val) =>
      match Pos.eq_dec (snd ij) c with
      | left pf =>
        match objD e (fst ij) with
        | Some eD =>
          Some (match pf in _ = X return obj[cats X] with
                | eq_refl => val eD
                end)
        | _ => None
        end
      | right _ => None
      end
    | _ => None
    end
  end.

Context {morGet : positive -> option { dc : catI * (obj_expr * obj_expr)
                                    & let '(C, (d,c)) := dc in
                                      match objD d C, objD c C with
                                      | Some d , Some c => d ~> c
                                      | _ , _ => Empty_set
                                      end}}.


Program Fixpoint morD (me : mor_expr) (C : catI) (d c : obj_expr) :
  option (match objD d C, objD c C with
          | Some dO, Some cO => @hom (cats C) dO cO
          | _, _ => Empty_set
          end) :=
  match me with
  | MRef r => _
  | MIdentity o => _
  | MCompose g f => _
  | MFun f ts es => _
  end.
