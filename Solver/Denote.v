Set Warnings "-notation-overridden".

Require Export Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

Corollary helper {f} :
  (let '(dom, cod) := tys[@f] in objs[@dom] ~> objs[@cod])
    -> objs[@(fst (tys[@f]))] ~> objs[@(snd (tys[@f]))].
Proof. destruct (tys[@f]); auto. Defined.

Fixpoint termD {dom cod} (t : Term tys dom cod) : objs[@dom] ~> objs[@cod] :=
  match t with
  | Ident => id
  | Morph f => helper (ith arrs f)
  | Comp f g => termD f ∘ termD g
  end.

(** Transform a 0-based [Fin.t] into a 1-based [positive]. *)
Fixpoint Fin_to_pos {n} (f : Fin.t n) : positive :=
  match f with
  | Fin.F1 => 1%positive
  | Fin.FS x => Pos.succ (Fin_to_pos x)
  end.

Definition Pos_to_fin {n} (p : positive) : option (Fin.t n).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; intros.
    destruct n.
      exact None.
    exact (Some Fin.F1).
  destruct n.
    exact None.
  destruct (IHp n).
    exact (Some (Fin.FS t)).
  exact None.
Defined.

Import EqNotations.

Program Fixpoint stermD_work dom (e : STerm) :
  option (∃  cod, objs[@dom] ~> objs[@cod]) :=
  match e with
  | SIdent => Some (dom; @id _ (objs[@dom]))
  | SMorph a =>
    match Pos_to_fin a with
    | Some f =>
      match Eq_eq_dec (fst (tys[@f])) dom with
      | left H =>
        Some (snd (tys[@f]);
              rew [fun x => objs[@x] ~> _] H in helper (ith arrs f))
      | _ => None
      end
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
  option (objs[@dom] ~> objs[@cod]) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod =>
      Some (rew [fun y => objs[@dom] ~> objs[@y]] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Program Fixpoint sexprD (e : SExpr) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some d, Some c =>
      match stermD d c f, stermD d c g with
      | Some f, Some g => f ≈ g
      | _, _ => False
      end
    | _, _ => False
    end
  | SAnd p q       => sexprD p ∧ sexprD q
  | SOr p q        => sexprD p + sexprD q
  | SImpl p q      => sexprD p -> sexprD q
  end.

End Denote.
