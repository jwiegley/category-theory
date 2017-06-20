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
  Context {cats : catI -> option Category}.
  (** TODO: This only captures unary functors *)
  Context {funcD : positive -> option { ij : catI * catI
                                     & match cats (fst ij) , cats (snd ij) with
                                       | Some d , Some c => @Functor d c
                                       | _ , _ => Empty_set
                                       end }}.
  Context {objGet : positive -> option { i : catI & match cats i with
                                                   | Some c => @obj c
                                                   | None => Empty_set
                                                   end }}.

  Fixpoint objD (e : obj_expr) (c : catI)
  : option match cats c with
           | None => Empty_set
           | Some c => obj[c]
           end.
  refine
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
            Some (match pf in _ = X return match cats X with
                                           | Some c => obj[c]
                                           | None => Empty_set
                                           end with
                  | eq_refl =>
                    match cats (fst ij) as X
                        , cats (snd ij) as Y
                          return match X with
                                 | Some d => match Y with
                                            | Some c2 => d ⟶ c2
                                            | None => Empty_set
                                            end
                                 | None => Empty_set
                                 end ->
                                 match X with
                                 | Some c2 => obj[c2]
                                 | None => Empty_set
                                 end -> match Y with
                                       | Some c2 => obj[c2]
                                       | None => _
                                       end
                    with
                    | Some _ , Some _ => fun F x => F x
                    | None , None => fun _ X => match X with end
                    | None , Some _ => fun _ X => match X with end
                    | Some _ , None => fun X _ => match X with end
                    end val eD
                  end)
          | _ => None
          end
        | right _ => None
        end
      | _ => None
      end
    end.
  Defined.


  Context {morGet : positive -> option { dc : catI * (obj_expr * obj_expr)
                                      & let '(C, (d,c)) := dc in
                                        match objD d C , objD c C with
                                        | Some d , Some c =>
                                          match cats C as X
                                                return match X with
                                                       | Some c => obj[c]
                                                       | None => Empty_set
                                                       end ->
                                                       match X with
                                                       | Some c => obj[c]
                                                       | None => Empty_set
                                                       end -> _
                                          with
                                          | Some C => fun d c =>
                                            d ~> c
                                          | None => fun z _ => match z with end
                                          end d c
                                        | _ , _ => Empty_set
                                        end}}.


  Fixpoint morD (me : mor_expr) (C : catI) (d c : obj_expr)
  : option (match objD d C , objD c C with
            | Some dO , Some cO =>
              match cats C as X
                    return match X with
                           | Some c => obj[c]
                           | None => Empty_set
                           end ->
                           match X with
                           | Some c => obj[c]
                           | None => Empty_set
                           end -> Type
              with
              | Some c => fun dO cO =>
                           @hom c dO cO
              | None => fun _ _ => Empty_set
              end dO cO
            | _ , _ => Empty_set
            end).
  refine
    match me with
    | MRef r => _
    | MIdentity o => _
    | MCompose g f => _
    | MFun f ts es => _
    end.