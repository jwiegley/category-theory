Require Import Coq.Unicode.Utf8.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(** This code is borrowed from the Fiat code base. *)

Section ilist.

Import VectorNotations.

Open Scope vector_scope.
Open Scope nat_scope.

Definition Vector_caseS'
           {A'} (Q : nat → Type)
           (P : ∀ {n} (v : Vector.t A' (S n)), Q n → Type)
           (H : ∀ h {n} t q, @P n (h :: t) q) {n} (v: Vector.t A' (S n))
           (q : Q n) : P v q.
Proof.
  specialize (fun h t => H h _ t q).
  change n with (pred (S n)) in H, q |- *.
  set (Sn := S n) in *.
  pose (fun Sn (v : Vector.t A' Sn) (q : Q (pred Sn)) =>
          match Sn return Vector.t A' Sn → Q (pred Sn) → Type with
            | S n' => P n'
            | 0 => fun _ _ => True
          end v q) as P'.
  change (match Sn return Type with
            | 0 => True
            | _ => P' Sn v q
          end).
  change (∀ h (t : match Sn with
                          | S n' => Vector.t A' n'
                          | 0 => Vector.t A' Sn
                        end),
            P' Sn (match Sn return match Sn with
                                     | S n' => Vector.t A' n'
                                     | 0 => Vector.t A' Sn
                                   end → Vector.t A' Sn
                   with
                     | S _ => fun t => h :: t
                     | 0 => fun t => t
                   end t) q) in H.
  clearbody P'; clear P.
  clearbody Sn.
  destruct v as [|h ? t].
  { constructor. }
  { apply H. }
Defined.

Context {A : Type}. (* The indexing type. *)
Context {B : A → Type}. (* The type of indexed elements. *)

Record prim_prod A B : Type :=
  { prim_fst : A;
    prim_snd : B }.

Arguments prim_fst {A B} _.
Arguments prim_snd {A B} _.

Fixpoint ilist {n} (l : Vector.t A n) : Type :=
  match l with
    | [] => unit
    | a :: l => @prim_prod (B a) (ilist l)
  end.

Definition vec_of `(x : @ilist n l) := l.

Definition icons
           (a : A)
           {n}
           {l : Vector.t A n}
           (b : B a)
           (il : ilist l) : ilist (a :: l) :=
  {| prim_fst := b; prim_snd := il |}.

Definition inil : ilist [] := tt.

(* Get the car of an ilist. *)
Definition ilist_hd {n} {As : Vector.t A n} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => B a
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => B a
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => prim_fst il
    | [] => fun il => tt
  end il.

(* Get the cdr of an ilist. *)
Definition ilist_tl {n} {As : Vector.t A n} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => ilist As'
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => ilist As'
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => prim_snd il
    | [] => fun il => tt
  end il.

Fixpoint ith {m : nat}
         {As : Vector.t A m}
         (il : ilist As)
         (n : Fin.t m) : B (Vector.nth As n) :=
  match n in Fin.t m return
        ∀ (As : Vector.t A m),
          ilist As
          → B (Vector.nth As n) with
    | @Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist As
                                  → B (Vector.nth As (@Fin.F1 n)))
                     (fun h n t => ilist_hd) As
    | @Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' => ilist As
                                      → B (Vector.nth As (@Fin.FS n n')))
                      (fun h n t m il => ith (ilist_tl il) m)
                      As n'
  end As il.

End ilist.
