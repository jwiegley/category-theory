Require Coq.Vectors.Vector.
Import Vectors.VectorDef.VectorNotations.

Set Implicit Arguments.

Definition Vector_caseS'
           {A'} (Q : nat -> Type)
           (P : forall {n} (v : Vector.t A' (S n)), Q n -> Type)
           (H : forall h {n} t q, @P n (h :: t) q) {n} (v: Vector.t A' (S n))
           (q : Q n)
: P v q.
Proof.
  specialize (fun h t => H h _ t q).
  change n with (pred (S n)) in H, q |- *.
  set (Sn := S n) in *.
  pose (fun Sn (v : Vector.t A' Sn) (q : Q (pred Sn)) =>
          match Sn return Vector.t A' Sn -> Q (pred Sn) -> Type with
            | S n' => P n'
            | 0 => fun _ _ => True
          end v q) as P'.
  change (match Sn return Type with
            | 0 => True
            | _ => P' Sn v q
          end).
  change (forall h (t : match Sn with
                          | S n' => Vector.t A' n'
                          | 0 => Vector.t A' Sn
                        end),
            P' Sn (match Sn return match Sn with
                                     | S n' => Vector.t A' n'
                                     | 0 => Vector.t A' Sn
                                   end -> Vector.t A' Sn
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
