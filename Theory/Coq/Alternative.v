
Reserved Notation "f <|> g" (at level 29, left associativity).

Class Alternative (F : Type → Type) :=
{ alt_is_applicative :> Applicative F

; empty : forall {X}, F X
; choose : forall {X}, F X → F X → F X
    where "f <|> g" := (choose f g)
(* ; some : forall {X}, F X → list (F X) *)
(* ; many : forall {X}, F X → list (F X) *)
}.

Notation "f <|> g" := (choose f g) (at level 29, left associativity).

(* Module Import LN := ListNotations. *)

(* #[export] *)
(* Program Instance list_Alternative : Alternative list := { *)
(*     empty := fun _ => []; *)
(*     choose := app *)
(* }. *)

#[export]
Instance Compose_Alternative
  `{Alternative F} `{Alternative G} : Alternative (F \o G) :=
{ empty  := fun A => @empty F _ (G A)
; choose := fun A => @choose F _ (G A) (* jww (2016-01-28): correct? *)
}.
