Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The category PROP of propositions *)

(* nLab: https://ncatlab.org/nlab/show/Heyting+algebra
   nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Heyting_algebra

   Objects are propositions (`Prop`) and a morphism P ~> Q is an implication,
   i.e. a proof of `P → Q` (`Basics.impl`). Since every hom-setoid is made
   trivial (`equiv f g := True`), this is a thin / posetal category: at most
   one arrow between any two objects, so P ~> Q is inhabited exactly when
   P entails Q. That makes Props the preorder of propositions ordered by
   implication.

   Equipped with the logical connectives below it is a bicartesian closed
   thin category — a Heyting prealgebra — modelling intuitionistic
   propositional logic:

       1 = True          (terminal,   Props_Terminal)
       0 = False         (initial,    Props_Initial)
       P × Q = P ∧ Q     (product,    Props_Cartesian)
       P + Q = P ∨ Q     (coproduct,  Props_Cocartesian)
       Q ^ P = P → Q     (exponent,   Props_Closed)

   The exponential is implication because cartesian closure is exactly the
   adjunction (R ∧ P) ⊢ Q  ↔  R ⊢ (P → Q), the deduction theorem. *)

Program Definition Props : Category := {|
  obj     := Prop;                         (* objects are propositions *)
  hom     := Basics.impl;                  (* P ~> Q is the implication P → Q *)
  (* The hom-setoid is trivial, so any two proofs P → Q are identified: Props
     is thin. (This needs no proof-irrelevance axiom; `equiv := True` does it
     definitionally, the same idiom as Proset.v and Roof.v.) *)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;                 (* identity implication P → P *)
  compose := fun _ _ _ g f x => g (f x)    (* transitivity of implication *)
|}.

(* Terminal object: True is the top proposition, with `I : True` giving the
   unique map P ~> True (every P implies True). *)
#[export]
Program Instance Props_Terminal : @Terminal Props := {
  terminal_obj := True;                    (* 1 = True *)
  one := fun _ _ => I                       (* ! : P → True *)
}.

(* Initial object: False is the bottom proposition; ex falso quodlibet gives
   the unique map False ~> P (False implies every P). *)
#[export]
Program Instance Props_Initial : @Initial Props := {
  terminal_obj := False;                   (* 0 = False (terminal in Props^op) *)
  one := fun _ _ => False_rect _ _          (* ¡ : False → P, by ex falso *)
}.

(* Product: conjunction. P ∧ Q is the meet, with proj1/proj2 the projections
   and conj the pairing of two implications. *)
#[export]
Program Instance Props_Cartesian : @Cartesian Props := {
  product_obj := and;                      (* P × Q = P ∧ Q *)
  fork := fun _ _ _ f g x => conj (f x) (g x);  (* ⟨f, g⟩ : R → P ∧ Q *)
  exl  := fun _ _ p => proj1 p;            (* first projection  P ∧ Q → P *)
  exr  := fun _ _ p => proj2 p             (* second projection P ∧ Q → Q *)
}.

(* Coproduct: disjunction. P ∨ Q is the join, with the injections or_introl/
   or_intror and case analysis providing the copairing. (product_obj names the
   coproduct here, since Cocartesian is Cartesian read in Props^op.) *)
#[export]
Program Instance Props_Cocartesian : @Cocartesian Props := {
  product_obj := or;                       (* P + Q = P ∨ Q *)
  fork := fun _ _ _ f g x =>               (* copairing [f, g] : P ∨ Q → R *)
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;        (* left injection  P → P ∨ Q *)
  exr  := fun _ _ p => or_intror p         (* right injection Q → P ∨ Q *)
}.

(* Exponential: implication. Q ^ P = P → Q, and exp_iso is the currying
   bijection Hom(R ∧ P, Q) ≅ Hom(R, P → Q) witnessing (- ∧ P) ⊣ (P → -). *)
#[export]
Program Instance Props_Closed : @Closed Props _ := {
  exponent_obj := Basics.impl;             (* Q ^ P = P → Q *)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
