Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Theory.Adamek.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Corollaries of Adámek's initial-algebra theorem *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   Adámek's theorem (Theory/Adamek.v) builds the initial [F]-algebra as the
   colimit of the ω-chain

       0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

   ([Construction/Chain.v], [Chain F : Omega ⟶ C]).  The theorem [adamek]
   there consumes a [Colimit (Chain F)] together with the honest hypothesis
   [AdamekData F L] recording that [F A] carries a colimit of the shifted
   diagram [F ◯ Chain F] whose injections are exactly the image legs
   [fmap[F] (colimit_inj HL n)].

   This file records the standard packaging corollary: in a *cocomplete*
   category the colimit [Colimit (Chain F)] is available for free — it is the
   colimit that cocompleteness furnishes for the ω-shaped diagram [Chain F] —
   so one need only supply the [AdamekData] leg-agreement to obtain the initial
   [F]-algebra.  A worked instance of the endofunctor side is recorded as
   [NatF], the option endofunctor on COQ.

   Ledger 17 / outstanding: the discharge [PreservesColimit -> AdamekData] is
   not carried here either.  As explained in the header of Theory/Adamek.v, an
   abstract [PreservesColimit] witness only records that [F A] carries SOME
   colimit of [F ◯ Chain F]; two colimit cocones at the shared apex [F A]
   differ by a free apex-automorphism, so it does not expose the leg agreement
   [colimit_inj (F-image colimit) n ≈ fmap[F] (colimit_inj HL n)] that the
   initiality argument consumes.  That leg-agreement bridge therefore remains a
   fast-follow; the [AdamekData] interface is the load-bearing contract in the
   interim and is threaded unchanged through the cocomplete corollary below. *)

(* [Cocomplete C] (Structure/Complete.v) is [∀ D (G : D ⟶ C), Colimit G].
   Applying it to the ω-shape [Omega] and the diagram [Chain F] yields the
   colimit [Colimit (Chain F)] that [adamek] requires, with no further
   hypotheses.  We then feed that colimit together with the supplied
   [AdamekData] to [adamek].  The [Colimit] argument is threaded explicitly and
   identically into both the type of [D] and the body, so the [AdamekData]'s
   ambient colimit [L] and the one consumed by [adamek] are the very same
   term. *)
Corollary adamek_cocomplete
  {C : Category} `{@Initial C} (F : C ⟶ C)
  (CC : @Cocomplete C)
  (D : AdamekData F (CC _ (Chain F))) :
  @Initial (FAlg F).
Proof.
  exact (adamek F (CC _ (Chain F)) D).
Qed.

(* The option endofunctor [NatF X := option X = 1 + X] on COQ (Instance/Coq.v).
   It is the polynomial endofunctor whose initial algebra is the type [nat]:
   the structure map [1 + nat ~> nat] is [O]/[S] ([None ↦ O], [Some k ↦ S k]),
   and initiality is exactly primitive recursion on [nat].

   [NatF] is the [A := unit] specialisation of the list endofunctor
   [ListF A X := option (A × X)] (Instance/Coq/Lists.v) up to the isomorphism
   [unit × X ≅ X]; that file carries the fully worked initial-algebra proof for
   [ListF A] (with [list A] the carrier), so the analogous [nat] initiality for
   [NatF] is exactly the [A := unit] reading of it.  Only the functor [NatF]
   itself is formalized below; the initial-algebra theorem [nat ≅ μ NatF] is
   not stated in the tree — it is recorded here as the informal cross-reference
   to [ListF A], not as a proven result. *)

(* Keep obligation handling explicit and predictable (as in Instance/Coq/Lists.v):
   surface each functor law as its own obligation rather than letting the ambient
   [cat_simpl] discharge or reshape them. *)
#[local] Obligation Tactic := idtac.

Program Definition NatF : Coq ⟶ Coq := {|
  fobj := fun X => option X;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None   => None
            | Some x => Some (f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality of functions *)
  intros X Y f g Hfg o.
  destruct o as [x|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros X o.
  destruct o as [x|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros X Y Z f g o.
  destruct o as [x|]; reflexivity.
Qed.
