Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Variety.

Generalizable All Variables.

(** * Comparing the group variety with the category of groups *)

(* Mac Lane §V.6, book p. 124; the comparison obligation raised by issue
   #440's QA correction, which asks for [GroupVariety ≅[Cat] Grp] now that
   #255 has landed [Grp].

   ** THE ISOMORPHISM IS NOT AVAILABLE, AND THE REASON IS STRUCTURAL

   [Grp]'s objects (Instance/Grp.v:184) carry an ARBITRARY [SetoidObject]:
   a type together with a chosen equivalence, with every law stated up to
   that `≈`.  [GroupVariety]'s objects carry a BARE TYPE, with every law a
   Leibniz [=], because that is what Instance/Comp.v's [OpAlgebra] and
   [EqSignature] are built on.  The functor below goes one way for nothing
   — a bare type is a setoid under [=] — and is fully faithful.  What
   is missing is essential surjectivity in the other direction: to hit a group
   whose `≈` is coarser than [=] one must quotient its carrier by `≈`, and
   this tree has no quotient of a setoid by its own equivalence that
   returns a TYPE.  (Construction/Quotient.v quotients a category's
   hom-setoids, not a carrier.)  So the isomorphism is neither proved nor
   refuted here; what IS refuted, at Test/ProbeVariety440.v's negative n4,
   is that the two categories are the same object.

   The honest discharge of the QA correction is therefore the strongest
   comparison that does hold, stated as such: [GroupVariety_to_Grp], full
   and faithful.  Full-and-faithful is exactly "an isomorphism onto a full
   subcategory", so the variety sits inside [Grp] as the full subcategory
   of groups whose equality is Leibniz.

   ** THIS WHOLE FILE CARRIES [functional_extensionality_dep]

   Not one constant here is closed under the global context, and the
   reason is inherited twice over.  [GroupVariety] mentions
   Instance/Comp.v:358's [GroupEq], which is [Defined] with the axiom; and
   the translation of an [AlgHom] into a [GrpHom] must turn
   [op_commute]'s argument-bundle equation into the pointwise statements
   [grp_map_unit] and [grp_map_mul], which is the same bundle rebuild that
   Instance/Variety.v's header describes.  Nothing here is gated;
   docs/AXIOMS.md records the file.

   This is also why the comparison lives in its own file: it keeps
   Instance/Grp.v's closure off Instance/Variety.v, and it keeps every
   axiom-carrying constant of this development in the two places
   docs/AXIOMS.md can point at. *)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Turning an algebra homomorphism into a group homomorphism

    Both lemmas are [op_commute] followed by a bundle rebuild, which is
    where the extensionality enters. *)

(* The three bundle-normalisation lemmas.  An argument bundle over a
   finite enumeration is pointwise determined by its values, but NOT
   convertible to the case split on them — a [match] on a variable does
   not reduce — so each of these is an extensionality step, and they are
   where this file's axiom actually enters.  Each is written in the shape
   Instance/Comp.v's own [one'], [mul'] and [inv'] use, so that the
   rewritten goal is convertible with the [Grp] statement. *)

Lemma nullary_bundle {A : Type} (k : UA.nullary → A) :
  k = (fun i => match i return A with end).
Proof. extensionality i; destruct i. Qed.

Lemma binary_bundle {A : Type} (k : UA.binary → A) :
  k = (fun i => match i return A with
                | UA.Fst => k UA.Fst
                | UA.Snd => k UA.Snd
                end).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma unary_bundle {A : Type} (k : UA.unary → A) : k = (fun _ => k UA.Only).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma alg_hom_one {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B) :
  UA.map f (UA.one' (G:=A)) = UA.one' (G:=B).
Proof.
  unfold UA.one'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i.
Qed.

Lemma alg_hom_mul {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B)
  (a b : UA.carrier A) :
  UA.map f (UA.mul' a b) = UA.mul' (UA.map f a) (UA.map f b).
Proof.
  unfold UA.mul'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i; reflexivity.
Qed.

(** ** The comparison functor *)

Section ToGrp.

(* The three group laws [Grp] asks for, read off the variety's own
   [equations] field at the corresponding equation name.  [assoc] arrives
   the other way round, hence the [symmetry]. *)

Program Definition GroupVariety_obj_to_Grp (x : GroupVariety) : GrpObject := {|
  grp_setoid := {| carrier   := UA.carrier (`1 x)
                 ; is_setoid := eq_Setoid (UA.carrier (`1 x)) |};
  grp_unit := UA.one' (G:=`1 x);
  grp_mul  := fun a b => UA.mul' a b;
  grp_inv  := fun a => UA.inv' a
|}.
(* [grp_mul_respects] is discharged by Lib.v's default [Obligation Tactic]
   — under [eq_Setoid] it is [Proper (eq ==> eq ==> eq)] — so the three
   obligations that remain are the three laws, in [GrpObject]'s order.
   Their binders are pre-bound: [x] is the algebra and [X] its
   satisfaction proof, the sigma having been destructed. *)
Next Obligation.
  symmetry.
  exact (X UA.assoc (fun i => match i with
                              | UA.One => a | UA.Two => b | UA.Three => c
                              end)).
Qed.
Next Obligation.
  exact (X UA.unit_left (fun _ => a)).
Qed.
Next Obligation.
  exact (X UA.inv_left (fun _ => a)).
Qed.

Program Definition GroupVariety_hom_to_Grp {x y : GroupVariety} (f : x ~> y) :
  GrpHom (GroupVariety_obj_to_Grp x) (GroupVariety_obj_to_Grp y) := {|
  grp_map := {| morphism := UA.map (`1 f) |}
|}.
(* Here too the binders are pre-bound and the sigma destructed, so [f] is
   the underlying [AlgHom] and not the pair. *)
Next Obligation.
  exact (alg_hom_one f).
Qed.
Next Obligation.
  exact (alg_hom_mul f a b).
Qed.

Program Definition GroupVariety_to_Grp : GroupVariety ⟶ Grp := {|
  fobj := GroupVariety_obj_to_Grp;
  fmap := fun _ _ f => GroupVariety_hom_to_Grp f
|}.

End ToGrp.

(** ** It is faithful, and full

    Faithful: both hom-setoids are pointwise Leibniz equality on the same
    carrier, so the hypothesis and the conclusion are the same statement.

    Full: a [GrpHom] between images preserves the unit and the
    multiplication pointwise, and that is enough to rebuild [op_commute]
    at each of the three operations — the arities are finite enumerations,
    so the bundle is rebuilt by case analysis (and one more use of
    extensionality). *)

Lemma GroupVariety_to_Grp_Faithful : Faithful GroupVariety_to_Grp.
Proof. construct; simpl in *; auto. Qed.

Program Definition GroupVariety_hom_from_Grp {x y : GroupVariety}
  (g : GroupVariety_obj_to_Grp x ~{Grp}~> GroupVariety_obj_to_Grp y) : x ~> y :=
  ({| UA.map := grp_map g |}; I).
Next Obligation.
  destruct o; simpl.
  - (* one: nullary.  Normalise both bundles to the empty match, after
       which the goal IS [grp_map_unit] by conversion. *)
    rewrite (nullary_bundle (fun i => grp_map g (args i))).
    rewrite (nullary_bundle args).
    exact (grp_map_unit g).
  - (* mul: binary *)
    rewrite (binary_bundle (fun i => grp_map g (args i))).
    rewrite (binary_bundle args).
    exact (grp_map_mul g (args UA.Fst) (args UA.Snd)).
  - (* inv: unary, where [inv'] uses a constant bundle *)
    rewrite (unary_bundle (fun i => grp_map g (args i))).
    rewrite (unary_bundle args).
    exact (grp_map_inv g (args UA.Only)).
Qed.

Program Definition GroupVariety_to_Grp_Full : Functor.Full GroupVariety_to_Grp := {|
  prefmap := fun _ _ g => GroupVariety_hom_from_Grp g
|}.
