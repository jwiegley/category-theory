Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.

Generalizable All Variables.

(** * Terminal object as the limit of the empty diagram *)

(* nLab:      https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   nLab: "A terminal object may also be viewed as a limit over the empty
   diagram." Wikipedia: "Terminal objects in a category C may also be defined
   as limits of the unique empty diagram 0 → C," and "a terminal object can be
   thought of as an empty product" (the nullary product).

   Here `0` is the empty category (Instance/Zero.v) and `F : 0 ⟶ C` is the
   unique empty diagram. [Terminal_Limit] shows the two notions coincide: F has
   a limit (a terminal cone over the empty diagram) iff C has a terminal object.
   A cone over the empty diagram carries no legs, so its apex is unconstrained;
   the limit's universal property then says exactly that this apex receives a
   unique morphism from every object, which is the definition of a terminal
   object (Structure/Terminal.v).

   Dually, an initial object is the colimit of the empty diagram — the empty
   coproduct — i.e. a terminal object of C^op (see Structure/Initial.v,
   Structure/Limit.v's [Colimit]). *)

Theorem Terminal_Limit (C : Category) (F : 0 ⟶ C) :
  Limit F ↔ @Terminal C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X]).
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); unshelve econstructor; intros.
        - inversion x0.
        - inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      apply unique_obj.
    + given (cone : Cone F). {
        unshelve (refine {| vertex_obj := x |}); unshelve econstructor; intros.
        - inversion x0.
        - inversion x0.
      }
      destruct (@ump_limits _ _ _ X cone).
      pose proof (uniqueness f).
      pose proof (uniqueness g).
      rewrite <- X0, <- X1.
      * reflexivity.
      * intro x0; inversion x0.
      * intro x0; inversion x0.
  - construct.
    + construct; [ | unshelve econstructor ].
      * exact terminal_obj.
      * inversion x.
      * inversion x.
    + simpl.
      unshelve eexists.
      * exact one.
      * intros.
        inversion x.
      * intros.
        apply one_unique.
Qed.
