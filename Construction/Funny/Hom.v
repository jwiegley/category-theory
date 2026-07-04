Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/funny+tensor+product
   Mark Weber, "Free products of higher operad algebras", TAC 28:2 (2013), §2.

   The internal hom [⟦B, E⟧] of the funny tensor product on Cat: its objects
   are functors [B ⟶ E], but its morphisms [F ~> G] are UNNATURAL (or "mere")
   transformations — families [τ : ∀ b, F b ~{E}~> G b] of E-morphisms
   subject to NO naturality condition.  Weber §2: "These components φ_a are
   not required to satisfy the usual naturality condition."  By the theorem
   of Foltz, Kelly and Lair (1980) there are, up to isomorphism, exactly two
   biclosed monoidal structures on Cat: the cartesian one, whose internal hom
   [Instance/Fun.v] takes natural transformations, and the funny one, whose
   internal hom is this category.

   Structurally this is [Theory/Natural/Transformation.v] minus [naturality]
   and [naturality_sym]: identities and composition are componentwise, the
   hom-setoid is componentwise [≈] in E, and every category law holds
   componentwise, inherited from E.  No [_sym] companion field is needed
   here: with the naturality square gone, no remaining law has a dual
   orientation beyond the category laws themselves, which already come in
   [comp_assoc]/[comp_assoc_sym] pairs. *)

Program Definition UFun (B E : Category) : Category := {|
  obj     := B ⟶ E;                    (* objects are functors B ⟶ E *)
  hom     := fun F G =>                 (* unnatural transformations: *)
    ∀ b : B, F b ~{E}~> G b;           (* components only, no square *)
  homset  := fun F G =>                 (* componentwise equivalence *)
    {| equiv := fun τ σ => ∀ b, τ b ≈ σ b |};
  id      := fun _ _ => id;             (* identity, componentwise *)
  compose := fun _ _ _ τ σ b => τ b ∘ σ b  (* composition, componentwise *)
|}.
Next Obligation.
  (* The componentwise equivalence relation; the remaining five obligations
     (properness of composition and the category laws, all componentwise in
     E) are discharged by the global [cat_simpl] obligation tactic once this
     setoid is in place. *)
  equivalence.
  now transitivity (y b).
Qed.

(* Level 0, like the repo's other closed-delimiter notations (e.g. [⟦ n ⟧]
   in Construction/PROP.v): a self-delimited production must be usable in
   function-argument position, which a level-90 production is not. *)
Notation "⟦ B , E ⟧" := (UFun B E)
  (at level 0, format "⟦ B ,  E ⟧") : category_scope.
