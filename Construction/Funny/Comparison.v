Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Instance.Two.
Require Import Coq.Lists.List.

Generalizable All Variables.

(** * The comparison functor κ : C □ D ⟶ C ∏ D

    The funny tensor product C □ D (Construction/Funny.v) and the cartesian
    product C ∏ D (Construction/Product.v) have the same objects; the
    comparison functor κ ([FunnyToProduct]) is the identity on objects and
    sends a word to its componentwise composite, one generating step at a
    time:

      lstep f ↦ (f, id)        rstep g ↦ (id, g)

    κ is bijective on objects ([FunnyToProduct_obj]) and full
    ([FunnyToProduct_Full]): every (f, g) in C ∏ D is the image of the word
    "g then f" — indeed of either diagonal of the fundamental square, since
    (f, g) ≈ (f, id) ∘ (id, g) ≈ (id, g) ∘ (f, id) there.  It is NOT faithful
    ([FunnyToProduct_not_faithful]): the two diagonals are identified by κ
    but remain distinct in C □ D ([funny_diagonals_distinct]).  Finally κ is
    natural in both arguments over strict functor equality
    ([FunnyToProduct_natural]).

    The non-faithfulness witness interprets _2 □ _2 in the free monoid on the
    booleans, regarded as a one-object category ([ListMon]): L-steps are
    tagged [true], R-steps [false], and the two diagonals map to the distinct
    words [true; false] and [false; true].  This is the one-object shadow of
    Weber's observation (TAC 28:2, §2) that on monoids − □ − is the free
    product (the coproduct of monoids), whereas − ∏ − is the direct product.
    It also pins down, as a regression test, that the congruence [feq] was
    not accidentally made too coarse: no interchange is derivable.

    Weber (TAC 28:2) further factorizes κ as bijective-on-objects followed by
    fully-faithful to obtain the Gray tensor product of 2-categories, where
    the two diagonals become isomorphic rather than equal; that factorization
    is out of scope here and recorded only as this remark. *)

(** ** The comparison functor *)

(* The separately functorial data of κ: each generating step becomes the
   corresponding one-sided morphism of the cartesian product.  Interchange
   holds in C ∏ D, so this data folds words through [FunnyUP] with no
   obstruction — κ is precisely where the two diagonals get identified. *)
Program Definition FunnyToProduct_sep {C D : Category} :
  SepFunctorial (E:=C ∏ D) (fun (c : C) (d : D) => (c, d)) := {|
  sf_lmap := fun _ _ f d => (f, id);
  sf_rmap := fun c _ _ g => (id, g)
|}.

Definition FunnyToProduct {C D : Category} : (C □ D) ⟶ (C ∏ D) :=
  FunnyUP FunnyToProduct_sep.

(* κ is (definitionally) bijective on objects. *)
Lemma FunnyToProduct_obj {C D : Category} (c : C) (d : D) :
  FunnyToProduct (c, d) = ((c, d) : C ∏ D).
Proof. reflexivity. Qed.

(* κ is full: (f, g) is the image of the word "g then f" (the R-then-L
   diagonal; the L-then-R one would do just as well). *)
#[export] Program Instance FunnyToProduct_Full {C D : Category} :
  Full (@FunnyToProduct C D) := {
  prefmap := fun x y fg => fconsR (snd fg) (fconsL (fst fg) fnil)
}.

(** ** The discriminating interpretation

    The free monoid on [bool], as a one-object category: morphisms are lists
    of booleans, composition is concatenation.  Words read source-to-target
    while composition reads right-to-left, so [v ∘ u] appends [u] in front:
    [compose v u = u ++ v]. *)

Program Definition ListMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => list bool;
  homset  := fun _ _ => Morphism_equality _ _;
  id      := fun _ => nil;
  compose := fun _ _ _ u v => (v ++ u)%list
|}.
Next Obligation. now rewrite app_nil_r. Qed.
Next Obligation. now rewrite app_assoc. Qed.
Next Obligation. now rewrite app_assoc. Qed.

(* Tag the single non-identity arrow of 2 with [b]; identities vanish. *)
Definition two_tag (b : bool) {x y : TwoObj} (f : TwoHom x y) : list bool :=
  match f with
  | TwoXY => b :: nil
  | _ => nil
  end.

(* The separately functorial interpretation _2 □ _2 ⟶ ListMon distinguishing
   the two diagonals: L-steps are tagged [true], R-steps [false]. *)
Program Definition FunnyTwo_sep :
  SepFunctorial (C:=_2) (D:=_2) (E:=ListMon) (fun _ _ => ttt) := {|
  sf_lmap := fun _ _ f _ => two_tag true f;
  sf_rmap := fun _ _ _ g => two_tag false g
|}.
Next Obligation. destruct c; reflexivity. Qed.
Next Obligation. destruct d; reflexivity. Qed.
Next Obligation.
  (* Finite case analysis on the endpoints; [TwoHom_inv] then pins each
     morphism to its unique inhabitant (Instance/Two.v idiom). *)
  destruct c, c', c'';
    try destruct (TwoHom_Y_X_absurd f);
    try destruct (TwoHom_Y_X_absurd f');
    pose proof (TwoHom_inv _ _ f);
    pose proof (TwoHom_inv _ _ f');
    simpl in *; subst; reflexivity.
Qed.
Next Obligation.
  destruct d, d', d'';
    try destruct (TwoHom_Y_X_absurd g);
    try destruct (TwoHom_Y_X_absurd g');
    pose proof (TwoHom_inv _ _ g);
    pose proof (TwoHom_inv _ _ g');
    simpl in *; subst; reflexivity.
Qed.

Definition FunnyTwoInterp : (_2 □ _2) ⟶ ListMon := FunnyUP FunnyTwo_sep.

(** ** The two diagonals of the fundamental square *)

(* The square in _2 □ _2 built from TwoXY in each coordinate; L first. *)
Definition diagLR : FunHom (C:=_2) (D:=_2) TwoX TwoX TwoY TwoY :=
  fconsL (C:=_2) (D:=_2) TwoXY (fconsR (C:=_2) (D:=_2) TwoXY fnil).

(* The same square, R first. *)
Definition diagRL : FunHom (C:=_2) (D:=_2) TwoX TwoX TwoY TwoY :=
  fconsR (C:=_2) (D:=_2) TwoXY (fconsL (C:=_2) (D:=_2) TwoXY fnil).

(* The separation theorem: the two diagonals are NOT identified by [feq].
   Folding through [FunnyTwo_sep] sends them to the distinct words
   [true; false] and [false; true] of the free monoid, and [ffold_respects]
   says the fold is [feq]-invariant.  This is the regression test that the
   congruence on words is not too coarse — no interchange law snuck in. *)
Theorem funny_diagonals_distinct : feq diagLR diagRL → False.
Proof.
  intro E.
  pose proof (ffold_respects FunnyTwo_sep E) as X.
  simpl in X.
  discriminate X.
Qed.

(* κ identifies the two diagonals (both map to (TwoXY, TwoXY)), so it cannot
   be faithful. *)
Corollary FunnyToProduct_not_faithful :
  Faithful (@FunnyToProduct _2 _2) → False.
Proof.
  intros [inj].
  apply funny_diagonals_distinct.
  apply (inj (TwoX, TwoX) (TwoY, TwoY) diagLR diagRL).
  simpl; split; reflexivity.
Qed.

(** ** Naturality of κ over strict functor equality

    κ is the component at (C, D) of a transformation from the funny tensor to
    the cartesian product of functors: κ ∘ (F □ G) ≈ (F ∏⟶ G) ∘ κ, in
    [Functor_StrictEq_Setoid].  Both sides agree definitionally on objects;
    on the generating steps the fixed coordinate needs [fmap_id] (an ≈-level
    equation, which is exactly why the statement lives at strict functor
    equality and not literal equality). *)

Lemma FunnyToProduct_natural {C C' D D' : Category}
  (F : C ⟶ C') (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' ∏ D'))
    (FunnyToProduct ◯ FunnyBimap F G) ((F ∏⟶ G) ◯ FunnyToProduct).
Proof.
  apply (Funny_strict_eq (FunnyToProduct ◯ FunnyBimap F G)
           ((F ∏⟶ G) ◯ FunnyToProduct) (fun _ _ => eq_refl)).
  - intros c c' f d; simpl; split; cat.
  - intros c d d' g; simpl; split; cat.
Qed.
