Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Naturality of the exponential laws *)

(* nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/exponential+object
   nLab: https://ncatlab.org/nlab/show/natural+transformation

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.5
   Exercise 2 (printed p. 44), asks that the familiar exponential laws

       z^(x × y) ≅ (z^y)^x,      (y × z)^x ≅ y^x × z^x,
       x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

   be shown NATURAL in each of their variables.  Riehl, "Category Theory in
   Context", §1.4 Example 1.4.11 (printed p. 29) reads the same four laws in
   the groupoid of finite sets and observes that applying the cardinality
   functor decategorifies them into the arithmetic identities
   z^(xy) = (z^y)^x, (yz)^x = y^x z^x, x(y+z) = xy + xz and x^(y+z) = x^y x^z;
   that half of the example is Instance/FinSet/Decategorify.v.

   The four isomorphisms themselves are already in the tree, as POINTWISE
   families indexed by three objects:

     - [exp_prod_l]     (Structure/Cartesian/Closed.v)  z^(x × y) ≅ (z^y)^x
     - [exp_prod_r]     (Structure/Cartesian/Closed.v)  (y × z)^x ≅ y^x × z^x
     - [prod_coprod_r]  (Structure/BiCCC.v)             x × (y+z) ≅ x×y + x×z
     - [exp_coprod]     (Structure/BiCCC.v)             x^(y+z) ≅ x^y × x^z

   What was missing is the statement that each family is a NATURAL
   isomorphism, i.e. an isomorphism in a functor category between the two
   sides read as functors of their three variables.  This file supplies that,
   as an UPGRADE and not as a replacement: every component of every
   transformation below is literally the [to] or [from] leg of the existing
   pointwise instance (recorded by the eight [_component] lemmas -- one per
   leg per law -- each of which holds by [reflexivity]), so nothing is rebuilt
   and the pointwise isos keep all their consumers.  The object action of
   each of the eight functors is likewise recorded by an [Example] holding by
   [eq_refl].

   ** Variances and domains

   Exponentiation is contravariant in the exponent and covariant in the base,
   so the four laws live over three different product categories.  The domains
   chosen here are

     - [exp_prod_l]     ((x, y), z) over ((C^op ∏ C^op) ∏ C)
     - [exp_prod_r]     (x, (y, z)) over (C^op ∏ (C ∏ C))
     - [prod_coprod_r]  (x, (y, z)) over (C ∏ (C ∏ C))
     - [exp_coprod]     ((y, z), x) over ((C^op ∏ C^op) ∏ C)

   with the bracketing of each domain matching the bracketing of the objects
   in the corresponding statement.  In each case both sides are given as
   DIRECT functor records (concrete [fobj] and [fmap]) rather than as
   composites of the internal-hom and product bifunctors; this keeps the
   naturality squares stated in the curry/eval calculus of
   Structure/Cartesian/Closed.v with no opposite-of-a-product bookkeeping.

   The arrow actions of the eight functors are built from three combinators:
   [ihom] below -- the action of the internal hom, exactly the [fmap] of
   [InternalHomFunctor] (Functor/Hom/Internal.v) written in C with no [op]
   coercion, an identification machine-checked below at Leibniz [eq_refl]
   ([ihom_is_InternalHomFunctor_fmap]) -- together with [split]
   (Structure/Cartesian.v) and [cover] (Structure/Cocartesian.v) for the
   product and coproduct actions.  The two Law-3 functors, whose statement
   has no exponentials, use only the latter two.

   ** The transpose triangle

   The final section relates the internal law [exp_prod_l] to the EXTERNAL
   currying bijection [exp_iso : x × y ~> z ≊ x ~> z^y] of
   Structure/Cartesian/Closed.v, whose two legs are [curry] and [uncurry]:
   postcomposition by [to exp_prod_l] computes, on an arbitrary generalized
   element f : w ~> z^(x × y), as a composite of [exp_iso] transposes -- one
   [uncurry], then two [curry]s -- through the associator, and dually for
   [from exp_prod_l].  So the
   internal iso is CARRIED by the external bijection; see
   [exp_prod_l_transpose] and [exp_prod_l_untranspose]. *)

(** ** Packaging a pointwise family of isomorphisms as a natural isomorphism

    Each of the four laws below is already available as a family of pointwise
    isomorphisms; what has to be added is one naturality square.  The two
    lemmas here move a square between the [to] and the [from] orientation (so
    that whichever leg is easier to compute with may be the one proved), and
    [NaturalIso_of_pointwise] assembles the family and the square into an
    isomorphism of the functor category, with the components UNCHANGED. *)

Section PointwiseNatural.

Context {D E : Category}.
Context {F G : D ⟶ E}.

Lemma natural_flip_from (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m.
Proof.
  intros x y m.
  assert (HA : from (comp y) ∘ (fmap[G] m ∘ to (comp x)) ≈ fmap[F] m).
  { rewrite nat, comp_assoc, iso_from_to; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_to_from.
  now rewrite id_right.
Qed.

Lemma natural_flip_to (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m.
Proof.
  intros x y m.
  assert (HA : to (comp y) ∘ (fmap[F] m ∘ from (comp x)) ≈ fmap[G] m).
  { rewrite nat, comp_assoc, iso_to_from; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_from_to.
  now rewrite id_right.
Qed.

(* The components of both legs are the components of [comp], on the nose. *)
Program Definition NaturalIso_of_pointwise (comp : ∀ p, F p ≅ G p)
        (nat : ∀ (x y : D) (m : x ~> y),
            fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  @Isomorphism ([D, E]) F G := {|
  to   := {| transform := fun p => to (comp p) |};
  from := {| transform := fun p => from (comp p) |}
|}.
(* The obligations are the naturality square of each leg in both
   orientations, together with whichever round trips the ambient obligation
   tactic has not already discharged.  [Program] neither fixes their order nor
   guarantees how many survive, so each is closed by one alternation: the
   square supplied, its flip, or invertibility of the component (the round
   trips arrive with the identity of [G] still written [fmap[G] id]). *)
Ltac natiso_obligation :=
  intros;
  try rewrite fmap_id;
  first [ now apply nat
        | symmetry; now apply nat
        | now apply natural_flip_from
        | symmetry; now apply natural_flip_from
        | now apply iso_to_from
        | now apply iso_from_to ].
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.

End PointwiseNatural.

Section ExpNatural.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** ** The internal-hom action, and its functoriality *)

(* [ihom f h : c^a ~> d^b] for f : b ~> a and h : c ~> d precomposes by f in
   the exponent and postcomposes by h in the base.  This is the [fmap] of
   Functor/Hom/Internal.v's [InternalHomFunctor] with the C^op arrow spelled
   as the underlying C arrow, so that no [op] re-reading occurs below -- an
   identification that holds at Leibniz [eq_refl], machine-checked after the
   laws ([ihom_is_InternalHomFunctor_fmap]).  The three lemmas that follow
   therefore re-prove that functor's three obligations in the [op]-free
   spelling rather than shadowing something weaker. *)
Definition ihom {a b c d : C} (f : b ~> a) (h : c ~> d) : c^a ~> d^b :=
  curry (h ∘ eval ∘ second f).

(* [simpl] is used below only to reduce the pair projections of a product
   category; it must not go on to unfold [ihom] into its transpose. *)
Arguments ihom : simpl never.

#[export] Program Instance ihom_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@ihom a b c d).
Next Obligation. proper; unfold ihom; now rewrites. Qed.

Lemma ihom_id {a c : C} : ihom (id[a]) (id[c]) ≈ id[c^a].
Proof. unfold ihom; unfork; cat. Qed.

Lemma ihom_comp {a b b' c d e : C}
      (f : b ~> a) (f' : b' ~> b) (h : c ~> d) (h' : d ~> e) :
  ihom f' h' ∘ ihom f h ≈ ihom (f ∘ f') (h' ∘ h).
Proof.
  unfold ihom.
  symmetry.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(* The identification asserted above, machine-checked: [ihom] IS the arrow
   action of [InternalHomFunctor], read in C, at Leibniz equality -- not
   merely up to [≈].  ((a, c) ~> (b, d) in C^op ∏ C is a pair of f : b ~> a
   in C and h : c ~> d.) *)
Example ihom_is_InternalHomFunctor_fmap {a b c d : C} (f : b ~> a) (h : c ~> d) :
  @fmap _ _ (InternalHomFunctor C) (a, c) (b, d) (f, h) = ihom f h := eq_refl.

(** ** Small [split] identities used to normalise arrow actions *)

Lemma first_as_split {x y z : C} (f : x ~> y) : first (z:=z) f ≈ split f id.
Proof. unfold first, split; cat. Qed.

Lemma second_as_split {x y z : C} (f : x ~> y) : second (z:=z) f ≈ split id f.
Proof. unfold second, split; cat. Qed.

(** ** Naturality of the associator

    Structure/Cartesian.v states the associator as a pointwise isomorphism
    only, with no naturality; the two general squares are supplied here for
    reuse.  The squares of Law 1 do not consume them directly -- their middle
    factor is an identity, and rewriting [first]/[second] into [split] form
    costs more than proving the two specialised shapes below outright -- so
    what the proofs actually use is [prod_assoc_second_first],
    [prod_assoc_first_first] and [prod_assoc_from_first]. *)

Lemma prod_assoc_to_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  to prod_assoc ∘ split (split f g) h ≈ split f (split g h) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_from_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  from prod_assoc ∘ split f (split g h) ≈ split (split f g) h ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

(* Two instances of associator naturality, in the exact shapes the squares
   below produce (the middle factor of each composite is an identity, so
   neither is a bare instance of [prod_assoc_to_natural]). *)
Lemma prod_assoc_second_first {a x y x' y' : C} (f : x' ~> x) (g : y' ~> y) :
  to prod_assoc ∘ (second g ∘ first (second (z:=a) f))
    ≈ second (split f g) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_first_first {a b x y : C} (k : a ~> b) :
  to prod_assoc ∘ first (z:=y) (first (z:=x) k) ≈ first (z:=x × y) k ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

(* [eval_first] under a further composite, so that no [comp_assoc] step has to
   be aimed by hand at one side of a naturality square. *)
Corollary eval_first_comp {a b c w : C} (k : a ~> c^b) (m : w ~> a × b) :
  eval ∘ (first k ∘ m) ≈ uncurry k ∘ m.
Proof. rewrite comp_assoc, eval_first; reflexivity. Qed.

(* Postcomposition by an internal-hom action, computed through a transpose:
   this is the single calculation every naturality square below reduces to. *)
Lemma ihom_curry {a b b' c c' : C} (f : b' ~> b) (h : c ~> c') (m : a × b ~> c) :
  ihom f h ∘ curry m ≈ curry (h ∘ m ∘ second f).
Proof.
  unfold ihom.
  rewrite curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- first_second.
  rewrite (comp_assoc eval).
  rewrite eval_first, uncurry_curry.
  now rewrite comp_assoc.
Qed.

(** ** Reading a contravariant slot back in C

    [C^op] has the objects and the hom-sets of [C] (Construction/Opposite.v),
    so both maps below are the identity.  They are nevertheless written out:
    without them the elaborator sees a slot of the domain typed at [C^op] and
    goes looking for a [@Cartesian (C^op)] -- that is, a [Cocartesian C] --
    when resolving [×] or [split].  Applying [opobj]/[oparr] pins the ambient
    category to [C], and simultaneously records the variance in the source
    text: [oparr] reverses the arrow. *)
Definition opobj (a : C^op) : C := a.
Definition oparr {a b : C^op} (f : a ~{C^op}~> b) : opobj b ~{C}~> opobj a := f.

(** ** Law 1: z^(x × y) ≅ (z^y)^x, natural in x, y and z

    Domain ((C^op ∏ C^op) ∏ C).  The object ((x, y), z) goes to z^(x × y) on
    the left and to (z^y)^x on the right.  A morphism ((f, g), h) out of it is
    a pair of C-arrows f : x' ~> x and g : y' ~> y -- the two contravariant
    slots, read in C^op -- together with h : z ~> z'. *)

(* The [to] and [from] legs of [exp_prod_l], named so that the calculations
   below never depend on how [Program] elaborated the instance; both hold by
   [reflexivity]. *)
Lemma exp_prod_l_to_unfold {x y z : C} :
  to (@exp_prod_l C _ _ x y z) ≈ curry (curry (eval ∘ to prod_assoc)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_from_unfold {x y z : C} :
  from (@exp_prod_l C _ _ x y z) ≈ curry (uncurry eval ∘ from prod_assoc).
Proof. reflexivity. Qed.

(* The object and arrow actions are given as ordinary definitions and only
   then assembled into a functor record.  Elaborating them inside the
   [Program Definition] would not do: [Program] defers an unresolved instance
   argument of [product_obj] into an OBLIGATION, which
   Lib/Foundation.v's [Unset Transparent Obligations] makes opaque, and the
   resulting [fobj] then converts with nothing -- in particular not with the
   endpoints of [exp_prod_l]. *)
Definition expProdL_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) × opobj (snd (fst p))).

Definition expProdL_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_lhs x ~> expProdL_lhs y :=
  ihom (split (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpProdL_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_lhs;
  fmap := @expProdL_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdL_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  ((snd p)^(opobj (snd (fst p))))^(opobj (fst (fst p))).

Definition expProdL_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_rhs x ~> expProdL_rhs y :=
  ihom (oparr (fst (fst m))) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpProdL_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_rhs;
  fmap := @expProdL_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_id.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_comp.
Qed.

(* The two object actions, recorded so that the shape of each side of Law 1 is
   machine-checked rather than only asserted in the header. *)
Example ExpProdL_LHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_LHS] ((x, y), z) = z^(opobj x × opobj y) := eq_refl.

Example ExpProdL_RHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_RHS] ((x, y), z) = (z^(opobj y))^(opobj x) := eq_refl.

(* The naturality square proper.  Both sides normalise to a double transpose
   by [ihom_curry] and [curry_comp_l]; what remains under the two [curry]s is
   naturality of the associator. *)
Lemma exp_prod_l_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y' ~> y) (h : z ~> z') :
  ihom f (ihom g h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x' y' z') ∘ ihom (split f g) h.
Proof.
  rewrite !exp_prod_l_to_unfold.
  rewrite !ihom_curry.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_second_first, prod_assoc_first_first.
  unfold ihom.
  rewrite eval_first_comp, uncurry_curry.
  now rewrite <- !comp_assoc.
Qed.

Definition exp_prod_l_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpProdL_LHS p ≅ ExpProdL_RHS p :=
  @exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p).

Definition exp_prod_l_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpProdL_LHS ExpProdL_RHS :=
  NaturalIso_of_pointwise exp_prod_l_iso
    (fun _ _ m => exp_prod_l_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

(* The transformation is the existing pointwise iso: its component at
   ((x, y), z) is [to exp_prod_l] on the nose, and dually for [from]. *)
Lemma exp_prod_l_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_prod_l_natural] p
    ≈ to (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_prod_l_natural] p
    ≈ from (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

(** ** Naturality of Law 1 in a single variable

    Instantiating the square at two identities leaves the square in the
    remaining variable; the base variable z is done here as the specimen. *)
Corollary exp_prod_l_natural_in_base {x y z z' : C} (h : z ~> z') :
  ihom (id[x]) (ihom (id[y]) h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x y z') ∘ ihom (id[x × y]) h.
Proof.
  pose proof (exp_prod_l_square (id[x]) (id[y]) h) as HA.
  now rewrite split_id in HA.
Qed.

(** ** The transpose triangle: the internal law is carried by [exp_iso]

    [exp_iso : x × y ~> z ≊ x ~> z^y] (Structure/Cartesian/Closed.v) is the
    EXTERNAL currying bijection of the product-exponential adjunction; [curry]
    and [uncurry] are its two legs.  The two statements below say that
    composing with the internal isomorphism [exp_prod_l] computes as a
    composite of [exp_iso] transposes taken through the associator: to
    transpose f : w ~> z^(x × y) across [to exp_prod_l], untranspose it once,
    reassociate, and transpose twice back.  They hold for EVERY generalized
    element f, not merely for the identity, which is what makes them a
    statement about the two bijections rather than about one value.

    [prod_assoc_from_first] is the associator naturality the second statement
    needs; the [to] orientation is [prod_assoc_first_first] above. *)
Lemma prod_assoc_from_first {a b x y : C} (k : a ~> b) :
  from prod_assoc ∘ first (z:=x × y) k
    ≈ first (z:=y) (first (z:=x) k) ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

Lemma exp_prod_l_transpose {w x y z : C} (f : w ~> z^(x × y)) :
  to (@exp_prod_l C _ _ x y z) ∘ f ≈ curry (curry (uncurry f ∘ to prod_assoc)).
Proof.
  rewrite exp_prod_l_to_unfold.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_first_first.
  now rewrite eval_first_comp.
Qed.

Lemma exp_prod_l_untranspose {w x y z : C} (g : w ~> (z^y)^x) :
  from (@exp_prod_l C _ _ x y z) ∘ g
    ≈ curry (uncurry (uncurry g) ∘ from prod_assoc).
Proof.
  rewrite exp_prod_l_from_unfold.
  rewrite curry_comp_l.
  f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_from_first.
  rewrite comp_assoc.
  now rewrite <- uncurry_comp, eval_first.
Qed.

(** ** Law 2: (y × z)^x ≅ y^x × z^x, natural in x, y and z

    Domain (C^op ∏ (C ∏ C)): the object (x, (y, z)) goes to (y × z)^x on the
    left and to y^x × z^x on the right.  Only the first slot is
    contravariant. *)

Lemma exp_prod_r_to_unfold {x y z : C} :
  to (@exp_prod_r C _ _ x y z) ≈ curry (exl ∘ eval) △ curry (exr ∘ eval).
Proof. reflexivity. Qed.

(* Two readings of [ihom] with one argument an identity, used to recognise the
   legs of [exp_prod_r] and [exp_coprod] as internal-hom actions. *)
Lemma ihom_id_l {a c d : C} (k : c ~> d) : ihom (id[a]) k ≈ curry (k ∘ eval).
Proof. unfold ihom; now rewrite second_id, id_right. Qed.

Lemma ihom_id_r {a b c : C} (k : b ~> a) :
  ihom k (id[c]) ≈ curry (eval ∘ second k).
Proof. unfold ihom; now rewrite id_left. Qed.

Definition expProdR_lhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p) × snd (snd p))^(opobj (fst p)).

Definition expProdR_lhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_lhs x ~> expProdR_lhs y :=
  ihom (oparr (fst m)) (split (fst (snd m)) (snd (snd m))).

Program Definition ExpProdR_LHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_lhs;
  fmap := @expProdR_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdR_rhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p))^(opobj (fst p)) × (snd (snd p))^(opobj (fst p)).

Definition expProdR_rhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_rhs x ~> expProdR_rhs y :=
  split (ihom (oparr (fst m)) (fst (snd m))) (ihom (oparr (fst m)) (snd (snd m))).

Program Definition ExpProdR_RHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_rhs;
  fmap := @expProdR_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpProdR_LHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_LHS] (x, (y, z)) = (y × z)^(opobj x) := eq_refl.

Example ExpProdR_RHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_RHS] (x, (y, z)) = y^(opobj x) × z^(opobj x) := eq_refl.

(* Both sides are forks, so the square splits into its two components, and
   each component is one application of [ihom_comp] modulo [exl_split] or
   [exr_split]. *)
Lemma exp_prod_r_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y ~> y') (h : z ~> z') :
  split (ihom f g) (ihom f h) ∘ to (@exp_prod_r C _ _ x y z)
    ≈ to (@exp_prod_r C _ _ x' y' z') ∘ ihom f (split g h).
Proof.
  rewrite !exp_prod_r_to_unfold.
  rewrite <- !ihom_id_l.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite exl_split | now rewrite exr_split ].
Qed.

Definition exp_prod_r_iso (p : C^op ∏ (C ∏ C)) :
  ExpProdR_LHS p ≅ ExpProdR_RHS p :=
  @exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p)).

Definition exp_prod_r_natural :
  @Isomorphism ([C^op ∏ (C ∏ C), C]) ExpProdR_LHS ExpProdR_RHS :=
  NaturalIso_of_pointwise exp_prod_r_iso
    (fun _ _ m => exp_prod_r_square (oparr (fst m)) (fst (snd m)) (snd (snd m))).

Lemma exp_prod_r_natural_component (p : C^op ∏ (C ∏ C)) :
  transform[to exp_prod_r_natural] p
    ≈ to (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma exp_prod_r_natural_component_from (p : C^op ∏ (C ∏ C)) :
  transform[from exp_prod_r_natural] p
    ≈ from (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(** ** Laws 3 and 4 need coproducts as well *)

Context `{@Cocartesian C}.

(* Duals of [exl_split] and [exr_split]; Structure/Cocartesian.v carries the
   [left]/[right] versions but not these. *)
Lemma cover_inl {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inl ≈ inl ∘ f.
Proof. unfold cover; now rewrite inl_merge. Qed.

Lemma cover_inr {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inr ≈ inr ∘ g.
Proof. unfold cover; now rewrite inr_merge. Qed.

(** ** Law 3: x × (y + z) ≅ x × y + x × z, natural in x, y and z

    Domain (C ∏ (C ∏ C)); every slot is covariant. *)

Lemma prod_coprod_r_from_unfold {x y z : C} :
  from (@prod_coprod_r C _ _ _ x y z) ≈ second inl ▽ second inr.
Proof. reflexivity. Qed.

Definition prodCoprodR_lhs (p : C ∏ (C ∏ C)) : C :=
  (fst p) × (fst (snd p) + snd (snd p)).

Definition prodCoprodR_lhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_lhs x ~> prodCoprodR_lhs y :=
  split (fst m) (cover (fst (snd m)) (snd (snd m))).

Program Definition ProdCoprodR_LHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_lhs;
  fmap := @prodCoprodR_lhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_lhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite cover_id, split_id.
Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite split_comp, cover_comp.
Qed.

Definition prodCoprodR_rhs (p : C ∏ (C ∏ C)) : C :=
  (fst p × fst (snd p)) + (fst p × snd (snd p)).

Definition prodCoprodR_rhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_rhs x ~> prodCoprodR_rhs y :=
  cover (split (fst m) (fst (snd m))) (split (fst m) (snd (snd m))).

Program Definition ProdCoprodR_RHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_rhs;
  fmap := @prodCoprodR_rhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_rhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite !split_id, cover_id.
Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite cover_comp, !split_comp.
Qed.

Example ProdCoprodR_LHS_obj (x y z : C) :
  fobj[ProdCoprodR_LHS] (x, (y, z)) = x × (y + z) := eq_refl.

Example ProdCoprodR_RHS_obj (x y z : C) :
  fobj[ProdCoprodR_RHS] (x, (y, z)) = x × y + x × z := eq_refl.

(* Proved in the [from] orientation -- where both sides are copairings and the
   whole calculation is [merge_comp] plus one projection law -- and turned
   round by [natural_flip_to]. *)
Lemma prod_coprod_r_from_square {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  split f (cover g h) ∘ from (@prod_coprod_r C _ _ _ x y z)
    ≈ from (@prod_coprod_r C _ _ _ x' y' z') ∘ cover (split f g) (split f h).
Proof.
  rewrite !prod_coprod_r_from_unfold.
  unfold cover.
  rewrite <- !merge_comp.
  apply merge_inv; split.
  - rewrite split_second, inl_merge.
    rewrite comp_assoc, inl_merge.
    now rewrite second_split.
  - rewrite split_second, inr_merge.
    rewrite comp_assoc, inr_merge.
    now rewrite second_split.
Qed.

Definition prod_coprod_r_iso (p : C ∏ (C ∏ C)) :
  ProdCoprodR_LHS p ≅ ProdCoprodR_RHS p :=
  @prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p)).

Definition prod_coprod_r_natural :
  @Isomorphism ([C ∏ (C ∏ C), C]) ProdCoprodR_LHS ProdCoprodR_RHS :=
  NaturalIso_of_pointwise prod_coprod_r_iso
    (natural_flip_to prod_coprod_r_iso
       (fun _ _ m => prod_coprod_r_from_square (fst m) (fst (snd m)) (snd (snd m)))).

Lemma prod_coprod_r_natural_component (p : C ∏ (C ∏ C)) :
  transform[to prod_coprod_r_natural] p
    ≈ to (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma prod_coprod_r_natural_component_from (p : C ∏ (C ∏ C)) :
  transform[from prod_coprod_r_natural] p
    ≈ from (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(** ** Law 4: x^(y + z) ≅ x^y × x^z, natural in x, y and z

    Domain ((C^op ∏ C^op) ∏ C), as for Law 1, but now the two contravariant
    slots are the summands of the exponent: ((y, z), x) goes to x^(y + z) on
    the left and to x^y × x^z on the right. *)

Lemma exp_coprod_to_unfold {x y z : C} :
  to (@exp_coprod C _ _ _ x y z)
    ≈ curry (eval ∘ second inl) △ curry (eval ∘ second inr).
Proof. reflexivity. Qed.

Definition expCoprod_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) + opobj (snd (fst p))).

Definition expCoprod_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_lhs x ~> expCoprod_lhs y :=
  ihom (cover (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpCoprod_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_lhs;
  fmap := @expCoprod_lhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite cover_id, ihom_id.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite ihom_comp, cover_comp.
Qed.

Definition expCoprod_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p))) × (snd p)^(opobj (snd (fst p))).

Definition expCoprod_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_rhs x ~> expCoprod_rhs y :=
  split (ihom (oparr (fst (fst m))) (snd m)) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpCoprod_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_rhs;
  fmap := @expCoprod_rhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpCoprod_LHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_LHS] ((y, z), x) = x^(opobj y + opobj z) := eq_refl.

Example ExpCoprod_RHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_RHS] ((y, z), x) = x^(opobj y) × x^(opobj z) := eq_refl.

Lemma exp_coprod_square {x y z x' y' z' : C}
      (g : y' ~> y) (h : z' ~> z) (f : x ~> x') :
  split (ihom g f) (ihom h f) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x' y' z') ∘ ihom (cover g h) f.
Proof.
  rewrite !exp_coprod_to_unfold.
  rewrite <- !ihom_id_r.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite cover_inl | now rewrite cover_inr ].
Qed.

Definition exp_coprod_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpCoprod_LHS p ≅ ExpCoprod_RHS p :=
  @exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p))).

Definition exp_coprod_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpCoprod_LHS ExpCoprod_RHS :=
  NaturalIso_of_pointwise exp_coprod_iso
    (fun _ _ m => exp_coprod_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

Lemma exp_coprod_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_coprod_natural] p
    ≈ to (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

Lemma exp_coprod_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_coprod_natural] p
    ≈ from (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

(* The single-variable specimen for Law 4: naturality in the first summand. *)
Corollary exp_coprod_natural_in_first_summand {x y z y' : C} (g : y' ~> y) :
  split (ihom g (id[x])) (ihom (id[z]) (id[x])) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x y' z) ∘ ihom (cover g (id[z])) (id[x]).
Proof. exact (exp_coprod_square g (id[z]) (id[x])). Qed.

End ExpNatural.
