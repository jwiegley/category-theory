Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The wide walking parallel pair *)

(* nLab:      https://ncatlab.org/nlab/show/parallel+morphisms
   nLab:      https://ncatlab.org/nlab/show/wide+pullback
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   This is the shape category of an ARBITRARY family of parallel arrows:
   two objects [ParX], [ParY], their identities, and one non-identity arrow
   [ParX ~> ParY] for each element of an index type [I],

                --- f i --->
        ParX                 ParY      (one arrow for every i : I)
                --- f j --->

   with no arrow [ParY ~> ParX] and no non-identity endomorphism, so that
   composition is forced.  A functor [WideParallel I ⟶ C] is exactly an
   [I]-indexed family of parallel morphisms in C; its limit is their wide
   equalizer and its colimit their wide coequalizer.  Mac Lane introduces
   the notion in passing: having presented the coequalizer as a universal
   arrow over the walking parallel pair, he remarks that coequalizers of an
   arbitrary set of parallel maps a → b are defined in the same way
   (Categories for the Working Mathematician, 2nd ed., §III.3, pp. 64-65).
   Wide equalizers are the shape Freyd's initial-object argument wants:
   there one equalizes ALL endomorphisms of a weakly initial object at once
   (Mac Lane §V.6).  Theory/WeaklyInitial.v reaches AN initial object by a
   product-plus-binary-equalizer detour, and Theory/WeaklyInitial/Wide.v
   runs the argument directly over this shape's equalizers instead — as an
   ADDITIVE second theorem, leaving the first untouched.  No passage
   between the two conclusions is established, so they are not identified.

   [Instance/Parallel.v]'s [Parallel] is the case I = 2, and the two files
   sit side by side rather than one replacing the other; the comparison
   [WideParallel_bool_Parallel] below relates them.

   NAMING.  The issue that motivated this file calls the shape [Parallel I].
   That name is already taken, by the two-arrow shape this generalizes, and
   this file Requires it (the comparison needs both); [WideParallel] is used
   instead.  The objects are NOT redeclared: [ParObj], [ParX] and [ParY] are
   imported from [Instance/Parallel.v], so "the same two objects" is a
   definitional fact rather than a convention.

   ENCODING, and why the obvious generalization is not the one taken.
   [Instance/Parallel.v] declares [ParHom : bool → ParObj → ParObj → Set],
   which invites the reading that its two non-identity arrows are already
   parameterized by an index type, so that the wide shape would be that file
   with [bool] replaced by [I].  That reading does not survive contact with
   the constructors: THREE of the four ([ParIdX], [ParIdY], [ParOne]) sit at
   the tag [true] and only [ParTwo] at [false].  The [bool] is a
   DISCRIMINATOR on the hom-set ParX ~> ParY that doubles as a dummy tag on
   the identities, not a free index; substituting an arbitrary [I] leaves
   the three identity-side constructors without a distinguished element of
   [I] to sit at, and the definition does not typecheck.  So the wide shape
   is a different encoding rather than a substitution instance, which is
   also why the comparison below has to be proved rather than observed.

   The encoding chosen here computes the hom-family by matching on the two
   objects,

     hom ParX ParX = poly_unit,  hom ParX ParY = I,
     hom ParY ParY = poly_unit,  hom ParY ParX = WParVoid,

   so that an arrow of the shape from ParX to ParY IS an index, on the nose
   ([wide_hom_XY], by [eq_refl]), and the arrow action of a diagram is
   literally the family ([awide_fmap_arr], by [eq_refl]).  [WParVoid] is a
   universe-polymorphic empty type declared here so that all four branches
   of the hom family are at one universe by construction; the tree carries
   no polymorphic empty type to reuse (searched: [Lib/], [Instance/Zero.v],
   which uses [Empty_set]).  It is NOT forced: rebuilding the shape with
   the standard [Set]-pinned [Empty_set] in that branch yields the same
   signature and a character-for-character identical constraint block, [Set]
   sitting below every [Type@{i}], so nothing is dragged down.  An earlier
   draft of this header claimed otherwise and was wrong.

   UNIVERSES, measured rather than assumed (reproduce with
   [Set Printing Universes. About WideParallel. About AWide.]):

     WideParallel@{i p} : Type@{i} → Category@{Set i p}
       (* i p |= i <= Logic_lemmas.equality.u0, i <= eq_ind_r.u0, i <= p *)

   The two stdlib bounds are the ordinary price of an [eq]-valued hom-setoid
   in this tree and are NOT introduced here: [Instance/Discrete.v]'s
   [DiscreteCat@{o h p}] — the tree's other [Type]-parameterized shape with
   [eq] homs, and the one [Theory/WeaklyInitial.v] already consumes —-
   carries SIX such constraints ([o <= eq.u0], [o <= Logic_lemmas.equality.u0],
   [h <= eq_ind.u0], [h <= Logic_lemmas.equality.u0], [h <= eq_ind_r.u0],
   [h <= p]) where this carries three.  The object universe is [Set] because
   [ParObj] is, exactly as in the donor.

     AWide@{i k o h p} : ... → WideParallel@{i k} I ⟶ C   with, among others,
       i <= h

   i.e. the index universe must sit at or below the AMBIENT hom universe.
   That is not a choice made here either: every [Functor] in this library
   pins the codomain hom level at or above the domain's, through the
   [respectful] instance inside [fmap_respects] (the same fact
   [Instance/Top/Forgetful.v] runs into from the other side).  For the
   Freyd application the index IS a hom-type, so the bound is met with
   nothing to spare and nothing to pay.  The bound is guarded, not merely
   recorded: Test/ProbeWideParallel.v rejects [AWide] at an index universe
   declared strictly above the target's hom universe and accepts it
   strictly below.

   The comparison section carries one further identification, and getting
   it down to that took explicit binders.  [Functor_StrictEq_Setoid]
   identifies the HOM and PROOF universes of the two categories it
   compares, so

     AWide_bool_APair : ∀ {C : Category@{u1 u3 u3}} ...

   — [h = p] at the target, at a FREE level.  Written without universe
   annotations on [Wide_of_Par] and [Par_of_Wide], minimization pins the
   shape's hom universe at [Set] (because [bool] is a [Set]) and
   [Functor_StrictEq_Setoid] then drags the TARGET's hom and proof
   universes down with it, giving the strictly weaker
   [C : Category@{u1 Set Set}].  Both comparison functors therefore carry
   explicit binders — [Wide_of_Par@{i p u v}], [Par_of_Wide@{i p u v}] —
   which is the same FAMILY of hazard that
   Construction/Free/Quiver/Examples.v records for
   [Build_Quiver_Standard_Eq], though neither the cause nor the repair is
   the same one: there a MONOMORPHIC donor
   ([Corelib.Classes.CRelationClasses.eq_equivalence@{u}]) pins the PROOF
   universe and the repair is to spend [Lib/Setoid.v]'s polymorphic
   [eq_equivalence@{t u}], whereas here minimization at unannotated
   definitions pins the HOM universe and the repair is explicit binders.
   [WideParallel_bool_Parallel] is over
   [Isomorphism@{u1 u0 u0} (WideParallel@{u0 u0} bool) Parallel@{Set u0}],
   with [u0] free for the same reason.

   DEGENERATE INDICES.  At a one-element index the shape is the walking
   arrow [Instance/Two.v]'s [_2] (same two objects, one non-identity arrow);
   at the empty index it is the DISCRETE category on two objects, so a limit
   over it is a binary PRODUCT rather than anything equalizer-shaped.
   NEITHER identification is proved, here or anywhere below — both are
   stated as orientation.  What IS proved, in [Structure/Equalizer/Wide.v]
   and its dual, is the consequence that matters: the elementary wide
   (co)equalizer record and the (co)limit over this shape come apart at an
   empty index, so the round trips between them take a member of the family
   as an explicit hypothesis.

   NOT DELIVERED.  No presheaf reading of this shape (the donor's
   [Presheaf_Graph] has no wide counterpart here).  No identification of
   [WideParallel poly_unit] with [_2], and none of [WideParallel] at an empty
   index with a discrete category, hence no identification of a limit over
   the empty-index shape with a binary product.  No functoriality of
   [WideParallel] in [I] (a map I → J does induce an identity-on-objects
   functor, but nothing below needs it and no such functor is built).  No
   claim that [WideParallel bool] and [Parallel] are Leibniz-equal as
   [Category] records, or that their hom-families are convertible: both are
   REFUTED,
   in Test/ProbeWideParallel.v. *)

(** ** The shape *)

(* A universe-polymorphic empty type, for the hom-set ParY ~> ParX. *)
Inductive WParVoid@{i} : Type@{i} := .

(* The hom-family of the wide shape, computed from the two objects.  Note
   [WParHom I ParX ParY] reduces to [I] itself. *)
Definition WParHom@{i} (I : Type@{i}) (x y : ParObj) : Type@{i} :=
  match x, y with
  | ParX, ParX => poly_unit@{i}
  | ParY, ParY => poly_unit@{i}
  | ParX, ParY => I
  | ParY, ParX => WParVoid@{i}
  end.

(* There is no arrow ParY ~> ParX; the analogue of the donor's
   [ParHom_Y_X_absurd]. *)
Lemma WParHom_Y_X_absurd@{i} {I : Type@{i}} : WParHom@{i} I ParY ParX → False.
Proof. intro e; destruct e. Qed.

Definition wpar_id@{i} {I : Type@{i}} (x : ParObj) : WParHom@{i} I x x :=
  match x with ParX => ttt | ParY => ttt end.

(* Composition is forced: an identity on either side returns the other
   argument, and the four object triples that would need an arrow
   ParY ~> ParX are refuted by its empty hom-set. *)
Definition wpar_compose@{i} {I : Type@{i}} {x y z : ParObj} :
  WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z :=
  match x, y, z
    return WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z with
  | ParX, ParX, ParX => fun _ _ => ttt
  | ParX, ParX, ParY => fun f _ => f
  | ParX, ParY, ParX => fun f _ => match f with end
  | ParX, ParY, ParY => fun _ g => g
  | ParY, ParX, ParX => fun _ g => match g with end
  | ParY, ParX, ParY => fun _ g => match g with end
  | ParY, ParY, ParX => fun f _ => match f with end
  | ParY, ParY, ParY => fun _ _ => ttt
  end.

(* The wide walking parallel pair on the index type [I].  Hom-equivalence is
   strict equality of indices, so distinct indices are distinct arrows and
   the shape is not thin unless [I] is subsingleton. *)
Program Definition WideParallel@{i p} (I : Type@{i}) : Category@{Set i p} := {|
  obj     := ParObj;
  hom     := WParHom@{i} I;
  homset  := fun x y =>
    {| equiv := @eq (WParHom@{i} I x y)
     ; setoid_equiv := @eq_equivalence@{i p} (WParHom@{i} I x y) |};
  id      := @wpar_id@{i} I;
  compose := @wpar_compose@{i} I
|}.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.

(* An arrow ParX ~> ParY of the shape IS an index, and the two endomorphism
   hom-sets are singletons. *)
Example wide_hom_XY (I : Type) : (ParX ~{WideParallel I}~> ParY) = I := eq_refl.
Example wide_hom_XX (I : Type) :
  (ParX ~{WideParallel I}~> ParX) = poly_unit := eq_refl.
Example wide_hom_YY (I : Type) :
  (ParY ~{WideParallel I}~> ParY) = poly_unit := eq_refl.

(** ** The diagram of a family of parallel arrows *)

(* Object action: ParX ↦ x, ParY ↦ y. *)
Definition wdiag@{o h p} {C : Category@{o h p}} (x y : C) (p : ParObj) : C :=
  match p with ParX => x | ParY => y end.

(* Arrow action: the index i is sent to the member f i of the family. *)
Definition awide_fmap@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) {a b : ParObj} :
  WParHom@{i} I a b → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b :=
  match a, b return WParHom@{i} I a b
                    → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b with
  | ParX, ParX => fun _ => id[x]
  | ParY, ParY => fun _ => id[y]
  | ParX, ParY => fun i => fs i
  | ParY, ParX => fun e => match e with end
  end.

Lemma awide_fmap_id@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a : ParObj) :
  awide_fmap@{i o h p} fs (@wpar_id@{i} I a) ≈ id{C}.
Proof. destruct a; reflexivity. Qed.

Lemma awide_fmap_comp@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a b c : ParObj) :
  ∀ (f : WParHom@{i} I b c) (g : WParHom@{i} I a b),
    awide_fmap@{i o h p} fs (@wpar_compose@{i} I a b c f g)
      ≈ awide_fmap@{i o h p} fs f ∘ awide_fmap@{i o h p} fs g.
Proof.
  destruct a, b, c; intros f g; simpl in *;
  try destruct f; try destruct g; cat.
Qed.

(* The diagram of the family [fs], the wide analogue of [APair]. *)
Program Definition AWide@{i k o h p}
  {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) : WideParallel@{i k} I ⟶ C := {|
  fobj := wdiag@{o h p} x y;
  fmap := fun a b m => awide_fmap@{i o h p} fs m;
  fmap_id := fun a => awide_fmap_id@{i o h p} fs a;
  fmap_comp := fun a b c f g => awide_fmap_comp@{i o h p} fs a b c f g
|}.

(* The arrow action is the family itself, definitionally. *)
Example awide_fmap_arr {I : Type} {C : Category} {x y : C}
  (fs : I → x ~> y) (i : I) :
  fmap[AWide fs] (i : ParX ~{WideParallel I}~> ParY) = fs i := eq_refl.

Example awide_obj_X {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParX = x := eq_refl.
Example awide_obj_Y {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParY = y := eq_refl.

(** ** Comparison with the two-arrow shape *)

(* The two comparison functors are the identity on objects; all the content
   is in the hom-sets, where a [Parallel] arrow ParX ~> ParY is a dependent
   pair whose bool tag decides between the two generators, and a
   [WideParallel bool] arrow ParX ~> ParY is that bool itself. *)

Definition wide_of_par_map@{i u v} {a b : ParObj} :
  (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b :=
  match a, b return (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b with
  | ParX, ParX => fun _ => ttt
  | ParY, ParY => fun _ => ttt
  | ParX, ParY => fun h => ``h
  | ParY, ParX => fun h => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
  end.

Definition par_of_wide_map@{i u v} {a b : ParObj} :
  WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) :=
  match a, b return WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) with
  | ParX, ParX => fun _ => (true; ParIdX)
  | ParY, ParY => fun _ => (true; ParIdY)
  | ParX, ParY => fun c => if c then (true; ParOne) else (false; ParTwo)
  | ParY, ParX => fun e => match e with end
  end.

Program Definition Wide_of_Par@{i p u v} :
  Parallel@{u v} ⟶ WideParallel@{i p} bool := {|
  fobj := fun p => p;
  fmap := fun a b h => wide_of_par_map@{i u v} h
|}.
Next Obligation.
  proper.
  destruct x, y; simpl in *; try assumption; try reflexivity;
  destruct (ParHom_Y_X_absurd _ e).
Qed.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, f, g;
  pose proof (ParHom_inv _ _ _ X0) as HX0;
  pose proof (ParHom_inv _ _ _ X) as HX;
  simpl in HX0, HX; try contradiction;
  subst; reflexivity.
Qed.

Program Definition Par_of_Wide@{i p u v} :
  WideParallel@{i p} bool ⟶ Parallel@{u v} := {|
  fobj := fun p => p;
  fmap := fun a b m => par_of_wide_map@{i u v} m
|}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z; simpl in *;
  try destruct f; try destruct g; reflexivity.
Qed.

(* In [Parallel] the tag of an endomorphism is forced to [true]: the two
   [false]-tagged cases of [ParHom_inv_t] at equal endpoints are [False]. *)
Lemma par_endo_tag (a : ParObj) (f : a ~{Parallel}~> a) : ``f = true.
Proof.
  destruct f as [bf hf]; destruct a, bf; simpl; try reflexivity;
  destruct (ParHom_inv _ _ _ hf).
Qed.

(* Both composites are the identity, and both round trips hold at STRICT
   functor equality: the object components are [eq_refl], so the transports
   of [Functor_StrictEq_Setoid] vanish and only the hom-level agreement is
   left to prove. *)
Lemma Par_of_Wide_Wide_of_Par :
  @equiv _ (@Functor_StrictEq_Setoid Parallel Parallel)
    (Par_of_Wide ◯ Wide_of_Par) (Id[Parallel]).
Proof.
  exists (fun _ => eq_refl).
  intros a b f; simpl; unfold Logic.transport_r, Logic.transport; simpl.
  destruct a, b; simpl in *.
  - symmetry; exact (par_endo_tag ParX f).
  - destruct f as [bf hf]; destruct bf; reflexivity.
  - destruct f as [bf hf]; destruct (ParHom_Y_X_absurd _ hf).
  - symmetry; exact (par_endo_tag ParY f).
Qed.

Lemma Wide_of_Par_Par_of_Wide :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) (WideParallel bool))
    (Wide_of_Par ◯ Par_of_Wide) (Id[WideParallel bool]).
Proof.
  exists (fun _ => eq_refl).
  intros a b m; simpl.
  destruct a, b; simpl in *;
  try destruct m; reflexivity.
Qed.

(* The wide shape at a two-element index IS the walking parallel pair, as a
   genuine isomorphism of categories: [≅[StrictCat]] compares functors by
   [Functor_StrictEq_Setoid] (object equality on the nose), unlike [≅[Cat]],
   which in this library is equivalence of categories. *)
Program Definition WideParallel_bool_Parallel :
  @Isomorphism StrictCat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation. exact Par_of_Wide_Wide_of_Par. Qed.
Next Obligation. exact Wide_of_Par_Par_of_Wide. Qed.

(* The weaker reading, derived: an isomorphism in [Cat] is an EQUIVALENCE of
   categories, so this says strictly less than the statement above. *)
Program Definition WideParallel_bool_Parallel_Cat :
  @Isomorphism Cat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Par_of_Wide_Wide_of_Par).
Qed.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Wide_of_Par_Par_of_Wide).
Qed.

(* The shape comparison alone says nothing about DIAGRAMS.  This does: the
   binary diagram [APair f g] pulled back along the comparison is the wide
   diagram at the two-element family, again at strict functor equality with
   [eq_refl] object components. *)
Lemma AWide_bool_APair {C : Category} {x y : C} (f g : x ~> y) :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) C)
    (AWide (fun b : bool => if b then f else g))
    (APair f g ◯ Par_of_Wide).
Proof.
  unshelve eexists.
  - intro p; destruct p; reflexivity.
  - intros a b m; simpl; unfold Logic.transport_r, Logic.transport; simpl.
    destruct a, b; simpl in *;
    try destruct m; reflexivity.
Qed.
