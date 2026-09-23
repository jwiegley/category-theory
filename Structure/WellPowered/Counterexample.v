Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.WellPowered.
Require Import Coq.Logic.Hurkens.

Generalizable All Variables.

(** * A category that is not well-powered *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   nLab:      https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox
   Wikipedia: https://en.wikipedia.org/wiki/System_U#Girard's_paradox

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   book p. 130, calls a category well-powered when the subobjects of each
   object form a small set; nLab's page states the same ("every object has
   a small poset of subobjects") and records that the property can be
   absent even from a locally small category with a strong generator.
   Structure/WellPowered.v states the notion with the index universe
   pinned at or below the hom universe, and its witnesses are all
   POSITIVE.  This file supplies the matching negative: a formal category,
   built with no axiom, that is provably NOT well-powered at the pin, so
   that the pin is seen to exclude something.

   ** The category

   [AntichainTop@{i o h}], the antichain with a top, has as objects
   [option Type@{i}]: a top object [None] and one object [Some A] for
   every type [A] of [Type@{i}], so its objects sit at [o] with [i < o].
   Its arrows are [Some A ~> Some B := A = B], [Some A ~> None := unit],
   [None ~> None := unit] and [None ~> Some B := False], every hom-set
   carrying the setoid in which all arrows are equal.  It is thin, so
   every arrow is monic, and each type [A] gives a subobject [at_sub A] of
   [None] by the arrow into the top.  Two such subobjects are isomorphic
   only when their types are equal, so the subobjects of [None] are at
   least as many as the types of [Type@{i}].

   ** The refutation

   Given a well-poweredness datum [W] at [None] whose index sits at or
   below [i], [fun X => wp_from W (at_sub X)] and [at_up W], which reads
   the object [Some B] off the domain of [wp_to W j], make [Type@{i}] a
   RETRACT of the index: [at_up_down] is read off the domain isomorphism
   that the exhaustiveness clause [wp_to_from] supplies.  A universe that
   is a retract of one of its own types is inconsistent by Hurkens'
   paradox.  The standard library proves this in
   [Coq.Logic.Hurkens.TypeNeqSmallType] for an EQUATION between a universe
   and a type, and says in its comment that only the retract is used;
   [retract_paradox] below restates it over the retract, with the same
   proof through the universe-polymorphic [Generic.paradox].  The result,
   [AntichainTop_not_WellPoweredAt], refutes the datum at every index
   universe [w <= i], and [AntichainTop_not_WellPowered] reads that at the
   pin: with the homs at [h <= i], [WellPowered AntichainTop] is refuted
   outright.  Every hom type is [A = B], which lies in [Prop], or [unit]
   or [False], so [h] may be taken as low as [Set]
   ([AntichainTop_Set_not_WellPowered]).  Read at [AntichainTop^op] the
   same theorem says that [AntichainTop^op] is not co-well-powered
   ([AntichainTop_op_not_CoWellPowered]), since [(AntichainTop^op)^op]
   converts to [AntichainTop].

   ** Positive controls, and what the refutation measures

   The refutation is about SIZE, and size relative to the hom universe
   the category is instantiated at.  Two controls inhabit the same
   per-object record at [None]:

     - [AntichainTop_trivial], one universe up at the object universe
       [o], with the trivial index [SubObj None] of Structure/
       WellPowered.v's [wp_trivial]; the pinned [WellPowered] excludes it
       because [o] exceeds the hom universe;
     - [AntichainTop_WellPoweredAt_up], AT the pin, once the homs are
       instantiated above the types the objects name ([i < h]): the index
       is [option Type@{i}] itself, [wp_to] ([at_name]) sends [None] to
       Theory/Subobject/Lattice.v's [sub_top] and [Some A] to [at_sub A],
       [wp_from] is [sub_dom], and exhaustiveness holds by thinness.

   So the verdict depends on the hom instantiation: [AntichainTop@{i o h}]
   is not well-powered at the pin when [h <= i], and its top object has a
   pinned datum when [i < h] (measured by the two constants).  That is the
   general shape of the pin, recorded in Structure/WellPowered.v's
   UNIVERSE paragraph: "small" means at or below the category's OWN hom
   universe, and a category whose hom universe is a free parameter, as a
   thin one's is, can be instantiated with its homs raised.  Where the hom
   universe is tied to the objects' carriers, as in [Sets] and the
   algebraic categories, it cannot be raised that way.

   ** Universes, measured

   Read with [Set Printing Universes] and [About], stdlib bounds omitted:

     AntichainTop@{i o h} : Category@{o h h}              (* i < o *)
     AntichainTop_not_WellPoweredAt@{i o h w s t} :
       WellPoweredAt@{w o s h t} None → False
       (* i < o, h < t, o <= s, h <= s, w <= i *)
     AntichainTop_not_WellPowered@{i o h w s t} :
       WellPowered@{o h w s t} AntichainTop@{i o h} → False
       (* i < o, h < t, o <= s, h <= s, w <= h, h <= i *)
     AntichainTop_op_not_CoWellPowered@{i o h w s t} :
       CoWellPowered@{o h w s t} (AntichainTop@{i o h}^op) → False
       (* the block of AntichainTop_not_WellPowered *)
     AntichainTop_trivial@{i o h t} : WellPoweredAt@{o o o h t} None
       (* i < o, h < t, h <= o *)
     AntichainTop_WellPoweredAt_up@{i o h s t} :
       WellPoweredAt@{h o s h t} None
       (* i < o, i < h, h < t, o <= s, h <= s *)

   ** Axioms

   None.  [Print Assumptions] reports every constant below closed under
   the global context; stdlib's Hurkens development is a theorem, not an
   axiom, and [retract_paradox] reports closed as well.

   ** Not delivered

   No non-well-powered category from the tree's concrete instances:
   [Sets] and [Grp] are well-powered one universe up (Instance/Sets/
   WellPowered.v, Instance/Grp/WellPowered.v; the other algebraic
   categories were not measured), and whether any of them is well-powered
   at the pin without a hypothesis is left open here.  The
   co-well-powered counterexample is only the dual one,
   [AntichainTop_op_not_CoWellPowered] at [AntichainTop^op], which is
   [AntichainTop_not_WellPowered] itself because [(AntichainTop^op)^op]
   converts to [AntichainTop]; no category that is well-powered but not
   co-well-powered is exhibited.  [AntichainTop] at [i < h] is not shown
   well-powered at objects other than [None]. *)

(** ** Hurkens' paradox over a retract *)

Lemma retract_paradox@{i +} (A : Type@{i}) (down : Type@{i} → A)
  (up : A → Type@{i}) (up_down : ∀ X : Type@{i}, up (down X) = X) : False.
Proof.
  Generic.paradox p.
  + exact Type@{i}.
  + exact (fun X => X).
  + cbn. exact (fun X F => ∀ x : X, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => ∀ x : A, F (up x)).
  + cbn. exact (fun _ f => fun x : A => f (up x)).
  + cbn. intros * f X.
    specialize (f (down X)).
    rewrite up_down in f.
    exact f.
  + exact A.
  + cbn. exact up.
  + cbn. exact (fun _ F => down (∀ x, up (F x))).
  + cbn. exact (fun _ F => down (∀ x, up (F x))).
  + cbn. exact (down False).
  + rewrite up_down in p.
    exact p.
  + cbn. easy.
  + cbn. intros ? f X.
    destruct (up_down X). cbn.
    reflexivity.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
Qed.

(** ** The antichain with a top *)

Section AntichainTop.

Universes i o h.
Constraint i < o.

Definition at_hom (a b : option Type@{i}) : Type@{h} :=
  match a, b with
  | Some A, Some B => A = B
  | Some _, None => Datatypes.unit
  | None, None => Datatypes.unit
  | None, Some _ => False
  end.

Definition at_id (a : option Type@{i}) : at_hom a a :=
  match a with Some A => eq_refl | None => tt end.

Definition at_comp {a b c : option Type@{i}} :
  at_hom b c → at_hom a b → at_hom a c :=
  match a, b, c return at_hom b c → at_hom a b → at_hom a c with
  | Some A, Some B, Some C => fun g f => eq_trans f g
  | Some A, Some B, None => fun _ _ => tt
  | Some A, None, None => fun _ _ => tt
  | Some A, None, Some C => fun g _ => match g with end
  | None, None, None => fun _ _ => tt
  | None, None, Some C => fun g _ => match g with end
  | None, Some B, _ => fun _ f => match f with end
  end.

(* Every two parallel arrows are equal. *)
Definition at_setoid (a b : option Type@{i}) : Setoid@{h h} (at_hom a b) :=
  {| equiv := fun _ _ => True ;
     setoid_equiv := {| Equivalence_Reflexive := fun _ => I ;
                        Equivalence_Symmetric := fun _ _ _ => I ;
                        Equivalence_Transitive := fun _ _ _ _ _ => I |} |}.

Definition AntichainTop : Category@{o h h} :=
  {| obj := option Type@{i} ;
     hom := at_hom ;
     homset := at_setoid ;
     id := at_id ;
     compose := @at_comp ;
     compose_respects := fun _ _ _ _ _ _ _ _ _ => I ;
     id_left := fun _ _ _ => I ;
     id_right := fun _ _ _ => I ;
     comp_assoc := fun _ _ _ _ _ _ _ => I ;
     comp_assoc_sym := fun _ _ _ _ _ _ _ => I |}.

(* The subobject of the top named by a type. *)
Definition at_sub (A : Type@{i}) : @SubObj AntichainTop None :=
  {| sub_dom := (Some A : obj[AntichainTop]) ;
     sub_mono := (tt : @hom AntichainTop (Some A) None) ;
     sub_is_monic := @Build_Monic AntichainTop (Some A) None
                       (tt : @hom AntichainTop (Some A) None)
                       (fun _ _ _ _ => I) |}.

(* Reading a type back off an index: the domain of the subobject it
   names. *)
Definition at_up (W : @WellPoweredAt AntichainTop None) (j : wp_index W) :
  Type@{i} :=
  match sub_dom (wp_to W j) with Some B => B | None => Datatypes.unit end.

(* The retract equation, from the domain isomorphism that exhaustiveness
   supplies: its forward arrow is [B = X] when the domain is [Some B], and
   inhabits [False] when it is [None]. *)
Lemma at_up_down (W : @WellPoweredAt AntichainTop None) (X : Type@{i}) :
  at_up W (wp_from W (at_sub X)) = X.
Proof.
  unfold at_up.
  destruct (wp_to_from W (at_sub X)) as [iso _].
  generalize (to iso). simpl.
  destruct (sub_dom (wp_to W (wp_from W (at_sub X)))) as [B|]; simpl.
  - intro e; exact e.
  - intro f; destruct f.
Qed.

End AntichainTop.

(** ** The refutation *)

(* No well-poweredness datum at the top object with index at or below
   [i]. *)
Theorem AntichainTop_not_WellPoweredAt@{i o h w s t |
    i < o, w <= i, h < t, o <= s, h <= s +}
  (W : @WellPoweredAt@{w o s h t} AntichainTop@{i o h} None) : False.
Proof.
  exact (retract_paradox (wp_index W) (fun X => wp_from W (at_sub X))
           (at_up W) (at_up_down W)).
Qed.

(* At the pin: with the homs at or below [i], [AntichainTop] is not
   well-powered. *)
Theorem AntichainTop_not_WellPowered@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (WP : WellPowered@{o h w s t} AntichainTop@{i o h}) : False.
Proof. exact (AntichainTop_not_WellPoweredAt@{i o h w s t} (WP None)). Qed.

(* Every hom type lies in [Prop] or [Set], so the homs may sit at
   [Set]. *)
Theorem AntichainTop_Set_not_WellPowered@{i o s t | i < o, Set < t, o <= s +}
  (WP : WellPowered@{o Set Set s t} AntichainTop@{i o Set}) : False.
Proof. exact (AntichainTop_not_WellPowered@{i o Set Set s t} WP). Qed.

(* The dual: [AntichainTop^op] is not co-well-powered, since
   [(AntichainTop^op)^op] is [AntichainTop] by conversion. *)
Theorem AntichainTop_op_not_CoWellPowered@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (CWP : CoWellPowered@{o h w s t} (AntichainTop@{i o h}^op)) : False.
Proof. exact (AntichainTop_not_WellPowered@{i o h w s t} CWP). Qed.

(* Positive control: one universe up, at the objects, the trivial datum
   exists, so the refutation measures size and nothing else. *)
Definition AntichainTop_trivial@{i o h t | i < o, h < t, h <= o +} :
  @WellPoweredAt@{o o o h t} AntichainTop@{i o h} None :=
  @wp_trivial@{o h o o t} AntichainTop@{i o h} None.

(* Second positive control: with the homs one universe above the types
   the objects name ([i < h]), the top object has a datum AT the pin,
   indexed by the objects themselves.  [at_name] names each object's
   subobject of [None]: the top one for [None], [at_sub A] for [Some A]. *)
Definition at_name@{i o h | i < o +} (a : option Type@{i}) :
  @SubObj AntichainTop@{i o h} None :=
  match a with
  | Some A => at_sub A
  | None => @sub_top AntichainTop@{i o h} None
  end.

Definition AntichainTop_WellPoweredAt_up@{i o h s t |
    i < o, i < h, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None.
Proof.
  unshelve refine {| wp_index := option Type@{i};
                     wp_to := at_name;
                     wp_from := fun u => sub_dom u |}.
  intros [d m Hm]; simpl.
  unshelve eexists.
  - destruct d as [A|]; simpl.
    + refine {| to := (eq_refl : @hom AntichainTop@{i o h} (Some A) (Some A));
                from := eq_refl; iso_to_from := I; iso_from_to := I |}.
    + refine {| to := (tt : @hom AntichainTop@{i o h} None None);
                from := tt; iso_to_from := I; iso_from_to := I |}.
  - exact I.
Defined.
