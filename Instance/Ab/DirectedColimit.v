(** * An abelian group is the colimit of its finitely generated subgroups

    Mac Lane, "Categories for the Working Mathematician" 2nd ed., Springer
    GTM 5 1998, §III.3 Exercise 7, printed p. 68 (`maclane:III.3:ex7`): "An
    abelian group A is the colimit of the (directed) diagram of its finitely
    generated subgroups, ordered by inclusion."  Cited by location.  The
    sentence in quotation marks is the issue catalog's paraphrase of the
    exercise, NOT a transcription: the printed text was not consulted while
    writing this file.

    WHAT IS DELIVERED.  For every [A : AbObject] there is an index category
    [FGSub A] of finitely generated subgroups of [A] ordered by inclusion, a
    diagram [FGDiagram A : FGSub A ⟶ Ab] carrying each to the corresponding
    object of [Ab], a cocone [FGCocone A] with apex [A] whose legs are the
    inclusions, and the theorem

        ab_fg_colimit A : IsColimitCocone (FGCocone A)

    saying that THAT cocone is universal.  [ab_fg_isacolimit] and
    [ab_fg_Colimit] repackage it at the apex-pinned and bundled levels.
    Directedness -- the parenthesis in Mac Lane's sentence -- is
    [FGSub_directed], and it is not decoration: it is exactly what
    [med_coherent] spends, and [med_coherent] is what every clause of the
    mediator's construction reduces to.

    THE HEADLINE IS CONE-LEVEL.  [IsColimitCocone] (Structure/Limit/
    Preservation.v:710) says every competing cocone factors through THIS
    cocone by a unique morphism compatible with THESE legs.  The apex-only
    [IsAColimit] (:545) pins the object [A] but takes its legs from
    whatever witness inhabits it, so on its own it does not say that the
    inclusions are the universal family; it is the weaker reading, and here
    it is DERIVED from the cone-level statement through
    [colimitcocone_isacolimit], never the other way round.  No separation
    between the two is proved in this file.

    [AbSubgroup] IS NEW, AND THE SURVEY BEHIND THAT HAS BEEN CORRECTED.
    Instance/Grp/Quotient.v:156's [Subgroup] is over [GrpObject], a flat
    record with [grp_unit]/[grp_mul]/[grp_inv] -- a different type from
    [AbObject], which layers [ab_neg] over Instance/CMon.v's [CMonObject]
    and so speaks [cmon_zero]/[cmon_plus].  Instance/Mod/Quotient.v:211's
    [Submodule] is over [RModObject] and carries a fifth field, [smod_smul],
    closure under a scalar action, which an abelian group has nothing to
    supply.  Those two have DIFFERENT shapes from each other -- membership
    plus four laws in both cases, but [Submodule]'s fourth is scalar-closure
    and it has NO negation field at all (Instance/Mod/Quotient.v:239 captions
    its negation lemma "THE FIFTH FIELD THAT IS NOT A FIELD").

    A THIRD RECORD EXISTS AND AN EARLIER DRAFT OF THIS HEADER MISSED IT.
    Instance/Ab/Character/Finite.v:624 declares [Record Subgroup (G :
    AbObject)] with [sg_mem]/[sg_resp]/[sg_zero]/[sg_add]/[sg_neg] -- over
    the RIGHT base type, in this same directory, with exactly the five
    fields [AbSubgroup] has -- plus a sixth, [sg_dec], demanding DECIDABLE
    membership; and it carries generated-subgroup machinery of its own
    ([Generated], :835).  So the ground an earlier draft gave, that no
    in-tree record is over [AbObject], was simply FALSE, and the survey it
    supported ("neither existing subobject record transfers") was wrong as
    stated.  The real ground for not reusing it is [sg_dec]: membership here
    is the inductively generated [InGen], which no constructive procedure
    decides, so that record cannot be instantiated by this development at
    all.  That is a good reason and it is the one that applies; the earlier
    draft made a different, false one.  The miss was avoidable -- the donor
    header quoted in the next paragraph names that very record TWICE, four
    lines above the line this file cites.  Read the relation to the existing
    tree precisely.  Instance/Mod/Quotient.v:136 already records that "the
    honest unifier is an [AbSubgroup] interface in Instance/Ab.v itself, of
    which [Submodule] would then be the module-level extension"; THIS FILE
    DOES NEITHER of those things.  The record is declared here rather than
    in Instance/Ab.v, and [Submodule] is untouched and is not exhibited as
    an extension of it.  That refactor stays open; what is settled is only
    that this development needed a subgroup notion and that the one in-tree
    record over [AbObject] demands a decidability field this one cannot
    supply.

    Membership is [Type]-valued for the reason Instance/Grp/Quotient.v's own
    header gives for [Subgroup]: the library's `≈` is [Type]-valued, so a
    [Prop]-valued membership could not be eliminated into a hom-setoid
    equation.  Here it is needed for something more basic still -- see the
    next paragraph.

    [Proset] CANNOT HOST *THIS* INDEX, WHICH IS WEAKER THAN IT SOUNDS AND
    IS NOT WHAT AN EARLIER DRAFT CLAIMED.  Instance/Proset.v:35 takes
    [{R : relation A}], and stdlib [relation A] is [A → A → Prop].  The
    inclusion used here is
    [FGHom A X Y := ∀ a, absub_mem (fg_sub X) a → absub_mem (fg_sub Y) a],
    which is [Type]-valued because [absub_mem] is; ascribing it as a
    [relation] is rejected with a universe inconsistency, "Cannot enforce
    ... <= Prop" (measured, against a positive control at the
    [inhabited]-squashed variant, which IS a [relation]).  That measurement
    is real and is pinned in Test/ProbeDirectedColimit330.v.

    WHAT IT DOES NOT SHOW.  An earlier draft of this header, and of the
    issue's own suggested route, concluded from it that "[Proset] is
    UNUSABLE for the index" and that the route is "IMPOSSIBLE, and that is
    MEASURED".  That is FALSE, and the refutation compiles.  The argument
    given covered only SQUASHING a [Type]-valued hom -- [inhabited (FGHom
    X Y)] -- which does need large elimination to get the witness back.  It
    never considered the obvious alternative: making MEMBERSHIP ITSELF
    [Prop]-valued.  Do that and [FGHom] is natively a [relation], nothing is
    squashed, and [fmap] never eliminates a [Prop] into a [Type] -- it only
    APPLIES a [Prop → Prop] function and packages the result in a [sigT],
    which is legal.  An audit ported this whole development that way and
    obtained [IsColimitCocone] for it, closed under the global context, with
    an [fmap] character-for-character the one below; the transport and the
    [Proset] application were then re-checked independently here.

    So the honest statement is: [Proset] cannot host the index GIVEN THIS
    FILE'S [Type]-VALUED MEMBERSHIP, which is a DESIGN CHOICE following
    Instance/Grp/Quotient.v (see the previous paragraph), not a necessity of
    the mathematics.  A [Prop]-valued variant is viable and is simply not
    what is built here.  Structure/Thin.v:57 records the [relation]-is-Prop
    fact from the other side -- "Coq's [relation] is Prop-valued while a hom
    lives in [Type]" -- and squashes with [inhabited] for its own reasons.

    [FGSub] is therefore built directly, COPYING (not reusing -- this file
    does not [Require] Instance/Proset.v at all) the one device that file
    supplies: the trivially-true hom-setoid
    [{| Setoid.equiv := fun _ _ => True |}] of Instance/Proset.v:41, which
    makes every categorical law free and makes [FGSub_Thin : Thin (FGSub A)]
    (Structure/Thin.v:76) a one-liner.  [FGSub_Thin] is PROVED but is
    consumed nowhere below -- including by the SCOPE paragraph's remark that
    duplicate presentations are harmless, which appeals to thinness in prose
    rather than through that lemma.

    SCOPE: OBJECTS CARRY A PRESENTATION, NOT JUST A SUBGROUP.  An object of
    [FGSub A] is a pair [{ S : AbSubgroup A & FinGen A S }], where [FinGen]
    supplies a LIST of generators together with mutual inclusion between
    [absub_mem S] and the generated [InGen].  Two different lists presenting
    the same subgroup therefore give two objects, and nothing in this file
    identifies them.  That is a deviation from Mac Lane's literal "poset of
    subgroups ordered by inclusion", and it is stated rather than hidden.
    What repairs it is that [FGSub A] is THIN: any two parallel inclusions
    are identified, so duplicate presentations are canonically isomorphic
    ([Ztwo_dup_iso] exhibits one such pair) and the colimit is unaffected:
    the universal property quantifies over cocones, and no competing cocone
    can tell duplicates apart, since [med_coherent] shows its legs agree on
    any two memberships of any two objects at ≈-equal elements.  That last
    clause is a theorem; "the colimit is unaffected" is the reading of it,
    and no comparison with a poset-indexed diagram is formalized -- there is
    no such diagram in this file.  The literal poset would need either a
    truncation of the presentation -- which would block extracting the
    generators, and the generators are exactly what directedness ([++] on
    lists) and the mediator (the cyclic subgroup on one element) use -- or
    proof irrelevance for [FinGen].  Neither is taken.  Note the file does
    NOT prove that two presentations of one subgroup are unequal; it proves
    they are isomorphic.

    THE CONSTRUCTION, AND WHERE THE WORK IS.  [mem_list a l] is [Type]-
    valued membership in a list up to `≈`.  [InGen A l] is the generated
    subgroup as an inductive family with five constructors -- a generator,
    zero, sum, negation, and ≈-saturation -- following the shape of
    Instance/Grp/Abelianization.v's [InCommutator], whose [inc_resp] is what
    makes the generated set ≈-saturated and is mirrored here as [ig_resp].
    [gen_sub A l] packages it as an [AbSubgroup] with all five fields
    literally the five constructors, so [fingen_gen]'s two legs are the
    identity function and [absub_mem (gen_sub A l) = InGen A l] holds by
    [eq_refl].

    The whole development rests on ONE induction over [InGen]: [gen_least],
    the least-subgroup property.  [gen_mono], the join inclusions, the
    presentation-duplication isomorphism, and the divisibility invariant
    used for the non-vacuity negatives are all instances of it, and the file
    contains exactly three [induction] TACTICS in total -- that one, and two
    on lists ([mem_list_app_l], [mem_list_app_r]).  Read that as the tactic
    count it is: [mem_list] is a [Fixpoint], so it is a fourth structural
    recursion that no [induction] appears in.

    Directedness is [++]: [fg_join X Y] is presented by the concatenation of
    the two generator lists, and [fg_join_left]/[fg_join_right] are the two
    inclusions.  [med_coherent] is the master lemma -- for any two objects,
    any two memberships and any two ≈-equal elements the cocone's legs
    agree -- proved by pushing both sides into the join and using the leg's
    own respectfulness.  The mediator [fg_med] is then the cocone's leg at
    the CYCLIC object [cyc a] (presented by the one-element list [a :: nil])
    applied to [a]; respectfulness, preservation of zero and preservation of
    addition are all applications of [med_coherent] (through [med_fun_at]),
    the last of them routed through the object presented by [a :: b :: nil].
    Uniqueness is immediate: any competitor commuting with the leg at
    [cyc a] already agrees with [fg_med] at [a].

    STRENGTHS, MEASURED RATHER THAN GUESSED.  These hold at [eq_refl]:
    [fg_cocone_apex] (the apex IS [A]), [fg_cocone_leg] (the leg IS the
    inclusion), [fg_med_value], [gen_sub_mem], [fg_sub_of_list],
    [fg_diagram_fmap_elem] (the diagram moves no element), and
    [Zjoin_gens].  [nu_transport] -- the cocone's coherence read pointwise
    -- is the donor lemma applied to a point, by conversion: its proof is a
    single [exact], with no rewriting.  The factorization triangle
    [fg_med_commutes] is `≈` and NOT Leibniz, and the cause is exactly the
    design above: the mediator evaluates the competing cocone at [cyc a]
    while the triangle's right-hand side evaluates it at [X], and those are
    different objects of the index, so the two values are related only
    through the cocone's coherence.  That rejection was measured, and the
    failure kind confirmed by stripping the [Fail] -- a genuine "cannot
    unify", not a name-resolution error.  No [Fail] probe is shipped in
    this file.

    NON-VACUITY, over ℤ.  Instance/Ab/Coproduct.v:264's [ab_Z] is
    [ring_ab Int_Ring], the additive group of Theory/Algebra/Rig.v's
    axiom-free integers; it is REUSED, no new group is built.  [Zmultiples
    d] is the subgroup of multiples of [d], and feeding it to [gen_least]
    gives [Zsingle_divides].  So the negatives come from an INVARIANT: they
    are not read off the generation, they are obtained by mapping the
    generated subgroup INTO [Zmultiples d] and contradicting divisibility.
    With it: [Ztwo_proper] and [Zthree_proper] show 2ℤ and 3ℤ are
    PROPER (1 lies in neither), [Zsub_incomparable] shows neither includes
    into the other -- so the join is not one of them in disguise -- and
    [Zjoin_one] shows 1 = 3 + (-2) does lie in the join, packaged with the
    two properness facts as [Zjoin_strictly_larger].  [Ztwo_dup_iso]
    exhibits the SCOPE paragraph's duplicate presentations.

    WHAT IS NOT DELIVERED, scoped to this file.

      * No general filtered- or directed-colimit theory.  There is none in
        tree (Instance/Sets/Chain.v:150 records the same absence), and
        nothing here is stated for a general filtered shape: [FGSub A] is
        one concrete index and [FGSub_directed] is a lemma about it, not an
        instance of a [Filtered] class, which does not exist.

      * No [Cocomplete Ab], and no other colimit in [Ab].  This is a single
        colimit identification, and no [Cocomplete]-typed constant anywhere
        in the tree mentions [Ab] (measured).

      * No analogue for non-abelian groups or for modules.  No argument
        below commutes two elements: commutativity enters exactly once, and
        only as a transported field ([AbSubgroupAb]'s [cmon_plus_comm] is
        [A]'s own, applied).  But the records and the category are [Ab]'s,
        and nothing is restated over [GrpObject] or [RModObject].

      * No [AbSubgroup] refactor: the record is not moved into
        Instance/Ab.v, [Submodule] is not made an extension of it, and
        Instance/Ab.v's [AbKernel] and [AbQuotient] are not rerouted
        through it.

      * No lattice of subgroups: no intersection, no sum of subgroups, no
        correspondence theorem, and no proof that [fg_join] is a JOIN in
        any order-theoretic sense (only that it receives both inclusions).

      * Nothing about which subgroups are finitely generated: [FinGen] is
        carried as data, and no group is shown to have, or to lack, a
        finite generating set.  In particular ℤ is not exhibited as an
        object of its own index.

      * No functoriality of [FGSub] or [FGDiagram] in [A], and no
        uniqueness-up-to-iso statement for the colimit beyond the one the
        universal property already gives. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Subgroups of an abelian group *)

(* Membership plus four laws, in the shape Instance/Grp/Quotient.v:156's
   [Subgroup] and Instance/Mod/Quotient.v:211's [Submodule] share.  It is
   [Type]-valued because the library's `≈` is, and because the diagram's
   [fmap] below must APPLY an inclusion to a membership witness -- see the
   header's paragraph on why [Proset] cannot host the index. *)
Record AbSubgroup (A : AbObject) := {
  absub_mem : carrier (cmon_setoid A) → Type;

  absub_resp : ∀ a b : carrier (cmon_setoid A),
    a ≈ b → absub_mem a → absub_mem b;
  absub_zero : absub_mem (cmon_zero A);
  absub_plus : ∀ a b : carrier (cmon_setoid A),
    absub_mem a → absub_mem b → absub_mem (cmon_plus A a b);
  absub_neg : ∀ a : carrier (cmon_setoid A),
    absub_mem a → absub_mem (ab_neg A a)
}.

Arguments absub_mem {A} _ _.
Arguments absub_resp {A} _ _ _ _ _.
Arguments absub_zero {A} _.
Arguments absub_plus {A} _ _ _ _ _.
Arguments absub_neg {A} _ _ _.

(** ** A subgroup as an object of Ab *)

(* The sigma carrier over membership, compared on elements only -- the shape
   Instance/Ab.v:299's [ab_ker_carrier] and Instance/Grp/Quotient.v:199's
   [sub_carrier] use, so a membership witness carries no equational weight
   and two witnesses of one element are already identified. *)
Section Subgroup.

Context {A : AbObject}.
Context (S : AbSubgroup A).

Definition absub_carrier : Type :=
  { a : carrier (cmon_setoid A) & absub_mem S a }.

Program Definition absub_setoid : Setoid absub_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Definition AbSubgroupAb : AbObject.
Proof using A S.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := absub_carrier
                         ; is_setoid := absub_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) (absub_zero S)
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q))
                    (absub_plus S _ _ (projT2 p) (projT2 q)) |};
    ab_neg := fun p =>
      existT _ (ab_neg A (projT1 p)) (absub_neg S _ (projT2 p))
  |}.
  - intros p p' Hp q q' Hq; simpl in *; now rewrite Hp, Hq.
  - intros a b c; simpl; apply cmon_plus_assoc.
  - intros a b; simpl; apply cmon_plus_comm.
  - intros a; simpl; apply cmon_plus_zero_l.
  - intros p q Hpq; simpl in *; now rewrite Hpq.
  - intros a; simpl; apply ab_neg_left.
Defined.

(* The inclusion: the first projection.  Respectfulness is the identity
   implication and both homomorphism laws hold on the nose; all three
   obligations are discharged by the ambient obligation tactic. *)
Program Definition absub_incl : AbSubgroupAb ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : absub_carrier => projT1 p |} |}.

End Subgroup.

Arguments absub_carrier {A} _.
Arguments AbSubgroupAb {A} _.
Arguments absub_incl {A} _.

(** * The subgroup generated by a finite list *)

(* [Type]-valued membership in a list, up to `≈'.  [Empty_set] is [Set], so
   it sits below every [Type@{i}] and needs no polymorphic empty type. *)
Fixpoint mem_list {A : AbObject} (a : carrier (cmon_setoid A))
  (l : list (carrier (cmon_setoid A))) : Type :=
  match l with
  | nil => Empty_set
  | x :: l' => ((x ≈ a) + mem_list a l')%type
  end.

Lemma mem_list_here {A : AbObject} (a : carrier (cmon_setoid A))
  (l : list (carrier (cmon_setoid A))) : mem_list a (a :: l).
Proof. exact (inl (reflexivity a)). Defined.

Lemma mem_list_app_l {A : AbObject} (x : carrier (cmon_setoid A))
  (l m : list (carrier (cmon_setoid A))) :
  mem_list x l → mem_list x (l ++ m).
Proof.
  induction l as [|y l IH]; simpl.
  - intro e; destruct e.
  - intros [Hy | Hl].
    + exact (inl Hy).
    + exact (inr (IH Hl)).
Defined.

Lemma mem_list_app_r {A : AbObject} (x : carrier (cmon_setoid A))
  (l m : list (carrier (cmon_setoid A))) :
  mem_list x m → mem_list x (l ++ m).
Proof.
  induction l as [|y l IH]; simpl.
  - exact (fun h => h).
  - exact (fun h => inr (IH h)).
Defined.

(* The generated subgroup, as an inductive family with five constructors:
   a generator, zero, sums, negations, and ≈-saturation.  The last is what
   Instance/Grp/Abelianization.v's [InCommutator] calls [inc_resp], and it
   is why [gen_sub] below needs no separate saturation argument. *)
Inductive InGen (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : carrier (cmon_setoid A) → Type :=
  | ig_gen (a : carrier (cmon_setoid A)) : mem_list a l → InGen a
  | ig_zero : InGen (cmon_zero A)
  | ig_plus (a b : carrier (cmon_setoid A)) :
      InGen a → InGen b → InGen (cmon_plus A a b)
  | ig_neg (a : carrier (cmon_setoid A)) :
      InGen a → InGen (ab_neg A a)
  | ig_resp (a b : carrier (cmon_setoid A)) :
      a ≈ b → InGen a → InGen b.

Arguments ig_gen {A l} _ _.
Arguments ig_zero {A l}.
Arguments ig_plus {A l} _ _ _ _.
Arguments ig_neg {A l} _ _.
Arguments ig_resp {A l} _ _ _ _.

(* All five fields ARE the five constructors, so [absub_mem (gen_sub A l)]
   is [InGen A l] on the nose (recorded below as [gen_sub_mem]). *)
Definition gen_sub (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : AbSubgroup A := {|
  absub_mem := @InGen A l;
  absub_resp := @ig_resp A l;
  absub_zero := @ig_zero A l;
  absub_plus := @ig_plus A l;
  absub_neg := @ig_neg A l
|}.

(* THE ONLY INDUCTION OVER [InGen] IN THIS FILE: the generated subgroup is
   the least one containing the generators.  Everything downstream that
   needs to say something about every member of a generated subgroup --
   [gen_mono], the join inclusions, the divisibility invariant used for the
   non-vacuity negatives -- is an instance of this. *)
Lemma gen_least (A : AbObject) (l : list (carrier (cmon_setoid A)))
  (S : AbSubgroup A) (H : ∀ x, mem_list x l → absub_mem S x) :
  ∀ a, InGen A l a → absub_mem S a.
Proof.
  intros a Ha.
  induction Ha as [a Hm | | a b _ IHa _ IHb | a _ IHa | a b Hab _ IHa].
  - exact (H a Hm).
  - exact (absub_zero S).
  - exact (absub_plus S _ _ IHa IHb).
  - exact (absub_neg S _ IHa).
  - exact (absub_resp S _ _ Hab IHa).
Defined.

Definition gen_mono (A : AbObject)
  (l m : list (carrier (cmon_setoid A)))
  (H : ∀ x, mem_list x l → InGen A m x) :
  ∀ a, InGen A l a → InGen A m a :=
  gen_least A l (gen_sub A m) H.

(** * Finitely generated subgroups, and the index category *)

(* A PRESENTATION of [S]: a finite list of generators, plus mutual
   inclusion between membership in [S] and membership in the subgroup that
   list generates.  Carrying the list (rather than truncating it) is what
   the header's SCOPE paragraph is about: it is what directedness and the
   mediator consume, and it is why two presentations of one subgroup give
   two objects of the index. *)
Record FinGen (A : AbObject) (S : AbSubgroup A) := {
  fg_list : list (carrier (cmon_setoid A));

  fg_into : ∀ a, absub_mem S a → InGen A fg_list a;
  fg_from : ∀ a, InGen A fg_list a → absub_mem S a
}.

Arguments fg_list {A S} _.
Arguments fg_into {A S} _ _ _.
Arguments fg_from {A S} _ _ _.

Definition FGObj (A : AbObject) : Type := { S : AbSubgroup A & FinGen A S }.

Definition fg_sub {A : AbObject} (X : FGObj A) : AbSubgroup A := projT1 X.

Definition fg_pres {A : AbObject} (X : FGObj A) : FinGen A (fg_sub X) :=
  projT2 X.

Definition fg_gens {A : AbObject} (X : FGObj A)
  : list (carrier (cmon_setoid A)) := fg_list (fg_pres X).

Definition FGHom (A : AbObject) (X Y : FGObj A) : Type :=
  ∀ a, absub_mem (fg_sub X) a → absub_mem (fg_sub Y) a.

(* The index category.  The hom-setoid is the trivially-true one of
   Instance/Proset.v:41, so every categorical law is free; [Proset] itself
   is unusable here because its homs must be [Prop]-valued (header). *)
Program Definition FGSub (A : AbObject) : Category := {|
  obj     := FGObj A;
  hom     := FGHom A;
  homset  := fun _ _ => {| Setoid.equiv := fun _ _ => True |};
  id      := fun _ _ p => p;
  compose := fun _ _ _ f g a p => f a (g a p)
|}.

(** ** Presented objects, and directedness by list concatenation *)

(* A list presents the subgroup it generates, with both legs the identity
   function -- the payoff of [gen_sub]'s fields being the constructors. *)
Definition fingen_gen (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : FinGen A (gen_sub A l) :=
  Build_FinGen A (gen_sub A l) l (fun _ p => p) (fun _ p => p).

Definition fg_of_list (A : AbObject) (l : list (carrier (cmon_setoid A)))
  : FGObj A := existT _ (gen_sub A l) (fingen_gen A l).

(* Directedness is list concatenation. *)
Definition fg_join {A : AbObject} (X Y : FGObj A) : FGObj A :=
  fg_of_list A (fg_gens X ++ fg_gens Y).

Definition fg_join_left {A : AbObject} (X Y : FGObj A)
  : X ~{FGSub A}~> fg_join X Y :=
  fun a p =>
    gen_mono A (fg_gens X) (fg_gens X ++ fg_gens Y)
      (fun x h => ig_gen x (mem_list_app_l x _ _ h))
      a (fg_into (fg_pres X) a p).

Definition fg_join_right {A : AbObject} (X Y : FGObj A)
  : Y ~{FGSub A}~> fg_join X Y :=
  fun a p =>
    gen_mono A (fg_gens Y) (fg_gens X ++ fg_gens Y)
      (fun x h => ig_gen x (mem_list_app_r x _ _ h))
      a (fg_into (fg_pres Y) a p).

(** The exercise's word "directed": any two objects of the index are jointly
    dominated by a third, namely the subgroup presented by the concatenation
    of their two lists of generators. *)
Lemma FGSub_directed {A : AbObject} (X Y : FGObj A) :
  { Z : FGSub A & ((X ~{FGSub A}~> Z) * (Y ~{FGSub A}~> Z))%type }.
Proof.
  exists (fg_join X Y).
  exact (fg_join_left X Y, fg_join_right X Y).
Defined.

(** * The diagram of finitely generated subgroups, and its cocone *)

(* The diagram.  Its arrow action retags a membership witness and leaves
   the underlying element alone ([fg_diagram_fmap_elem] below records that
   by [eq_refl]); since the subgroup carriers compare first projections,
   all six obligations -- the three of the [CMonHom] and the three functor
   laws -- are discharged by the ambient obligation tactic. *)
Program Definition FGDiagram (A : AbObject) : FGSub A ⟶ Ab := {|
  fobj := fun X => AbSubgroupAb (fg_sub X);
  fmap := fun X Y f =>
    {| cmon_map :=
         {| morphism := fun p => existT _ (projT1 p) (f (projT1 p) (projT2 p))
          |} |}
|}.

(* The cocone whose universality is the theorem: apex [A], legs the
   inclusions. *)
Program Definition FGCocone (A : AbObject) : Cocone (FGDiagram A) := {|
  vertex_obj := A;
  coneFrom   := {| vertex_map := fun X => absub_incl (fg_sub X) |}
|}.

(** * The mediating homomorphism out of A *)

Section Mediator.

Context {A : AbObject}.
Context (N : Cocone (FGDiagram A)).

(* The competing cocone's leg at [X], evaluated at an element of [A]
   together with a witness that it lies in [X]'s subgroup. *)
Definition nu_val (X : FGObj A) (a : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) : carrier (cmon_setoid vertex_obj[N]) :=
  cmon_map (cocone_inj N X) (existT _ a p).

Lemma nu_transport (X Y : FGObj A) (f : X ~{FGSub A}~> Y)
  (a : carrier (cmon_setoid A)) (p : absub_mem (fg_sub X) a) :
  nu_val Y a (f a p) ≈ nu_val X a p.
Proof using A N. exact (cocone_inj_coherence N f (existT _ a p)). Qed.

(** The master coherence lemma: the cocone's legs agree on any two
    memberships of any two objects, at ≈-equal elements.  Everything below is
    an application of it, and it is exactly where directedness is spent. *)
Lemma med_coherent (X Y : FGObj A) (a b : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) (q : absub_mem (fg_sub Y) b) (Hab : a ≈ b) :
  nu_val X a p ≈ nu_val Y b q.
Proof using A N.
  rewrite <- (nu_transport X (fg_join X Y) (fg_join_left X Y) a p).
  rewrite <- (nu_transport Y (fg_join X Y) (fg_join_right X Y) b q).
  unfold nu_val.
  apply proper_morphism; exact Hab.
Qed.

(** The cyclic subgroup on one element, and its distinguished member. *)

Definition cyc (a : carrier (cmon_setoid A)) : FGObj A :=
  fg_of_list A (a :: nil).

Definition cyc_mem (a : carrier (cmon_setoid A))
  : absub_mem (fg_sub (cyc a)) a := ig_gen a (mem_list_here a nil).

Definition med_fun (a : carrier (cmon_setoid A))
  : carrier (cmon_setoid vertex_obj[N]) := nu_val (cyc a) a (cyc_mem a).

Lemma med_fun_at (X : FGObj A) (a : carrier (cmon_setoid A))
  (p : absub_mem (fg_sub X) a) : med_fun a ≈ nu_val X a p.
Proof using A N.
  exact (med_coherent (cyc a) X a a (cyc_mem a) p (reflexivity a)).
Qed.

Lemma med_fun_respects : Proper (equiv ==> equiv) med_fun.
Proof using A N.
  intros a b Hab.
  exact (med_coherent (cyc a) (cyc b) a b (cyc_mem a) (cyc_mem b) Hab).
Qed.

Lemma med_fun_zero : med_fun (cmon_zero A) ≈ cmon_zero vertex_obj[N].
Proof using A N.
  rewrite (med_fun_at (cyc (cmon_zero A)) (cmon_zero A)
             (absub_zero (fg_sub (cyc (cmon_zero A))))).
  exact (cmon_map_zero (cocone_inj N (cyc (cmon_zero A)))).
Qed.

Lemma med_fun_plus (a b : carrier (cmon_setoid A)) :
  med_fun (cmon_plus A a b)
    ≈ cmon_plus vertex_obj[N] (med_fun a) (med_fun b).
Proof using A N.
  pose (Z := fg_of_list A (a :: b :: nil)).
  pose (pa := ig_gen (l := a :: b :: nil) a (mem_list_here a (b :: nil))).
  pose (pb := ig_gen (l := a :: b :: nil) b
                (inr (mem_list_here b nil))).
  rewrite (med_fun_at Z a pa), (med_fun_at Z b pb).
  rewrite (med_fun_at Z (cmon_plus A a b)
             (absub_plus (fg_sub Z) a b pa pb)).
  exact (cmon_map_plus (cocone_inj N Z) (existT _ a pa) (existT _ b pb)).
Qed.

(* The mediator: evaluate the competing cocone at the cyclic object on the
   element itself.  All three [CMonHom] fields are supplied by name, so no
   obligation is generated. *)
Program Definition fg_med : A ~{Ab}~> vertex_obj[N] := {|
  cmon_map := {| morphism := med_fun ; proper_morphism := med_fun_respects |};
  cmon_map_zero := med_fun_zero;
  cmon_map_plus := med_fun_plus
|}.

End Mediator.

(** * The theorem: A is the colimit of its finitely generated subgroups *)

(* The factorization triangle.  This is `≈' and not Leibniz: the left side
   evaluates [N] at [cyc a] and the right side at [X], and those are
   different objects of the index (header, STRENGTHS). *)
Lemma fg_med_commutes {A : AbObject} (N : Cocone (FGDiagram A))
  (X : FGSub A) :
  fg_med N ∘ cocone_inj (FGCocone A) X ≈ cocone_inj N X.
Proof.
  intro z; destruct z as [a p].
  exact (med_fun_at N X a p).
Qed.

Lemma fg_med_unique {A : AbObject} (N : Cocone (FGDiagram A))
  (v : A ~{Ab}~> vertex_obj[N])
  (Hv : ∀ X : FGSub A, v ∘ cocone_inj (FGCocone A) X ≈ cocone_inj N X) :
  fg_med N ≈ v.
Proof.
  intro a.
  symmetry.
  exact (Hv (cyc a) (existT _ a (cyc_mem a))).
Qed.

(* Mac Lane §III.3 Exercise 7: the inclusion cocone is universal. *)
Definition ab_fg_colimit (A : AbObject) : IsColimitCocone (FGCocone A).
Proof.
  intro M.
  unshelve refine {| unique_obj := fg_med M |}.
  - exact (fg_med_commutes M).
  - exact (fg_med_unique M).
Defined.

(* The apex-pinned and bundled readings, both derived from the cone-level
   statement rather than proved separately. *)
Definition ab_fg_isacolimit (A : AbObject) : IsAColimit (FGDiagram A) A :=
  colimitcocone_isacolimit (ab_fg_colimit A).

Definition ab_fg_Colimit (A : AbObject) : Colimit (FGDiagram A) :=
  limitcone_limit (FGCocone A) (ab_fg_colimit A).

(** ** Acceptance tests: what the pieces are, on the nose *)

Example fg_cocone_apex (A : AbObject) : vertex_obj[FGCocone A] = A := eq_refl.

Example fg_cocone_leg (A : AbObject) (X : FGSub A) :
  cocone_inj (FGCocone A) X = absub_incl (fg_sub X) := eq_refl.

Example fg_med_value (A : AbObject) (N : Cocone (FGDiagram A))
  (a : carrier (cmon_setoid A)) :
  cmon_map (fg_med N) a = nu_val N (cyc a) a (cyc_mem a) := eq_refl.

(** Membership in the generated subgroup IS the inductive family, which is
    what makes both legs of [fingen_gen] the identity function. *)
Example gen_sub_mem (A : AbObject) (l : list (carrier (cmon_setoid A))) :
  absub_mem (gen_sub A l) = InGen A l := eq_refl.

Example fg_sub_of_list (A : AbObject) (l : list (carrier (cmon_setoid A))) :
  fg_sub (fg_of_list A l) = gen_sub A l := eq_refl.

(** The diagram's arrow action moves no element: it retags a membership
    witness and leaves the underlying element alone. *)
Example fg_diagram_fmap_elem (A : AbObject) (X Y : FGSub A)
  (f : X ~{FGSub A}~> Y) (p : carrier (cmon_setoid (FGDiagram A X))) :
  projT1 (cmon_map (@fmap _ _ (FGDiagram A) X Y f) p) = projT1 p := eq_refl.

(** The index is thin, so any two parallel inclusions are identified. *)
Lemma FGSub_Thin (A : AbObject) : Thin (FGSub A).
Proof. intros X Y f g; exact I. Qed.

(** * Non-vacuity over the integers *)

(* [Instance/Ab/Coproduct.v]'s [ab_Z] is [ring_ab Int_Ring], the additive
   group of Theory/Algebra/Rig.v's axiom-free integers.  It is reused here;
   no new group is built, and [ab_Z]'s `≈` is Leibniz equality of [Z]
   ([Z_eqT]), which is what makes the computations below close by [eq_refl]. *)

(** ** The multiples of d, as a subgroup: the invariant that yields negatives *)

Lemma Zmult_resp (d : Z) : ∀ a b : carrier (cmon_setoid ab_Z),
  a ≈ b → Z.divide d a → Z.divide d b.
Proof.
  intros a b Hab H.
  assert (a = b) as E by exact Hab.
  now rewrite <- E.
Qed.

Lemma Zmult_zero (d : Z) : Z.divide d (cmon_zero ab_Z).
Proof. apply Z.divide_0_r. Qed.

Lemma Zmult_plus (d : Z) : ∀ a b : carrier (cmon_setoid ab_Z),
  Z.divide d a → Z.divide d b → Z.divide d (cmon_plus ab_Z a b).
Proof. intros a b Ha Hb; now apply Z.divide_add_r. Qed.

Lemma Zmult_neg (d : Z) : ∀ a : carrier (cmon_setoid ab_Z),
  Z.divide d a → Z.divide d (ab_neg ab_Z a).
Proof. intros a Ha; now apply Z.divide_opp_r. Qed.

Definition Zmultiples (d : Z) : AbSubgroup ab_Z :=
  Build_AbSubgroup ab_Z (fun a => Z.divide d a)
    (Zmult_resp d) (Zmult_zero d) (Zmult_plus d) (Zmult_neg d).

(** ** Two proper finitely generated subgroups, 2ℤ and 3ℤ *)

Definition Ztwo : FGObj ab_Z := fg_of_list ab_Z (2%Z :: nil).
Definition Zthree : FGObj ab_Z := fg_of_list ab_Z (3%Z :: nil).

Lemma Zsingle_divides (d : Z) :
  ∀ a, absub_mem (fg_sub (fg_of_list ab_Z (d :: nil))) a → Z.divide d a.
Proof.
  apply (gen_least ab_Z (d :: nil) (Zmultiples d)).
  intros x [Hx | e].
  - assert (d = x) as E by exact Hx.
    rewrite <- E.
    apply Z.divide_refl.
  - destruct e.
Qed.

Lemma Ztwo_proper : absub_mem (fg_sub Ztwo) 1%Z → False.
Proof.
  intro H.
  destruct (Zsingle_divides 2%Z 1%Z H) as [z Hz].
  lia.
Qed.

Lemma Zthree_proper : absub_mem (fg_sub Zthree) 1%Z → False.
Proof.
  intro H.
  destruct (Zsingle_divides 3%Z 1%Z H) as [z Hz].
  lia.
Qed.

(** ** Their join, which is strictly larger than either *)

Definition Zjoin : FGObj ab_Z := fg_join Ztwo Zthree.

Example Zjoin_gens : fg_gens Zjoin = (2%Z :: 3%Z :: nil) := eq_refl.

Lemma Zjoin_one : absub_mem (fg_sub Zjoin) 1%Z.
Proof.
  refine (ig_resp (cmon_plus ab_Z 3%Z (ab_neg ab_Z 2%Z)) 1%Z _ _).
  - reflexivity.
  - apply ig_plus.
    + apply ig_gen; simpl; right; left; reflexivity.
    + apply ig_neg; apply ig_gen; simpl; left; reflexivity.
Defined.

(** The two objects are INCOMPARABLE: neither includes into the other, so
    the join is not just one of them in disguise.  This is what makes
    directedness say something here. *)

Lemma Ztwo_two : absub_mem (fg_sub Ztwo) 2%Z.
Proof. apply ig_gen; simpl; left; reflexivity. Defined.

Lemma Zthree_three : absub_mem (fg_sub Zthree) 3%Z.
Proof. apply ig_gen; simpl; left; reflexivity. Defined.

Lemma Zsub_incomparable :
  (((Ztwo ~{FGSub ab_Z}~> Zthree) → False)
     * ((Zthree ~{FGSub ab_Z}~> Ztwo) → False))%type.
Proof.
  split.
  - intro f.
    destruct (Zsingle_divides 3%Z 2%Z (f 2%Z Ztwo_two)) as [z Hz]; lia.
  - intro f.
    destruct (Zsingle_divides 2%Z 3%Z (f 3%Z Zthree_three)) as [z Hz]; lia.
Qed.

(** So the index really is directed in a non-degenerate way: their join
    contains an element that lies in neither. *)
Lemma Zjoin_strictly_larger :
  (((absub_mem (fg_sub Ztwo) 1%Z → False)
      * (absub_mem (fg_sub Zthree) 1%Z → False))
     * absub_mem (fg_sub Zjoin) 1%Z)%type.
Proof. exact ((Ztwo_proper, Zthree_proper), Zjoin_one). Defined.

(** ** Two presentations of one subgroup are isomorphic in the index *)

Definition Ztwo_dup : FGObj ab_Z := fg_of_list ab_Z (2%Z :: 2%Z :: nil).

Definition Ztwo_incl_dup : Ztwo ~{FGSub ab_Z}~> Ztwo_dup.
Proof.
  refine (gen_mono ab_Z (2%Z :: nil) (2%Z :: 2%Z :: nil) _).
  intros x [Hx | e].
  - apply ig_gen; simpl; left; exact Hx.
  - destruct e.
Defined.

Definition Ztwo_dup_incl : Ztwo_dup ~{FGSub ab_Z}~> Ztwo.
Proof.
  refine (gen_mono ab_Z (2%Z :: 2%Z :: nil) (2%Z :: nil) _).
  intros x [Hx | [Hx | e]].
  - apply ig_gen; simpl; left; exact Hx.
  - apply ig_gen; simpl; left; exact Hx.
  - destruct e.
Defined.

Definition Ztwo_dup_iso : @Isomorphism (FGSub ab_Z) Ztwo Ztwo_dup := {|
  to          := Ztwo_incl_dup;
  from        := Ztwo_dup_incl;
  iso_to_from := I;
  iso_from_to := I
|}.
