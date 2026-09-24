Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Concrete.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(* Cogenerators of [Sets]: the object of truth values, under [Untruncate]
   or under [IEM]; the trivial large family, unconditionally; and why no
   SMALL one is unconditional

   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 127 (PDF p. 136), dualizes his Definition 4: a set Q of
   objects COGENERATES a category when, for every parallel pair
   h ≠ h' : a → b, some q ∈ Q carries g : b → q with g ∘ h ≠ g ∘ h'; his
   example is that any two-point set is a cogenerator of Set (catalogue
   item maclane:V.7:def5).  Riehl, "Category Theory in Context", 2nd ed.,
   Definition 4.7.7, printed p. 177 (PDF p. 197), names the same notion a
   coseparating set: a separating set of C^op.  The notion is the third
   hypothesis of the special initial-object theorem, Mac Lane §V.8
   Theorem 1, book p. 128 (PDF pp. 137–138), and Riehl Lemma 4.7.11,
   printed p. 177 (PDF pp. 197–198), whose in-tree form is
   Adjunction/SAFT/InitialObject.v.  This file supplies the premise at
   [Sets]; Instance/Sets/SpecialInitial.v runs the theorem on it.

   WHAT IS BUILT.  Everything is stated against Adjunction/SAFT.v's
   [Cogenerator] record, whose field [cog_separates] is the positive
   cancellation law (arrows agreeing after every test arrow are equal);
   Instance/Sets/Generator.v's header records why the positive form, and
   not Mac Lane's "≠" form, is the one that makes sense over a
   [Type]-valued hom-setoid with no decision procedure.  In the refusals
   quoted in this header, a universe the compile generated is written
   <1>, <2>, ..., numbered afresh in each quote in order of first
   appearance, as Test/ProbeSpecialInitial452.v writes them, so that the
   numerals carry identity and no serial number is a claim.

     - [Sets_Cogenerator_untruncate U]: a one-member family, the setoid
       [Powerset_Prop_truth] of Instance/Sets/Powerset.v ([Prop] under
       mutual implication).  The test arrow at a point [y0] is that file's
       [Powerset_Prop_singleton_pred y0], the truncated singleton
       b ↦ ‖y0 ≈ b‖, reused rather than rebuilt.  Given [f g : x ~> y]
       agreeing after every test arrow, the test at [f a] gives
       ‖f a ≈ f a‖ ↔ ‖f a ≈ g a‖; the left side holds by reflexivity, and
       [Untruncate] (Instance/Sets/Classifier/OneLevel.v) removes the
       truncation from the right.  The hypothesis is used exactly once.
     - [Sets_Cogenerator_IEM E]: a one-member family, the two-element
       setoid [BoolSetoid] of Instance/Sets/Classifier/OneLevel.v, with
       test arrow [sets_bool_char E y0] sending [b] to [ptrue] exactly
       when [E] decides [y0 ≈ b] positively.  This is Mac Lane's two-point
       set, literally.  [inl] and [inr] are written [Datatypes.inl] and
       [Datatypes.inr]: under an import list that includes
       Structure/Cocartesian.v, that file's [inl] shadows the constructor
       and the unqualified pattern is refused with "Unknown constructor:
       inl" (measured: this file's import list plus that one refuses a
       one-line [match] on [inl]/[inr], this file's list alone accepts
       it), so the qualified names keep the proof independent of what a
       later edit imports.
     - Under [IEM] the first is available too: Instance/Sets/Classifier/
       OneLevel.v's [untruncate_of_IEM] turns [E : IEM] into an
       [Untruncate], and [Sets_Cogenerator_untruncate (untruncate_of_IEM
       E)] is accepted in a scratch file, closed under the global context,
       with the first's [Set < o].  What [Sets_Cogenerator_IEM] adds is the
       literal two-point object and the absence of that bound: at
       [o := Set] the composite is refused, "The term
       "untruncate_of_IEM@{Set} E" has type "Untruncate@{Set}" while it is
       expected to have type "Untruncate@{<1>}" (universe inconsistency:
       Cannot enforce <1> = Set because Set < <1>)", while
       [Sets_Cogenerator_IEM E] is accepted there, which is what
       Instance/Sets/SpecialInitial.v's [sets_special_initial_IEM_at_Set]
       uses.
     - [Sets_Cogenerator_large]: the trivial LARGE family, with no
       hypothesis.  Its index is the type [SetoidObject@{o o}] of all
       objects and each object is its own member; for [f g : x ~> y],
       the test arrow [id] into the member [y] already separates, so
       arrows agreeing after every test agree outright.  It is not SMALL
       in the sense the special initial-object theorem needs: its index
       universe [c] lies strictly above [o] ([o < c], UNIVERSES below),
       while Adjunction/SAFT.v's [cogen_prod] identifies the index
       universe with the shape universe of its [Complete], which at
       Instance/Sets/Complete.v's [Sets_Complete] ([Complete@{o o o so}])
       is [o].  Test/ProbeSpecialInitial452.v's N13 and N14, labelled
       P_large_cog, pin the refusal.  With [o < c] and [Sets_Complete]
       ascribed [Complete@{o o o so}], N13
       ([p452_n13_large_prod_sets]), [cogen_prod Sets_Complete
       Sets_Cogenerator_large@{c o so}], is refused at the family: "The
       term "Sets_Cogenerator_large" has type "Cogenerator@{c so o}
       Sets@{o so}" while it is expected to have type "Cogenerator@{o so
       o} Sets@{o so}" (universe inconsistency: Cannot enforce c = o
       because o < c)"; N14 ([p452_n14_large_sio_sets]),
       [special_initial_object] there over the least subobject, is
       refused with the same text.  The controls: the constant itself at
       the universes below ([p452_large_cog]), and [cogen_prod] and
       [special_initial_object] at [Sets_Complete] with
       [Sets_Cogenerator_untruncate U] ([p452_small_prod_sets],
       [p452_small_sio_sets]).
     - [Sets_terminal_not_cogenerates]: the premise is a genuine
       condition at [Sets].  No family of copies of the terminal object
       cogenerates, whatever its index type, because every two arrows
       into the terminal object agree (Structure/Terminal.v's
       [one_unique]) while [Sets] has parallel arrows that differ
       (Theory/Concrete.v's [Sets_two_arrows]).  It is the counterpart of
       Instance/Sets/Generator.v's [Sets_empty_not_separates]: the empty
       set has no probes, the singleton has no discriminating tests.  It
       is a theorem about a well-typed hypothesis, not a refusal probe.

   All seven constants of this file are closed under the global context
   (Print Assumptions on each).  The three cogenerators are transparent
   ([Defined]), and the members of the two small ones read back by
   [eq_refl] ([sets_cogenerator_untruncate_obj],
   [sets_cogenerator_IEM_obj]).

   WHY THERE IS NO UNCONDITIONAL SMALL COGENERATOR AT [Sets] IN THIS
   TREE.  A measured refusal of one construction, not an impossibility
   proof: nothing here shows that [Sets] has no small [Cogenerator],
   small meaning indexed at [Sets_Complete]'s shape universe [o], where
   [cogen_prod] needs it; an unconditional LARGE one is
   [Sets_Cogenerator_large] above.  Classically the cogenerator is the
   object of truth values, and the test arrow at [y0] sends [b] to the
   truth value of [y0 ≈ b].  In this library [≈] is
   [Type]-valued (Lib/Setoid.v's [crelation]), so for an object [Y] of
   [Sets@{o so}] that truth value is a [Type@{o}].  Two ways of receiving
   it are pinned by Test/ProbeSpecialInitial452.v's N11 and N12, labelled
   P_type_truth, whose import list contains this file's and this file
   itself, each beside a positive control and each read by un-wrapping
   the refused command in its own copy of the WHOLE probe.  The object of
   truth values there is [Type@{l}] under [iffT], its equivalence proved
   in full ([p452_iff_setoid]), so that each refused command differs from
   its control in a universe only:

     (i) N11 ([p452_n11_truth_at]): [Type@{o}] under [iffT] as an object
         of [Sets@{o so}] is refused, because the carrier [Type@{o}]
         lives at [o+1]:
           "The term "{| carrier := Type; is_setoid := p452_iff_setoid |}"
            has type "SetoidObject" while it is expected to have type
            "obj[Sets]" (universe inconsistency: Cannot enforce <1> = o
            because o < <1>)."
         The control, the same setoid one level down on [Type@{l}] with
         [l < o] ([p452_truth_low]), is accepted.  The form first
         measured on #452, in a scratch probe that left the equivalence
         proof as a hole, is refused with the same bound; the probe pins
         the closed form, since a hole could make the command refuse for
         its own reason.
     (ii) N12 ([p452_n12_char_at]): into that lower setoid, the test
         arrow [fun b => @equiv _ (is_setoid Y) y0 b] is refused for an
         arbitrary object [Y] of [Sets@{o so}]:
           "The term "y0 ≈ b" has type "Type" while it is expected to have
            type "carrier {| carrier := Type; is_setoid := p452_iff_setoid
            |}" (universe inconsistency: Cannot enforce o <= l because
            l < o)."
         The control, for [Y : SetoidObject@{l l}] ([p452_char_low]), is
         accepted, and so is [Sets_Cogenerator_untruncate] at the same
         universes ([p452_cog_untruncate]).  Both refusals are universe
         inconsistencies, not missing instances.

   This is the size wall of Structure/Complete.v's size note met from the
   other side: a [Type]-valued relation on a carrier sits one universe
   above it.  [Prop] and [poly_bool] truth values fit at [o], but reading
   an equation back out of them is exactly what [Untruncate] (from ‖P‖ to
   P) or [IEM] (deciding P) provides, and the tree has neither
   unconditionally; Instance/Sets/Classifier/OneLevel.v proves [DecImage]
   equivalent to [IEM] and leaves open whether [Untruncate] gives [IEM];
   the converse is its [untruncate_of_IEM] (above).
   The position is the same as that of [Sets]' subobject classifier
   (that file's [Sets_Classifier U]) and of its well-poweredness at the
   pin (Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate U]).

   UNIVERSES, measured with [Set Printing Universes. About …], stdlib
   bounds left out:

     Sets_Cogenerator_untruncate@{c o so} :
       Untruncate@{o} → Cogenerator@{c so o} Sets@{o so}
       (* Set < o, o < so *)
     sets_bool_char@{o so} : ∀ {Y : SetoidObject@{o o}},
       IEM@{o} → Y → Y ~{ Sets@{o so} }~> BoolSetoid@{o}
       (* o < so *)
     Sets_Cogenerator_IEM@{c o so} :
       IEM@{o} → Cogenerator@{c so o} Sets@{o so}
       (* o < so *)
     Sets_Cogenerator_large@{c o so} :
       Cogenerator@{c so o} Sets@{o so}
       (* o < c, o < so *)

   The [Set < o] of the first is [Prop]'s: [Powerset_Prop_truth] has
   carrier [Prop : Type@{Set+1}], as Instance/Sets/Powerset.v records.
   The [IEM] cogenerator carries no [Set] bound, and
   Instance/Sets/SpecialInitial.v's [sets_special_initial_IEM_at_Set]
   takes it at [o := Set].  The index universe [c] is free in the two
   small cogenerators.  The binders name what minimization already
   delivered: an unannotated draft of this file measured
   [Sets_Cogenerator_untruncate@{u u0 u1} : Untruncate@{u} →
   Cogenerator@{u0 u1 u} Sets@{u u1}] with [Set < u] and [u < u1], the
   same shape; they are there so that later edits cannot drift it.  A
   consumer through Adjunction/SAFT.v's [cogen_prod] identifies [c] with
   the shape universe of its [Complete] (the collapse recorded in
   Adjunction/SAFT/InitialObject.v), which at Instance/Sets/Complete.v's
   [Sets_Complete] is [o].  [Sets_Cogenerator_large] bounds [c] strictly
   above [o], its index being the type of objects, and that is the
   identification refused above.

   PLACEMENT.  Instance/Sets/Generator.v, beside [Sets_Generator], would
   be the natural home, and the import cost rules it out.  Measured as the
   transitive closure over .Makefile.coq.d, counting the root: that file's
   closure is 23 modules, and adding the three imports these constants
   need beyond it (Adjunction/SAFT.v, Instance/Sets/Powerset.v,
   Instance/Sets/Classifier/OneLevel.v) raises it to 87.  This file's own
   closure is 85 modules.

   NOT DELIVERED.  No unconditional SMALL [Cogenerator] at [Sets] (above):
   the unconditional [Sets_Cogenerator_large] is large, and [cogen_prod]
   at [Sets_Complete] refuses it.  No [BoolSetoid] cogenerator from
   [Untruncate] alone: the test arrow above needs a decision, which
   truncation does not supply, and no other route was tried.  No
   comparison of the three cogenerators, and no claim that any is
   minimal.  No cogenerator of any other concrete category
   ([Grp], [Ab] with Q/Z, [FinSet]) in this file.  (Since #454 other
   files build some: Instance/Mod/Cogenerator.v's unconditional but
   large [RMod_Cogenerator_large], which [cogen_prod] refuses as this
   file's [Sets_Cogenerator_large] is refused, and its conditional
   [QZ_Cogenerator] at [Ab] and [QZ_injective_cogenerator] at [RMod R],
   whose premise is Mac Lane's Exercise 2(b) fact about Q/Z and is shown
   there to entail double-negation elimination; and Instance/Mod/
   WellPowered.v's unconditional [RModop_Cogenerator] at (RMod R)^op.
   None is at [Grp] or [FinSet].)  Structure/Generator/Dual.v's
   [cog_of_gen] already gives one at [Sets^op] from [Sets_Generator];
   Instance/Sets/SpecialInitial.v applies it. *)

(** ** Under [Untruncate]: truth values in [Prop] *)

Definition Sets_Cogenerator_untruncate@{c o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit
            (fun _ => Powerset_Prop_truth@{o}) _).
  intros x y f g H a.
  pose proof (H tt (Powerset_Prop_singleton_pred@{o} (f a)) a) as Ha.
  simpl in Ha.
  apply U.
  exact (proj1 Ha (Powerset_squash_intro@{o} (reflexivity (f a)))).
Defined.

Example sets_cogenerator_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  cog_obj (Sets_Cogenerator_untruncate U : Cogenerator Sets@{o so}) tt
    = Powerset_Prop_truth@{o} := eq_refl.

(** ** Under [IEM]: truth values in [poly_bool] *)

(* The characteristic map of the point [y0], decided by [E]. *)
Definition sets_bool_char@{o so +| o < so +} {Y : SetoidObject@{o o}}
  (E : IEM@{o}) (y0 : carrier Y) : Y ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun b => match E (@equiv _ (is_setoid Y) y0 b) with
                 | Datatypes.inl _ => ptrue@{o}
                 | Datatypes.inr _ => pfalse@{o}
                 end) _).
  intros b b' Hbb'; simpl.
  destruct (E (y0 ≈ b)) as [h|n], (E (y0 ≈ b')) as [h'|n']; try reflexivity.
  - destruct (n' (transitivity h Hbb')).
  - destruct (n (transitivity h' (symmetry Hbb'))).
Defined.

Definition Sets_Cogenerator_IEM@{c o so +| o < so +}
  (E : IEM@{o}) : Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} unit (fun _ => BoolSetoid@{o}) _).
  intros x y f g H a.
  pose proof (H tt (sets_bool_char E (f a)) a) as Ha.
  simpl in Ha.
  destruct (E (f a ≈ f a)) as [_|n]; [|destruct (n (reflexivity _))].
  destruct (E (f a ≈ g a)) as [h|_]; [exact h|discriminate Ha].
Defined.

Example sets_cogenerator_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  cog_obj (Sets_Cogenerator_IEM E : Cogenerator Sets@{o so}) tt
    = BoolSetoid@{o} := eq_refl.

(** ** Unconditionally, but large: every object tested by its identity *)

Definition Sets_Cogenerator_large@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so}.
Proof.
  refine (@Build_Cogenerator Sets@{o so} SetoidObject@{o o} (fun Y => Y) _).
  intros x y f g H a.
  exact (H y (@id Sets@{o so} y) a).
Defined.

(** ** The condition is genuine *)

(* A family of copies of the terminal object never cogenerates [Sets]:
   every two arrows into it agree, while the identity and negation of the
   two-element setoid differ. *)
Lemma Sets_terminal_not_cogenerates@{c o so +| o < so +} (I : Type@{c})
  (H : ∀ (x y : SetoidObject@{o o}) (f g : x ~{Sets@{o so}}~> y),
         (∀ (j : I)
            (k : y ~{Sets@{o so}}~> @terminal_obj Sets@{o so} Sets_Terminal),
            k ∘ f ≈ k ∘ g) → f ≈ g) : False.
Proof.
  apply Sets_two_arrows.
  apply H; intros j k.
  exact (@one_unique Sets@{o so} Sets_Terminal _ _ _).
Qed.
