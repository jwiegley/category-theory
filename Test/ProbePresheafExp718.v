Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Closed.
Require Import Category.Instance.Two.

Open Scope category_scope.

Generalizable All Variables.

(** * Probe for issue #718 -- exponentials of presheaves *)

(* Every refutation command below was stripped ONE AT A TIME, compiled
   alone, and its WHOLE error read; the kind is read off the error TEXT.
   FORMABILITY = a "universe inconsistency: Cannot enforce ..." clause;
   CONVERSION = "cannot unify" between two terms of ONE type; TYPING = a
   plain "has type ... while it is expected to have type ..." with
   neither a cannot-unify nor a universe clause, or a bare
   "The type of this term is a product while it is expected to be ...".

   1 instrument check + 14 negatives:
     9 FORMABILITY  (1a, 1b, 1c, 1d, 2, 3, 4a, 4b, 4c)
     2 CONVERSION   (5, 6)
     3 TYPING       (7, 8, 9)

   The probe mirrors the target's FULL Require list -- a short prefix is
   what makes a negative pass for the wrong reason -- plus
   Instance/Fun/Closed.v and Instance/Two.v for the unconditional
   corollary, and Functor/Hom/Yoneda.v with
   Functor/Hom/Yoneda/Natural.v for the route measurement.  Note that a
   refutation command which does what it is supposed to do prints
   NOTHING, so each was stripped rather than trusted.

   GUARD COVERAGE, measured mechanically over the comment-stripped file:
   56 identifiers occur inside a refutation command and 49 of them also
   occur outside every one.  The seven exceptions are exhaustively the
   keyword [Fail] itself, the five [probe718_*] names DECLARED by a
   refutation command (which therefore never enter the environment), and
   the instrument's deliberately absent name.  No bound variable is among
   them.

   RENAME SIMULATION, 3/3.  Exactly three TARGET constants are named
   inside a refutation command -- [PshExp], [presheaf_exp_iso] and
   [Functor_Category_Closed] -- which is measured, not guessed: the same
   mechanical pass intersects the identifiers inside a refutation command
   with the 46 constants Instance/Fun/Exponential.v contributes and the
   four Instance/Fun/Closed.v gains, and returns those three.  Each was
   renamed in the TARGET ONLY -- whole-word, in both library files in
   place, their [.vo] rebuilt, and the files restored byte-exact
   afterwards -- and this file recompiled against the renamed library:
   every one broke at a [Check] line of the guard block below, and NONE
   inside a refutation command.  The guard
   block nevertheless names every constant of both library files that
   this probe could break on, not merely those three. *)

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

(* A deliberately absent name.  If this were to succeed, the refutation
   commands below would be measuring nothing. *)
Fail Check probe718_this_name_does_not_exist.

(* ------------------------------------------------------------------ *)
(** ** Guard controls -- every constant a negative names, named outside *)

Check @PshExp.
Check @PshExp_obj.
Check @PshExp_fmap.
Check @to_exp.
Check @to_exp_inner.
Check @from_exp.
Check @from_to_exp.
Check @to_from_exp.
Check @presheaf_exp_iso.
Check @to_exp_natural_X.
Check @from_exp_natural_X.
Check @Functor_Category_Closed.
Check @Functor_Category_Closed_cov.
Check @presheaf_terminal.
Check @presheaf_terminal_is_donor.
Check @exp_obj_is_display85.
Check @exponent_obj_is_PshExp.
Check @curry_is_to_exp.
Check @uncurry_is_from_exp.
Check @eval_is_at_identity.
Check @one_exp_iso.
Check @one_exp_to.
Check @one_exp_from.
Check @Psh2_Cart.
Check @Psh2_Closed.
Check @pq_point_distinct_unconditional.
Check @awodey_pointwise_not_exponential_unconditional.
Check @objectwise_candidate.
Check @PresheafP.
Check @PresheafQ.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Sets_Terminal.
Check @Curried_CoHom.
Check @Yoneda_Lemma.
Check @yoneda_natural_pre.
Check @YoNatPre.
Check @Closed.
Check @exponent_obj.
Check @exp_iso.
Check @curry'.
Check @uncurry'.
Check @eval'.
Check @first.
Check @split.
Check @product_obj.
Check @Fun.
Check @Opposite.
Check @Functor.
Check @Sets.
Check @Terminal.
Check @_2.
Check @_1.

(* ------------------------------------------------------------------ *)
(** ** Positive controls the file's claims rest on *)

(* The instance is found by typeclass resolution, at an arbitrary C. *)
Definition probe718_resolves (C : Category) : @Closed ([C^op, Sets]) _ := _.

(* And so is the terminal object of the same category. *)
Definition probe718_resolves_terminal (C : Category) :
  @Terminal ([C^op, Sets]) := _.

(* Awodey display (8.5), restated from OUTSIDE the target so that a
   rename in the target breaks this file. *)
Example probe718_display85 {C : Category} (P Q : C^op ⟶ Sets) (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]](
        @product_obj _ (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
          (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's data, read back from outside. *)
Example probe718_exponent {C : Category} (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

Example probe718_terminal (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(* Riehl's covariant reading is the same constant at the opposite
   category, on the nose. *)
Example probe718_cov (C : Category) :
  Functor_Category_Closed_cov C = Functor_Category_Closed (C^op) := eq_refl.

(* WHY [first] AND NOT [split _ id]: in the pointwise-cartesian presheaf
   category the identity factor of [first] leaves NO [fmap[P] id]
   residue, so the second component of a pair passes through untouched
   and the first is precomposition on the nose.  Both close by [eq_refl].
   WHY it reduces is not isolated and no claim is made about it. *)
Section FirstReduces.
Context {C : Category}.
Context (P : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).
Context (c c' : C) (h : c ~{C^op}~> c') (d : C^op).
Context (hp : fobj[@product_obj _ PshCart (Curried_CoHom C c') P] d).

Example probe718_first_snd :
  snd (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp) = snd hp
  := eq_refl.

Example probe718_first_fst :
  fst (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp)
    = op h ∘ fst hp
  := eq_refl.
End FirstReduces.

(* The two identifications that hold at [≈] and not at [eq_refl], stated
   from outside as the controls for negatives 5 and 6. *)
Example probe718_eval_weak {C : Category} (P Q : C^op ⟶ Sets) (c : C)
  (gy : fobj[@product_obj _
               (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
               (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy)
  := eval_is_at_identity P Q c gy.

(* The unconditional corollary of Instance/Fun/Closed.v, exercised from
   outside: the hypothesis that file's section F is stated over is now
   discharged by this issue's instance. *)
Check (awodey_pointwise_not_exponential_unconditional
         : @Isomorphism Sets
             ((@exponent_obj _ Psh2_Cart Psh2_Closed PresheafP PresheafQ) TwoY)
             objectwise_candidate -> False).
Check pq_point_distinct_unconditional.

(* ------------------------------------------------------------------ *)
(** ** The clone of the instance written WITHOUT universe binders *)

(* Byte-for-byte the shipped body, with the [@{o h so +}] binder list,
   the [Category@{o h h}] annotation on C and the explicit [Sets@{h so}]
   all removed.  Measured, [About] under [Set Printing Universes]:

     probe718_closed_unannotated@{u u0} :
       forall C : Category@{u0 u0 u0}, Closed@{u u0 u}

   -- object, hom AND proof identified, where the shipped instance reads
   [forall C : Category@{o h h}, Closed@{so h u}] with block
   [h < so, h < u, o <= h, o <= so].  Negative 4c uses this clone. *)
Program Definition probe718_closed_unannotated (C : Category) :
  @Closed ([C^op, Sets])
    (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(* ------------------------------------------------------------------ *)
(** ** (1) The smallness bound: C's objects at or below Sets' carriers *)

Section SmallC.
Universes coB chB oB soB.
Constraint oB < soB.
Constraint coB <= oB.
Context (Csm : Category@{coB chB chB}).
Context (Ps Qs : Csm^op ⟶ Sets@{oB soB}).

(* CONTROL: with C's objects bounded by [Sets]' carrier universe, the
   display-(8.5) object IS an object of that same [Sets], and so are the
   functor, the isomorphism and the instance. *)
Check ([[[Csm^op, Sets@{oB soB}]]](Ps, Qs) : obj[Sets@{oB soB}]).
Check (PshExp Ps Qs).
Check (Functor_Category_Closed Csm).
End SmallC.

Section BigC.
Universes coA chA oA soA.
Constraint oA < soA.
Constraint oA < coA.
Context (Cbig : Category@{coA chA chA}).
Context (Xb Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(* CONTROLS.  The presheaf category itself is perfectly formable at a C
   whose OBJECTS sit strictly ABOVE [Sets]' carrier universe -- so the
   bound the four negatives below pin is NOT the presheaf category's.
   Nor is it the terminal object's: [presheaf_terminal] ascribed at that
   very category is accepted.  (Why it is accepted -- the terminal
   presheaf is constant at [1] and so has no family indexed by C's
   objects in it -- is an explanation and not part of the measurement.)
   And [PshExp] READ ALONE is accepted too, landing in a LARGER [Sets]:
   measured, its printed result type is [Cbig^op ⟶ Sets@{u u0}] for
   fresh levels carrying [coA <= u]. *)
Check ([Cbig^op, Sets@{oA soA}]).
Check (presheaf_terminal Cbig : @Terminal ([Cbig^op, Sets@{oA soA}])).
Check (PshExp Pb Qb).

(* NEGATIVE 1a (FORMABILITY).  The display-(8.5) object is not an object
   of that same [Sets].  The stripped error ends "(universe
   inconsistency: Cannot enforce ... = oA because oA < coA <= ...)", and
   the bound [coA <= ...] in the message is exactly [Transform]'s
   [Type@{max(o1,p2)}]: a set of natural transformations is a family
   indexed by C's objects. *)
Fail Check ([[[Cbig^op, Sets@{oA soA}]]](Pb, Qb) : obj[Sets@{oA soA}]).

(* NEGATIVE 1b (FORMABILITY).  This is the discriminating one against
   the third control: [PshExp] is accepted only because it may choose a
   BIGGER target: forced to land in the same [Sets] its arguments take
   values in, it is refused. *)
Fail Check (PshExp Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(* NEGATIVE 1c (FORMABILITY).  [presheaf_exp_iso] is the constant that
   forces that collapse -- its statement puts the exponential on the
   right of a hom-setoid of the SAME presheaf category -- so it is
   refused here. *)
Fail Check (presheaf_exp_iso Xb Pb Qb).

(* NEGATIVE 1d (FORMABILITY).  And so, therefore, is the headline.  This
   is Awodey's "for any small category C", as a measurement. *)
Fail Check (Functor_Category_Closed Cbig).
End BigC.

(* ------------------------------------------------------------------ *)
(** ** (2)-(3) Hom = proof in the binder is the donors' doing *)

Section HomBelowProof.
Universes coC chC cpC oC soC.
Constraint chC < cpC.
Constraint oC < soC.
Context (Cu : Category@{coC chC cpC}).

(* CONTROLS accepted at levels where hom and proof are DECLARED APART:
   the hom type, an identity, and the bare functor type into [Sets].  So
   [Functor] is NOT a donor of [ch = cp]. *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (@Functor Cu Sets@{oC soC}).

(* NEGATIVE 2 (FORMABILITY).  [Opposite] forces [ch = cp] on its own; the
   stripped error ends "Cannot enforce cpC = chC because chC < cpC". *)
Fail Check (Cu^op).

(* NEGATIVE 3 (FORMABILITY).  So does [Fun], with NO [^op] anywhere in
   the command -- two INDEPENDENT donors, same error shape. *)
Fail Check ([Cu, Sets@{oC soC}]).
End HomBelowProof.

(* ------------------------------------------------------------------ *)
(** ** (4) The route, and the load-bearing annotation *)

Section Route.
Universes coD oD soD.
Constraint oD < soD.
Constraint coD < oD.
Context (Cr : Category@{coD oD oD}).
Context (Pr Qr Xr : Cr^op ⟶ Sets@{oD soD}).

(* C's hom level MUST be pinned at [Sets]' carrier level for this section
   to measure anything: with it left free the Yoneda constants silently
   instantiate their own [Sets], and a refusal, when one surfaces at all,
   fires at some other pinned argument rather than at the lemma's
   category.  [Fun] pins it
   anyway, which is why the context above writes [Category@{coD oD oD}].

   CONTROLS, all accepted at a C whose OBJECTS sit strictly BELOW its
   homs: the presheaf category itself, the [*Pre] Yoneda functor (whose
   object universe is free), the display-(8.5) object, and every headline
   of the target, the covariant reading [Functor_Category_Closed_cov]
   included (it is annotated like the instance for exactly this
   reason). *)
Check ([Cr^op, Sets@{oD soD}]).
Check (@YoNatPre Cr).
Check ([[[Cr^op, Sets@{oD soD}]]](Pr, Qr) : obj[Sets@{oD soD}]).
Check (PshExp Pr Qr).
Check (presheaf_exp_iso Xr Pr Qr).
Check (Functor_Category_Closed Cr).
Check (Functor_Category_Closed_cov Cr).

(* NEGATIVE 4a, 4b (FORMABILITY).  [Yoneda_Lemma] is declared over
   [Category@{u0 u0 u0}] and is refused at that very C, with
   "Cannot enforce oD = coD because coD < oD".  [yoneda_natural_pre] is
   refused identically.  So a route through the Yoneda LEMMA would have
   narrowed the theorem, which is the measured content of the header's
   route paragraph. *)
Fail Check (@Yoneda_Lemma Cr Pr).
Fail Check (yoneda_natural_pre Cr).

(* NEGATIVE 4c (FORMABILITY).  The UNANNOTATED clone of the instance is
   refused here too, with the same message, where the shipped
   [Functor_Category_Closed Cr] above is accepted.  That is what makes
   the universe annotations load-bearing rather than decorative --
   jointly: measured one at a time out of tree, either the binder on C
   or the [Sets@{h so}] annotation alone keeps the object universe free,
   and only their joint absence collapses it (the target's header
   records both variants). *)
Fail Check (probe718_closed_unannotated Cr).
End Route.

(* ------------------------------------------------------------------ *)
(** ** (5)-(6) The two conversion boundaries *)

Section Conv.
Context {C : Category}.
Context (P Q : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* CONTROLS: the two spellings of Awodey's [y h × 1_P] both elaborate,
   and at the SAME type -- so the refusal below is about conversion and
   not about formability. *)
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
           (@id ([C^op,Sets]) P)).

(* NEGATIVE 5 (CONVERSION).  They are not the same term: the stripped
   error is "cannot unify" between two terms of one type.  The target
   uses [first], whose reduction the two [probe718_first_*] controls
   above pin. *)
Fail Definition probe718_first_is_split (c c' : C) (h : c ~{C^op}~> c') :
  @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)
    = @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
        (@id ([C^op,Sets]) P)
  := eq_refl.

(* NEGATIVE 6 (CONVERSION).  Riehl's counit formula ev_c(γ,y) =
   γ_c(id_c,y) does NOT hold at [eq_refl]: [eval'] is [uncurry' id] and
   the identity of a functor category has component [fmap[−] id], so the
   value is γ_c(op id ∘ id, y) and the residue is one [id_left].  The
   [≈] form is [probe718_eval_weak] above. *)
Fail Example probe718_eval_strict (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    = (fst gy) c (id[c], snd gy)
  := eq_refl.
End Conv.

(* ------------------------------------------------------------------ *)
(** ** (7)-(9) Three typing boundaries *)

Section Typing.
Context {C : Category}.
Context (P Q X : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* CONTROL: the exponential IS a presheaf. *)
Check (PshExp P Q : C^op ⟶ Sets).

(* NEGATIVE 7 (TYPING).  It is not a COVARIANT functor: the stripped
   error is a plain "The term "PshExp P Q" has type "C^op ⟶ Sets" while
   it is expected to have type "C ⟶ Sets"", with no cannot-unify and no
   universe clause.  (The covariant reading of the THEOREM is
   [Functor_Category_Closed_cov], which is the instance at the opposite
   category, not this ascription.) *)
Fail Definition probe718_psh_covariant : C ⟶ Sets := PshExp P Q.

(* CONTROL: [exponent_obj y z] is z^y, so [PshExp P Q] is Q^P and the
   transposition names P as the factor and Q as the target. *)
Check (presheaf_exp_iso X P Q
         : @Isomorphism Sets
             ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
             ([[[C^op, Sets]]]( X, PshExp P Q ))).

(* NEGATIVE 8 (TYPING).  The two arguments of [PshExp] are not
   interchangeable: ascribing the same isomorphism with [PshExp Q P] on
   the right is a plain has-type mismatch. *)
Fail Definition probe718_swapped :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp Q P ))
  := presheaf_exp_iso X P Q.

(* NEGATIVE 9 (TYPING).  The objectwise assignment c |-> Q(c)^{P(c)} is a
   bare FAMILY of objects of [Sets] and not a presheaf: the stripped
   error is "The type of this term is a product while it is expected to
   be (C^op ⟶ Sets)".  READ THAT NARROWLY.  It pins the SHAPE of the
   objectwise data -- values with no action -- and is NOT a proof that no
   contravariant action on those values exists; Instance/Fun/Closed.v's
   header records that for the family at hand one does.  What refutes the
   objectwise formula is that file's
   [awodey_pointwise_not_exponential_unconditional], checked above, which
   shows the objectwise VALUE is already the wrong object. *)
Fail Definition probe718_objectwise : C^op ⟶ Sets :=
  fun c => @exponent_obj Sets Sets_Cartesian Sets_Closed
             (fobj[P] c) (fobj[Q] c).
End Typing.
