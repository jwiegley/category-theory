Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(** * Connected categories, and the structure of a connected groupoid *)

(* nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book:      Riehl, "Category Theory in Context", §1.5, printed p. 35 (the
              running definition of a connected category) and Proposition
              1.5.13, printed pp. 35-36
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

   A category is CONNECTED when any two objects are joined by a finite
   zig-zag of morphisms: a chain

       x --> a_1 <-- a_2 --> ... <-- y

   in which each step points either forwards or backwards.  [ZigZag] below is
   that chain as an inductive type and [Connected C] is the statement that one
   exists between every pair of objects.

   COLLAPSE TO THE ONE-ARROW FORM.  In a groupoid the zig-zag form and the
   much simpler "there is an arrow x ~> y" agree, because a backward step can
   be inverted and the chain composed: [zigzag_hom] does exactly that, and
   [hom_zigzag] is the trivial converse.  Outside groupoids the two forms come
   apart, and the difference is not a technicality — [Roof] (the walking span
   RNeg <-- RZero --> RPos) is connected in the zig-zag sense while carrying
   no arrow whatever between RNeg and RPos.  That is proved below
   ([Roof_Connected], [Roof_no_arrow_neg_pos], [Roof_not_groupoid]), so the
   zig-zag form is not merely the more general definition on paper; it is
   strictly more general in this library, and it is the form that will be
   reusable for connected limits.

   ALTERNATION.  Riehl's chain alternates direction.  Requiring strict
   alternation costs nothing: [Fence] below is the strictly alternating form
   (each step a span x --> m <-- y), and [fence_zigzag]/[zigzag_fence] convert
   between the two in both directions — the interesting direction pads a lone
   step with an identity arrow.  So [Connected] is stated with the free chain
   without loss.

   Contents:

       ZigZag x y             a finite chain of arrows in either direction
       Connected C            a zig-zag between every pair of objects
       Fence x y              the strictly alternating (span-chain) form
       fence_zigzag, zigzag_fence   the two forms are interderivable
       zigzag_hom G           collapse of a zig-zag in a groupoid
       connected_arrow        Connected + IsGroupoid gives an arrow x ~> y
       arrow_connected        and conversely
       vertex_incl G x        B (hom(x,x)) ⟶ C, fully faithful
       connected_deloop_equiv Riehl Proposition 1.5.13
       deloop_equiv_connected its converse: the hypothesis is necessary
       connected_iff_deloop_equiv       the two directions together
       WideDeloop M A         a concrete connected groupoid with |A| objects
       Bool_Wide_structure    the structure theorem at a two-object groupoid
       Roof_Connected         a connected category that is NOT a groupoid
       Two_Discrete_no_deloop_equivalence  a groupoid where the conclusion
                                           is false, connectedness having
                                           been dropped *)

(* What the structure theorem says, and what it does not

   nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the
          London Mathematical Society 19, 1987

   Mac Lane's remark after §I.5 Definition 9, and Riehl's Proposition 1.5.13,
   say the same thing: a connected groupoid is determined, up to equivalence,
   by a single vertex group.  The proof is one line once the pieces are in
   place — the inclusion of the vertex group is fully faithful BY DEFINITION
   of hom(x, x), and essentially surjective BY connectedness, so the
   full-and-faithful-and-essentially-surjective criterion applies.  In this
   library that criterion is Theory/Equivalence/FullFaithful.v's
   [FF_ESO_Equivalence], and the whole of [connected_deloop_equiv] is the
   assembly of three small records.

   The content is in what "up to equivalence" does and does not mean.  The
   delooping has ONE object; a connected groupoid may have a proper class of
   them, all isomorphic.  So the theorem cannot be an isomorphism of
   categories, and the statement is not that a connected groupoid IS a group,
   but that no categorical property distinguishes it from one.  The witness
   below makes the gap concrete: [WideDeloop Bool_Xor_Grp bool] has two
   objects and eight arrows, [Deloop Bool_Xor_Grp] has one object and two
   arrows, and [connected_deloop_equiv] relates them.

   This is also the precise sense in which the fundamental groupoid of a
   path-connected space carries no more information than its fundamental
   group, while for a space with several path components — where the
   groupoid is not connected — it carries strictly more, which is Brown's
   argument for the groupoid-valued van Kampen theorem (Brown 1987).

   Connectedness is not merely a sufficient hypothesis.  It is equivalent to
   the conclusion ([connected_iff_deloop_equiv]), and the groupoid with two
   objects and only their identity arrows refutes the conclusion outright
   ([Two_Discrete_no_deloop_equivalence]) while satisfying every other
   hypothesis — it is a groupoid, and Structure/Groupoid.v's
   [conjugation_iso] applies to it just the same. *)

(** ** Zig-zags *)

(* A finite chain of arrows between x and y, each step pointing either
   forwards ([zz_fwd]) or backwards ([zz_bwd]).  This is Riehl's §1.5
   definition made into data: an inhabitant is an actual chain, not the mere
   assertion that one exists, which is what lets [zigzag_hom] compute the
   composite arrow in a groupoid.  It therefore lands in [Type] rather than
   [Prop], in the same split, choice-carrying style as
   [EssentiallySurjective] (Theory/Equivalence.v: "there exists a preimage"
   becomes "here is one"). *)
Inductive ZigZag {C : Category} : C → C → Type :=
  | zz_nil (x : C) : ZigZag x x
  | zz_fwd (x y z : C) (f : x ~> y) (s : ZigZag y z) : ZigZag x z
  | zz_bwd (x y z : C) (f : y ~> x) (s : ZigZag y z) : ZigZag x z.

Arguments zz_nil {C} x.
Arguments zz_fwd {C x y z} f s.
Arguments zz_bwd {C x y z} f s.

(* Riehl §1.5: C is connected when every pair of objects is joined by a
   zig-zag. *)
Definition Connected (C : Category) : Type := ∀ x y : C, ZigZag x y.

(* A single arrow is a one-step zig-zag, so the one-arrow form implies the
   zig-zag form in ANY category. *)
Definition hom_zigzag {C : Category} {x y : C} (f : x ~> y) : ZigZag x y :=
  zz_fwd f (zz_nil y).

Definition arrow_connected {C : Category} (H : ∀ x y : C, x ~> y) :
  Connected C := fun x y => hom_zigzag (H x y).

(* Zig-zags compose end to end, which is what makes "joined by a zig-zag" a
   transitive relation (with [zz_nil] for reflexivity).  It is not symmetric
   by this operation alone; symmetry needs the chain reversed, which is
   [zigzag_sym] below. *)
Fixpoint zigzag_trans {C : Category} {x y z : C}
  (s : ZigZag x y) : ZigZag y z → ZigZag x z :=
  match s in ZigZag a b return ZigZag b z → ZigZag a z with
  | zz_nil _     => fun t => t
  | zz_fwd f s'  => fun t => zz_fwd f (zigzag_trans s' t)
  | zz_bwd f s'  => fun t => zz_bwd f (zigzag_trans s' t)
  end.

(* Reversal, by turning every forward step into a backward one and vice
   versa.  Stated through [zigzag_trans] because a reversed chain is built
   from the tail outwards. *)
Fixpoint zigzag_sym {C : Category} {x y : C} (s : ZigZag x y) : ZigZag y x :=
  match s in ZigZag a b return ZigZag b a with
  | zz_nil w    => zz_nil w
  | zz_fwd f s' => zigzag_trans (zigzag_sym s') (zz_bwd f (zz_nil _))
  | zz_bwd f s' => zigzag_trans (zigzag_sym s') (zz_fwd f (zz_nil _))
  end.

(** ** The strictly alternating form *)

(* A fence: a chain of spans x --> m <-- y, each step alternating forwards
   then backwards by construction.  This is Riehl's "alternating directions"
   read literally. *)
Inductive Fence {C : Category} : C → C → Type :=
  | fence_nil (x : C) : Fence x x
  | fence_cons (x m y z : C) (f : x ~> m) (g : y ~> m) (t : Fence y z) :
      Fence x z.

Arguments fence_nil {C} x.
Arguments fence_cons {C x} m {y z} f g t.

(* A fence is a zig-zag: expand each span into a forward step followed by a
   backward one. *)
Fixpoint fence_zigzag {C : Category} {x y : C} (t : Fence x y) : ZigZag x y :=
  match t with
  | fence_nil w             => zz_nil w
  | fence_cons _ f g t'     => zz_fwd f (zz_bwd g (fence_zigzag t'))
  end.

(* And conversely — the direction that shows strict alternation is no
   restriction.  A lone forward step x ~> y is padded to the span
   x --> y <-- y with an identity, and a lone backward step to x --> x <-- y;
   so every chain becomes alternating at the cost of identity arrows only. *)
Fixpoint zigzag_fence {C : Category} {x y : C} (s : ZigZag x y) : Fence x y :=
  match s with
  | zz_nil w      => fence_nil w
  | zz_fwd f s'   => fence_cons _ f id (zigzag_fence s')
  | zz_bwd f s'   => fence_cons _ id f (zigzag_fence s')
  end.

(** ** Collapse to the one-arrow form in a groupoid *)

(* In a groupoid a zig-zag composes to a single arrow: forward steps compose
   as they stand and backward steps are inverted first.  Together with
   [hom_zigzag] this is the promised collapse — for a groupoid, "joined by a
   zig-zag" and "joined by an arrow" are inhabited together. *)
Fixpoint zigzag_hom {C : Category} (G : IsGroupoid C) {x y : C}
  (s : ZigZag x y) : x ~> y :=
  match s in ZigZag a b return a ~> b with
  | zz_nil w    => id[w]
  | zz_fwd f s' => zigzag_hom G s' ∘ f
  | zz_bwd f s' => zigzag_hom G s' ∘ ginv G f
  end.

Definition connected_arrow {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ~> y := zigzag_hom G (K x y).

(* And therefore any two objects of a connected groupoid are isomorphic —
   the form the structure theorem consumes. *)
Definition connected_iso {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ≅ y := giso G (connected_arrow G K x y).

(** ** The structure theorem *)

(* The inclusion of the vertex group at x: the delooping of hom(x, x) sent to
   the single object x, an arrow of the delooping being an endomorphism of x
   already.  The morphism action is the identity function, so respectfulness
   is immediate; and composition in [Deloop (vertex_group G x)] IS
   composition in C, and its identity IS id[x], so both functor laws are
   reflexivity of `≈`.  No obligation survives the ambient Program tactic,
   which is why no proof script follows.

   This is a fully faithful functor, not a subcategory: nothing here claims
   that its object map is a monomorphism onto a class of objects of C, only
   that the hom-map is bijective.  (Its object map is in fact injective, the
   source having a single object, but the useful statement is the one about
   homs.) *)
Program Definition vertex_incl {C : Category} (G : IsGroupoid C) (x : C) :
  Deloop (vertex_group G x) ⟶ C := {|
  fobj := fun _ => x;
  fmap := fun _ _ f => f
|}.

(* Fullness and faithfulness hold with NO hypothesis on C beyond the groupoid
   structure used to form the vertex group: the hom-map is the identity
   function on hom(x, x).  This is Riehl's "fully faithful by definition of
   the vertex group", and both records are correspondingly NEAR-TRIVIAL —
   the chosen preimage is the arrow itself and injectivity is the identity
   implication.  The mathematical work of the structure theorem is entirely
   in [vertex_incl_ESO] below; these two are recorded because
   [FF_ESO_Equivalence] consumes them, not because they are difficult.

   As with [conjugation] in Structure/Groupoid.v, each record below is built
   by applying its constructor to an explicit functor argument: the field
   types mention [fobj[?F]], which the identity hom-map does not determine by
   unification. *)
Definition vertex_incl_Full {C : Category} (G : IsGroupoid C) (x : C) :
  Full (vertex_incl G x) :=
  @Build_Full _ _ (vertex_incl G x)
    (fun _ _ g => g) (fun _ _ g => reflexivity g).

Definition vertex_incl_Faithful {C : Category} (G : IsGroupoid C) (x : C) :
  Faithful (vertex_incl G x) :=
  @Build_Faithful _ _ (vertex_incl G x) (fun _ _ _ _ H => H).

(* Essential surjectivity is where connectedness enters, and it is the ONLY
   place it enters: every object of C is isomorphic to x because a zig-zag
   from x to it collapses to an arrow, which the groupoid structure inverts. *)
Definition vertex_incl_ESO {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x : C) : EssentiallySurjective (vertex_incl G x) :=
  @Build_EssentiallySurjective _ _ (vertex_incl G x)
    (fun _ => ttt) (fun d => connected_iso G K x d).

(* Riehl, Proposition 1.5.13; Mac Lane §I.5, the remark after Definition 9.
   A connected groupoid is equivalent to the delooping of the vertex group at
   ANY of its objects — x is universally quantified, and no property of it is
   used. *)
Theorem connected_deloop_equiv {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : EquivalenceOfCategories (vertex_incl G x).
Proof.
  exact (@FF_ESO_Equivalence _ _ (vertex_incl G x)
           (vertex_incl_Full G x) (vertex_incl_Faithful G x)
           (vertex_incl_ESO G K x)).
Defined.

(* The quasi-inverse, extracted: it sends every object of C to the single
   object of the delooping, and an arrow to its conjugate into hom(x, x). *)
Definition connected_deloop_inverse {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : C ⟶ Deloop (vertex_group G x) :=
  @quasi_inverse _ _ _ (connected_deloop_equiv G K x).

(** ** Connectedness is necessary, not merely sufficient *)

(* [vertex_incl G x] sends EVERY object to x, so an essential-surjectivity
   witness for it is exactly a family of isomorphisms x ≅ d — the chosen
   preimage object carries no information, there being only one to choose. *)
Definition vertex_incl_ESO_iso {C : Category} (G : IsGroupoid C) (x : C)
  (E : EssentiallySurjective (vertex_incl G x)) (d : C) : x ≅ d :=
  @eso_iso _ _ (vertex_incl G x) E d.

(* Hence the converse of the structure theorem.  If the inclusion of the
   vertex group at some object is an equivalence, C is connected: every
   object is isomorphic to x, so any two are joined through x by a
   one-step chain.  Connectedness is therefore not a convenient hypothesis
   that happens to make the proof go through — it is equivalent to the
   conclusion. *)
Theorem deloop_equiv_connected {C : Category} (G : IsGroupoid C) (x : C)
  (E : EquivalenceOfCategories (vertex_incl G x)) : Connected C.
Proof.
  pose proof (Equivalence_EssSurj E) as Eso.
  intros y z.
  apply hom_zigzag.
  exact (to (vertex_incl_ESO_iso G x Eso z)
           ∘ from (vertex_incl_ESO_iso G x Eso y)).
Defined.

(* The two directions together.  For a groupoid with a chosen object, being
   connected and being equivalent to the delooping of the vertex group at
   that object are interderivable. *)
Theorem connected_iff_deloop_equiv {C : Category} (G : IsGroupoid C) (x : C) :
  Connected C ↔ EquivalenceOfCategories (vertex_incl G x).
Proof.
  split.
  - intro K.
    exact (connected_deloop_equiv G K x).
  - intro E.
    exact (deloop_equiv_connected G x E).
Defined.

(** ** A concrete connected groupoid *)

(* The delooping of M spread over a whole type of objects: same object set A,
   the elements of M as the arrows between EVERY pair, composition and
   identity as in [Deloop].  Every category law is again a monoid law by
   projection, exactly as in Construction/Deloop.v — the single object of
   [Deloop] plays no role in any of them, which is why widening it changes
   nothing.

   For A = [poly_unit] this is [Deloop] on the nose ([WideDeloop_Deloop]
   below).  For A with more than one element it is a genuinely larger
   category with the same vertex group at every object, and it is the witness
   that exercises the structure theorem beyond the trivial case. *)
Definition WideDeloop (M : MonObject) (A : Type) : Category := {|
  obj     := A;
  hom     := fun _ _ => carrier M;
  homset  := fun _ _ => is_setoid M;
  id      := fun _ => mon_unit;
  compose := fun _ _ _ f g => mon_op f g;

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(* The delooping is the one-object case, on the nose.  (An equality of
   CATEGORIES, which is far stronger than anything stated with `≈`; it holds
   by [eq_refl] because every field of [Deloop] is repeated verbatim above
   with [poly_unit] in place of A.) *)
Example WideDeloop_Deloop (M : MonObject) : WideDeloop M poly_unit = Deloop M
  := eq_refl.

(* Its endomorphism monoid at every object is M itself, on the nose — the
   [hom_monoid_Deloop] round trip of Construction/Deloop.v, widened. *)
Example WideDeloop_hom_monoid (M : MonObject) (A : Type) (a : A) :
  hom_monoid (WideDeloop M A) a = M := eq_refl.

(* If M is a group then [WideDeloop M A] is a groupoid: the inverse of an
   arrow is the inverse of the element, at any pair of objects. *)
Definition WideDeloop_IsGroupoid (G : GrpObject) (A : Type) :
  IsGroupoid (WideDeloop G A).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (WideDeloop G A) x y f (grp_inv f) _ _).
  - apply grp_inv_r.
  - apply grp_inv_l.
Defined.

(* And it is connected, by the one-step zig-zag carrying the unit of M —
   every hom-set is inhabited, whatever A is. *)
Definition WideDeloop_Connected (M : MonObject) (A : Type) :
  Connected (WideDeloop M A) :=
  @arrow_connected (WideDeloop M A) (fun _ _ => mon_unit).

(** ** The structure theorem, exercised *)

(* Two objects, eight arrows, vertex group Z/2 at each of them. *)
Definition Bool_Wide : Category := WideDeloop Bool_Xor_Grp bool.

Definition Bool_Wide_IsGroupoid : IsGroupoid Bool_Wide :=
  WideDeloop_IsGroupoid Bool_Xor_Grp bool.

Definition Bool_Wide_Connected : Connected Bool_Wide :=
  WideDeloop_Connected Bool_Xor_Grp bool.

(* Its vertex group at [true] really is Z/2: both data fields agree with
   [Bool_Xor_Grp] on the nose. *)
Example Bool_Wide_vertex_monoid :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid true) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(* The structure theorem at this groupoid: the two-object [Bool_Wide] is
   equivalent to the one-object delooping of its vertex group at [true].  The
   objects [true] and [false] are distinct, so the equivalence genuinely
   contracts the object set rather than being an identity in disguise. *)
Definition Bool_Wide_structure :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid true) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected true.

(* The same statement at the other object, to exhibit the "any one vertex
   group" clause with a second choice actually made. *)
Definition Bool_Wide_structure_false :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid false) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected false.

(* And the conjugation isomorphism between the two vertex groups, which is
   what makes the two statements above compatible. *)
Definition Bool_Wide_conjugation :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  conjugation_iso Bool_Wide_IsGroupoid
    (connected_arrow Bool_Wide_IsGroupoid Bool_Wide_Connected true false).

(** ** Connected does not mean "joined by an arrow" *)

(* [Roof] (Instance/Roof.v) is the walking span RNeg <-- RZero --> RPos.  It
   is connected: every pair of objects is joined by a zig-zag through RZero. *)
Definition Roof_Connected : Connected Roof.
Proof.
  intros x y.
  (* [destruct] replaces the objects by bare [RoofObj] constructors, which no
     longer carry the category in their type, so each chain names [Roof]
     explicitly. *)
  destruct x, y.
  - exact (@zz_nil Roof RNeg).
  - exact (@zz_bwd Roof RNeg RZero RZero ZeroNeg (@zz_nil Roof RZero)).
  - exact (@zz_bwd Roof RNeg RZero RPos ZeroNeg
             (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos))).
  - exact (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg)).
  - exact (@zz_nil Roof RZero).
  - exact (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos)).
  - exact (@zz_bwd Roof RPos RZero RNeg ZeroPos
             (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg))).
  - exact (@zz_bwd Roof RPos RZero RZero ZeroPos (@zz_nil Roof RZero)).
  - exact (@zz_nil Roof RPos).
Defined.

(* Yet there is no arrow at all from RNeg to RPos, so the one-arrow form of
   connectedness does NOT hold of [Roof].  This is what makes the zig-zag
   definition strictly more general, rather than merely more verbose.
   (Instance/Roof.v proves the emptiness of that hom-set as
   [RNeg_RPos_absurd]; it is restated here at the categorical hom so the
   claim is about [Roof] as a category.) *)
Theorem Roof_no_arrow_neg_pos : (RNeg ~{Roof}~> RPos) → False.
Proof. exact RNeg_RPos_absurd. Qed.

Corollary Roof_not_arrow_connected : (∀ x y : Roof, x ~> y) → False.
Proof. intro H. exact (Roof_no_arrow_neg_pos (H RNeg RPos)). Qed.

(* The two forms can come apart only outside groupoids, since [zigzag_hom]
   collapses them inside one.  [Roof] is indeed not a groupoid: the arrow
   ZeroNeg has no inverse, there being no arrow RNeg ~> RZero. *)
Theorem Roof_not_groupoid : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (RNeg_RZero_absurd (ginv G ZeroNeg)).
Qed.

(* And the link is not merely suggestive: the same conclusion follows from
   the two facts just proved, with no further inspection of [Roof].  Were
   [Roof] a groupoid, [zigzag_hom] would collapse the chain
   RNeg <-- RZero --> RPos into the arrow RNeg ~> RPos that
   [Roof_no_arrow_neg_pos] rules out.  So the collapse really is what the
   groupoid hypothesis buys, and its absence really is what separates the
   two forms here. *)
Corollary Roof_not_groupoid_via_collapse : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (Roof_no_arrow_neg_pos (zigzag_hom G (Roof_Connected RNeg RPos))).
Qed.

(** ** A groupoid that is not connected, and for which the theorem's
       conclusion is false *)

(* [Two_Discrete] (Instance/Two/Discrete.v) has two objects and only their
   identity arrows.  It is a groupoid — an identity is its own inverse — so
   it satisfies every hypothesis of the structure theorem except
   connectedness, and it shows that hypothesis cannot be dropped. *)
Definition Two_Discrete_IsGroupoid : IsGroupoid Two_Discrete.
Proof.
  intros x y f.
  destruct f.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDX TwoDX TwoDIdX TwoDIdX _ _);
      reflexivity.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDY TwoDY TwoDIdY TwoDIdY _ _);
      reflexivity.
Defined.

(* Every arrow of a discrete category has equal endpoints, so every zig-zag
   does too — a chain cannot leave the object it starts at. *)
Lemma TwoDHom_endpoints {x y : TwoDObj} (f : TwoDHom x y) : x = y.
Proof. now destruct f. Qed.

Lemma Two_Discrete_zigzag_endpoints {x y : Two_Discrete} (s : ZigZag x y) :
  x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact (TwoDHom_endpoints f) | exact IH ].
  - transitivity b; [ symmetry; exact (TwoDHom_endpoints f) | exact IH ].
Qed.

Theorem Two_Discrete_not_connected : Connected Two_Discrete → False.
Proof.
  intro K.
  pose proof (Two_Discrete_zigzag_endpoints (K TwoDX TwoDY)) as H.
  discriminate H.
Qed.

(* So the conclusion of the structure theorem is genuinely false here: the
   delooping of the vertex group at TwoDX is NOT equivalent to
   [Two_Discrete].  This is [deloop_equiv_connected] used in earnest — the
   necessity direction turns a missing hypothesis into a refutation. *)
Theorem Two_Discrete_no_deloop_equivalence :
  EquivalenceOfCategories (vertex_incl Two_Discrete_IsGroupoid TwoDX) → False.
Proof.
  intro E.
  exact (Two_Discrete_not_connected
           (deloop_equiv_connected Two_Discrete_IsGroupoid TwoDX E)).
Qed.
