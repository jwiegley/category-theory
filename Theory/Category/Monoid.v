Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * A category is a monoid in composable pairs (Mac Lane, CWM I.2, Remark 1) *)

(* nLab:  https://ncatlab.org/nlab/show/internal+category
   nLab:  https://ncatlab.org/nlab/show/span
   Book:  Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          Section I.2, Remark 1 (printed p. 10)

   Immediately after giving the set-based definition of a category, Mac Lane
   observes that the definition says exactly one thing: a category is a MONOID
   for the product over its object set.  Spelled out, one is given two sets --
   a set O of objects and a set A of arrows -- together with two functions
   dom, cod : A -> O; the composable pairs form the fibred product

       A x_O A  =  { (g, f) in A x A | dom g = cod f },

   and a category structure on the graph (O, A, dom, cod) is precisely a unit

       e : O -> A          with  dom (e x) = cod (e x) = x

   and a multiplication

       m : A x_O A -> A    with  dom (m (g, f)) = dom f,
                                 cod (m (g, f)) = cod g

   that is associative and unital.  That is the germ of two later notions: a
   category internal to a category with pullbacks (replace "set" by "object of
   E" and the fibred product by a pullback), and a monad in the bicategory of
   spans, whose composition IS the fibred product above (nLab, "internal
   category"). *)

(* What this file is, and what it is not

   SCOPE.  This is the SET-LEVEL remark only -- the germ, not the theory.  A
   general internal category, in an arbitrary ambient category with pullbacks,
   is deliberately out of scope, as is the bicategory of spans, and so are
   functors/homomorphisms between the structures defined here.  The object
   sort O is a bare [Type] compared with Coq's strict [eq], NOT a setoid.
   That is faithful to the source: Mac Lane's remark is about the set-based
   presentation, where dom and cod are honest functions into a set of objects
   and the composability condition `dom g = cod f` is an equation between
   elements of that set.  The library's own [Category] does the same -- its
   [obj] is a [Type] and objects are compared by [eq] (see [dom_comp] and
   [cod_comp] in Theory/Category.v) -- so nothing new is being assumed here.
   The arrow sort, by contrast, IS a setoid: morphism comparisons are up to
   the chosen `≈`, as everywhere in this library.

   WHY THIS FILE LIVES HERE.  Theory/Category/ collects re-presentations of
   the [Category] class itself: Theory/Category/Raw.v strips the hom-setoid
   and the laws, Theory/Category/Semi.v drops the identities.  This file adds
   the two-sorted monoid presentation, and like its siblings its payload is a
   round trip with [Category].  It is NOT Construction/Span/Monoid.v: nothing
   here is a construction performed inside an ambient category, and
   Construction/Span/Category.v is about spans in a category, which is a
   different (and heavier) subject.

   WHAT IS NEARBY, AND HOW IT DIFFERS.

   - Structure/Monoid.v defines [MonoidObject]: a monoid in a MONOIDAL
     category, in the sense of Benabou.  That is a different theorem shape.
     There the tensor is a global bifunctor on one category; here the
     "tensor" is the fibred product A x_O A, which is the hom-composition of
     the bicategory of spans over O and is not a monoidal structure on any
     single category in the tree.  The two only coincide after one builds
     Span(Set), which this file does not.

   - Structure/Span.v defines [Span C := Roof ⟶ C]: the diagram SHAPE of a
     span, with no composition and no bicategory structure.  So the
     "monoid in spans" reading of Mac Lane's remark is not available there,
     and this file does not use it either -- it works with the fibred product
     directly.

   - Theory/Metacategory.v and Theory/Metacategory/ArrowsOnly.v formalize
     Mac Lane's OTHER re-presentation, the single-sorted "arrows-only"
     metacategory of CWM I.1, where objects are recovered as identity arrows
     and composition is partial.  This file is the two-sorted remark of I.2:
     objects are a primitive sort and composition is total on the fibred
     product.

   - Construction/Enriched.v (header) already records in prose that
     enrichment is not internalization, and Theory/DoubleCategory.v (header)
     that a double category is a category internal to Cat.  Neither file
     defines an internal category; this one supplies the set-level case those
     remarks point at.

   HONESTY ABOUT STRENGTH (proved below, see the numbered notes in situ).

   1. [Category_from_SpanMonoid] -- the monoid presentation yields a
      [Category] -- is unconditional and axiom-free.

   2. [Category_SpanMonoid] -- an ordinary [Category] yields a monoid
      structure on its graph of bundled arrows -- is proved under an explicit
      hypothesis [HomRigid C]: transport of a morphism along object-equality
      proofs does not depend on WHICH proofs are chosen.  [HomRigid] follows
      at once from UIP on the objects ([HomRigid_of_ObjUIP]), which in turn is
      axiom-free by Hedberg whenever object equality is decidable -- the
      discipline of Construction/Grothendieck/Strict.v and Instance/FinSet.v.
      It is a HYPOTHESIS here, never an [Axiom].  The obstruction is real and
      is isolated at [Category_SpanMonoid]'s [sm_mul_respects]: multiplying
      along two different proofs of the same composability equation composes
      with two transports of one arrow that differ by a loop at the
      INTERMEDIATE object, and the arrow equivalence's freedom to choose paths
      at the two OUTER objects cannot repair a discrepancy in the middle.
      In the set-based reading Mac Lane intends, O is a set and the question
      does not arise.

   3. Round trips.  Objects match definitionally in both directions
      ([SpanMonoid_roundtrip_obj], [Category_roundtrip_obj], both [eq_refl]).
      On arrows, one composite of each round trip is the identity on the nose
      and the other only up to the relevant `≈`; that is exactly what is
      proved below, and no more is claimed.  Starting from a [Category] the
      comparison assembles into an ISOMORPHISM in [Cat]
      ([Category_monoid_iso]), not merely an equivalence, because both
      functors are the identity on objects.

   UNIVERSES (measured, not asserted -- read off [About] with [Set Printing
   Universes]).

   - [Graph@{o a p}] carries gobj : Type@{o} and garr : Type@{a}
     independently, with p the setoid's proof level.

   - [Category_from_SpanMonoid@{o a} : Graph@{o a a} → … → Category@{o a a}]:
     objects stay at the graph's object level and homs at its arrow level.
     No level is raised.

   - [Category_Graph@{a p _ o} : Category@{o p p} → Graph@{o a p}] with the
     constraints o ≤ a and p ≤ a: the bundled-arrow sort ∃ x y, x ~> y sits
     at the maximum of the object and hom universes, and nowhere higher.
     There is no successor bump in either direction, and [Category_Graph] and
     [Category_SpanMonoid] impose NO relation between the object and hom
     levels of the category they start from.

   - Re-building a [Category] from that graph does impose one: because
     [Category_from_SpanMonoid] wants the graph's arrow and proof levels to
     coincide, [Rebuild_to], [Rebuild_from] and [Category_monoid_iso] all
     carry the constraint o ≤ h, the object universe below the hom universe.
     That is the price of asking the original and the rebuilt category to be
     objects of the SAME [Cat]. *)

(** ** Two-sorted graphs *)

(* A graph in Mac Lane's sense: an object sort [gobj], an arrow sort [garr]
   with a chosen equivalence, and the two boundary maps.  The two
   respectfulness fields say that `≈`-equivalent arrows have equal endpoints;
   they are what makes the arrow sort a graph over [gobj] rather than merely a
   setoid with two functions out of it, and they are exactly what the arrow
   round trip below needs. *)
Record Graph := {
  gobj : Type;                          (* the object sort O *)
  garr : Type;                          (* the arrow sort A *)
  garr_setoid : Setoid garr;            (* arrows are compared up to ≈ *)

  gdom : garr → gobj;                   (* dom : A → O *)
  gcod : garr → gobj;                   (* cod : A → O *)

  gdom_respects (a b : garr) :          (* ≈-equal arrows share a domain *)
    @equiv _ garr_setoid a b → gdom a = gdom b;
  gcod_respects (a b : garr) :          (* ≈-equal arrows share a codomain *)
    @equiv _ garr_setoid a b → gcod a = gcod b
}.

Arguments gdom {_} _.
Arguments gcod {_} _.
Arguments gdom_respects {_ _ _} _.
Arguments gcod_respects {_ _ _} _.

#[export] Existing Instance garr_setoid.

(** ** The composable pairs A ×_O A *)

(* The fibred product `A ×_O A = { (g, f) | dom g = cod f }`, kept as data (a
   record, i.e. a sigma) rather than as a subset: [cp_match] is a genuine
   inhabitant of an equality type, available for transport.  [cp_outer] and
   [cp_inner] are the two projections; in the composite `m (g, f)` the outer
   arrow g is the one applied last, matching the library's convention that
   `f ∘ g` runs g first. *)
Record Composable (G : Graph) := {
  cp_outer : garr G;                             (* g *)
  cp_inner : garr G;                             (* f *)
  cp_match : gdom cp_outer = gcod cp_inner       (* the composability equation *)
}.

Arguments cp_outer {_} _.
Arguments cp_inner {_} _.
Arguments cp_match {_} _.
Arguments Build_Composable {_} _ _ _.

(* Two composable pairs are identified when their two projections are.  This
   is the correct setoid on a pullback taken over a sort compared by strict
   equality: the third component is a proof of an equation in [gobj] and
   carries no further information about the pair.  Note that it is NOT `eq` on
   [Composable] -- see [Composable_ump_unique]. *)
Definition Composable_equiv {G : Graph} (p q : Composable G) : Type :=
  (cp_outer p ≈ cp_outer q) ∧ (cp_inner p ≈ cp_inner q).

Definition Composable_Setoid (G : Graph) : Setoid (Composable G).
Proof.
  refine {| equiv := @Composable_equiv G; setoid_equiv := _ |}.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct X; split; now symmetry.
  - destruct X, X0; split; etransitivity; eassumption.
Defined.

(* Both projections respect that equivalence, so each is a setoid map
   `A ×_O A → A`. *)
Lemma cp_outer_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_outer p ≈ cp_outer q.
Proof. now intros [H _]. Qed.

Lemma cp_inner_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_inner p ≈ cp_inner q.
Proof. now intros [_ H]. Qed.

(* The universal property, in the only form available without quotients: a
   pair of maps into [garr] whose boundaries agree factors through the
   composable pairs, on the nose on both projections. *)
Definition Composable_med {G : Graph} {X : Type}
           (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x))
           (x : X) : Composable G :=
  Build_Composable (u x) (v x) (H x).

Lemma Composable_med_outer {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_outer (Composable_med u v H x) = u x.
Proof. reflexivity. Qed.

Lemma Composable_med_inner {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_inner (Composable_med u v H x) = v x.
Proof. reflexivity. Qed.

(* Uniqueness, stated honestly: the mediating map is determined by its two
   projections UP TO [Composable_equiv], not up to `eq`.  Two mediating maps
   with the same projections can still differ in the proof component, and
   identifying those would need proof irrelevance or UIP on [gobj], neither of
   which is assumed.  Since [Composable_equiv] is the equivalence the
   multiplication is required to respect, this is the uniqueness that is
   actually used. *)
Lemma Composable_ump_unique {G : Graph} {X : Type} (k k' : X → Composable G) :
  (∀ x, cp_outer (k x) ≈ cp_outer (k' x)) →
  (∀ x, cp_inner (k x) ≈ cp_inner (k' x)) →
  ∀ x, Composable_equiv (k x) (k' x).
Proof. intros Ho Hi x; split; [ apply Ho | apply Hi ]. Qed.

(** ** The monoid structure on a graph *)

(* Mac Lane's unit and multiplication, with their boundary conditions and
   laws.  The multiplication is presented in curried form, taking the
   composability proof as an explicit argument, because that is how it is
   applied; [sm_pair_mul] below repackages it as the map `A ×_O A → A` of the
   remark and [sm_pair_mul_respects] shows the curried respectfulness field is
   exactly respectfulness for the pullback setoid.

   All laws are stated up to the arrow setoid's `≈`, and universally over the
   composability proofs.  Quantifying over the proofs is not a weakening: it
   is the content of "m is a function on A ×_O A", since two composable pairs
   with the same components are the same element of the pullback whatever
   proof witnesses their composability. *)
Record SpanMonoid (G : Graph) := {
  sm_unit : gobj G → garr G;                     (* e : O → A *)
  sm_unit_dom : ∀ x, gdom (sm_unit x) = x;       (* dom (e x) = x *)
  sm_unit_cod : ∀ x, gcod (sm_unit x) = x;       (* cod (e x) = x *)

  sm_mul (g f : garr G) : gdom g = gcod f → garr G;   (* m : A ×_O A → A *)

  sm_mul_dom : ∀ g f p, gdom (sm_mul g f p) = gdom f;  (* dom (m (g,f)) = dom f *)
  sm_mul_cod : ∀ g f p, gcod (sm_mul g f p) = gcod g;  (* cod (m (g,f)) = cod g *)

  (* m is a map out of the pullback setoid: it respects `≈` componentwise and
     does not depend on the composability witness. *)
  sm_mul_respects : ∀ g g' f f' p p',
    g ≈ g' → f ≈ f' → sm_mul g f p ≈ sm_mul g' f' p';

  sm_id_left  : ∀ f p, sm_mul (sm_unit (gcod f)) f p ≈ f;   (* e ∘ f = f *)
  sm_id_right : ∀ f p, sm_mul f (sm_unit (gdom f)) p ≈ f;   (* f ∘ e = f *)

  (* Associativity, in the orientation of [comp_assoc]. *)
  sm_assoc : ∀ h g f (p : gdom h = gcod g) (q : gdom g = gcod f)
               (pl : gdom (sm_mul h g p) = gcod f)
               (pr : gdom h = gcod (sm_mul g f q)),
    sm_mul h (sm_mul g f q) pr ≈ sm_mul (sm_mul h g p) f pl
}.

Arguments sm_unit {_} _ _.
Arguments sm_unit_dom {_} _ _.
Arguments sm_unit_cod {_} _ _.
Arguments sm_mul {_} _ _ _ _.
Arguments sm_mul_dom {_} _ _ _ _.
Arguments sm_mul_cod {_} _ _ _ _.
Arguments sm_mul_respects {_} _ {_ _ _ _} _ _ _ _.
Arguments sm_id_left {_} _ _ _.
Arguments sm_id_right {_} _ _ _.
Arguments sm_assoc {_} _ _ _ _ _ _ _ _.

(* The multiplication as a map out of the composable pairs, which is the shape
   in which Mac Lane states it. *)
Definition sm_pair_mul {G : Graph} (M : SpanMonoid G) (p : Composable G) : garr G :=
  sm_mul M (cp_outer p) (cp_inner p) (cp_match p).

(* ...and the curried respectfulness field is precisely respectfulness for the
   pullback setoid.  Both directions, so that neither presentation is
   privileged. *)
Lemma sm_pair_mul_respects {G : Graph} (M : SpanMonoid G) (p q : Composable G) :
  Composable_equiv p q → sm_pair_mul M p ≈ sm_pair_mul M q.
Proof.
  intros [Ho Hi]; unfold sm_pair_mul.
  now apply (sm_mul_respects M).
Qed.

Lemma sm_mul_of_pair {G : Graph} (M : SpanMonoid G)
      (m : Composable G → garr G)
      (Hm : ∀ p q, Composable_equiv p q → m p ≈ m q)
      (g g' f f' : garr G) (p : gdom g = gcod f) (p' : gdom g' = gcod f') :
  g ≈ g' → f ≈ f' → m (Build_Composable g f p) ≈ m (Build_Composable g' f' p').
Proof. intros Hg Hf; now apply Hm; split. Qed.

(** ** From the monoid presentation to a [Category] *)

(* The hom from x to y: an arrow together with proofs pinning its endpoints.
   The proofs are kept as data so that they may be used to build the
   composability witness; they are invisible to the hom-setoid, which compares
   only the underlying arrows. *)
Definition SpanArrow (G : Graph) (x y : gobj G) : Type :=
  { a : garr G & (gdom a = x) ∧ (gcod a = y) }.

Definition sa_arr {G : Graph} {x y : gobj G} (f : SpanArrow G x y) : garr G := `1 f.
Definition sa_dom {G : Graph} {x y : gobj G} (f : SpanArrow G x y)
  : gdom (sa_arr f) = x := fst (`2 f).
Definition sa_cod {G : Graph} {x y : gobj G} (f : SpanArrow G x y)
  : gcod (sa_arr f) = y := snd (`2 f).

(* The hom-setoid compares only the underlying arrows: the endpoint proofs are
   invisible to it. *)
Definition SpanArrow_equiv {G : Graph} {x y : gobj G}
           (f g : SpanArrow G x y) : Type := sa_arr f ≈ sa_arr g.

Definition SpanArrow_Setoid (G : Graph) (x y : gobj G)
  : Setoid (SpanArrow G x y).
Proof.
  refine {| equiv := @SpanArrow_equiv G x y; setoid_equiv := _ |}.
  unfold SpanArrow_equiv.
  constructor.
  - intros f; reflexivity.
  - intros f g H; symmetry; exact H.
  - intros f g h H1 H2; transitivity (sa_arr g); assumption.
Defined.

(* The identity at x is the unit e x, carrying its two boundary laws. *)
Definition span_id {G : Graph} (M : SpanMonoid G) (x : gobj G) : SpanArrow G x x :=
  (sm_unit M x; (sm_unit_dom M x, sm_unit_cod M x)).

(* Two homs that meet at y are composable in the graph: their endpoint proofs
   compose to the required equation `dom g = cod f`. *)
Definition span_match {G : Graph} {x y z : gobj G}
           (g : SpanArrow G y z) (f : SpanArrow G x y)
  : gdom (sa_arr g) = gcod (sa_arr f) :=
  eq_trans (sa_dom g) (eq_sym (sa_cod f)).

(* Composition is the monoid multiplication; the boundary laws of the
   multiplication supply the endpoint proofs of the result. *)
Definition span_compose {G : Graph} (M : SpanMonoid G) {x y z : gobj G}
           (g : SpanArrow G y z) (f : SpanArrow G x y) : SpanArrow G x z :=
  (sm_mul M (sa_arr g) (sa_arr f) (span_match g f);
    (eq_trans (sm_mul_dom M _ _ _) (sa_dom f),
     eq_trans (sm_mul_cod M _ _ _) (sa_cod g))).

(* NOTE 1.  Unconditional and axiom-free: no UIP, no rigidity, no hypothesis
   on [gobj] beyond its being a [Type].  Every law follows from the
   corresponding [SpanMonoid] field, the proof-independence of
   [sm_mul_respects] absorbing the fact that the composability witness built
   by [span_match] depends on the endpoint proofs carried by the homs, which
   the hom-setoid cannot see. *)
Definition Category_from_SpanMonoid {G : Graph} (M : SpanMonoid G) : Category.
Proof.
  unshelve refine (Build_Category' (SpanArrow G) (span_id M) (@span_compose G M)).
  - exact (SpanArrow_Setoid G).
  - proper.
    unfold span_compose, sa_arr; simpl.
    now apply (sm_mul_respects M).
  - intros x y f.
    unfold span_compose, span_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pc.
    now apply (sm_id_left M).
  - intros x y f.
    unfold span_compose, span_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pd.
    now apply (sm_id_right M).
  - intros x y z w f g h.
    unfold span_compose, sa_arr; simpl.
    apply (sm_assoc M).
Defined.

(** ** Bundled arrows, and transport along object equalities *)

(* The bundled-arrow sigma ∃ x y, x ~> y, as a record. *)
Record Arrow (C : Category) := {
  asrc : C;
  atgt : C;
  aarr : asrc ~> atgt
}.

Arguments asrc {_} _.
Arguments atgt {_} _.
Arguments aarr {_} _.
Arguments Build_Arrow {_} _ _ _.

(* The groupoid laws for [eq] that the transport pack needs.  Each is proved by
   [destruct] with both endpoints universally quantified, which is what makes
   it applicable later at a LOOP `e : x = x`, where [destruct] is unavailable.
   None of this is UIP: no two proofs of the same equation are identified. *)
Lemma eq_trans_id_l {A : Type} {x y : A} (e : x = y) : eq_trans eq_refl e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_id_r {A : Type} {x y : A} (e : x = y) : eq_trans e eq_refl = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_sym_l {A : Type} {x y : A} (e : x = y) :
  eq_trans (eq_sym e) e = eq_refl.
Proof. destruct e; reflexivity. Qed.

(* Transport of a morphism along equalities of its two endpoints.  Everything
   in this section is proved by [destruct]ing the equalities in their general
   form (both endpoints universally quantified), so none of it uses UIP. *)
Definition hom_transport {C : Category} {x x' y y' : C}
           (p : x = x') (q : y = y') (f : x ~> y) : x' ~> y' :=
  match p in (_ = X) return (X ~> y') with
  | eq_refl => match q in (_ = Y) return (x ~> Y) with
               | eq_refl => f
               end
  end.

(* Keep [simpl] from tearing the transports open into raw [match]es: every
   fact about them below is stated at the level of [hom_transport] itself. *)
Arguments hom_transport : simpl never.

#[export]
Instance hom_transport_respects {C : Category} {x x' y y' : C}
         (p : x = x') (q : y = y') :
  Proper (equiv ==> equiv) (hom_transport p q).
Proof. destruct p, q; repeat intro; assumption. Qed.

Lemma hom_transport_refl {C : Category} {x y : C} (f : x ~> y) :
  hom_transport eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

Lemma hom_transport_trans {C : Category} {x1 x2 x3 y1 y2 y3 : C}
      (p : x1 = x2) (p' : x2 = x3) (q : y1 = y2) (q' : y2 = y3) (f : x1 ~> y1) :
  hom_transport p' q' (hom_transport p q f)
    = hom_transport (eq_trans p p') (eq_trans q q') f.
Proof. destruct p, p', q, q'; reflexivity. Qed.

Lemma hom_transport_sym_inv {C : Category} {x x' y y' : C}
      (p : x = x') (q : y = y') (f : x ~> y) :
  hom_transport (eq_sym p) (eq_sym q) (hom_transport p q f) = f.
Proof. destruct p, q; reflexivity. Qed.

Lemma hom_transport_id {C : Category} {x x' : C} (u : x = x') :
  hom_transport u u (id[x]) = id[x'].
Proof. destruct u; reflexivity. Qed.

(* Transport of a composite splits into transport of the two outer endpoints;
   the shared middle object is untouched. *)
Lemma hom_transport_comp {C : Category} {x x' y z z' : C}
      (p : x = x') (r : z = z') (f : y ~> z) (g : x ~> y) :
  hom_transport p r (f ∘ g)
    = hom_transport eq_refl r f ∘ hom_transport p eq_refl g.
Proof. destruct p, r; reflexivity. Qed.

(* Transport at the middle object slides across a composite. *)
Lemma hom_transport_slide {C : Category} {w x x' y : C}
      (u : x = x') (f : x ~> y) (g : w ~> x) :
  f ∘ g = hom_transport u eq_refl f ∘ hom_transport eq_refl u g.
Proof. destruct u; reflexivity. Qed.

(** ** The graph of a category *)

(* Two bundled arrows are equivalent when there are equalities of their
   endpoints carrying one to the other up to `≈`.  The equalities are kept as
   data ([sigT], not [ex]) so the witnesses can be chosen and reused. *)
Definition Arrow_equiv {C : Category} (a b : Arrow C) : Type :=
  { p : asrc a = asrc b &
  { q : atgt a = atgt b & hom_transport p q (aarr a) ≈ aarr b }}.

Definition Arrow_Setoid (C : Category) : Setoid (Arrow C).
Proof.
  refine {| equiv := @Arrow_equiv C; setoid_equiv := _ |}.
  constructor; repeat intro.
  - exists eq_refl, eq_refl; reflexivity.
  - destruct X as [p [q H]].
    exists (eq_sym p), (eq_sym q).
    rewrite <- H, hom_transport_sym_inv.
    reflexivity.
  - destruct X as [p [q H]], X0 as [p' [q' H']].
    exists (eq_trans p p'), (eq_trans q q').
    rewrite <- hom_transport_trans, H.
    exact H'.
Defined.

Definition Category_Graph (C : Category) : Graph.
Proof.
  unshelve refine {| gobj := obj[C]
                   ; garr := Arrow C
                   ; garr_setoid := Arrow_Setoid C
                   ; gdom := @asrc C
                   ; gcod := @atgt C |}.
  - intros a b H; exact (`1 H).
  - intros a b H; exact (`1 (`2 H)).
Defined.

(** ** Rigidity: when transport does not see which proof it travelled along *)

(* NOTE 2.  The hypothesis under which an ordinary category yields a monoid on
   its graph of bundled arrows.  It says that transporting a morphism along
   object equalities depends only on the endpoints, not on the proofs.  This
   is implied by UIP on the objects, and holds trivially in the set-based
   reading Mac Lane intends.  It is never assumed as an [Axiom]: every result
   below that needs it takes it as an argument. *)
Definition HomRigid (C : Category) : Type :=
  ∀ (x x' y y' : C) (p p' : x = x') (q q' : y = y') (f : x ~> y),
    hom_transport p q f ≈ hom_transport p' q' f.

Definition ObjUIP (C : Category) : Type :=
  ∀ (x y : C) (p q : x = y), p = q.

(* UIP on objects gives rigidity.  [ObjUIP] is axiom-free for every category
   whose object equality is decidable, by Hedberg's argument -- the discipline
   already used in Instance/FinSet.v and Theory/Multicategory/Endomorphism.v. *)
Lemma HomRigid_of_ObjUIP {C : Category} : ObjUIP C → HomRigid C.
Proof.
  intros U x x' y y' p p' q q' f.
  rewrite (U _ _ p p'), (U _ _ q q').
  reflexivity.
Qed.

(* The calculation behind functoriality of the comparison [Rebuild_from]
   below, stated once over arbitrary transport data.  Composing two arrows
   after transporting their boundaries is the same as transporting the
   boundaries of their composite, provided one may ignore WHICH object paths
   were used -- which is what [HomRigid] grants.  The intermediate objects of
   the two composites differ (one meets at the domain of the outer arrow, the
   other at the shared object of the two homs), so [hom_transport_slide] is
   what carries the one to the other. *)
Lemma hom_transport_compose_compare {C : Category} (rigid : HomRigid C)
      {xa ya xb yb x y z : C} (α : xa ~> ya) (β : xb ~> yb)
      (da : xa = y) (ca : ya = z) (db : xb = x) (cb : yb = y)
      (P : xa = yb) (dc : xb = x) (cc : ya = z) :
  hom_transport dc cc (α ∘ hom_transport eq_refl (eq_sym P) β)
    ≈ hom_transport da ca α ∘ hom_transport db cb β.
Proof.
  rewrite hom_transport_comp, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r.
  rewrite (hom_transport_slide da (hom_transport eq_refl cc α)
                                  (hom_transport dc (eq_sym P) β)).
  rewrite !hom_transport_trans, !eq_trans_id_l, !eq_trans_id_r.
  now rewrite (rigid _ _ _ _ da da cc ca α),
              (rigid _ _ _ _ dc db (eq_trans (eq_sym P) da) cb β).
Qed.

(** ** From a [Category] to the monoid presentation *)

(* The unit is the identity arrow; the multiplication is composition, after
   transporting the inner arrow's codomain to the outer arrow's domain along
   the composability proof. *)
Definition arrow_unit {C : Category} (x : C) : Arrow C :=
  Build_Arrow x x (id[x]).

Definition arrow_mul {C : Category} (g f : Arrow C) (p : asrc g = atgt f)
  : Arrow C :=
  Build_Arrow (asrc f) (atgt g)
    (aarr g ∘ hom_transport eq_refl (eq_sym p) (aarr f)).

(* The two unit laws hold WITHOUT rigidity.  The trick is that the arrow
   equivalence lets one choose the object paths: the very proof [p] that has
   to be transported along is offered back as the witness, and the two
   transports cancel by [eq_trans_sym_l] / [hom_transport_id].  This is worth
   isolating, because it confines the obstruction of [arrow_mul_respects]
   below to that one law rather than to the correspondence at large. *)
Lemma arrow_mul_id_left {C : Category} (f : Arrow C) (p : atgt f = atgt f) :
  Arrow_equiv (arrow_mul (arrow_unit (atgt f)) f p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold Arrow_equiv, arrow_mul, arrow_unit; simpl.
  exists eq_refl, p.
  rewrite id_left, hom_transport_trans, eq_trans_sym_l, eq_trans_id_l.
  now rewrite hom_transport_refl.
Qed.

Lemma arrow_mul_id_right {C : Category} (f : Arrow C) (p : asrc f = asrc f) :
  Arrow_equiv (arrow_mul f (arrow_unit (asrc f)) p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold Arrow_equiv, arrow_mul, arrow_unit; simpl.
  exists (eq_sym p), eq_refl.
  rewrite hom_transport_comp, hom_transport_refl, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r, hom_transport_id.
  now rewrite id_right.
Qed.

(* NOTE 3.  Respectfulness of the multiplication is where the correspondence
   first meets [HomRigid], and it is the essential use.  Multiplying the same
   pair along two proofs p, p' of the same composability equation composes the
   outer arrow with two transports of the inner arrow that differ by a loop at
   the INTERMEDIATE object -- the object where the two arrows meet.  The arrow
   equivalence is free to pick paths at the source and the target of the
   composite, but neither is the intermediate object, so that freedom cannot
   repair the discrepancy.  (This is an account of why the proof needs the
   hypothesis, not a proof that the hypothesis is unavoidable: exhibiting a
   category in which the two composites genuinely differ would need a model in
   which [eq] on objects is not a proposition, which Coq alone cannot supply.)

   The exact tally over the four laws of [SpanMonoid], as proved here: the two
   unit laws are rigidity-free ([arrow_mul_id_left], [arrow_mul_id_right]);
   [arrow_mul_respects] and [arrow_mul_assoc] both use it, the latter because
   the record quantifies over ARBITRARY witnesses for the two derived
   composability equations, so the same intermediate-object discrepancy
   arises there too. *)
Lemma arrow_mul_respects {C : Category} (rigid : HomRigid C)
      (g g' f f' : Arrow C) (p : asrc g = atgt f) (p' : asrc g' = atgt f') :
  Arrow_equiv g g' → Arrow_equiv f f' →
  Arrow_equiv (arrow_mul g f p) (arrow_mul g' f' p').
Proof.
  destruct g as [xg yg φg], g' as [xg' yg' φg'],
           f as [xf yf φf], f' as [xf' yf' φf']; simpl in *.
  intros [pg [qg Hg]] [pf [qf Hf]]; simpl in *.
  destruct pg, qg, pf, qf.
  rewrite hom_transport_refl in Hg.
  rewrite hom_transport_refl in Hf.
  unfold Arrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl, Hg, Hf.
  now rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym p) (eq_sym p') φf').
Qed.

(* [pl] and [pr] repeat the types of [q] and [p] -- that is not redundancy but
   the reduced form of the record's [sm_assoc] hypotheses, since the boundary
   laws of [arrow_mul] hold by [eq_refl] here.  They are separate arguments
   precisely because they are separate PROOFS. *)
Lemma arrow_mul_assoc {C : Category} (rigid : HomRigid C)
      (h g f : Arrow C) (p : asrc h = atgt g) (q : asrc g = atgt f)
      (pl : asrc g = atgt f) (pr : asrc h = atgt g) :
  Arrow_equiv (arrow_mul h (arrow_mul g f q) pr)
              (arrow_mul (arrow_mul h g p) f pl).
Proof.
  destruct h as [xh yh χ], g as [xg yg γ], f as [xf yf φ]; simpl in *.
  unfold Arrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl.
  rewrite (rigid xf xf yg xh eq_refl eq_refl (eq_sym pr) (eq_sym p)
                 (γ ∘ hom_transport eq_refl (eq_sym q) φ)).
  rewrite hom_transport_comp, hom_transport_refl.
  rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym q) (eq_sym pl) φ).
  apply comp_assoc.
Qed.

Definition Category_SpanMonoid (C : Category) (rigid : HomRigid C)
  : SpanMonoid (Category_Graph C).
Proof.
  unshelve refine (Build_SpanMonoid (Category_Graph C)
                     (@arrow_unit C) _ _ (@arrow_mul C) _ _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros g g' f f' pp pp' Hg Hf.
    exact (arrow_mul_respects rigid g g' f f' pp pp' Hg Hf).
  - intros f pp; exact (arrow_mul_id_left f pp).
  - intros f pp; exact (arrow_mul_id_right f pp).
  - intros h g f pp qq pl pr.
    exact (arrow_mul_assoc rigid h g f pp qq pl pr).
Defined.

(** ** Round trip I: starting from the monoid presentation *)

Section MonoidRoundTrip.

Context {G : Graph}.
Context (M : SpanMonoid G).

Notation C' := (Category_from_SpanMonoid M).

(* Objects are literally the same type -- no comparison is needed. *)
Lemma SpanMonoid_roundtrip_obj : obj[C'] = gobj G.
Proof. reflexivity. Qed.

(* Two homs of the constructed category are identified exactly when their
   underlying arrows are: the endpoint proofs are invisible. *)
Lemma span_hom_equiv {x y : gobj G} (f g : x ~{C'}~> y) :
  sa_arr f ≈ sa_arr g → f ≈ g.
Proof. intro H; exact H. Qed.

(* The identity of the constructed category IS the unit of M ... *)
Lemma span_id_arr (x : gobj G) : sa_arr (@id C' x) = sm_unit M x.
Proof. reflexivity. Qed.

(* ... and its composition IS the multiplication of M, along ANY proof of the
   composability equation.  This is the sense in which the category structure
   and the monoid structure are the same structure. *)
Lemma span_compose_arr {x y z : gobj G} (g : y ~{C'}~> z) (f : x ~{C'}~> y)
      (pf : gdom (sa_arr g) = gcod (sa_arr f)) :
  sa_arr (g ∘ f) ≈ sm_mul M (sa_arr g) (sa_arr f) pf.
Proof. apply (sm_mul_respects M); reflexivity. Qed.

(* Now the graph round trip: bundle an arrow with the endpoints its own
   boundary maps assign to it, and unbundle by forgetting them again. *)
Definition sm_bundle (a : garr G) : garr (Category_Graph C') :=
  @Build_Arrow (Category_from_SpanMonoid M)
    (gdom a) (gcod a) (a; (eq_refl, eq_refl)).

Definition sm_unbundle (u : garr (Category_Graph C')) : garr G := sa_arr (aarr u).

Lemma sm_bundle_dom (a : garr G) : gdom (sm_bundle a) = gdom a.
Proof. reflexivity. Qed.

Lemma sm_bundle_cod (a : garr G) : gcod (sm_bundle a) = gcod a.
Proof. reflexivity. Qed.

Lemma sm_unbundle_dom (u : garr (Category_Graph C')) :
  gdom (sm_unbundle u) = gdom u.
Proof. exact (sa_dom (aarr u)). Qed.

Lemma sm_unbundle_cod (u : garr (Category_Graph C')) :
  gcod (sm_unbundle u) = gcod u.
Proof. exact (sa_cod (aarr u)). Qed.

(* Transporting a hom of C' along object equalities leaves the underlying
   arrow alone -- C' stores the endpoints separately from the arrow. *)
Lemma sa_arr_transport {x y x' y' : gobj G} (p : x = x') (q : y = y')
      (h : x ~{C'}~> y) :
  sa_arr (@hom_transport (Category_from_SpanMonoid M) x x' y y' p q h)
    = sa_arr h.
Proof. destruct p, q; reflexivity. Qed.

(* ONE composite of the round trip is the identity on the nose. *)
Lemma sm_unbundle_bundle (a : garr G) : sm_unbundle (sm_bundle a) = a.
Proof. reflexivity. Qed.

(* THE OTHER is the identity only up to `≈`, and that is exactly right: the
   bundled form re-derives the endpoints from [gdom] and [gcod], which agree
   with the recorded ones only propositionally.  No stronger statement holds
   here, and none is claimed. *)
Lemma sm_bundle_unbundle (u : garr (Category_Graph C')) :
  sm_bundle (sm_unbundle u) ≈ u.
Proof.
  destruct u as [x y h].
  exists (sa_dom h), (sa_cod h).
  apply span_hom_equiv.
  now rewrite sa_arr_transport.
Qed.

(* Both comparisons respect `≈`.  Together with the two composites above and
   the four boundary lemmas, that makes the pair a setoid isomorphism
   commuting with [gdom] and [gcod] -- a comparison of GRAPHS, not merely a
   bijection of the underlying types. *)
Lemma sm_bundle_respects (a b : garr G) : a ≈ b → sm_bundle a ≈ sm_bundle b.
Proof.
  intro H.
  exists (gdom_respects H), (gcod_respects H).
  apply span_hom_equiv.
  rewrite sa_arr_transport.
  exact H.
Qed.

Lemma sm_unbundle_respects (u v : garr (Category_Graph C')) :
  u ≈ v → sm_unbundle u ≈ sm_unbundle v.
Proof.
  intros [p [q H]]; unfold sm_unbundle.
  rewrite <- (sa_arr_transport p q (aarr u)).
  exact H.
Qed.

End MonoidRoundTrip.

(* Conjugating by identity isomorphisms does nothing.  This is the shape
   [Functor_Setoid]'s naturality condition takes when the two functors agree
   on objects definitionally, as both comparisons below do. *)
Lemma iso_id_conj {D : Category} {x y : D} (h : x ~> y) :
  from (@iso_id D y) ∘ h ∘ to (@iso_id D x) ≈ h.
Proof. simpl; now rewrite id_right, id_left. Qed.

(** ** Round trip II: starting from a [Category] *)

Section CategoryRoundTrip.

Context (C : Category).
Context (rigid : HomRigid C).

Notation Rebuilt := (Category_from_SpanMonoid (Category_SpanMonoid C rigid)).

(* Objects are literally the same type. *)
Lemma Category_roundtrip_obj : obj[Rebuilt] = obj[C].
Proof. reflexivity. Qed.

Definition rb_to {x y : C} (f : x ~> y) : x ~{Rebuilt}~> y :=
  (Build_Arrow x y f; (eq_refl, eq_refl)).

Definition rb_from {x y : C} (h : x ~{Rebuilt}~> y) : x ~> y :=
  @hom_transport C _ _ _ _ (sa_dom h) (sa_cod h) (aarr (sa_arr h)).

(* ONE composite is the identity on the nose. *)
Lemma rb_from_to {x y : C} (f : x ~> y) : rb_from (rb_to f) = f.
Proof. reflexivity. Qed.

(* THE OTHER only up to `≈`, for the same reason as before. *)
Lemma rb_to_from {x y : C} (h : x ~{Rebuilt}~> y) : rb_to (rb_from h) ≈ h.
Proof.
  apply (span_hom_equiv (Category_SpanMonoid C rigid)).
  exists (eq_sym (sa_dom h)), (eq_sym (sa_cod h)).
  unfold rb_to, rb_from; simpl.
  now rewrite hom_transport_sym_inv.
Qed.

(* The two comparisons are functors.  [Rebuild_to] is unconditional;
   [Rebuild_from] uses rigidity twice, once to see that it respects `≈` and
   once for functoriality, since it has to compare transports of one morphism
   along independently chosen object paths. *)
Definition Rebuild_to : C ⟶ Rebuilt.
Proof.
  unshelve refine (@Build_Functor C Rebuilt
                    (λ x : C, x)
                    (λ (x y : C) (f : x ~> y), rb_to f) _ _ _).
  - intros x y f g Hfg.
    apply (span_hom_equiv (Category_SpanMonoid C rigid)).
    exists eq_refl, eq_refl.
    now rewrite hom_transport_refl.
  - reflexivity.
  - reflexivity.
Defined.

Definition Rebuild_from : Rebuilt ⟶ C.
Proof.
  unshelve refine (@Build_Functor Rebuilt C
                    (λ x : Rebuilt, x)
                    (λ (x y : Rebuilt) (h : x ~{Rebuilt}~> y), rb_from h) _ _ _).
  - intros x y h h' Hh.
    destruct Hh as [pp [qq HH]].
    unfold rb_from.
    rewrite <- HH, hom_transport_trans.
    apply rigid.
  - reflexivity.
  - intros x y z h h'.
    unfold rb_from; simpl.
    apply (hom_transport_compose_compare rigid).
Defined.

(* NOTE 4.  The round trip is an ISOMORPHISM of categories in [Cat], not
   merely an equivalence: both object maps are the identity function on
   obj[C], so the comparison isomorphisms are identities and only the two hom
   round trips above are at issue.  Recall the strength of those: one leg is
   the identity on the nose ([rb_from_to]) and the other holds up to `≈`
   ([rb_to_from]).  Cat's hom-setoid identifies functors up to natural
   isomorphism, which is exactly enough to package that. *)
Definition Category_monoid_iso : C ≅[Cat] Rebuilt.
Proof.
  unshelve refine (@Build_Isomorphism Cat C Rebuilt Rebuild_to Rebuild_from _ _).
  - exists (λ x, iso_id).
    intros x y h.
    rewrite iso_id_conj.
    apply rb_to_from.
  - exists (λ x, iso_id).
    intros x y f.
    rewrite iso_id_conj.
    reflexivity.
Defined.

End CategoryRoundTrip.
