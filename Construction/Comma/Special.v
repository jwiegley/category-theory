Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** * The comma of two constant functors is the discrete category on a hom-set *)

(* Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
              2nd ed., §II.6, pp. 46-47 [maclane:II.6:remark1]: the general
              comma category subsumes all the earlier cases; in the catalog's
              paraphrase (doc/plan/books/maclane/inventory/II.json, not the
              book's wording), taking S and T to be objects a and b (functors
              from 1), (T ↓ S) is the discrete category on the hom-set
              C(b, a) — the source of the historical notation (T, S) and the
              name "comma category".
   nLab:      https://ncatlab.org/nlab/show/comma+category
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Lawvere's original notation for the comma category was the pair (T, S),
   generalizing the hom-set notation C(b, a) that this file's theorem recovers:
   when T and S are objects — that is, functors out of the terminal category 1
   — the comma category (T, S) IS the hom-set C(b, a), regarded as a category
   with no non-trivial arrows.  The comma of the notation is where the name of
   the construction comes from, a name that Wikipedia records displeased even
   its author.  Mac Lane's remark is thus simultaneously the degenerate case of
   the definition and its etymology, which is why this file exists as a
   separate statement rather than as a parenthesis somewhere.

   ** Mac Lane's list of specializations, and where each is recorded

   The remark enumerates the specializations of (T ↓ S).  Every one of them is
   a theorem or a definition somewhere in this library; the point of this recap
   is that the list is now closed, with this file supplying the last entry.

     T = b : 1 ⟶ C, S arbitrary   the category of objects S-under b
                                  — [maclane:II.6:def3], the comma (=(b) ↓ S)
                                    as it stands; used pervasively, e.g. as the
                                    domain of Freyd's construction in
                                    Adjunction/GAFT.v and as
                                    [ElementsComma := =(SetsOne) ↓ K] in
                                    Construction/Elements.v:232.

     T = b, S = Id[C]              the coslice b/C
                                  — [Comma_Coslice], Construction/Slice.v:181.

     T = Id[C], S = a              the slice C/a
                                  — [Comma_Slice], Construction/Slice.v:140;
                                    and for a terminal a the slice is C itself,
                                    [Slice_Terminal] in
                                    Construction/Slice/Terminal.v.

     T = S = Id[C]                 the arrow category C^2
                                  — [Arrow := (Id[C] ↓ Id[C])],
                                    Construction/Arrow.v:131.

     T = b, S = a  (both objects)  the discrete category on C(b, a)
                                  — THIS FILE, [Comma_Discrete_Hom].

   Two neighbouring readings are worth naming because they are easy to confuse
   with the last row.  First, the arrow category has a functor-category
   presentation, [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C] in Theory/Shapes.v,
   over the walking arrow [_2]; that is the C^2 of Mac Lane's notation made
   literal, and it is related to but not consumed by anything here.  Second,
   Construction/Product/Comma.v proves [Comma_Product]: when the two functors
   have terminal CODOMAIN the comma is the product category C ∏ D.  That file's
   header already contrasts itself with the present case — "this is distinct
   from the special case in which the *domains* of the two functors are 1,
   where the comma category is instead the discrete category of morphisms
   between the two selected objects" — and states it in prose only.  This file
   is the promotion of those lines (Construction/Product/Comma.v:32-35) to a
   theorem.

   ** THE PACKAGING CHOICE: setoid-discrete, not [DiscreteCat]

   "The discrete category on the hom-set C(b, a)" has to be read carefully in a
   setoid-based library, and the reading is forced by what the comma category
   actually is.  Unfold (=(b) ↓ =(a)):

   - an object is a triple (u, v, h) with u, v the unique object of 1 and
     h : b ~> a, so objects ARE the hom-set, up to two units of padding;

   - a morphism (u, v, h) ~> (u', v', h') is a pair of morphisms of 1 — again
     units, carrying no information — subject to the commuting square
     h' ∘ fmap[=(b)] _ ≈ fmap[=(a)] _ ∘ h.  Both constant functors send every
     arrow to an identity, so the square says h' ∘ id ≈ id ∘ h, i.e. h ≈ h'.

   So a morphism of the comma category is a WITNESS OF `h ≈ h'` in the
   hom-setoid, and there is one exactly when h ≈ h'.  The matching "discrete
   category" is therefore the one whose objects are the carrier of a setoid and
   whose homs are that setoid's own equivalence — [DiscreteSetoidCat] below.

   Instance/Discrete.v's [DiscreteCat A] is a DIFFERENT category: its homs are
   proofs of Rocq's `=`.  An isomorphism with it is not merely unproven here,
   it is unavailable: it would require `h ≈ h' → h = h'`, which is exactly the
   collapse of the hom-setoid to strict equality that this library declines to
   assume.  Block C makes that precise rather than leaving it as a remark; see
   below.

   Nothing in the tree could be reused for [DiscreteSetoidCat], and the reason
   is a genuine typing obstruction, not an oversight.  Instance/Proset.v's
   [Proset] builds a thin category out of a [PreOrder], and an equivalence
   relation is a preorder, so `Proset` at the hom-setoid's equivalence looks
   like the construction wanted.  But [Proset] is stated over
   `Coq.Relations.Relation_Definitions.relation`, i.e. a `Prop`-valued
   relation, whereas this library's `≈` is a `crelation` — `Type`-valued, so
   that equivalence proofs may carry computational content (Lib/Setoid.v).  The
   gap is not cosmetic: a comma morphism carries its square proof as `sigT`
   data, so building one demands the `Type`-valued witness, and a `Prop`-valued
   (or `Prop`-squashed) preorder cannot be eliminated into it.  Hence the
   construction below, which is [Proset] transposed to `crelation`s.

   The closest thing already in the tree is [Blurry A] of
   Instance/Discrete/Reconstruct.v, which is precisely [DiscreteSetoidCat] at
   the `eq` setoid — objects `A`, homs `x = y`, all parallel arrows identified.
   It was introduced there as a countermodel; the present file gives the
   general construction of which it is an instance.  It is not imported from
   there, since that file pulls in Instance/StrictCat and Eqdep_dec for
   purposes unrelated to this one.

   ** What is delivered, and at what strength

   [Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat] HomDiscrete b a].  Note `≅[Cat]`
   is EQUIVALENCE of categories in this library, Cat's hom-setoid being
   [Functor_Setoid] (Instance/Cat.v); no isomorphism of categories is claimed.
   Both round trips are nevertheless as tight as the encodings allow, and the
   two are not equally tight:

   - [Comma_Hom ◯ Hom_Comma] is the identity of [HomDiscrete b a] with a
     DEFINITIONALLY identical object map (h ↦ ((ttt, ttt); h) ↦ h), so its
     natural isomorphism has [iso_id] components and its coherence clause is
     trivially true, the target being thin.

   - [Hom_Comma ◯ Comma_Hom] sends (u, v, h) to ((ttt, ttt); h), replacing the
     two unit paddings by the canonical ones.  Its components are the canonical
     comma isomorphisms [comma_const_iso], whose data is again units.  The
     object map is not the identity as a Rocq term — `u` is a variable, not
     `ttt` — although it becomes so after case analysis; no strict statement is
     claimed and none is needed.

   ** Block C: the plain [DiscreteCat] reading, and its exact price

   The functor [Comma_Discrete_eq : DiscreteCat (b ~> a) ⟶ (=(b) ↓ =(a))]
   exists with no hypothesis at all: `=` implies `≈`.  It is essentially
   surjective, again with no hypothesis.  What it is not, in general, is fully
   faithful, and this file measures the two obstructions exactly:

     [Full Comma_Discrete_eq]      ⟺  [HomStrict b a] : f ≈ g → f = g
     [Faithful Comma_Discrete_eq]  ⟺  [HomUIP b a]    : uniqueness of identity
                                                        proofs on `b ~> a`

   Faithfulness breaks down for a structural reason worth stating: the comma
   here is THIN — all parallel morphisms are `≈`, since the only data in a
   morphism lives in 1 ([comma_const_thin]) — while [DiscreteCat]'s hom-setoid
   is strict `eq` on equality proofs.  So the hypothesis of faithfulness is
   vacuously satisfied and its conclusion is literally UIP.

   Consequently the naive expectation, that Mac Lane's remark should hold with
   [DiscreteCat] under the single hypothesis `f ≈ g → f = g`, is FALSE, and
   [comma_discrete_iso_forces_UIP] proves it: ANY isomorphism
   [DiscreteCat (b ~> a) ≅[Cat] (=(b) ↓ =(a))] in Cat entails [HomUIP b a],
   because both legs of a Cat-isomorphism are faithful unconditionally
   ([Cat_Iso_to_Faithful], Instance/Cat.v) — no hypothesis, and not specific to
   the functor built here.  So the conditional reading
   [Comma_Discrete_Hom_eq] takes BOTH [HomStrict] and [HomUIP].  This is the
   same shape as [DiscreteRigid] in Instance/Discrete/Reconstruct.v and as the
   [ObjUIP]-style hypotheses of Theory/Metacategory/General.v: an honest,
   explicitly quantified side condition, never an axiom.

   ** Block D: one hypothesis necessary, the other not droppable, both
      jointly satisfiable

   Neither hypothesis is decoration, and neither claim is left as prose.

   [HomUIP] is necessary by [comma_discrete_iso_forces_UIP] above, for any
   isomorphism whatever.  [HomStrict] is necessary too, and the witness is
   [Blur]: one object, hom-type [bool], and a hom-setoid that identifies the two
   arrows.  There [HomUIP] HOLDS ([Blur_HomUIP], Hedberg at [bool]'s decidable
   equality, axiom-free) while [HomStrict] is refutable outright
   ([Blur_HomStrict_absurd]) — and the conclusion is refutable with it:
   [Blur_no_discrete_iso] shows no isomorphism
   [DiscreteCat bool ≅[Cat] (=(ttt) ↓ =(ttt))] exists over [Blur] at all.  So
   [HomUIP] alone does not suffice, which is what makes [HomStrict] a genuine
   second hypothesis rather than a convenience of the proof.

   And the two are jointly satisfiable, so [Comma_Discrete_Hom_eq] is not a
   conditional with an empty premise: over the terminal category `1` both hold
   ([One_HomStrict] is the identity function, the hom-setoid of `1` being strict
   equality; [One_HomUIP] is Hedberg at [poly_unit]) and
   [One_Comma_Discrete_Hom_eq] is the resulting isomorphism.  That witness is
   degenerate — one object, one arrow — and is offered as an inhabitation check
   on the hypothesis pair, not as an interesting instance. *)

(** ** Block A: the discrete category on a setoid *)

(* [Proset] transposed from `Prop`-valued preorders to the `crelation`s this
   library's `≈` lives in: objects are the carrier, a morphism x ~> y is a
   proof of x ≈ y, identity is reflexivity and composition is transitivity.
   Like [Proset] it is THIN — the hom-setoid identifies all parallel arrows —
   so every category law is an equation between parallel morphisms and is
   discharged by the default obligation tactic.

   [Blurry A] (Instance/Discrete/Reconstruct.v) is this construction at the
   `eq` setoid; [Proset] is its `Prop`-valued analogue, unusable here for the
   reason given in the header. *)
Program Definition DiscreteSetoidCat {A : Type} (S : Setoid A) : Category := {|
  obj     := A;                                (* objects are the carrier *)
  hom     := fun x y => @equiv A S x y;        (* a morphism IS a proof of ≈ *)
  homset  := fun _ _ => {| equiv := fun _ _ => True |};   (* thin *)
  id      := fun x => @Equivalence_Reflexive A (@equiv A S) (@setoid_equiv A S) x;
  compose := fun x y z g f =>
    @Equivalence_Transitive A (@equiv A S) (@setoid_equiv A S) x y z f g
|}.

(* Thinness, in the form used below: any two parallel arrows agree. *)
Lemma DiscreteSetoidCat_thin {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(* The discrete category on the hom-set C(b, a) — Mac Lane's "discrete
   category on the hom-set", read at the hom-SETOID as the header explains. *)
Definition HomDiscrete {C : Category} (b a : C) : Category :=
  DiscreteSetoidCat (@homset C b a).

(** ** Block B: the comma of two constant functors *)

Section CommaConstant.

Context {C : Category}.
Context {b a : C}.

(* The canonical comma object attached to an arrow h : b ~> a, padded with the
   unique object of 1 on both sides. *)
Definition comma_const_obj (h : b ~{C}~> a) : (=(b) ↓ =(a)) := ((ttt, ttt); h).

(* The comma of two constant functors is THIN: the only data in one of its
   morphisms is a pair of arrows of 1, and 1 has exactly one arrow.  This is
   the engine of the file's comma-side obligations — every functor and
   isomorphism law whose goal lands IN the comma is an instance of it.  (Laws
   landing in [HomDiscrete] are discharged by that category's own trivially
   true hom-setoid instead: those goals are equations the setoid makes
   vacuous, which [comma_const_thin] cannot even be applied to by typing.) *)
Lemma comma_const_thin (X Y : (=(b) ↓ =(a))) (m n : X ~> Y) : m ≈ n.
Proof.
  destruct m as [[u1 u2] Hm], n as [[v1 v2] Hn]; simpl.
  now split; destruct u1, u2, v1, v2.
Qed.

(* A morphism of the comma category yields the ≈ its square asserts.  The
   square is `h' ∘ fmap[=(b)] _ ≈ fmap[=(a)] _ ∘ h`, and both constant functors
   send every arrow to an identity, so it says h' ≈ h. *)
Lemma comma_const_equiv {X Y : (=(b) ↓ =(a))} (m : X ~> Y) : `2 X ≈ `2 Y.
Proof.
  destruct m as [uv Hm]; simpl in *.
  rewrite id_left, id_right in Hm.
  now symmetry.
Qed.

(* ... and conversely, a ≈ yields a morphism; written out rather than left to
   the default obligation tactic, since this direction is the file's claim that
   a comma morphism here IS a witness of `≈`. *)
#[local] Obligation Tactic := idtac.

Program Definition comma_const_mor {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ~> Y := ((ttt, ttt); _).
Next Obligation.
  intros X Y e; simpl.
  (* the square is `2 Y ∘ id ≈ id ∘ `2 X, both constant functors sending every
     arrow of 1 to an identity *)
  rewrite id_left, id_right; now symmetry.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Comma objects are isomorphic exactly when their arrows agree: an arrow of
   the comma IS a witness of `≈` ([comma_const_equiv] the other way), so this is
   the object-level reading of thinness. *)
Program Definition comma_const_obj_iso {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ≅ Y := {|
  to   := comma_const_mor e;
  from := comma_const_mor (symmetry e)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(* Every comma object is canonically isomorphic to the canonical one on its own
   arrow; only the unit padding changes. *)
Program Definition comma_const_iso (X : (=(b) ↓ =(a))) :
  comma_const_obj (`2 X) ≅ X := {|
  to   := comma_const_mor (Y:=X) (reflexivity _);
  from := comma_const_mor (X:=X) (reflexivity _)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(* Read off the arrow: the comma of two constant functors ⟶ the hom-set. *)
Program Definition Comma_Hom : (=(b) ↓ =(a)) ⟶ HomDiscrete b a := {|
  fobj := fun X => `2 X;
  fmap := fun _ _ m => comma_const_equiv m
|}.

(* ... and back, padding an arrow into a comma object. *)
Program Definition Hom_Comma : HomDiscrete b a ⟶ (=(b) ↓ =(a)) := {|
  fobj := comma_const_obj;
  fmap := fun x y e => comma_const_mor (X:=comma_const_obj x)
                                       (Y:=comma_const_obj y) e
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(* Mac Lane, §II.6, remark [maclane:II.6:remark1]: the comma category of two
   objects, regarded as functors out of 1, is the discrete category on the
   hom-set between them.  `≅[Cat]` is EQUIVALENCE of categories here
   (Instance/Cat.v); see the header for what each round trip achieves. *)
(* [idtac] so that BOTH clauses are written out rather than left to the default
   obligation tactic; restored immediately afterwards. *)
#[local] Obligation Tactic := idtac.

Program Definition Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat] HomDiscrete b a := {|
  to   := Comma_Hom;
  from := Hom_Comma
|}.
Next Obligation.
  (* Comma_Hom ◯ Hom_Comma ≈ Id[HomDiscrete b a]: the identity on objects
     definitionally (h ↦ ((ttt, ttt); h) ↦ h), so [iso_id] components serve, and
     the coherence clause is trivially true, the target being thin. *)
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (* Hom_Comma ◯ Comma_Hom ≈ Id[(=(b) ↓ =(a))]: renormalise the unit padding.
     The coherence clause is an equation between parallel comma morphisms. *)
  exists comma_const_iso.
  intros X Y m.
  first [ apply comma_const_thin | (split; reflexivity) ].
Qed.

#[local] Obligation Tactic := cat_simpl.

End CommaConstant.

(** ** Block C: the plain [DiscreteCat] reading and its exact price *)

Section CommaDiscreteEq.

Context {C : Category}.
Context {b a : C}.

(* The always-available comparison: `=` implies `≈`, so the strictly discrete
   category on the hom-TYPE maps into the comma category.  Every equality proof
   goes to the canonical comma morphism on the reflexivity witness it
   transports.

   Not [DiscreteCat_Functor comma_const_obj], though the two are extensionally
   the same functor.  [Full], [Faithful] and [EssentiallySurjective] each carry
   only THREE universe parameters (measured: `About Full` reports
   `Full@{u u0 u1}`), so each identifies the hom AND proof universes of its
   source and target categories.  [DiscreteCat_Functor] carries the `Set` pin
   in its OWN signature — its type mentions `DiscreteCat@{u Set Set}`, fixed
   when that constant was defined — so using it here would make the class
   demand `Set` for C's hom universe too, which at this abstract use site is a
   universe inconsistency, not merely a pin.  Building the functor by hand leaves those universes free
   to unify with C's, which is what Block C's statements need; the same
   consideration is why Instance/Discrete/Reconstruct.v's [Discrete_Compare]
   carries explicit `@{o h p}` binders rather than going through [Program]. *)
(* `=` implies `≈`: transport the reflexivity witness along the equality. *)
Definition discrete_eq_equiv (x y : b ~{C}~> a) (e : x = y) : x ≈ y :=
  match e in _ = z return x ≈ z with eq_refl => reflexivity x end.

Definition comma_const_eq_mor (x y : b ~{C}~> a) (e : x = y) :
  comma_const_obj x ~> comma_const_obj y :=
  comma_const_mor (X := comma_const_obj x) (Y := comma_const_obj y)
    (discrete_eq_equiv x y e).

(* Every functor law is an instance of [comma_const_thin]; [Proper] is a
   definitional single-field class, so its field too is supplied as a plain
   lambda rather than through [Program]. *)
Definition Comma_Discrete_eq : DiscreteCat (b ~{C}~> a) ⟶ (=(b) ↓ =(a)) :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (=(b) ↓ =(a))
    comma_const_obj comma_const_eq_mor
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _)
    (fun _ => comma_const_thin _ _ _ _)
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _).

(* The hypothesis that would make the hom-setoid strict. *)
Definition HomStrict : Type := ∀ f g : b ~{C}~> a, f ≈ g → f = g.

(* ... and uniqueness of identity proofs on the hom-type. *)
Definition HomUIP : Type := ∀ (f g : b ~{C}~> a) (p q : f = g), p = q.

(* Essential surjectivity is free: every comma object is the canonical one on
   its own arrow, up to the unit-renormalising isomorphism. *)
Program Definition Comma_Discrete_eq_ESO :
  EssentiallySurjective Comma_Discrete_eq := {|
  eso_obj := fun X => `2 X;
  eso_iso := comma_const_iso
|}.

(* Fullness is EXACTLY the collapse of the hom-setoid.  Forwards: a witness of
   f ≈ g is a comma morphism between the images, whose preimage is the wanted
   equality.  Backwards: the required section law is free, the comma category
   being thin. *)
Theorem Comma_Discrete_eq_Full_iff : Full Comma_Discrete_eq ↔ HomStrict.
Proof.
  split.
  - intros F f g e.
    exact (@prefmap _ _ _ F f g (comma_const_mor (X:=comma_const_obj f)
                                                 (Y:=comma_const_obj g) e)).
  - intro HE.
    exact (@Build_Full _ _ Comma_Discrete_eq
             (fun f g m => HE f g (comma_const_equiv m))
             (fun f g m => comma_const_thin _ _ _ _)).
Qed.

(* Faithfulness is EXACTLY UIP on the hom-type.  The comma category is thin, so
   the hypothesis `fmap p ≈ fmap q` is vacuous and the conclusion `p ≈ q` is,
   in [DiscreteCat], strict equality of the two proofs. *)
Theorem Comma_Discrete_eq_Faithful_iff : Faithful Comma_Discrete_eq ↔ HomUIP.
Proof.
  split.
  - intros F f g p q.
    exact (@fmap_inj _ _ _ F f g p q (comma_const_thin _ _ _ _)).
  - intro HU.
    constructor; intros f g p q _; exact (HU f g p q).
Qed.

(* The conditional reading, with both hypotheses.  [HomStrict] builds the
   backward functor's action and [HomUIP] discharges its three laws, each of
   which is an equation between equality proofs. *)
Definition Hom_Discrete_eq (HE : HomStrict) (HU : HomUIP) :
  HomDiscrete b a ⟶ DiscreteCat (b ~{C}~> a) :=
  @Build_Functor (HomDiscrete b a) (DiscreteCat (b ~{C}~> a))
    (fun h => h) HE
    (fun _ _ _ _ _ => HU _ _ _ _)     (* fmap_respects *)
    (fun _ => HU _ _ _ _)             (* fmap_id *)
    (fun _ _ _ _ _ => HU _ _ _ _).    (* fmap_comp *)

(* The other leg, again hand-built rather than [DiscreteCat_Functor] so that no
   universe is baked in; every law is an equation in the thin [HomDiscrete]. *)
Definition Discrete_eq_Hom : DiscreteCat (b ~{C}~> a) ⟶ HomDiscrete b a :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (HomDiscrete b a)
    (fun h => h) discrete_eq_equiv
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

#[local] Obligation Tactic := idtac.

Program Definition Discrete_HomDiscrete (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] HomDiscrete b a := {|
  to   := Discrete_eq_Hom;
  from := Hom_Discrete_eq HE HU
|}.
Next Obligation.
  (* Discrete_eq_Hom ◯ Hom_Discrete_eq ≈ Id[HomDiscrete b a]: identity on
     objects definitionally, and the target is thin. *)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (* Hom_Discrete_eq ◯ Discrete_eq_Hom ≈ Id[DiscreteCat ...]: identity on
     objects definitionally; the coherence clause is an equation between
     equality proofs in the hom-type, hence exactly [HomUIP]. *)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y p; apply HU.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Mac Lane's remark in its literal, strictly-discrete form — available exactly
   under the two explicit hypotheses, and (by the theorem after it) not for
   free. *)
Definition Comma_Discrete_Hom_eq (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a)) :=
  iso_compose (iso_sym Comma_Discrete_Hom) (Discrete_HomDiscrete HE HU).

(* The necessity of [HomUIP], for ANY isomorphism, not merely for the one built
   above: both legs of an isomorphism in Cat are faithful with no hypothesis
   ([Cat_Iso_to_Faithful], Instance/Cat.v), and faithfulness of a functor into
   this thin comma category is literally UIP on the hom-type.  So the plain
   [DiscreteCat] reading of Mac Lane's remark cannot be had unconditionally in
   this library. *)
Theorem comma_discrete_iso_forces_UIP
  (iso : DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a))) : HomUIP.
Proof.
  intros f g p q.
  exact (@fmap_inj _ _ _ (Cat_Iso_to_Faithful iso) f g p q
           (comma_const_thin _ _ _ _)).
Qed.

End CommaDiscreteEq.

(** ** Block D: witnesses — both hypotheses inhabited, and both necessary *)

(* Non-vacuity of Block C is proved rather than assumed, in both directions.

   [HomUIP] alone is not enough: [Blur] below is a category whose hom-type is
   [bool], on which UIP holds by Hedberg, yet Mac Lane's remark in its plain
   [DiscreteCat] form is outright FALSE there ([Blur_no_discrete_iso]) — so
   [HomStrict] is a genuine second hypothesis, not a convenience.  The two
   hypotheses are pinned at DIFFERENT strengths, stated precisely:
   [comma_discrete_iso_forces_UIP] shows [HomUIP] NECESSARY for any such
   isomorphism (a genuine implication), while for [HomStrict] what is shown is
   that it is NOT DROPPABLE ([Blur]: the other hypothesis alone does not
   suffice) — no implication from the isomorphism to [HomStrict] is claimed.
   And the pair is simultaneously satisfiable: over the terminal
   category both hold and [Comma_Discrete_Hom_eq] applies
   ([One_Comma_Discrete_Hom_eq]). *)

From Coq Require Import Eqdep_dec.

(* One object, two parallel arrows, and a hom-setoid that identifies them: the
   minimal category on which the hom-setoid is a genuine quotient.  Every
   category law is an equation in the trivial hom-setoid, hence free — the same
   device as Instance/Proset.v and as [Blurry] in
   Instance/Discrete/Reconstruct.v, whence the name. *)
Program Definition Blur : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ _ _ => true
|}.

(* Its hom-setoid does not collapse to equality: `true ≈ false` yet
   `true <> false`. *)
Lemma Blur_HomStrict_absurd : @HomStrict Blur ttt ttt → False.
Proof. intro HE; discriminate (HE true false I). Qed.

(* But UIP on the hom-type does hold, by Hedberg's theorem at the decidable
   equality of [bool] (stdlib [UIP_dec]; no axiom). *)
Lemma Blur_HomUIP : @HomUIP Blur ttt ttt.
Proof.
  intros f g p q; apply UIP_dec.
  intros x y; destruct x, y; solve [ now left | right; discriminate ].
Qed.

(* Hence [HomUIP] does not suffice: over [Blur] no isomorphism in Cat between
   the strictly discrete category on the hom-type and the comma of the two
   constant functors exists at all.

   The argument is short.  Over [Blur] any two arrows are `≈`, so any two
   objects of the comma are isomorphic ([comma_const_obj_iso]).  A functor
   preserves isomorphisms ([fobj_iso]), so the two objects `true` and `false` of
   [DiscreteCat bool] have isomorphic images under `from ◯ to`; but in a
   [DiscreteCat] an isomorphism carries an equality of its endpoints, and the
   round trip `from ◯ to ≈ Id` identifies each image with its argument.  So
   `true = false`. *)
Theorem Blur_no_discrete_iso :
  (DiscreteCat (ttt ~{Blur}~> ttt) ≅[Cat] (=((ttt : Blur)) ↓ =((ttt : Blur)))) → False.
Proof.
  intro iso.
  (* the two comma images are isomorphic, all Blur-arrows being ≈ *)
  pose proof (comma_const_obj_iso
                (X := to iso true) (Y := to iso false) I) as Hcomma.
  (* transport that isomorphism back along `from iso` *)
  pose proof (@fobj_iso _ _ (from iso) _ _ Hcomma) as Hback.
  (* the round trip identifies `from (to x)` with `x` *)
  pose proof (`1 (iso_from_to iso) true) as Ht.
  pose proof (`1 (iso_from_to iso) false) as Hf.
  assert (Heq : (true : DiscreteCat (ttt ~{Blur}~> ttt)) = false).
  { transitivity (from iso (to iso true)).
    - exact (eq_sym (to Ht)).
    - transitivity (from iso (to iso false)).
      + exact (to Hback).
      + exact (to Hf). }
  discriminate Heq.
Qed.

(* [Blur] also settles the sibling file's strictness question.
   Construction/Slice/Terminal.v argues in prose that Mac Lane's "isomorphic"
   is unavailable for the slice over a terminal object — slice objects carry
   their structure morphism as data, and [one_unique] gives only `≈`.  Here
   that argument becomes a theorem: [Blur]'s trivially-true hom-setoid makes
   EVERY arrow a `one`, so `Slice Blur ttt` has two objects `(ttt; true)` and
   `(ttt; false)` where [Blur] has one object, and a strict isomorphism of
   categories would force `true = false` through its object round trip.
   (Adapted from the adversarial audit's probe, with thanks.) *)
Program Definition Blur_Terminal : @Terminal Blur := {|
  terminal_obj := ttt;
  one := fun _ => true
|}.

Theorem slice_terminal_not_strict :
  (@Slice Blur (@terminal_obj Blur Blur_Terminal) ≅[StrictCat] Blur) → False.
Proof.
  intro iso.
  pose proof (`1 (iso_from_to iso) ((ttt; true) : @Slice Blur ttt)) as Ht.
  pose proof (`1 (iso_from_to iso) ((ttt; false) : @Slice Blur ttt)) as Hf.
  assert (Hmid : fobj[to iso] ((ttt; true) : @Slice Blur ttt)
               = fobj[to iso] ((ttt; false) : @Slice Blur ttt)).
  { now destruct (fobj[to iso] ((ttt; true) : @Slice Blur ttt)),
                 (fobj[to iso] ((ttt; false) : @Slice Blur ttt)). }
  assert (Heq : ((ttt; true) : @Slice Blur ttt) = (ttt; false)).
  { transitivity (fobj[from iso] (fobj[to iso] ((ttt; true) : @Slice Blur ttt))).
    - exact (eq_sym Ht).
    - transitivity (fobj[from iso] (fobj[to iso] ((ttt; false) : @Slice Blur ttt))).
      + exact (f_equal (fobj[from iso]) Hmid).
      + exact Hf. }
  exact (Bool.diff_true_false
           (f_equal (fun s : @Slice Blur ttt => projT2 s) Heq)).
Qed.

(* The other side: over the terminal category both hypotheses hold, so
   [Comma_Discrete_Hom_eq] is not a conditional with an empty premise.  The
   hom-setoid of `1` is strict equality, so [HomStrict] is the identity, and
   [HomUIP] is Hedberg at [poly_unit]. *)
Lemma One_HomStrict : @HomStrict _1 ttt ttt.
Proof. intros f g e; exact e. Qed.

Lemma One_HomUIP : @HomUIP _1 ttt ttt.
Proof.
  intros f g p q.
  apply UIP_dec.
  now intros x y; destruct x, y; left.
Qed.

Definition One_Comma_Discrete_Hom_eq :
  DiscreteCat (ttt ~{_1}~> ttt) ≅[Cat] (=((ttt : _1)) ↓ =((ttt : _1))) :=
  Comma_Discrete_Hom_eq One_HomStrict One_HomUIP.
