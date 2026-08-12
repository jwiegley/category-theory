Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(** * Base points: the vertex groups of a connected groupoid *)

(* nLab:      https://ncatlab.org/nlab/show/groupoid
   nLab:      https://ncatlab.org/nlab/show/vertex+group
   nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/fully+faithful+functor
   nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
   Book:      Riehl, "Category Theory in Context", Corollary 1.5.14, printed
              p. 36 (PDF p. 56), the corollary drawn there from Proposition
              1.5.13 (printed pp. 35-36)
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

   In a connected groupoid the vertex groups at any two objects are isomorphic
   as GROUPS.  Riehl records this at the location above as a corollary of the
   structure theorem for connected groupoids — her Proposition 1.5.13, which is
   Structure/Groupoid/Connected.v:274's [connected_deloop_equiv].  That
   sentence, and everything else this file says about what a printed source
   states, is a paraphrase of the statement at the cited location and not a
   quotation; the proof below is this library's own.

   Contents:

       Full_Compose             fullness is closed under functor composition
       Faithful_Compose         and so is faithfulness
       deloop_ff_moniso         a fully faithful functor between one-object
                                categories is a monoid isomorphism
       deloop_equiv_moniso      the same for an equivalence, via Full+Faithful
       connected_vertex_moniso  the headline: vertex groups at any two objects
                                of a connected groupoid are isomorphic
       Bool_Wide_vertex_moniso  the headline instantiated at a groupoid with
                                two distinct objects, both of whose vertex
                                groups are Z/2
       Bool_Wide_vertex_groups_agree,
       Bool_Wide_vertex_moniso_trivial
                                and the measurement of exactly how much that
                                instantiation demonstrates: not much

   EXPORTED, WITH NO CURRENT CONSUMER.  Counted from the `.glob` reference
   records rather than by reading, seven of the 27 constants below are
   referenced by nothing in the tree, this file included.  Six of them are
   terminal by design — [Bool_Wide_objects_distinct],
   [Bool_Wide_vertex_monoid_false], [Bool_Wide_vertex_inv_false],
   [Bool_Wide_vertex_groups_agree], [Bool_Wide_vertex_moniso_trivial] and
   [Bool_Wide_vertex_moniso] exist precisely to be the end of a chain.  The
   seventh, [deloop_equiv_moniso], is a genuine orphan: it is the
   equivalence-level form of [deloop_ff_moniso], and the headline does not go
   through it because [connected_vertex_moniso] has [Full] and [Faithful] of a
   COMPOSITE in hand rather than an [EquivalenceOfCategories] of it, so it
   calls [deloop_ff_moniso] directly.  It completes the pair and is kept;
   nothing here is removed on this file's own judgement, and the decision to
   keep or drop is the maintainer's.  (The headline [connected_vertex_moniso]
   itself is not in that list: Instance/Top/FundamentalGroupoid.v uses it.) *)

(* Two routes to the same type, and why this file takes the longer one

   The type [MonIso (vertex_group G x) (vertex_group G y)] is ALREADY
   inhabited in this tree.  Structure/Groupoid.v:521's [conjugation_iso] takes
   an arrow f : x ~> y and produces a [MonIso] between those very two vertex
   groups by conjugation, a ↦ f ∘ a ∘ f⁻¹, checking the two round trips by a
   direct cancellation; and Structure/Groupoid/Connected.v:421's
   [Bool_Wide_conjugation] is that route taken at a concrete connected
   groupoid, with the arrow supplied by Connected.v:211's [connected_arrow].
   That is the short route, and it is not the one taken here.

   This file derives the isomorphism from the STRUCTURE THEOREM instead.  The
   chain is:

     - [vertex_incl G x] (Connected.v:234) includes the delooping of the
       vertex group at x into C, fully faithfully (Connected.v:253, :258);

     - [connected_deloop_equiv G K y] (Connected.v:274) says the corresponding
       inclusion at y is an EQUIVALENCE OF CATEGORIES — not an isomorphism of
       categories, and the difference is real: the delooping has exactly one
       object (Structure/Groupoid.v:360's [Deloop_one_object]) while the
       [Bool_Wide] witness at the end of this file has two.  Its quasi-inverse
       Q : C ⟶ B(hom(y,y)) is again full and faithful, by
       Theory/Equivalence/FullFaithful.v:214's [Equivalence_Full] applied to
       the symmetric equivalence (Theory/Equivalence.v:256's
       [EquivalenceOfCategories_sym]) and by that file's
       [Equivalence_Inverse_Faithful] at line 184;

     - so the composite Q ◯ [vertex_incl G x] is a full and faithful functor
       between two DELOOPINGS, and [deloop_ff_moniso] below turns any such
       functor into a [MonIso] — a pair of monoid homomorphisms that are
       mutually inverse up to `≈`, hence an isomorphism of the underlying
       setoids, rather than only an equivalence of one-object categories.

   Two honest caveats.  First, nothing here claims the isomorphism produced
   below agrees with the conjugation isomorphism; both are constructed from
   choices (a zig-zag, a quasi-inverse), and no comparison between them is
   proved.  Second, "isomorphic as groups" is justified because
   Structure/Groupoid.v:441's [MonHom_grp_inv] shows a monoid homomorphism
   between groups automatically preserves inverses — the reason that file
   defines no separate class of group homomorphisms, as its own note at lines
   401-407 records.  So [MonIso] between the underlying monoids of two vertex
   groups IS a group isomorphism, and its fields do assert an element-level
   correspondence: [moniso_to_from] and [moniso_from_to]
   (Structure/Groupoid.v:428, :429) say the two maps are mutually inverse up
   to `≈`.

   What the longer route buys is that the group-level statement is exhibited
   as a CONSEQUENCE of the category-level one rather than as a parallel fact
   proved twice.  The intermediate step, [deloop_ff_moniso], is the missing
   half of the group/one-object-groupoid dictionary that Construction/Deloop.v
   deliberately left out: its header (lines 45-48) defers "the functor-level
   half of the dictionary — that functors between deloopings are exactly
   monoid homomorphisms" to later work.  This is the isomorphism-level part of
   that half. *)

(** ** Fullness and faithfulness are closed under composition *)

(* Neither lemma is in the tree: no in-tree statement concludes [Full] or
   [Faithful] of a composite.  Both are immediate.

   In each proof the two [Full] (resp. [Faithful]) hypotheses are ordinary
   explicit arguments, and every projection below names its record in full —
   [@prefmap C D G FG x y ...] rather than a bare [prefmap].  No instance
   search takes part in either proof, so nothing turns on which of the two
   hypotheses resolution would otherwise have picked. *)

(* The composite of two full functors is full: take the preimage under F
   first, then the preimage of THAT under G.  [fmap[F ◯ G]] is
   [fmap[F] ∘ fmap[G]] by definition of Theory/Functor.v:258's [Compose], so
   the two sections cancel in turn — the inner one underneath [fmap[F]], where
   [fmap_respects] carries it, and the outer one outright. *)
Definition Full_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Full F) (FG : Full G) : Full (F ◯ G).
Proof.
  refine (@Build_Full C E (F ◯ G)
            (fun x y h => @prefmap C D G FG x y
                            (@prefmap D E F FF (G x) (G y) h)) _).
  intros x y h.
  transitivity (@fmap D E F (G x) (G y) (@prefmap D E F FF (G x) (G y) h)).
  - apply (@fmap_respects D E F (G x) (G y)).
    exact (@fmap_sur C D G FG x y (@prefmap D E F FF (G x) (G y) h)).
  - exact (@fmap_sur D E F FF (G x) (G y) h).
Defined.

(* The composite of two faithful functors is faithful: reduce the goal by G's
   injectivity, then by F's, which lands exactly on the hypothesis. *)
Definition Faithful_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Faithful F) (FG : Faithful G) : Faithful (F ◯ G).
Proof.
  refine (@Build_Faithful C E (F ◯ G) _).
  intros x y f g H.
  apply (@fmap_inj C D G FG x y).
  apply (@fmap_inj D E F FF (G x) (G y)).
  exact H.
Defined.

(** ** A fully faithful functor between deloopings is a monoid isomorphism *)

(* Construction/Deloop.v:193 makes [Deloop M] a category with the single
   object [ttt] (its object type is [poly_unit], as
   Structure/Groupoid.v:360's [Deloop_one_object] records by [eq_refl]), whose
   hom-setoid at that object IS the carrier setoid of M, whose identity IS the
   unit and whose composition IS the operation.  Each of those is a
   definitional equality, not a coincidence to be transported; they are among
   the agreements that let Construction/Deloop.v:242's [hom_monoid_Deloop]
   close by [eq_refl] (the note there, lines 230-241, adds the law fields and
   record eta).

   Consequently a functor F : B M ⟶ B N carries, at the unique object, a map
   [carrier M → carrier N] which is a monoid homomorphism for free — the two
   functor laws ARE the two homomorphism laws, and [fmap_respects] IS the
   [Proper] field.  That direction is [deloop_fwd] below and costs nothing.

   The content is the other direction.  [Full] (Theory/Functor.v:331) supplies
   only a SECTION [prefmap] of the hom-map, with no functoriality demanded of
   it — that file's header (lines 326-330) says so in terms, recording that a
   previous definition's [prefmap_respects], [prefmap_id] and [prefmap_comp]
   fields were extraneous.  So that [prefmap] is a monoid homomorphism has to
   be PROVED, and faithfulness is what proves it: each law is checked after
   applying the injective [fmap[F]], where the section law [fmap_sur] collapses
   everything.  [deloop_bwd_respects], [deloop_bwd_unit] and [deloop_bwd_op]
   below are those three arguments written out.

   The [Proof using F FF Ffaith] annotation appears on FOUR lemmas below, not
   three: those three, and [deloop_bwd_fwd], which settles the other round
   trip by the same appeal to faithfulness.  The annotation is forced by the
   [Default Proof Using "Type"] setting of Lib.v:13: [Ffaith] is used in each
   of those four proofs but does not occur in any of their statements, so it
   would otherwise not be retained when the section closes.  The section's
   other four lemmas — [deloop_fwd_bwd], [deloop_fwd_respects],
   [deloop_fwd_unit] and [deloop_fwd_op] — do not need it: the last three are
   functor laws read off through the delooping dictionary and the first is
   [Full]'s section law verbatim, so none of them mentions [Ffaith] at all.
   This is the same per-lemma idiom as Adjunction/Continuity.v:96 rather than
   Construction/Localization/Universal.v:22's file-wide
   [Set Default Proof Using "All"]. *)

Section DeloopFullyFaithful.

Context {M N : MonObject}.
Context (F : Deloop M ⟶ Deloop N).
Context (FF : Full F).
Context (Ffaith : Faithful F).

(* The forward map: the hom-map of F at the unique object.  Its type is
   [carrier M → carrier N] on the nose, the hom-setoids of the two deloopings
   being the two carrier setoids. *)
Definition deloop_fwd (a : carrier M) : carrier N := @fmap _ _ F ttt ttt a.

(* The backward map: the chosen section of that hom-map. *)
Definition deloop_bwd (b : carrier N) : carrier M :=
  @prefmap _ _ F FF ttt ttt b.

(* One round trip is the section law verbatim. *)
Lemma deloop_fwd_bwd (b : carrier N) : deloop_fwd (deloop_bwd b) ≈ b.
Proof. exact (@fmap_sur _ _ F FF ttt ttt b). Qed.

(* The other follows from it by faithfulness: the two elements have the same
   image under the injective hom-map. *)
Lemma deloop_bwd_fwd (a : carrier M) : deloop_bwd (deloop_fwd a) ≈ a.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  exact (@fmap_sur _ _ F FF ttt ttt (deloop_fwd a)).
Qed.

(* The forward map is a monoid homomorphism, by the three functor laws read
   through the delooping dictionary: [fmap_respects] is respectfulness,
   [fmap_id] is preservation of the unit (the identity arrow IS the unit), and
   [fmap_comp] is preservation of the operation (composition IS the
   operation). *)
Lemma deloop_fwd_respects : Proper (equiv ==> equiv) deloop_fwd.
Proof. exact (@fmap_respects _ _ F ttt ttt). Qed.

Lemma deloop_fwd_unit : deloop_fwd mon_unit ≈ mon_unit.
Proof. exact (@fmap_id _ _ F ttt). Qed.

Lemma deloop_fwd_op (a b : carrier M) :
  deloop_fwd (mon_op a b) ≈ mon_op (deloop_fwd a) (deloop_fwd b).
Proof. exact (@fmap_comp _ _ F ttt ttt ttt a b). Qed.

(* The backward map is a monoid homomorphism too, but nothing in [Full]
   asserts it: each of the three laws is established by applying the injective
   forward map and then cancelling with [deloop_fwd_bwd]. *)

Lemma deloop_bwd_respects : Proper (equiv ==> equiv) deloop_bwd.
Proof using F FF Ffaith.
  intros b b' Hb.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity b; [ exact (deloop_fwd_bwd b) | ].
  transitivity b'; [ exact Hb | ].
  symmetry.
  exact (deloop_fwd_bwd b').
Qed.

Lemma deloop_bwd_unit : deloop_bwd mon_unit ≈ mon_unit.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (@mon_unit N); [ exact (deloop_fwd_bwd mon_unit) | ].
  symmetry.
  exact deloop_fwd_unit.
Qed.

Lemma deloop_bwd_op (a b : carrier N) :
  deloop_bwd (mon_op a b) ≈ mon_op (deloop_bwd a) (deloop_bwd b).
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (mon_op a b); [ exact (deloop_fwd_bwd (mon_op a b)) | ].
  transitivity (mon_op (deloop_fwd (deloop_bwd a)) (deloop_fwd (deloop_bwd b))).
  - apply (mon_op_respects N); symmetry; apply deloop_fwd_bwd.
  - symmetry.
    exact (deloop_fwd_op (deloop_bwd a) (deloop_bwd b)).
Qed.

(* The two records are built the way [conjugation] is at
   Structure/Groupoid.v:485 — constructor applied to explicit monoid arguments
   rather than record syntax.  The note there (lines 483-484) gives the
   reason: the field type [carrier (mon_setoid ?M)] does not determine ?M by
   unification alone. *)
Definition deloop_MonHom_fwd : MonHom M N :=
  @Build_MonHom M N deloop_fwd deloop_fwd_respects deloop_fwd_unit
    deloop_fwd_op.

Definition deloop_MonHom_bwd : MonHom N M :=
  @Build_MonHom N M deloop_bwd deloop_bwd_respects deloop_bwd_unit
    deloop_bwd_op.

Definition deloop_ff_moniso : MonIso M N :=
  @Build_MonIso M N deloop_MonHom_fwd deloop_MonHom_bwd
    deloop_fwd_bwd deloop_bwd_fwd.

End DeloopFullyFaithful.

(* The equivalence-level form, by the two halves of the full-and-faithful
   characterization in Theory/Equivalence/FullFaithful.v ([Equivalence_Full]
   at line 214, [Equivalence_Faithful] at line 171). *)
Definition deloop_equiv_moniso {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : MonIso M N :=
  deloop_ff_moniso F (Equivalence_Full E) (Equivalence_Faithful E).

(** ** The headline: base-point independence of the vertex group *)

(* Riehl's Corollary 1.5.14, in the form paraphrased at the head of this file.
   The comparison functor is assembled from the structure theorem at the
   TARGET base point y: quasi-invert the inclusion of hom(y, y), then precede
   it by the inclusion of hom(x, x).  What comes out is a functor between two
   one-object categories, and [deloop_ff_moniso] converts it. *)

Section ConnectedVertex.

Context {C : Category}.
Context (G : IsGroupoid C).
Context (K : Connected C).
Context (x y : C).

(* The structure theorem at y. *)
Definition basepoint_equiv : EquivalenceOfCategories (vertex_incl G y) :=
  connected_deloop_equiv G K y.

(* The comparison functor B(hom(x, x)) ⟶ B(hom(y, y)).  It factors through C,
   which is the whole point: the two vertex groups are compared THROUGH the
   groupoid, not by a formula written down in advance. *)
Definition basepoint_compare :
  Deloop (vertex_group G x) ⟶ Deloop (vertex_group G y) :=
  @quasi_inverse _ _ _ basepoint_equiv ◯ vertex_incl G x.

(* Its fullness: the right factor by [vertex_incl_Full], the left by
   [Equivalence_Full] at the symmetric equivalence — the quasi-inverse of an
   equivalence is an equivalence, hence full. *)
Definition basepoint_compare_Full : Full basepoint_compare :=
  Full_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (@Equivalence_Full _ _ _
       (@EquivalenceOfCategories_sym _ _ _ basepoint_equiv))
    (vertex_incl_Full G x).

(* Its faithfulness, the same way; the left factor is
   [Equivalence_Inverse_Faithful], which is that same symmetric-equivalence
   argument already packaged in Theory/Equivalence/FullFaithful.v:184. *)
Definition basepoint_compare_Faithful : Faithful basepoint_compare :=
  Faithful_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (Equivalence_Inverse_Faithful basepoint_equiv)
    (vertex_incl_Faithful G x).

(* The vertex groups at any two objects of a connected groupoid are isomorphic
   as groups.  Both objects are universally quantified and no property of
   either is used, so the vertex groups at ALL objects of a connected groupoid
   are isomorphic to one another.

   Not proved, and not claimed: that this family of isomorphisms is coherent —
   that the one from x to z agrees with the composite of those from x to y and
   from y to z.  Each is built from a choice (the zig-zag inside K, the
   quasi-inverse inside [basepoint_equiv]), and no comparison between choices
   is made anywhere below. *)
Definition connected_vertex_moniso :
  MonIso (vertex_group G x) (vertex_group G y) :=
  deloop_ff_moniso basepoint_compare
    basepoint_compare_Full basepoint_compare_Faithful.

End ConnectedVertex.

(** ** The hypotheses are satisfiable, and the derivation runs *)

(* [Bool_Wide] (Structure/Groupoid/Connected.v:387) is
   [WideDeloop Bool_Xor_Grp bool]: its objects are the booleans, and its
   hom-setoid at every pair is the carrier setoid of Z/2.  It is a groupoid
   (Connected.v:389) and connected (Connected.v:392), which are exactly the two
   hypotheses of the headline, so [connected_vertex_moniso] applies to it, and
   [Bool_Wide_vertex_moniso] below is that application.

   WHAT THIS WITNESS DOES NOT SHOW, AND WHY.  It does not show that the
   conclusion is ever informative, and the reason is structural rather than
   incidental.  [WideDeloop] fixes the hom TYPE uniformly — Connected.v:341
   reads [hom := fun _ _ => carrier M] — so the vertex group at [true] and the
   vertex group at [false] are not merely isomorphic groups but the SAME
   monoid.  [Bool_Wide_vertex_groups_agree] below records that by [eq_refl] at
   the monoid data field, which is exactly the field a [MonIso] is a statement
   about; and [Bool_Wide_vertex_moniso_trivial] then inhabits the very type of
   [Bool_Wide_vertex_moniso] with the identity maps and [reflexivity] alone —
   no [Connected], no [deloop_ff_moniso], no structure theorem, nothing from
   this file.  So what [Bool_Wide_vertex_moniso] exercises is that the two
   HYPOTHESES are satisfiable together and that the derivation type-checks;
   the type it lands in was already inhabited without any of it.  Choosing a
   different group would not help: [WideDeloop S3_Grp bool] has the same
   defect, at every [M] and every [A].

   The objects [true] and [false] are indeed distinct
   ([Bool_Wide_objects_distinct] below), so the instance does compare vertex
   groups at two different OBJECTS rather than at one object with itself.
   That is a statement about the objects and NOT about the groups: here
   distinct objects do not give distinct vertex groups, and an earlier
   revision of this note put the two side by side in a way that implied they
   did.

   NO IN-TREE OBJECT DOES BETTER TODAY.  The only connected groupoids the
   library builds are the [WideDeloop] family, which has the defect just
   described, and [FundamentalGroupoid X] for a path-connected X, whose sole
   witness is [TwoPoint_Indiscrete] (Instance/Top/FundamentalGroupoid.v:1489 —
   a forward reference; that file depends on this one and not the other way
   round).  There the two vertex groups are at least different monoids, on
   different carriers, so the identity does not inhabit the type; but both are
   TRIVIAL ([TwoPoint_Indiscrete_loops_trivial] there), so an isomorphism is
   again available without the theorem.  ([Roof] is connected but is not a
   groupoid, so it does not enter.)  Making the conclusion informative would
   need a connected groupoid whose vertex group depends on the object and is
   nonabelian; Structure/Groupoid.v's [S3_Grp] supplies such a group, but
   nothing in the tree spreads it over objects non-uniformly.

   Both vertex groups really are Z/2, in both data fields and on the nose.
   Connected.v:397 and :401 record the underlying monoid and the inversion
   operation at [true]; two of the [Example]s below record the same at
   [false].  (Each [=] is an equality of a data field, which is strictly
   stronger than any statement made with `≈`, and each holds by [eq_refl].)

   Nothing is asserted about the underlying map of [Bool_Wide_vertex_moniso]:
   it is built from the quasi-inverse chosen by [FF_ESO_Equivalence], this
   file computes nothing about it, and in particular it is NOT proved to be
   the identity isomorphism exhibited below. *)

Example Bool_Wide_objects_distinct : (true : Bool_Wide) = false → False.
Proof. discriminate. Qed.

Example Bool_Wide_vertex_monoid_false :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid false) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv_false :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid false) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(* The two vertex groups are the same monoid, not two isomorphic ones.  The
   whole [GrpObject]s are NOT equal — their law fields are distinct opaque
   proof terms, the point Structure/Groupoid.v:381-392 makes for
   [vertex_group_Deloop_monoid] — but [MonIso] reads only the monoid, which is
   the field compared here. *)
Example Bool_Wide_vertex_groups_agree :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true)
    = grp_monoid (vertex_group Bool_Wide_IsGroupoid false) := eq_refl.

(* Hence the type of [Bool_Wide_vertex_moniso] is inhabited by the identity,
   with no appeal to connectedness or to the structure theorem.  Every field is
   [fun a => a] or [reflexivity], and each typechecks only because of the
   agreement recorded just above. *)
Example Bool_Wide_vertex_moniso_trivial :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  @Build_MonIso _ _
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid true)
                   (vertex_group Bool_Wide_IsGroupoid false)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid false)
                   (vertex_group Bool_Wide_IsGroupoid true)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (fun b => reflexivity b) (fun a => reflexivity a).

Definition Bool_Wide_vertex_moniso :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  connected_vertex_moniso Bool_Wide_IsGroupoid Bool_Wide_Connected true false.
