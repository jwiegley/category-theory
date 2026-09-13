Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The category of groupoids *)

(* nLab:      https://ncatlab.org/nlab/show/Grpd
   nLab:      https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid

   Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
         Example 4.1.15, printed p. 137 (PDF pp. 157-158)
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         §I.5, printed p. 19

   [Grpd] is the full subcategory of [Cat] whose objects are the categories
   in which every morphism is invertible.  It is built with
   Construction/Subcategory.v's [Build_Subcategory] out of exactly one
   predicate on objects, Structure/Groupoid.v's [IsGroupoid], and the
   maximal choice of morphisms: [shom] ignores its arguments and returns
   [True], so the two closure conditions are [I] and fullness
   ([Grpd_Full]) is [I] as well.  This is the shape Instance/Variety.v uses
   for the algebras of a variety, and it is used here for the same reason
   the header of that file gives: a fresh [Category] record duplicating
   [Cat]'s composition and hom-setoid would have to re-derive every law that
   [Sub] already derives once and generically, and the inclusion would have
   to be built by hand instead of being read off as [Incl].

   The objects of [Grpd] are therefore PAIRS: a category together with a
   chosen inverse-assigning function, since [IsGroupoid] is [Type]-valued
   and its inhabitant carries a chosen inverse for each arrow.  The choice
   is immaterial up to `≈` (Structure/Groupoid.v's [ginv_choice_irrelevant]),
   but it is data, so two membership proofs for one category give two
   objects of [Grpd] -- isomorphic, by [Full_membership_iso]; no [=]
   between them is asserted anywhere here.
   The morphisms are functors between the underlying categories, with no
   condition whatever: a functor between groupoids preserves inverses
   automatically, which is precisely what fullness of the inclusion records.

   The inclusion [Grpd_Incl : Grpd ⟶ Cat] is [Incl], and it is faithful
   ([Grpd_Incl_Faithful], generic) and full ([Grpd_Incl_Full], from
   [Grpd_Full]).  Construction/Groupoid/Core.v makes the maximal-subgroupoid
   construction of Construction/Groupoid.v into its right adjoint. *)

(* Why a category of groupoids, and why it sits inside Cat

   nLab:  https://ncatlab.org/nlab/show/core
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
          the London Mathematical Society 19, 1987
   Paper: Hofmann and Streicher, "The groupoid model refutes uniqueness of
          identity proofs", LICS 1994

   A single groupoid generalises a group by letting the symmetries move
   between objects rather than fixing one; the CATEGORY of groupoids
   generalises the category of groups in the same way, and it is the
   setting in which that generalisation pays.  Brown's survey makes the
   case with the van Kampen theorem: stated for fundamental GROUPS it needs
   a connected intersection, while the groupoid statement -- one base point
   per component, the conclusion a pushout in [Grpd] -- proves a stronger
   theorem more simply (Brown 1987, following Higgins).  A pushout is a
   colimit, so it is a statement about the category of groupoids, not about
   any one of them; the object-level construction alone cannot express it.

   [Grpd] sits inside [Cat] in an unusually strong way.  The inclusion has
   adjoints on BOTH sides -- the left one inverts every morphism formally
   (the category of fractions), the right one discards the non-invertible
   ones (the core) -- so [Grpd] is simultaneously reflective and
   coreflective in [Cat] (Riehl §4.1, Example 4.1.15; nLab: core).  This
   file and Construction/Groupoid/Core.v deliver the right-hand half of that
   adjoint triple as a theorem.  An earlier revision of this sentence added
   that the left-hand half "remains prose"; that is a correction to make,
   because Construction/Fractions/Adjunction.v now proves it, and
   [riehl_4_1_15] there assembles the whole triple over THIS [Grpd] and
   THIS inclusion.

   The type-theoretic reading is not an analogy.  In intensional Martin-Löf
   type theory the identity proofs of a type compose, invert and associate,
   so every type carries the structure of a groupoid, and the interpretation
   of types as OBJECTS OF [Grpd] -- functions as functors between them -- is
   what Hofmann and Streicher used to show that uniqueness of identity
   proofs is not derivable (LICS 1994).  That model is a functor into
   [Grpd], which again is a statement one can only make once the category
   exists. *)

(** ** The subcategory data *)

(* Full, and cut out by a predicate on objects alone: [shom] discards its
   morphism argument entirely.  Every closure proof is therefore [I]. *)

Definition Grpd_sub : Subcategory Cat :=
  @Build_Subcategory Cat
    IsGroupoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Grpd : Category := Sub Cat Grpd_sub.

(** ** Accessors

    An object of [Grpd] is a category paired with a proof that it is a
    groupoid; these two projections name the halves, so that downstream
    files need not spell `1 and `2 at every use. *)

Definition grpd_cat (G : Grpd) : Category := `1 G.

Definition grpd_is_groupoid (G : Grpd) : IsGroupoid (grpd_cat G) := `2 G.

(** ** Fullness and the inclusion *)

Definition Grpd_Full : Full Cat Grpd_sub := fun _ _ _ _ _ => I.

Definition Grpd_Incl : Grpd ⟶ Cat := Incl Cat Grpd_sub.

Definition Grpd_Incl_Faithful : Functor.Faithful Grpd_Incl :=
  Incl_Faithful Cat Grpd_sub.

(* The inclusion is FULL as a functor, not merely full as data:
   Construction/Subcategory.v turns the one into the other. *)

Definition Grpd_Incl_Full : Functor.Full Grpd_Incl :=
  Full_Implies_Full_Functor Cat Grpd_sub Grpd_Full.

(* [shom] ignores its morphism argument, so it is closed under `≈` for the
   trivial reason; this is the hypothesis Construction/Subcategory.v's
   [Full_Functor_Implies_Full] needs, and with it the "full subcategory iff
   full inclusion" biconditional holds for [Grpd] in both directions. *)

Definition Grpd_ShomRespects : ShomRespects Cat Grpd_sub :=
  fun _ _ _ _ _ _ _ _ => I.

(** ** Repleteness

    A category isomorphic in [Cat] to a groupoid is a groupoid.  Note what
    `≅[Cat]` means here: Instance/Cat.v's hom-setoid is [Functor_Setoid], so
    the two round trips are NATURAL ISOMORPHISMS, not identities -- the
    statement proved is therefore the one about equivalences, not the
    stricter one about isomorphisms on the nose.  The transported inverse of
    h : x ~> y is conjugated by the components of that natural isomorphism,
    which is where the two [comp_assoc] chains below come from. *)

Lemma IsGroupoid_transport (C D : Category) (i : C ≅[Cat] D) :
  IsGroupoid C → IsGroupoid D.
Proof.
  intros HC x y h.
  (* The counit-side natural isomorphism: to i ◯ from i ≈ Id[D]. *)
  destruct (iso_to_from i) as [n Hn].
  pose proof (Hn _ _ h) as Hnat; simpl in Hnat.
  (* Hnat : fmap[to i] (fmap[from i] h) ≈ from (n y) ∘ h ∘ to (n x) *)
  assert (Hl : h ∘ to (n x) ≈ to (n y) ∘ fmap[to i] (fmap[from i] h)).
  { rewrite Hnat.
    rewrite !comp_assoc.
    rewrite (iso_to_from (n y)), id_left.
    reflexivity. }
  assert (Hr : from (n y) ∘ h ≈ fmap[to i] (fmap[from i] h) ∘ from (n x)).
  { rewrite Hnat.
    rewrite <- !comp_assoc.
    rewrite (iso_to_from (n x)), id_right.
    reflexivity. }
  unshelve econstructor.
  - exact (to (n x) ∘ fmap[to i] (ginv HC (fmap[from i] h)) ∘ from (n y)).
  - (* h ∘ h⁻¹ ≈ id *)
    rewrite !comp_assoc.
    rewrite Hl.
    rewrite <- (comp_assoc (to (n y))).
    (* Keyed rewriting does not pick this occurrence up from the bare
       [fmap_comp]; the instance is therefore given in full. *)
    rewrite <- (@fmap_comp _ _ (to i) _ _ _
                  (fmap[from i] h) (ginv HC (fmap[from i] h))).
    rewrite ginv_right, fmap_id, id_right.
    apply (iso_to_from (n y)).
  - (* h⁻¹ ∘ h ≈ id *)
    rewrite <- !comp_assoc.
    rewrite Hr.
    rewrite (comp_assoc (fmap[to i] (ginv HC (fmap[from i] h)))).
    rewrite <- fmap_comp.
    rewrite ginv_left, fmap_id, id_left.
    apply (iso_to_from (n x)).
Qed.

Definition Grpd_Replete : Replete Cat Grpd_sub :=
  fun x ox y f => (IsGroupoid_transport x y f ox; (I, I)).

(** ** Not vacuous, and not the whole of Cat

    [Grpd] is a PROPER subcategory of [Cat]: the delooping of (ℕ, +) is a
    category whose arrow 1 has no inverse, so it is not an object of [Grpd].
    The witness is Structure/Groupoid.v's [deloop_nat_not_groupoid], whose
    own content is the specific non-invertible arrow rather than an appeal
    to "ℕ is not a group".  Without this the whole development would be
    consistent with [Grpd_sub] selecting every object of [Cat], in which
    case Construction/Groupoid/Core.v's [Core] would be the identity and its
    adjunction trivial. *)

Lemma Grpd_proper_subcategory : sobj Cat Grpd_sub (Deloop Nat_Plus) → False.
Proof. exact deloop_nat_not_groupoid. Qed.

(* The companion witness: the delooping of Z/2 IS a groupoid, so the
   predicate cutting [Grpd] out separates the two deloopings. *)

Definition Grpd_Deloop_Bool : Grpd :=
  (Deloop Bool_Xor_Grp; deloop_bool_groupoid).
