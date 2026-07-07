Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Structure.Premonoidal.Centre.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(** * Freyd categories and effectful functors

    nLab: https://ncatlab.org/nlab/show/Freyd+category

    Levy–Power–Thielecke ("Modelling environments in call-by-value
    programming languages", Inf. Comput. 185(2), 2003) and Power–Thielecke
    ("Closed Freyd- and kappa-categories", ICALP 1999) distil the
    categorical semantics of call-by-value effects into a FREYD CATEGORY:
    an identity-on-objects functor J : V ⟶ K from a monoidal category of
    values into a premonoidal category of computations, strictly
    preserving the premonoidal structure and landing in the centre Z(K).
    Every strong monad on a symmetric monoidal base produces one — the
    Kleisli premonoidal structure of Monad/Kleisli/Premonoidal.v — and
    Freyd categories are exactly the monad-independent formulation of
    that situation.

    A caveat on the name: both papers ask for more than this file
    formalizes.  They additionally require finite products on V (a
    CARTESIAN category of values), a symmetry on the premonoidal K, and
    strict preservation of that symmetry by J.  Symmetric premonoidal
    structure is not yet formalized in this library, so the [Freyd]
    class below drops all three requirements.  What it captures is the
    (strict) EFFECTFUL CATEGORY of Levy and Román, of which the
    classical Freyd category is the cartesian/symmetric special case.

    The notion is delivered in two layers:

      - [EffectfulFunctor]: the centrality half alone — a functor whose
        image consists of central morphisms (Structure/Binoidal.v).  Such
        a functor factors through the centre ([Effectful_Centre]) as a
        functor V ⟶ Z(K), and the factorization J = Incl ∘ Effectful_Centre
        holds definitionally ([Effectful_Centre_factors]).  Since Z(K) is
        monoidal (Structure/Premonoidal/Centre.v, [Centre_Monoidal]), an
        effectful functor out of a monoidal V is the raw material of a
        monoidal-to-monoidal comparison.

      - [Freyd]: the full packaging.  Identity-on-objects is rendered
        strictly, as a section/retraction pair of Leibniz object
        equalities ([freyd_obj_section]/[freyd_obj_eq]/[freyd_sec_eq]),
        and strict preservation of unit and tensor is rendered with the
        library's transported-identity discipline: object-level
        equalities [freyd_obj_I]/[freyd_obj_tensor], plus morphism-level
        laws transported along them by [id_cast]
        (Construction/Quotient.v).  This is the same [match]-shaped
        formulation as the "Formulation note" of
        Structure/Monoidal/Strict.v and the strict monoidal functors of
        Functor/Structure/Monoidal/Strict.v; [id_cast] is deliberately
        spelled so those fields and these read alike.  In both instances
        below every object equality is [eq_refl], so every cast reduces
        to [id] definitionally and the morphism-level fields collapse to
        the underlying coherence facts.

    Two instances close the file:

      - [Freyd_Kleisli], the flagship (Power–Thielecke 1999,
        Levy–Power–Thielecke 2003): for a strong monad M on a symmetric
        monoidal category C, the pure functor
        [Kleisli_Pure] : C ⟶ Kl(M) of Monad/Kleisli/Premonoidal.v is a
        Freyd category over [Kleisli_Binoidal]/[Kleisli_Premonoidal].
        Objects of Kl(M) ARE the objects of C, so all object equalities
        are [eq_refl]; centrality of the image is [pure_central]; the
        two tensoring strictness fields are the pure-morphism transfer
        laws [pure_inj_left]/[pure_inj_right]; and the structural-map
        fields hold at reflexivity level because the premonoidal unitors
        and associator of Kl(M) are themselves [kpure] images.

      - [Freyd_Id], the degenerate example: any monoidal category over
        itself through [Monoidal_Binoidal]/[Monoidal_Premonoidal]
        (Structure/Premonoidal/Monoidal.v), with J the identity functor
        and centrality supplied by [Monoidal_all_central].  For a
        cartesian V — take [CC_Monoidal] of
        Structure/Monoidal/Internal/Product.v, or its alias
        [Cartesian_Monoidal] — this recovers the classical Freyd-category
        reading "cartesian values inside effectful computations", here at
        the trivial effect. *)

(** ** Effectful functors

    The centrality half of the Freyd notion, isolated: a functor
    J : V ⟶ K into a binoidal K is effectful when every morphism in its
    image is central.  No strictness and no structure preservation is
    demanded yet, so the class is stated over a bare binoidal target. *)

Section Effectful.

Context {V K : Category}.
Context `{BK : @Binoidal K}.

Class EffectfulFunctor (J : V ⟶ K) := {
  eff_central {x y} (f : x ~{V}~> y) : central (fmap[J] f)
}.

(** The image of an effectful functor lands in the wide subcategory
    Z(K) = [Centre K] of Structure/Binoidal/Central.v, so J factors as a
    functor into the centre.  The functor laws are the underlying laws of
    J because [Sub]-homsets compare first projections. *)

Definition Effectful_Centre_fmap {J : V ⟶ K} `{E : @EffectfulFunctor J}
    {x y : V} (f : x ~{V}~> y) :
  ((fobj[J] x; ttt) : Centre K) ~{Centre K}~> ((fobj[J] y; ttt) : Centre K) :=
  (fmap[J] f; eff_central f).

Lemma Effectful_Centre_respects {J : V ⟶ K} `{E : @EffectfulFunctor J}
      (x y : V) :
  Proper (equiv ==> equiv) (@Effectful_Centre_fmap J E x y).
Proof.
  intros f g eqv; simpl.
  now rewrite eqv.
Qed.

Lemma Effectful_Centre_id {J : V ⟶ K} `{E : @EffectfulFunctor J} (x : V) :
  @Effectful_Centre_fmap J E x x (@id V x)
    ≈ @id (Centre K) (fobj[J] x; ttt).
Proof.
  simpl.
  apply fmap_id.
Qed.

Lemma Effectful_Centre_comp {J : V ⟶ K} `{E : @EffectfulFunctor J}
      {x y z : V} (f : y ~{V}~> z) (g : x ~{V}~> y) :
  @Effectful_Centre_fmap J E x z (f ∘ g)
    ≈ @compose (Centre K) (fobj[J] x; ttt) (fobj[J] y; ttt) (fobj[J] z; ttt)
        (Effectful_Centre_fmap f) (Effectful_Centre_fmap g).
Proof.
  simpl.
  apply fmap_comp.
Qed.

Definition Effectful_Centre {J : V ⟶ K} `{E : @EffectfulFunctor J} :
  V ⟶ Centre K := {|
  fobj := fun x : V => ((fobj[J] x; ttt) : Centre K);
  fmap := fun (x y : V) (f : x ~{V}~> y) => Effectful_Centre_fmap f;
  fmap_respects := Effectful_Centre_respects;
  fmap_id := Effectful_Centre_id;
  fmap_comp := fun (x y z : V) (f : y ~{V}~> z) (g : x ~{V}~> y) =>
                 Effectful_Centre_comp f g
|}.

(** The factorization J = Incl ∘ Effectful_Centre is definitional on
    morphisms: including the centred image back into K returns exactly
    the original action of J. *)

Corollary Effectful_Centre_factors {J : V ⟶ K} `{E : @EffectfulFunctor J}
          {x y : V} (f : x ~{V}~> y) :
  fmap[Incl K (@CentralSub K BK)] (fmap[@Effectful_Centre J E] f)
    ≈ fmap[J] f.
Proof. reflexivity. Qed.

End Effectful.

(** ** Freyd categories

    A Freyd category over the monoidal (V, ⨂, I) and the premonoidal
    (K, ⊗, premon_I) is a functor J : V ⟶ K that

      - has a central image ([freyd_central]);
      - is bijective on objects, witnessed strictly by a section together
        with both Leibniz round-trip equalities;
      - preserves the unit and the tensor strictly on objects, and
        preserves the tensorings and the structural isomorphisms on
        morphisms up to the [id_cast] transports along those object
        equalities.

    The two tensoring fields relate V's joint tensor with an identity in
    one slot to K's one-sided tensorings ⋉ / ⋊, one field per slot; the
    unitor and associator fields express that J sends V's structural
    isomorphisms to K's, modulo the cast bookkeeping that connects
    J-images of compound objects with compounds of J-images.  In a fully
    strict situation (both instances in this file) every equality is
    [eq_refl], the composite equalities [eq_trans _ (f_equal _ _)]
    compute to [eq_refl], and every [id_cast] disappears
    definitionally. *)

Section Freyd.

Context {V K : Category}.
Context `{MV : @Monoidal V}.
Context `{BK : @Binoidal K}.
Context `{PK : @Premonoidal K BK}.

Class Freyd (J : V ⟶ K) := {
  (* Every morphism in the image of J is central in K. *)
  freyd_central {x y} (f : x ~{V}~> y) : central (fmap[J] f);

  (* Identity-on-objects, rendered as a strict object bijection. *)
  freyd_obj_section (k : K) : V;
  freyd_obj_eq (k : K) : fobj[J] (freyd_obj_section k) = k;
  freyd_sec_eq (v : V) : freyd_obj_section (fobj[J] v) = v;

  (* Strict preservation of the unit and the tensor on objects. *)
  freyd_obj_I : fobj[J] (@I V MV) = @premon_I K BK PK;
  freyd_obj_tensor {x y : V} :
    fobj[J] ((x ⨂ y)%object) = (fobj[J] x ⊗ fobj[J] y)%object;

  (* Morphism-level strictness of the two tensorings, transported by
     [id_cast]: tensoring with an identity in V maps to the one-sided
     tensoring in K. *)
  freyd_map_left {x y : V} (f : x ~{V}~> y) (z : V) :
    id_cast (@freyd_obj_tensor y z) ∘ fmap[J] (f ⨂ id[z])
      ≈ (fmap[J] f ⋉ fobj[J] z) ∘ id_cast (@freyd_obj_tensor x z);

  freyd_map_right {x y : V} (f : x ~{V}~> y) (z : V) :
    id_cast (@freyd_obj_tensor z y) ∘ fmap[J] (id[z] ⨂ f)
      ≈ (fobj[J] z ⋊ fmap[J] f) ∘ id_cast (@freyd_obj_tensor z x);

  (* J sends V's structural isomorphisms to K's, across the casts that
     mediate between J-images of compound objects and compounds of
     J-images. *)
  freyd_unit_left {x : V} :
    fmap[J] (to (@unit_left V MV x))
      ≈ to (@premon_unit_left K BK PK (fobj[J] x))
          ∘ id_cast
              (eq_trans (@freyd_obj_tensor (@I V MV) x)
                        (f_equal (fun i : K => (i ⊗ fobj[J] x)%object)
                                 freyd_obj_I));

  freyd_unit_right {x : V} :
    fmap[J] (to (@unit_right V MV x))
      ≈ to (@premon_unit_right K BK PK (fobj[J] x))
          ∘ id_cast
              (eq_trans (@freyd_obj_tensor x (@I V MV))
                        (f_equal (fun i : K => (fobj[J] x ⊗ i)%object)
                                 freyd_obj_I));

  freyd_assoc {x y z : V} :
    id_cast
        (eq_trans (@freyd_obj_tensor x ((y ⨂ z)%object))
                  (f_equal (fun i : K => (fobj[J] x ⊗ i)%object)
                           (@freyd_obj_tensor y z)))
      ∘ fmap[J] (to (@tensor_assoc V MV x y z))
      ≈ to (@premon_assoc K BK PK (fobj[J] x) (fobj[J] y) (fobj[J] z))
          ∘ id_cast
              (eq_trans (@freyd_obj_tensor ((x ⨂ y)%object) z)
                        (f_equal (fun i : K => (i ⊗ fobj[J] z)%object)
                                 (@freyd_obj_tensor x y)))
}.

(** Projecting away the strictness data leaves an effectful functor, so
    every Freyd category factors through the centre of its computation
    category ([Freyd_Centre] below, through [Effectful_Centre]).  Since
    the centre is monoidal ([Centre_Monoidal]), the value category of a
    Freyd category always maps into a monoidal subcategory of K. *)

Definition Freyd_Effectful {J : V ⟶ K} (F : Freyd J) :
  @EffectfulFunctor V K BK J :=
  @Build_EffectfulFunctor V K BK J
    (fun (x y : V) (f : x ~{V}~> y) => @freyd_central J F x y f).

Definition Freyd_Centre {J : V ⟶ K} (F : Freyd J) : V ⟶ Centre K :=
  @Effectful_Centre V K BK J (Freyd_Effectful F).

End Freyd.

(** ** The flagship instance: the Kleisli category of a strong monad

    The motivating example of Power–Thielecke 1999 and
    Levy–Power–Thielecke 2003, built on the premonoidal structure of
    Kl(M) established by Power–Robinson 1997.  For a strong monad M on a
    symmetric monoidal C, the pure functor [Kleisli_Pure] : C ⟶ Kl(M)
    is the identity on objects — [obj Kl(M)] is definitionally [obj C] —
    so the section is the identity and every object equality is
    [eq_refl].  All casts in the morphism-level fields therefore reduce
    to [id], and the fields collapse to:

      - the tensoring transfer laws [pure_inj_left]/[pure_inj_right] of
        Monad/Kleisli/Premonoidal.v (the η-compat laws of the two
        strengths, packaged);
      - reflexivity-level agreements for the unitors and associator,
        because the structural isomorphisms of [Kleisli_Premonoidal] are
        BY CONSTRUCTION the [kpure] images of C's.

    Centrality of the image is [pure_central] — the four double-strength
    unit laws of Monad/Strong/Symmetric.v, needing no commutativity. *)

Section FreydKleisli.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

Lemma Freyd_Kleisli_map_left {x y : C} (f : x ~{C}~> y) (z : C) :
  @compose Kleisli _ _ _ id (fmap[Kleisli_Pure] (f ⨂ id[z]))
    ≈ @compose Kleisli _ _ _
        (fmap[@inj_left Kleisli Kleisli_Binoidal z] (fmap[Kleisli_Pure] f))
        id.
Proof.
  rewrite id_left, id_right.
  symmetry.
  apply pure_inj_left.
Qed.

Lemma Freyd_Kleisli_map_right {x y : C} (f : x ~{C}~> y) (z : C) :
  @compose Kleisli _ _ _ id (fmap[Kleisli_Pure] (id[z] ⨂ f))
    ≈ @compose Kleisli _ _ _
        (fmap[@inj_right Kleisli Kleisli_Binoidal z] (fmap[Kleisli_Pure] f))
        id.
Proof.
  rewrite id_left, id_right.
  symmetry.
  apply pure_inj_right.
Qed.

Lemma Freyd_Kleisli_unit_left {x : C} :
  fmap[Kleisli_Pure] (to (@unit_left C _ x))
    ≈ @compose Kleisli _ _ _
        (to (@premon_unit_left Kleisli Kleisli_Binoidal Kleisli_Premonoidal x))
        id.
Proof. now rewrite id_right. Qed.

Lemma Freyd_Kleisli_unit_right {x : C} :
  fmap[Kleisli_Pure] (to (@unit_right C _ x))
    ≈ @compose Kleisli _ _ _
        (to (@premon_unit_right Kleisli Kleisli_Binoidal Kleisli_Premonoidal x))
        id.
Proof. now rewrite id_right. Qed.

Lemma Freyd_Kleisli_assoc {x y z : C} :
  @compose Kleisli _ _ _ id (fmap[Kleisli_Pure] (to (@tensor_assoc C _ x y z)))
    ≈ @compose Kleisli _ _ _
        (to (@premon_assoc Kleisli Kleisli_Binoidal Kleisli_Premonoidal x y z))
        id.
Proof. now rewrite id_left, id_right. Qed.

Definition Freyd_Kleisli :
  @Freyd C Kleisli _ Kleisli_Binoidal Kleisli_Premonoidal Kleisli_Pure :=
  @Build_Freyd C Kleisli _ Kleisli_Binoidal Kleisli_Premonoidal Kleisli_Pure
    (fun (x y : C) (f : x ~{C}~> y) => pure_central f)
    (fun k : Kleisli => (k : C))
    (fun k : Kleisli => eq_refl)
    (fun v : C => eq_refl)
    eq_refl
    (fun x y : C => eq_refl)
    (fun (x y : C) (f : x ~{C}~> y) (z : C) => Freyd_Kleisli_map_left f z)
    (fun (x y : C) (f : x ~{C}~> y) (z : C) => Freyd_Kleisli_map_right f z)
    (fun x : C => Freyd_Kleisli_unit_left)
    (fun x : C => Freyd_Kleisli_unit_right)
    (fun x y z : C => Freyd_Kleisli_assoc).

End FreydKleisli.

(** ** The degenerate instance: a monoidal category over itself

    Every monoidal category is a Freyd category over its own premonoidal
    reading (Structure/Premonoidal/Monoidal.v), with J the identity
    functor: the identity is bijective on objects on the nose, the
    binoidal tensor of [Monoidal_Binoidal] is definitionally the
    monoidal one, and every morphism is central by
    [Monoidal_all_central].  With a cartesian monoidal V this is the
    classical base point of the Freyd-category hierarchy: the effect-free
    computation category is the value category itself. *)

Section FreydId.

Context {V : Category}.
Context `{MV : @Monoidal V}.

Lemma Freyd_Id_map_left {x y : V} (f : x ~{V}~> y) (z : V) :
  id ∘ fmap[Id[V]] (f ⨂ id[z])
    ≈ fmap[@inj_left V (@Monoidal_Binoidal V MV) z] (fmap[Id[V]] f) ∘ id.
Proof. now rewrite id_left, id_right. Qed.

Lemma Freyd_Id_map_right {x y : V} (f : x ~{V}~> y) (z : V) :
  id ∘ fmap[Id[V]] (id[z] ⨂ f)
    ≈ fmap[@inj_right V (@Monoidal_Binoidal V MV) z] (fmap[Id[V]] f) ∘ id.
Proof. now rewrite id_left, id_right. Qed.

Lemma Freyd_Id_unit_left {x : V} :
  fmap[Id[V]] (to (@unit_left V MV x))
    ≈ to (@premon_unit_left V (@Monoidal_Binoidal V MV)
            (@Monoidal_Premonoidal V MV) x) ∘ id.
Proof. now rewrite id_right. Qed.

Lemma Freyd_Id_unit_right {x : V} :
  fmap[Id[V]] (to (@unit_right V MV x))
    ≈ to (@premon_unit_right V (@Monoidal_Binoidal V MV)
            (@Monoidal_Premonoidal V MV) x) ∘ id.
Proof. now rewrite id_right. Qed.

Lemma Freyd_Id_assoc {x y z : V} :
  id ∘ fmap[Id[V]] (to (@tensor_assoc V MV x y z))
    ≈ to (@premon_assoc V (@Monoidal_Binoidal V MV)
            (@Monoidal_Premonoidal V MV) x y z) ∘ id.
Proof. now rewrite id_left, id_right. Qed.

Definition Freyd_Id :
  @Freyd V V MV (@Monoidal_Binoidal V MV) (@Monoidal_Premonoidal V MV)
    (Id[V]) :=
  @Build_Freyd V V MV (@Monoidal_Binoidal V MV) (@Monoidal_Premonoidal V MV)
    (Id[V])
    (fun (x y : V) (f : x ~{V}~> y) => @Monoidal_all_central V MV x y f)
    (fun v : V => v)
    (fun v : V => eq_refl)
    (fun v : V => eq_refl)
    eq_refl
    (fun x y : V => eq_refl)
    (fun (x y : V) (f : x ~{V}~> y) (z : V) => Freyd_Id_map_left f z)
    (fun (x y : V) (f : x ~{V}~> y) (z : V) => Freyd_Id_map_right f z)
    (fun x : V => Freyd_Id_unit_left)
    (fun x : V => Freyd_Id_unit_right)
    (fun x y z : V => Freyd_Id_assoc).

End FreydId.
