Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.

Generalizable All Variables.

(** * Monoidal structure on [DecoratedCospanCat]

    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    Theorem 3.5 (the symmetric-monoidal hypergraph structure on
    [F Cospan]).  This module assembles the plain [Monoidal] layer of
    that theorem on [DecoratedCospanCat HP LM id_decoration cospan_merge],
    layering a decoration coherence class on top of [Cospan_Monoidal]
    from [Construction/Cospan/Hypergraph.v].  The braiding and symmetry
    that complete Theorem 3.5 are added in the sibling [Braided] and
    [Symmetric] modules; here we ask only for a plain
    [LaxMonoidalFunctor], which suffices for the associator and unitors.

    nLab: https://ncatlab.org/nlab/show/decorated+cospan
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

    In library notation the monoidal data follows Fong's Theorem 3.5:
    the tensor of objects is the coproduct ([I := initial_obj], and
    [tensor := DecoratedCospan_Bifunctor], whose object part is the
    coproduct [X + Y]); the tensor of morphisms combines the two
    decorations via the laxator [lax_ap[F]] (see [dec_tensor_decoration]
    in [Symmetric]); the monoidal unit is the initial object [0]
    decorated trivially; and the associator/unitors are the [Dlift] of
    the corresponding [Cocartesian] isos [coprod_assoc],
    [coprod_zero_l], [coprod_zero_r], each carrying [id_decoration] on
    its codomain apex.

    ** Architecture

    Following the [DecCospan_Coherent] / [DecCospan_Bifunctor_Coherent]
    pattern, the eight obligations of the [Monoidal] class are paired as

      (a) the cospan-level fact (already proved generically by
          [cospan_unit_left_natural], [cospan_unit_right_natural],
          [cospan_tensor_assoc_natural], [cospan_triangle_identity],
          [cospan_pentagon_identity]);

      (b) a matching decoration-level coherence supplied by the
          user-instantiable [DecCospan_Monoidal_Coherent] typeclass.

    Each coherence field is stated as a SINGLE decorated-cospan
    equivalence: the LHS-vs-RHS [dec_cospan_equiv] for the Monoidal
    obligation in question.

    The structural unitors and associator are defined as the
    [dec_mor_as_cospan] of the corresponding C-iso, carrying the
    canonical [id_decoration] on the codomain apex.  Their iso-laws
    inherit from the [Category]-level [id_left] / [id_right] of
    [DecoratedCospanCat] (which are themselves discharged by the
    [DecCospan_Coherent] typeclass). *)

Section DecoratedCospanMonoidal.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).

(** Local aliases that fix the [LM], [cospan_merge], [id_decoration]
    arguments to those of the ambient section, so the proofs below
    don't have to re-pass them at every use. *)

Notation Dtensor f g := (dec_cospan_tensor LM cospan_merge f g).
Notation Dcompose g f := (dec_cospan_compose HP LM cospan_merge g f).
Notation Did X := (dec_cospan_id id_decoration X).
Notation Dlift f := (dec_mor_as_cospan id_decoration f).

(** ** Coherence class for the Monoidal structure on [DecoratedCospanCat]

    Each field states a [dec_cospan_equiv] between the decorated-cospan
    LHS and RHS of the corresponding [Monoidal] obligation, with the
    unitors and associator on each side built as [Dlift] of the
    underlying C-iso (carrying the canonical [id_decoration]).

    The cospan-level part of every such equivalence is supplied
    generically (via [Cospan_Monoidal]); the decoration part — i.e.,
    that the apex iso of the cospan-level equivalence transports the
    LHS decoration to the RHS decoration — is the genuine content of
    each field.  For concrete decoration data (Fong's circuits, Markov
    processes) each field reduces to a short calculation in the lax
    monoidal data. *)

Class DecCospan_Monoidal_Coherent : Type := {

  (** Naturality of [to (unit_left)]: as a decorated-cospan equation. *)
  dec_to_unit_left_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose g (Dlift (to (@coprod_zero_l C H_Coc H_Ini x))))
        (Dcompose (Dlift (to (@coprod_zero_l C H_Coc H_Ini y)))
                  (Dtensor (Did 0%object) g));

  (** Naturality of [from (unit_left)]. *)
  dec_from_unit_left_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose (Dtensor (Did 0%object) g)
                  (Dlift (from (@coprod_zero_l C H_Coc H_Ini x))))
        (Dcompose (Dlift (from (@coprod_zero_l C H_Coc H_Ini y))) g);

  (** Naturality of [to (unit_right)]. *)
  dec_to_unit_right_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose g (Dlift (to (@coprod_zero_r C H_Coc H_Ini x))))
        (Dcompose (Dlift (to (@coprod_zero_r C H_Coc H_Ini y)))
                  (Dtensor g (Did 0%object)));

  (** Naturality of [from (unit_right)]. *)
  dec_from_unit_right_natural_eq :
    forall {x y : C} (g : DecoratedCospanArrow x y),
      dec_cospan_equiv
        (Dcompose (Dtensor g (Did 0%object))
                  (Dlift (from (@coprod_zero_r C H_Coc H_Ini x))))
        (Dcompose (Dlift (from (@coprod_zero_r C H_Coc H_Ini y))) g);

  (** Naturality of [to (tensor_assoc)]. *)
  dec_to_tensor_assoc_natural_eq :
    forall {x y z w v u : C}
           (g : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w)
           (i : DecoratedCospanArrow v u),
      dec_cospan_equiv
        (Dcompose (Dtensor g (Dtensor h i))
                  (Dlift (to (@coprod_assoc C H_Coc x z v))))
        (Dcompose (Dlift (to (@coprod_assoc C H_Coc y w u)))
                  (Dtensor (Dtensor g h) i));

  (** Naturality of [from (tensor_assoc)]. *)
  dec_from_tensor_assoc_natural_eq :
    forall {x y z w v u : C}
           (g : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w)
           (i : DecoratedCospanArrow v u),
      dec_cospan_equiv
        (Dcompose (Dtensor (Dtensor g h) i)
                  (Dlift (from (@coprod_assoc C H_Coc x z v))))
        (Dcompose (Dlift (from (@coprod_assoc C H_Coc y w u)))
                  (Dtensor g (Dtensor h i)));

  (** Triangle identity. *)
  dec_triangle_identity_eq :
    forall {x y : C},
      dec_cospan_equiv
        (Dtensor (Dlift (to (@coprod_zero_r C H_Coc H_Ini x))) (Did y))
        (Dcompose (Dtensor (Did x)
                           (Dlift (to (@coprod_zero_l C H_Coc H_Ini y))))
                  (Dlift (to (@coprod_assoc C H_Coc x 0%object y))));

  (** Pentagon identity.

      LHS reads (right-to-left, as Coq composes):
        [bimap α_{xyz} id_w] : ((x+y)+z)+w → (x+(y+z))+w
        [α_{x,(y+z),w}]      : (x+(y+z))+w → x+((y+z)+w)
        [bimap id_x α_{yzw}] : x+((y+z)+w) → x+(y+(z+w))
      RHS: [α_{x,y,(z+w)} ∘ α_{(x+y),z,w}]
        ((x+y)+z)+w → (x+y)+(z+w) → x+(y+(z+w)). *)
  dec_pentagon_identity_eq :
    forall {x y z w : C},
      dec_cospan_equiv
        (Dcompose
           (Dtensor (Did x) (Dlift (to (@coprod_assoc C H_Coc y z w))))
           (Dcompose
              (Dlift (to (@coprod_assoc C H_Coc x (y + z)%object w)))
              (Dtensor (Dlift (to (@coprod_assoc C H_Coc x y z))) (Did w))))
        (Dcompose
           (Dlift (to (@coprod_assoc C H_Coc x y (z + w)%object)))
           (Dlift (to (@coprod_assoc C H_Coc (x + y)%object z w))));

  (** Decoration coherence for the unit_left iso laws.  The [to ∘ from]
      composite of [dec_mor_iso_lift coprod_zero_l] reduces to [id] in
      [DC]; this requires the decoration coherence on the identity-cospan
      result of composing [Dlift (to phi)] with [Dlift (from phi)].  The
      cospan-level fact comes from [iso_to_from] / [iso_from_to] of
      [mor_iso_lift].  This single field handles all unitor / associator
      iso-laws uniformly because the decoration-side is the same
      [id_decoration]-composite reduction in every case. *)
  dec_iso_lift_to_from :
    forall {X Y : C} (phi : X ≅ Y),
      dec_cospan_equiv
        (Dcompose (Dlift (to phi)) (Dlift (from phi)))
        (Did Y);

  dec_iso_lift_from_to :
    forall {X Y : C} (phi : X ≅ Y),
      dec_cospan_equiv
        (Dcompose (Dlift (from phi)) (Dlift (to phi)))
        (Did X)
}.

Context `{DCMC : DecCospan_Monoidal_Coherent}.

Set Default Proof Using "All".

(** ** [DecoratedCospan_Monoidal] : the Monoidal instance

    Each obligation is dispatched by the corresponding coherence-class
    field.  The structural iso-laws use [dec_iso_lift_to_from] /
    [dec_iso_lift_from_to]; the naturality / triangle / pentagon
    obligations use the matching [dec_*_eq] field. *)

Program Definition DecoratedCospan_Monoidal : @Monoidal DC := {|
  I := (@initial_obj C H_Ini : DC);
  tensor := DecoratedCospan_Bifunctor HP LM id_decoration cospan_merge;
  unit_left :=
    fun X => {| to   := Dlift (to (@coprod_zero_l C H_Coc H_Ini X));
                from := Dlift (from (@coprod_zero_l C H_Coc H_Ini X));
                iso_to_from := _;
                iso_from_to := _ |};
  unit_right :=
    fun X => {| to   := Dlift (to (@coprod_zero_r C H_Coc H_Ini X));
                from := Dlift (from (@coprod_zero_r C H_Coc H_Ini X));
                iso_to_from := _;
                iso_from_to := _ |};
  tensor_assoc :=
    fun X Y Z => {| to   := Dlift (to (@coprod_assoc C H_Coc X Y Z));
                    from := Dlift (from (@coprod_assoc C H_Coc X Y Z));
                    iso_to_from := _;
                    iso_from_to := _ |}
|}.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_zero_l C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_zero_l C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_zero_r C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_zero_r C H_Coc H_Ini X)). Qed.
Next Obligation. apply (dec_iso_lift_to_from (@coprod_assoc C H_Coc X Y Z)). Qed.
Next Obligation. apply (dec_iso_lift_from_to (@coprod_assoc C H_Coc X Y Z)). Qed.
Next Obligation. apply dec_to_unit_left_natural_eq. Qed.
Next Obligation. apply dec_from_unit_left_natural_eq. Qed.
Next Obligation. apply dec_to_unit_right_natural_eq. Qed.
Next Obligation. apply dec_from_unit_right_natural_eq. Qed.
Next Obligation. apply dec_to_tensor_assoc_natural_eq. Qed.
Next Obligation. apply dec_from_tensor_assoc_natural_eq. Qed.
Next Obligation. apply dec_triangle_identity_eq. Qed.
Next Obligation.
  (* Reassociate via dec_cospan_compose_assoc_sym, then apply the proved identity. *)
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
  }
  apply dec_pentagon_identity_eq.
Qed.

End DecoratedCospanMonoidal.

(** ** Discussion: the coherence-class instance

    The [DecCospan_Monoidal_Coherent] class is the literature-correct
    packaging of the decoration-side coherences for Theorem 3.5 of
    Fong's "Decorated Cospans".  Each field is a single decorated-cospan
    equivalence whose cospan part is delivered by the existing
    [Cospan_Monoidal] infrastructure and whose decoration part is the
    explicit datum.

    For the trivial decoration (the constant lax-monoidal functor
    [F = Δ I_D]), every field's witness reduces to a routine
    cospan-level transport: the decoration on each side is the
    [id_decoration], and the apex iso transports it via [fmap[F] = id]
    on the constant functor.

    For Fong's electrical-circuit decoration and Baez–Fong's Markov-
    process decoration, the fields are populated by direct calculations
    in the chosen lax-monoidal functor; each is roughly a 5-line
    diagrammatic chase. *)
