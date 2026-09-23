Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * Colimits in the setoid variety, from the adjoint functor theorem *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
   nLab:      https://ncatlab.org/nlab/show/weak+excluded+middle
   Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)
   Wikipedia: https://en.wikipedia.org/wiki/Coequalizer
   Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
              §IV.2 (the adjoints of the diagonal, book p. 87), §V.6
              Theorem 2 (Freyd's adjoint functor theorem), §V.7
              Exercise 4 (book p. 128, PDF p. 137), §IX.1 Exercise 2
              (book p. 214, PDF p. 221)

   Colimits of algebras are not computed on underlying sets -- the
   coproduct of two groups is not their disjoint union -- and the
   adjoint functor theorem is the uniform way to get them: a category has
   all colimits of shape J exactly when the diagonal Δ[J] : C ⟶ [J, C]
   has a left adjoint (Mac Lane §IV.2), and Freyd's theorem produces that
   left adjoint from completeness, preservation of limits and a solution
   set.  Mac Lane asks for this in the two exercises this file answers,
   here for the SETOID VARIETY [SVariety E] of Instance/Variety/Free.v:
   coequalizers in a variety by the adjoint functor theorem (§V.7
   Exercise 4); every variety cocomplete by the same theorem, with its
   initial object described and the question "when is it empty" answered
   (§IX.1 Exercise 2).  §V.7's Exercises 1 and 2 (groups and rings) are
   not here.

   ** Which variety, and why not #440's

   Exercise 4 is delivered on [SVariety E], whose carriers are setoids
   and whose quotients are coarser `≈` on the same carrier (Free.v's
   header), and NOT on #440's Leibniz [Variety E] of Instance/Variety.v,
   whose carriers are bare types compared by [=].  The reason is a
   theorem, not a preference: [leibniz_coequalizers_iff_quotients] proves
   that coequalizers in the Leibniz variety of the EMPTY signature
   ([NoOp], [NoEq]) are exactly a quotient-type former for arbitrary
   [Prop]-valued relations, with its non-dependent eliminator and the
   uniqueness of maps out of it ([QuotElim]); [About] reads the
   biconditional back at [QuotElim@{u10 u11 u11 u11 u11}], the quotiented
   type, the quotient and both eliminator targets all at the variety's
   carrier universe [u11].  Forward, the coequalizer of
   the two projections out of the relation's graph is the quotient;
   backward, the quotient by "is the image of a common element" is the
   coequalizer.  This tree has no such former (Instance/Variety/
   GroupComparison.v's header records that no quotient of a setoid by its
   own equivalence returns a TYPE), so the Leibniz variety has no
   coequalizers here uniformly in [E] -- already at [NoEq] it would get
   them only together with quotient types.  The qualifier matters: for a
   degenerate [E] the Leibniz variety does have coequalizers without
   quotients -- if [E] is the equation x = y over the empty signature,
   every carrier is a subsingleton, any two parallel arrows agree, and
   the codomain with its identity is their coequalizer (an argument
   recorded here, not a constant in tree); the boundary theorem is
   stated at [NoEq] only.  No claim is made that [QuotElim] is
   unprovable in Coq.

   ** Names

   Issue #450 suggests a module Instance/Variety/Coequalizer.v, and its
   verification block runs [Print Assumptions Variety_coequalizers].
   Neither name is used (measured: [grep -rnw Variety_coequalizers] over
   the [.v] files finds only this paragraph).  The coequalizers are this
   file's [SVariety_coequalizers_via_GAFT], on [SVariety E]; a constant
   named [Variety_coequalizers] would suggest #440's Leibniz [Variety E],
   the category the section above shows has no coequalizers here.

   ** The method: the adjoint functor theorem at the diagonal

   [SVariety_colim_via_GAFT E J] is [GAFT] (Adjunction/GAFT.v) applied to
   [@Diagonal (SVariety E) J] with its three inputs:

     - completeness, Instance/Variety/Limit.v's [SVariety_Complete];
     - preservation, Adjunction/Diagonal/Limit.v's [Diagonal_continuous]
       through Construction/Comma/Creation.v's
       [Continuous_PreservesImageLimit];
     - at each diagram [D], the solution set
       [Diagonal_SVariety_solution_set]: its index [VCongIdx] is the
       [Prop]-valued congruences ([IsVCong]) on the term algebra over the
       disjoint union [SVGen] of the carriers that satisfy [E], make every
       insertion a homomorphism respecting `≈`, and make the insertions a
       cocone; the member at an index is the term algebra modulo it; a
       cocone into [c] is covered by the KERNEL of its extension along
       the term algebra ([vker]), with the extension itself ([vker_ev]) as
       the mediator and the covering equation [reflexivity] per element.

   The kernel is a [Prop] only because [c] carries [soa_prop]
   (Instance/Variety/Free.v's header, "The carrier's `≈` is a
   proposition"): read through [pequiv], it is a relation on a type at
   the carrier universe that lives in the carrier universe, which is what
   Structure/Complete.v's size note says a solution-set index must do.
   A family indexed by a Σ over the OBJECTS of [SVariety E] would sit one
   universe too high (the size note, item 3; Instance/Variety/Spanning.v
   records the refusal at its [variety_solution_set]).

   From the left adjoint, Adjunction/Diagonal/Limit.v's
   [Diagonal_left_adjoint_HasColimits] reads off the colimit of every
   J-shaped diagram, and [SVariety_Cocomplete_via_GAFT] is §IX.1
   Exercise 2's cocompleteness.  The binary coproduct, the coequalizers and
   an initial object come from Structure/Limit/Finite.v's existing
   bridges and no new one: [SVariety_Cocartesian_via_GAFT] through
   [FinitelyComplete_Cartesian] of
   [FinitelyCocomplete_FinitelyComplete_op], [SVariety_coequalizers_via_GAFT]
   (§V.7 Exercise 4) through [HasCoequalizers_of_HasEqualizers_op] of
   [FinitelyComplete_HasEqualizers], and [SVariety_Initial_via_GAFT]
   through [FinitelyCocomplete_Initial].  Read off the bodies of those
   bridges (Instance/Grp/Colimit.v's FINITE COLIMITS gives the detail):
   the coproduct is the AFT pushout over the AFT initial object, the
   coequalizer of Exercise 4 is ASSEMBLED from AFT pushouts and the AFT
   initial object, and the initial object is the AFT colimit of the
   empty diagram; every one of those colimits is itself a [GAFT] colimit
   at a diagonal.  The direct reading -- the coproduct as [GAFT]'s
   colimit over a discrete two-object shape, the coequalizer as its
   colimit over the walking parallel pair, the reading closest to Mac
   Lane's wording -- is NOT the one used; the same bridge assembly
   serves all three categories of #450.  At a presentation whose
   [EqSignature] is built without extensionality they are closed
   constants: [CommMagma_Cocartesian] and [CommMagma_coequalizers], at
   #440's [CommEq] (Instance/Variety.v, gated there).

   ** The initial object, and when it is empty

   [SVariety_Initial] is the free algebra on the empty set, for every
   ⟨Ω,E⟩: [Free_Variety E] at [Sets]'s initial object, initial because a
   map out of the empty set exists uniquely and Free.v's
   [free_alg_hom_unique] makes the extension unique.  Its carrier IS the
   closed terms, [UA.Tree S False], at [eq_refl]
   ([SVariety_Initial_carrier]), and [SVariety_Initial_agrees] identifies
   it with the adjoint functor theorem's initial object up to
   isomorphism.

   Mac Lane's "when is Alg_τ empty" cannot be about the CATEGORY, which
   is never empty: [SVariety_Terminal] is the limit of the empty diagram
   (Structure/Limit/Finite.v's [FinitelyComplete_Terminal] at its
   [EmptyShape]), whose carrier is the compatible families over no
   index, all of them `≈` -- the one-element algebra up to `≈`, which
   satisfies every equation -- as Instance/Comp.v's [Algs_Terminal] is
   for the equation-free algebras.
   It is read as a statement about the initial algebra's carrier, and
   answered constructively:

     - [closed_terms_empty_iff]: the closed terms are empty exactly when
       every operation's arity is NOT empty (double negation, both
       directions by plain induction and one [node]);
     - [closed_terms_empty_iff_no_constant], the book's own wording:
       empty exactly when no operation is a constant, a constant being
       an operation whose arity is empty; and
       [SVariety_initial_empty_iff] states it at the initial object of
       ⟨Ω,E⟩ -- independent of [E], since equations change `≈` and not
       the carrier.

   The converse direction "inhabited ⇒ some constant" needs more.
   [dec_closed_term_constant] proves it under decidable emptiness of each
   arity, which holds in the book's finitary case (a finite arity is
   decidably empty).  [closed_term_constant_implies_WLEM]
   shows the hypothesis cannot simply be dropped: stated uniformly in the
   signature, the converse implies weak excluded middle, ¬P ∨ ¬¬P for
   every proposition P, which intuitionistic logic does not prove (nLab,
   "weak excluded middle").  The witness signature [WLEM_sig P] has two
   operations of arities [P] and [¬P]; it always has the closed term
   [WLEM_term P], and a constant of it is exactly a proof of ¬P or of
   ¬¬P.

   ** Mac Lane's own route to the free algebra

   The same method at the forgetful functor: [SVariety_Forget_solution_set]
   is indexed by the [Prop]-valued congruences on the term algebra over
   [X] ([IsFCong]), a map into [c] being covered by the kernel of
   Free.v's [free_alg_ext]; with [SVariety_Complete] and
   Instance/Variety/Limit.v's [SVariety_Forget_continuous],
   [Free_Variety_via_GAFT] is Mac Lane §V.6's construction of the free
   algebra, and [Free_Variety_via_GAFT_agrees] identifies its left
   adjoint with Free.v's [Free_Variety_Functor] up to natural isomorphism
   (Theory/Adjunction.v's [left_adjoint_iso]).  The congruence index
   REPLACES Mac Lane's family of generated subalgebras rather than
   bounding its size, as Instance/Grp/FreeAFT.v's does for groups.

   ** Universes, measured

   With [About] under [Set Printing Universes], the stdlib-global bounds
   ([Projections], [compose], [eq_ind], [prod_rect], [JMeq], [Fin.case0],
   [VectorDef] and the like) dropped:

     VCongIdx : … (E : UA.EqSignature@{u1 u2 u3 u4 u u0} S)
                  {J : Category@{u5 u6 u6}}, J ⟶ SVariety E → Type@{u16}
     (* Set < u16 / u3 <= u16 / u5 <= u3 / u3 = u4 / … *)

   so the index may sit AT the carrier universe [u3]; its only strict
   lower bound is [Set].

     SVariety_colim_via_GAFT : … (E : UA.EqSignature@{u8 u9 u3 u3 u6 u7} S)
       (J : Category@{u10 u3 u3}),
       ∃ L : [J, SVariety E] ⟶ SVariety E, L ⊣ Diagonal J
     (* Set < u3 / u3 < u0 / u10 <= u3 / u6 <= u3 / u7 <= u3 / … *)

     SVariety_Cocomplete_via_GAFT :
       … (E : UA.EqSignature@{u9 u10 u u u7 u8} S), Cocomplete@{u u0 u u1}
     (* Set < u / u < u2 / u0 <= u / u2 <= u1 / … *)

   THE SHAPE DISCIPLINE this imposes: a shape's homs are AT the carrier
   universe and its objects at or below it.  That is
   [SVariety_Complete]'s discipline ([Complete@{u u4 u u5}] with
   [u4 <= u]); [Sets_Complete@{u u0} : Complete@{u u u u0}] is stricter,
   its shapes' objects AT the carrier universe, [Category] not being
   cumulative.  Instance/Two/Discrete.v's
   [Two_Discrete] is [Category@{u Set Set}], its homs at [Set], and is
   refused as a shape: [SVariety_colim_via_GAFT E Two_Discrete] stops
   with "universe inconsistency: Cannot enforce Set = TD.57 because Set <
   TD.57" (a scratch file's name for the carrier universe), while
   [SVariety_colim_via_GAFT E (DiscreteCat bool)] is accepted by the same
   file.  The binary coproduct above comes through
   Structure/Limit/Finite.v, whose finite shapes fit the discipline.  The
   one new side condition is [Set < carrier], and, as for groups and
   rings (Instance/Grp/Colimit.v and Instance/Rng/Colimit.v), it is
   [GAFT]'s: [GAFT] puts its solution set's index AT the carrier
   universe, while the congruence index -- carrier-sized because
   [soa_prop] makes each kernel a [Prop] -- sits strictly above [Set],
   an index of [Prop]-valued relations.  The solution set itself
   elaborates at a [Set] carrier, and so does [GAFT] applied to every
   argument but it; only the full application is refused there
   (Test/ProbeVarietyColimit450.v's N4 and its two controls).  No
   universe is instantiated at [Set].

     Free_Variety_via_GAFT :
       … (E : UA.EqSignature@{u7 u8 u9 u9 u5 u6} S),
       ∃ F : Sets@{u9 u2} ⟶ SVariety E, F ⊣ SVariety_Forget E
     (* Set < u9 / u9 < u2 / u5 <= u9 / u6 <= u9 / … *)

   ** Transparency, measured

   Each [Defined] was flipped to [Qed] in a scratch copy of this file.
   Load-bearing: [vq_leg] (stops [vq_arr]); [vq_arr] and [vker_med] (stop
   the covering equation of [Diagonal_SVariety_solution_set], which is
   [reflexivity]); [fq_arr] and [fker_med] (the same, for
   [SVariety_Forget_solution_set]); [SVariety_Initial] (stops the
   [eq_refl] of [SVariety_Initial_carrier]); [NoEq] (stops [bare_alg],
   which destructs its equations); [bare_alg] (stops [bare_hom]); and
   [bare_hom] (stops [leibniz_coequalizers_give_quotients]).  The other
   six -- both solution sets, [dec_closed_term_constant] and the three
   Leibniz theorems -- flip with the file still compiling.  [GAFT] itself
   ends in [Qed], so every colimit and the GAFT free algebra are OPAQUE:
   no [eq_refl] readback of their carriers is possible or claimed.

   ** Assumptions, measured

   [Print Assumptions] on every constant of the module, enumerated by
   [Print Module] (heads, the two records [IsVCong] and [IsFCong] with
   their constructors and projections, and [Program] obligations, which
   [.glob] heads omit) returns "Closed under the global context" for
   each, [CommMagma_Cocartesian] and [CommMagma_coequalizers] among them.
   Instantiating any of this at Instance/Comp.v's [UA.GroupEq] inherits
   [functional_extensionality_dep] from the building of that
   [EqSignature] (Instance/Variety/Free.v's header says why); no such
   instance is named here, so none is gated.

   ** Not delivered

   No explicit, transparent colimit: the term algebra modulo the LEAST
   cocone congruence (an impredicative intersection of the [IsVCong]
   relations) would be one, and is not built -- every colimit here is
   [GAFT]'s.  No colimits at shapes outside the discipline above.  No
   coequalizers for #440's Leibniz variety, for the reason proved above,
   and the boundary lemma is stated for the empty signature only.  No
   "inhabited ⇒ some constant" without the decidability hypothesis.  No
   comparison of the coproduct with any explicit construction (Free.v's
   [soa_prod] is a product, not a coproduct).  No preservation or
   creation of colimits by any functor, and nothing on filtered colimits,
   Mac Lane's primary route in §IX.1.  §V.7 Exercises 1 and 2 (the free
   product of groups and the coproduct of rings) are not in this file. *)

Module UA := Category.Instance.Comp.UniversalAlgebra.

#[local] Obligation Tactic := idtac.

(** ** Block A: a solution set for the diagonal *)

Section DiagonalSolutionSet.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (D : J ⟶ SVariety E).

(* The generators: the disjoint union of the carriers of the diagram, as a
   BARE type.  Respect for each component's `≈` is imposed by the
   congruence ([vc_resp]), not by a setoid on the generators. *)
Definition SVGen : Type := { j : J & carrier (soa_obj (`1 (D j))) }.

Definition svgen (j : J) (x : carrier (soa_obj (`1 (D j)))) : UA.Tree S SVGen :=
  UA.generator S SVGen (j; x).

(* A [Prop]-valued congruence on the term algebra over the generators that
   satisfies [E], makes every insertion a homomorphism respecting `≈`, and
   makes the insertions a cocone.  The fields [vc_resp] and [vc_nat] STORE
   the components' [Type]-valued `≈` and [fmap[D]] as premises; the record
   itself is a [Prop]. *)
Record IsVCong (Rq : UA.Tree S SVGen → UA.Tree S SVGen → Prop) : Prop := {
  vc_refl  : ∀ t, Rq t t;
  vc_sym   : ∀ t u, Rq t u → Rq u t;
  vc_trans : ∀ t u v, Rq t u → Rq u v → Rq t v;
  vc_op    : ∀ o (k1 k2 : UA.arity o → UA.Tree S SVGen),
               (∀ i, Rq (k1 i) (k2 i)) →
               Rq (UA.node S SVGen o k1) (UA.node S SVGen o k2);
  vc_law   : ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.Tree S SVGen),
               Rq (@UA.lhs S E (UA.Free S SVGen) e args)
                  (@UA.rhs S E (UA.Free S SVGen) e args);
  vc_resp  : ∀ j (x y : carrier (soa_obj (`1 (D j)))),
               x ≈ y → Rq (svgen j x) (svgen j y);
  vc_hom   : ∀ j o (k : UA.arity o → carrier (soa_obj (`1 (D j)))),
               Rq (svgen j (soa_op (`1 (D j)) o k))
                  (UA.node S SVGen o (fun i => svgen j (k i)));
  vc_nat   : ∀ j j' (f : j ~{J}~> j') (x : carrier (soa_obj (`1 (D j)))),
               Rq (svgen j' (salg_map (`1 (fmap[D] f)) x)) (svgen j x)
}.

Definition VCongIdx : Type :=
  { Rq : UA.Tree S SVGen → UA.Tree S SVGen → Prop & IsVCong Rq }.

Definition VQ_setoid (i : VCongIdx) : Setoid (UA.Tree S SVGen) :=
  {| equiv := `1 i
   ; setoid_equiv := {| Equivalence_Reflexive  := vc_refl  (`1 i) (`2 i)
                      ; Equivalence_Symmetric  := vc_sym   (`1 i) (`2 i)
                      ; Equivalence_Transitive := vc_trans (`1 i) (`2 i) |} |}.

(* The member at index [i]: the term algebra with `≈` the congruence.  Its
   [PropEquiv] is the congruence itself, and its satisfaction of [E] is
   [vc_law]. *)
Definition VQ_soa (i : VCongIdx) : SetoidOpAlgebra S := {|
  soa_obj := {| carrier := UA.Tree S SVGen ; is_setoid := VQ_setoid i |};
  soa_op := UA.node S SVGen;
  soa_op_respects := vc_op (`1 i) (`2 i);
  soa_prop := @PropEquiv_of_relation _ (VQ_setoid i) (`1 i)
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition VQ_alg (i : VCongIdx) : SVariety E :=
  (VQ_soa i; vc_law (`1 i) (`2 i)).

Definition vq_leg (i : VCongIdx) (j : J) : D j ~{SVariety E}~> VQ_alg i.
Proof.
  unshelve refine (@Build_SAlgHom S (`1 (D j)) (VQ_soa i) (svgen j) _ _; I).
  - intros x y Hxy; exact (vc_resp (`1 i) (`2 i) j x y Hxy).
  - intros o k; exact (vc_hom (`1 i) (`2 i) j o k).
Defined.

(* The arrow of the solution set: the cocone of insertions, as an arrow of
   [[J, SVariety E]] into the constant diagram. *)
Definition vq_arr (i : VCongIdx) :
  D ~{[J, SVariety E]}~> fobj[@Diagonal (SVariety E) J] (VQ_alg i).
Proof.
  unshelve refine (@Build_Transform J (SVariety E) D
                     (fobj[@Diagonal (SVariety E) J] (VQ_alg i))
                     (fun j => vq_leg i j) _ _).
  - intros j j' f x; simpl.
    apply (vc_sym (`1 i) (`2 i)); exact (vc_nat (`1 i) (`2 i) j j' f x).
  - intros j j' f x; simpl.
    exact (vc_nat (`1 i) (`2 i) j j' f x).
Defined.

(* The covering.  A cocone [h] into [c] extends along the term algebra by
   Instance/Comp.v's [induced_map]; its KERNEL, read through [c]'s
   [PropEquiv], is a [Prop]-valued congruence of the kind indexed above,
   and the extension itself is the mediator.  The kernel is a [Prop] only
   because [c] carries [soa_prop]: this is where the field is consumed. *)
Section Kernel.

Context (c : SVariety E).
Context (h : D ~{[J, SVariety E]}~> fobj[@Diagonal (SVariety E) J] c).

Definition vker_ev : UA.Tree S SVGen → carrier (soa_obj (`1 c)) :=
  UA.induced_map S SVGen (soa_alg (`1 c))
    (fun p => salg_map (`1 (@transform _ _ _ _ h (`1 p))) (`2 p)).

Definition vker (t u : UA.Tree S SVGen) : Prop :=
  @pequiv _ _ (soa_prop (`1 c)) (vker_ev t) (vker_ev u).

Lemma vker_cong : IsVCong vker.
Proof.
  unfold vker; constructor.
  - intro t; apply pequiv_from; reflexivity.
  - intros t u H; apply pequiv_from; symmetry; exact (pequiv_to _ _ H).
  - intros t u v H1 H2; apply pequiv_from;
      exact (transitivity (pequiv_to _ _ H1) (pequiv_to _ _ H2)).
  - intros o k1 k2 H; apply pequiv_from; simpl.
    apply (soa_op_respects (`1 c) o); intro i; exact (pequiv_to _ _ (H i)).
  - intros e args; apply pequiv_from; unfold vker_ev.
    set (g := fun p : SVGen => salg_map (`1 (@transform _ _ _ _ h (`1 p))) (`2 p)).
    assert (HL : UA.induced_map S SVGen (soa_alg (`1 c)) g
                   (@UA.lhs S E (UA.Free S SVGen) e args)
                 = @UA.lhs S E (soa_alg (`1 c)) e
                     (fun i => UA.induced_map S SVGen (soa_alg (`1 c)) g (args i)))
      by exact (@UA.lhs_natural S E (UA.Free S SVGen) (soa_alg (`1 c))
                  (UA.induced_hom S SVGen (soa_alg (`1 c)) g) e args).
    assert (HR : UA.induced_map S SVGen (soa_alg (`1 c)) g
                   (@UA.rhs S E (UA.Free S SVGen) e args)
                 = @UA.rhs S E (soa_alg (`1 c)) e
                     (fun i => UA.induced_map S SVGen (soa_alg (`1 c)) g (args i)))
      by exact (@UA.rhs_natural S E (UA.Free S SVGen) (soa_alg (`1 c))
                  (UA.induced_hom S SVGen (soa_alg (`1 c)) g) e args).
    rewrite HL, HR.
    exact (`2 c e (fun i => UA.induced_map S SVGen (soa_alg (`1 c)) g (args i))).
  - intros j x y Hxy; apply pequiv_from; simpl.
    exact (salg_respects (`1 (@transform _ _ _ _ h j)) x y Hxy).
  - intros j o k; apply pequiv_from; simpl.
    exact (salg_commute (`1 (@transform _ _ _ _ h j)) o k).
  - intros j j' f x; apply pequiv_from; simpl.
    symmetry; exact (@naturality _ _ _ _ h j j' f x).
Qed.

Definition vker_idx : VCongIdx := (vker; vker_cong).

Definition vker_med : VQ_alg vker_idx ~{SVariety E}~> c.
Proof.
  unshelve refine (@Build_SAlgHom S (VQ_soa vker_idx) (`1 c) vker_ev _ _; I).
  - intros t u H; exact (pequiv_to _ _ H).
  - intros o k; simpl; reflexivity.
Defined.

End Kernel.

Definition Diagonal_SVariety_solution_set :
  SolutionSet (@Diagonal (SVariety E) J) D.
Proof.
  unshelve refine (@Build_SolutionSet (SVariety E) ([J, SVariety E])
                     (@Diagonal (SVariety E) J) D VCongIdx VQ_alg vq_arr _).
  intros c h.
  exists (vker_idx c h), (vker_med c h).
  intros j x; simpl; reflexivity.
Defined.

End DiagonalSolutionSet.

Arguments SVGen {_} _ {_} _.
Arguments svgen {_} _ {_} _ _ _.
Arguments IsVCong {_} _ {_} _ _.
Arguments VCongIdx {_} _ {_} _.
Arguments VQ_setoid {_} _ {_} _ _.
Arguments VQ_soa {_} _ {_} _ _.
Arguments VQ_alg {_} _ {_} _ _.
Arguments vq_leg {_} _ {_} _ _ _.
Arguments vq_arr {_} _ {_} _ _.
Arguments vker_ev {_} _ {_} _ _ _ _.
Arguments vker {_} _ {_} _ _ _ _ _.
Arguments vker_cong {_} _ {_} _ _ _.
Arguments vker_idx {_} _ {_} _ _ _.
Arguments vker_med {_} _ {_} _ _ _.
Arguments Diagonal_SVariety_solution_set {_} _ {_} _.

(** ** Block B: the adjoint functor theorem at the diagonal *)

Definition SVariety_colim_via_GAFT {S : UA.OpSignature} (E : UA.EqSignature S)
  (J : Category) :
  { L : [J, SVariety E] ⟶ SVariety E & L ⊣ @Diagonal (SVariety E) J } :=
  GAFT (@Diagonal (SVariety E) J) (SVariety_Complete E)
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_SVariety_solution_set S E J).

Definition SVariety_Cocomplete_via_GAFT {S : UA.OpSignature}
  (E : UA.EqSignature S) : @Cocomplete (SVariety E) :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (SVariety_colim_via_GAFT E J)) F.

Definition SVariety_Cocartesian_via_GAFT {S : UA.OpSignature}
  (E : UA.EqSignature S) : @Cocartesian (SVariety E) :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op
       (Cocomplete_FinitelyCocomplete (SVariety_Cocomplete_via_GAFT E))).

Definition SVariety_coequalizers_via_GAFT {S : UA.OpSignature}
  (E : UA.EqSignature S) : HasCoequalizers (SVariety E) :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op
          (Cocomplete_FinitelyCocomplete (SVariety_Cocomplete_via_GAFT E)))).

Definition SVariety_Initial_via_GAFT {S : UA.OpSignature}
  (E : UA.EqSignature S) : @Initial (SVariety E) :=
  FinitelyCocomplete_Initial
    (Cocomplete_FinitelyCocomplete (SVariety_Cocomplete_via_GAFT E)).

(** ** Block C: the initial algebra is the free algebra on the empty set *)

(* The category is never empty: the limit of the empty diagram is a
   terminal object, and Instance/Variety/Limit.v computes it. *)
Definition SVariety_Terminal {S : UA.OpSignature} (E : UA.EqSignature S) :
  @Terminal (SVariety E) :=
  FinitelyComplete_Terminal (Complete_FinitelyComplete (SVariety_Complete E)).

Definition SVariety_Initial {S : UA.OpSignature} (E : UA.EqSignature S) :
  @Initial (SVariety E).
Proof.
  unshelve refine (@Build_Terminal ((SVariety E)^op)
                     (Free_Variety E (@initial_obj Sets _))
                     (fun c => free_alg_hom c (@zero Sets _ (SVariety_Forget E c))) _).
  intros c f g. apply (free_alg_hom_unique c f g). intros [].
Defined.

Example SVariety_Initial_carrier {S : UA.OpSignature} (E : UA.EqSignature S) :
  carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
    = UA.Tree S False := eq_refl.

Definition SVariety_Initial_agrees {S : UA.OpSignature} (E : UA.EqSignature S) :
  @initial_obj (SVariety E) (SVariety_Initial E)
    ≅ @initial_obj (SVariety E) (SVariety_Initial_via_GAFT E) :=
  initial_unique (SVariety_Initial E) (SVariety_Initial_via_GAFT E).

(** ** Block D: when the initial algebra's carrier is empty *)

Section ClosedTerms.

Context (S : UA.OpSignature).

Theorem closed_terms_empty_iff :
  (UA.Tree S False → False) ↔
  (∀ o : UA.operation S, (UA.arity o → False) → False).
Proof.
  split.
  - intros H o n. apply H. exact (UA.node S False o (fun i => False_rect _ (n i))).
  - intros H t. induction t as [ x | o k IH ].
    + exact x.
    + exact (H o IH).
Qed.

Definition constant_closed_term :
  { o : UA.operation S & UA.arity o → False } → UA.Tree S False :=
  fun c => UA.node S False (`1 c) (fun i => False_rect _ (`2 c i)).

Definition dec_closed_term_constant
  (dec : ∀ o : UA.operation S, (UA.arity o → False) + UA.arity o) :
  UA.Tree S False → { o : UA.operation S & UA.arity o → False }.
Proof.
  intro t. induction t as [ x | o k IH ].
  - destruct x.
  - destruct (dec o) as [ n | i ].
    + exact (o; n).
    + exact (IH i).
Defined.

Lemma closed_term_nn_constant :
  UA.Tree S False →
  ((∀ o : UA.operation S, (UA.arity o → False) → False) → False).
Proof. intros t H. exact (snd closed_terms_empty_iff H t). Qed.

Theorem closed_terms_empty_iff_no_constant :
  (UA.Tree S False → False) ↔
  ({ o : UA.operation S & UA.arity o → False } → False).
Proof.
  split.
  - intros H c. exact (H (constant_closed_term c)).
  - intros H. apply (snd closed_terms_empty_iff).
    intros o n. exact (H (o; n)).
Qed.

End ClosedTerms.

Theorem SVariety_initial_empty_iff {S : UA.OpSignature} (E : UA.EqSignature S) :
  (carrier (soa_obj (`1 (@initial_obj (SVariety E) (SVariety_Initial E))))
     → False) ↔
  ({ o : UA.operation S & UA.arity o → False } → False).
Proof. exact (closed_terms_empty_iff_no_constant S). Qed.

Definition WLEM_sig (P : Prop) : UA.OpSignature :=
  {| UA.operation := bool
   ; UA.arity := fun b => if b then P else (P → False) |}.

Definition WLEM_term (P : Prop) : UA.Tree (WLEM_sig P) False :=
  UA.node (WLEM_sig P) False true
    (fun p => UA.node (WLEM_sig P) False false
                (fun np => False_rect _ (np p))).

Theorem closed_term_constant_implies_WLEM :
  (∀ S : UA.OpSignature,
     UA.Tree S False → { o : UA.operation S & UA.arity o → False }) →
  ∀ P : Prop, (P → False) + ((P → False) → False).
Proof.
  intros H P.
  destruct (H (WLEM_sig P) (WLEM_term P)) as [ [|] n ].
  - left; exact n.
  - right; exact n.
Qed.

(** ** Block E: the Leibniz variety, where coequalizers are quotients *)

Definition NoOp : UA.OpSignature :=
  {| UA.operation := Empty_set ; UA.arity := fun o => match o with end |}.

Definition NoEq : UA.EqSignature NoOp.
Proof.
  unshelve refine {| UA.eq := Empty_set ; UA.eq_arity := fun e => match e with end |}.
  - intros A e; destruct e.
  - intros A e; destruct e.
  - intros A B f e; destruct e.
  - intros A B f e; destruct e.
Defined.

Definition bare_alg (A : Type) : Variety NoEq.
Proof.
  unshelve refine (UA.Build_OpAlgebra NoOp A _; _).
  - intros o; destruct o.
  - intros e; destruct e.
Defined.

Definition bare_hom {A B : Type} (f : A → B) :
  bare_alg A ~{Variety NoEq}~> bare_alg B.
Proof.
  unshelve refine (@UA.Build_AlgHom NoOp (`1 (bare_alg A)) (`1 (bare_alg B)) f _; I).
  intros o; destruct o.
Defined.

Definition QuotElim : Type :=
  ∀ (A : Type) (R : A → A → Prop),
    { Q : Type & { q : A → Q &
      ((∀ a b, R a b → q a = q b) *
       (∀ (B : Type) (f : A → B), (∀ a b, R a b → f a = f b) →
          { g : Q → B & ∀ a, g (q a) = f a }) *
       (∀ (B : Type) (g g' : Q → B), (∀ a, g (q a) = g' (q a)) →
          ∀ z, g z = g' z))%type } }.

(* Any function out of the carrier of an algebra of the empty signature
   is a homomorphism: there is no operation to commute with. *)
Definition noop_hom {x y : Variety NoEq}
  (f : UA.carrier (`1 x) → UA.carrier (`1 y)) : x ~{Variety NoEq}~> y :=
  (@UA.Build_AlgHom NoOp (`1 x) (`1 y) f (fun o => match o with end); I).

Theorem leibniz_coequalizers_give_quotients :
  HasCoequalizers (Variety NoEq) → QuotElim.
Proof.
  intros HC A R.
  set (K := { p : A * A & R (fst p) (snd p) }).
  destruct (@coeq _ HC (bare_alg K) (bare_alg A)
              (bare_hom (fun p : K => fst (`1 p)))
              (bare_hom (fun p : K => snd (`1 p))))
    as [Qo [e He]].
  exists (UA.carrier (`1 Qo)), (UA.map (`1 e)).
  refine ((_, _), _).
  - intros a b r. exact (cofork He ((a, b); r)).
  - intros B f Hf.
    destruct (coeq_desc He (bare_hom (B:=B) f) (fun p => Hf _ _ (`2 p)))
      as [u Hu _].
    exists (UA.map (`1 u)). exact Hu.
  - intros B g g' Hg z.
    set (h := @noop_hom Qo (bare_alg B) g ∘ e).
    assert (Hh : h ∘ bare_hom (fun p : K => fst (`1 p))
                 ≈ h ∘ bare_hom (fun p : K => snd (`1 p))).
    { intro p; simpl; f_equal; exact (cofork He p). }
    destruct (coeq_desc He h Hh) as [u Hu Huniq].
    pose proof (Huniq (@noop_hom Qo (bare_alg B) g) (fun a => eq_refl)) as H1.
    pose proof (Huniq (@noop_hom Qo (bare_alg B) g')
                  (fun a => eq_sym (Hg a))) as H2.
    exact (eq_trans (eq_sym (H1 z)) (H2 z)).
Defined.

Theorem quotients_give_leibniz_coequalizers :
  QuotElim → HasCoequalizers (Variety NoEq).
Proof.
  intros HQ; constructor; intros x y f g.
  set (R := fun b b' : UA.carrier (`1 y) =>
              ex (fun a => and (UA.map (`1 f) a = b) (UA.map (`1 g) a = b'))).
  destruct (HQ _ R) as [Q [q [[Hresp Hlift] Huniq]]].
  exists (bare_alg Q), (@noop_hom y (bare_alg Q) q).
  unshelve econstructor.
  - intro a; simpl. apply Hresp. exact (ex_intro _ a (conj eq_refl eq_refl)).
  - intros z h Hh.
    assert (Hr : ∀ b b', R b b' → UA.map (`1 h) b = UA.map (`1 h) b').
    { intros b b' [a [Hf Hg]]. rewrite <- Hf, <- Hg. exact (Hh a). }
    destruct (Hlift _ (UA.map (`1 h)) Hr) as [u Hu].
    unshelve refine {| unique_obj := @noop_hom (bare_alg Q) z u |}.
    + intro b; simpl; exact (Hu b).
    + intros v Hv w; simpl.
      apply (Huniq _ u (UA.map (`1 v))).
      intro b. exact (eq_trans (Hu b) (eq_sym (Hv b))).
Defined.

Corollary leibniz_coequalizers_iff_quotients :
  HasCoequalizers (Variety NoEq) ↔ QuotElim.
Proof.
  split.
  - exact leibniz_coequalizers_give_quotients.
  - exact quotients_give_leibniz_coequalizers.
Defined.

(** ** Block F: non-vacuity at a presentation built without extensionality *)

Definition CommMagma_Cocartesian : @Cocartesian (SVariety CommEq) :=
  SVariety_Cocartesian_via_GAFT CommEq.

Definition CommMagma_coequalizers : HasCoequalizers (SVariety CommEq) :=
  SVariety_coequalizers_via_GAFT CommEq.

(** ** Block G: Mac Lane's own route to the free algebra *)

Section ForgetSolutionSet.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context (X : Sets).

(* The same indexing as Block A, at the forgetful functor: [Prop]-valued
   congruences on the term algebra over [X] that satisfy [E] and respect
   the generators' `≈`. *)
Record IsFCong (Rq : UA.Tree S X → UA.Tree S X → Prop) : Prop := {
  fc_refl  : ∀ t, Rq t t;
  fc_sym   : ∀ t u, Rq t u → Rq u t;
  fc_trans : ∀ t u v, Rq t u → Rq u v → Rq t v;
  fc_op    : ∀ o (k1 k2 : UA.arity o → UA.Tree S X),
               (∀ i, Rq (k1 i) (k2 i)) →
               Rq (UA.node S X o k1) (UA.node S X o k2);
  fc_law   : ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.Tree S X),
               Rq (@UA.lhs S E (UA.Free S X) e args)
                  (@UA.rhs S E (UA.Free S X) e args);
  fc_resp  : ∀ x y : X, x ≈ y → Rq (UA.generator S X x) (UA.generator S X y)
}.

Definition FCongIdx : Type :=
  { Rq : UA.Tree S X → UA.Tree S X → Prop & IsFCong Rq }.

Definition FQ_setoid (i : FCongIdx) : Setoid (UA.Tree S X) :=
  {| equiv := `1 i
   ; setoid_equiv := {| Equivalence_Reflexive  := fc_refl  (`1 i) (`2 i)
                      ; Equivalence_Symmetric  := fc_sym   (`1 i) (`2 i)
                      ; Equivalence_Transitive := fc_trans (`1 i) (`2 i) |} |}.

Definition FQ_soa (i : FCongIdx) : SetoidOpAlgebra S := {|
  soa_obj := {| carrier := UA.Tree S X ; is_setoid := FQ_setoid i |};
  soa_op := UA.node S X;
  soa_op_respects := fc_op (`1 i) (`2 i);
  soa_prop := @PropEquiv_of_relation _ (FQ_setoid i) (`1 i)
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition FQ_alg (i : FCongIdx) : SVariety E :=
  (FQ_soa i; fc_law (`1 i) (`2 i)).

Definition fq_arr (i : FCongIdx) : X ~{Sets}~> SVariety_Forget E (FQ_alg i).
Proof.
  unshelve refine {| morphism := UA.generator S X |}.
  intros x y Hxy; exact (fc_resp (`1 i) (`2 i) x y Hxy).
Defined.

Section Kernel.

Context (c : SVariety E).
Context (h : X ~{Sets}~> SVariety_Forget E c).

Definition fker (t u : UA.Tree S X) : Prop :=
  @pequiv _ _ (soa_prop (`1 c)) (free_alg_ext c h t) (free_alg_ext c h u).

Lemma fker_cong : IsFCong fker.
Proof.
  unfold fker; constructor.
  - intro t; apply pequiv_from; reflexivity.
  - intros t u H; apply pequiv_from; symmetry; exact (pequiv_to _ _ H).
  - intros t u v H1 H2; apply pequiv_from;
      exact (transitivity (pequiv_to _ _ H1) (pequiv_to _ _ H2)).
  - intros o k1 k2 H; apply pequiv_from; simpl.
    apply (soa_op_respects (`1 c) o); intro i; exact (pequiv_to _ _ (H i)).
  - intros e args; apply pequiv_from.
    apply (free_alg_ext_respects E X c h).
    exact (tc_law E X e args).
  - intros x y Hxy; apply pequiv_from; simpl.
    exact (proper_morphism h x y Hxy).
Qed.

Definition fker_idx : FCongIdx := (fker; fker_cong).

Definition fker_med : FQ_alg fker_idx ~{SVariety E}~> c.
Proof.
  unshelve refine (@Build_SAlgHom S (FQ_soa fker_idx) (`1 c)
                     (free_alg_ext c h) _ _; I).
  - intros t u H; exact (pequiv_to _ _ H).
  - intros o k; simpl; reflexivity.
Defined.

End Kernel.

Definition SVariety_Forget_solution_set : SolutionSet (SVariety_Forget E) X.
Proof.
  unshelve refine (@Build_SolutionSet (SVariety E) Sets (SVariety_Forget E) X
                     FCongIdx FQ_alg fq_arr _).
  intros c h.
  exists (fker_idx c h), (fker_med c h).
  intro x; simpl; reflexivity.
Defined.

End ForgetSolutionSet.

Arguments IsFCong {_} _ _ _.
Arguments FCongIdx {_} _ _.
Arguments FQ_setoid {_} _ _ _.
Arguments FQ_soa {_} _ _ _.
Arguments FQ_alg {_} _ _ _.
Arguments fq_arr {_} _ _ _.
Arguments fker {_} _ _ _ _ _ _.
Arguments fker_cong {_} _ _ _ _.
Arguments fker_idx {_} _ _ _ _.
Arguments fker_med {_} _ _ _ _.
Arguments SVariety_Forget_solution_set {_} _ _.

Definition Free_Variety_via_GAFT {S : UA.OpSignature} (E : UA.EqSignature S) :
  { F : Sets ⟶ SVariety E & F ⊣ SVariety_Forget E } :=
  GAFT (SVariety_Forget E) (SVariety_Complete E)
       (Continuous_PreservesImageLimit (SVariety_Forget_continuous E))
       (SVariety_Forget_solution_set E).

Definition Free_Variety_via_GAFT_agrees {S : UA.OpSignature}
  (E : UA.EqSignature S) :
  projT1 (Free_Variety_via_GAFT E) ≈ Free_Variety_Functor E :=
  left_adjoint_iso (SVariety_Forget E) _ _
    (projT2 (Free_Variety_via_GAFT E)) (Free_Variety_adjunction E).
