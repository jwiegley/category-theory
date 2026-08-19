Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Normal subgroups, the quotient group, and its universal property

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
    (printed pp. 57-59) [maclane:III.1:construction5, maclane:III.1:ex4];
    Awodey, "Category Theory", 2nd ed., §4.2 (printed pp. 83-85)
    [awodey:4.2:construction-factor-group, awodey:4.2:thm4].
    nLab: https://ncatlab.org/nlab/show/quotient+group
    Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

    For N normal in G, the projection p : G -> G/N is a UNIVERSAL ELEMENT
    of the functor of homomorphisms killing N.  Mac Lane's point in §III.1
    is that every further property of quotient groups follows from that
    universality alone, with no second look at cosets; this file proves the
    universality, and Instance/Grp/Quotient/Isomorphism.v draws the named
    consequences from it.

    ERRATUM, recorded here rather than only in a commit message.  Issue
    #313's "Current state in the library" section says the area is
    "Absent", that a search for quotient/normal/coset vocabulary "returns
    zero formal hits", and that "no category Grp exists".  All three were
    stale when this file was written: #255 landed Instance/Grp.v with
    [GrpObject], [GrpHom], [Grp], [Grp_Forget], [Grp_Zero],
    [Grp_Cartesian] and [Grp_injectivity_is_monic], and the tree also
    carries Instance/Grp/Abelianization.v, Instance/Grp/Epi.v,
    Instance/Grp/Center.v, Instance/Grp/Free.v and Instance/Ab.v, several
    of which quotient by something.  What IS absent, and was measured
    against the parent commit rather than taken on the issue's word, is a
    [NormalSubgroup] interface: AT THE PARENT COMMIT the token occurred in
    the tree exactly once, at Instance/Grp/Abelianization.v:77, and there
    it occurred inside a prose disclosure that no such class existed.
    (That paragraph is rewritten by this same change, so the line number
    is a statement about the parent commit and not about the tree as it
    now stands.)  The only [Subgroup] record in the tree is
    Instance/Ab/Character/Finite.v:624, which is over [AbObject] and
    carries a DECIDABILITY field [sg_dec]; it is therefore not a donor
    here, since nothing below decides membership.

    THE FIVE FACTS.  Instance/Grp/Abelianization.v's "SCOPE OF THE
    QUOTIENT" paragraph (at the parent commit, :71-81) disclosed that its
    quotient by the commutator subgroup consumes only five properties of
    that subgroup -- "≈-saturation, unit, closure under product and
    inverse, normality" -- and that a generic quotient "is extractable by
    abstraction over exactly those five facts", left as future work.  That
    is what [Subgroup] and [NormalSubgroup] below are: four laws and one
    more, no membership decision, no smallness, no choice.  The extraction
    is carried out rather than merely announced -- Abelianization.v is
    refactored in the same change to obtain its five congruence lemmas
    from the generic ones, with its statements byte-identical (the
    Theory/EckmannHilton.v precedent), and its [CommutatorNS] supplies the
    five fields with the five facts it had already proved.

    WHAT THE UNIFICATION DOES AND DOES NOT COVER, measured.  The same
    disclosure counts "three unshared quotient constructions
    (Instance/Ab.v's [ab_coset_eq], Instance/Grp/Epi.v's [Grp_Coset], and
    this one)".  Reading the two other constructions' actual record types
    corrects the count:

      - Instance/Grp/Epi.v:433's [Grp_Coset] is a [SetoidObject], NOT a
        [GrpObject], and it is the coset space of the image of an
        ARBITRARY homomorphism.  Epi.v's whole argument turns on that
        image being possibly NON-normal (its own header, :171 and :1488,
        and the witness [grp_two_sym3] at :1644, are explicit that the
        non-normal case is the one the file exists for).  So it is not a
        quotient GROUP, is not an instance of anything below, and could
        not be: a normal-subgroup quotient is exactly what it declines to
        assume.  It is left untouched.

      - Instance/Ab.v:427's [ab_coset_eq] IS a quotient group, of an
        abelian group by the image of a homomorphism.  It is not routed
        through this file either, and the reason is a dependency
        direction rather than a mathematical obstruction: [AbObject]
        extends [CMonObject], Instance/Ab.v requires neither
        Instance/Grp.v nor anything below it, and the only bridge in tree,
        [Ab_to_GrpOb], lives DOWNSTREAM in Abelianization.v:333.  Routing
        Ab.v's quotient through a [GrpObject]-level construction would
        move that bridge upstream and give Ab.v a dependency on Grp.
        That is a defensible change and it is deliberately not made here.

    So of the three, one is unified, one is shown not to be an instance of
    the notion at all, and one is declined with its reason stated.  No
    fourth quotient construction is introduced: everything below, and
    everything in the two sibling files, quotients by [quot_rel].

    THE SETOID QUOTIENT.  As in Abelianization.v, G/N needs no new
    carrier: it is G's carrier under the coarser relation
    [quot_rel N a b := N (a * b⁻¹)].  The equivalence laws are the group
    laws; multiplication and inversion respect the relation by NORMALITY,
    which is where [ns_conj] earns its keep.  Elements of G/N are
    therefore elements of G, and no coset object is ever formed -- which
    is convenient, but is NOT what makes the derivations below universal:
    the arguments in the sibling files run through [quot_universal_element] and
    the mediator's uniqueness, not through element representatives, and
    where an element-level step does occur it is called out.

    WHAT IS DELIVERED HERE.  [Subgroup] and [NormalSubgroup]; the subgroup
    as an object of [Grp] with its inclusion; [QuotientGrp] with the
    projection [quot_proj]; the functor [KillsFunctor N : Grp ⟶ Sets] of
    homomorphisms killing N, and [quot_universal_element], the statement
    that ⟨G/N, p⟩ is a universal element of it, over #303's
    [AUniversalElement] -- the CLASS is used directly, and none of
    Theory/Universal/Element.v's Yoneda packaging
    ([universal_element_yoneda], [universal_element_representation]) is
    touched, so the universe restriction that packaging carries (object,
    hom and proof universes identified) is not inherited; the sibling
    files likewise reach [universal_element_iso], which lives in that
    file's Yoneda-free section;
    Awodey's Theorem 4.4 as the biconditional [hom_theorem]; the kernel of
    a homomorphism as a normal subgroup ([KernelNS], the transplant from
    #301); and the degenerate cases named and separated by proof
    ([TrivialNS], [TotalNS], and the S3 witnesses).

    WHAT IS NOT DELIVERED HERE.  No lattice of subgroups, no index, no
    Lagrange, no correspondence theorem, no solvability; no [HasCokernels]
    instance for [Grp] (the cokernel of a SINGLE map is built in the
    Colimit sibling, but no choice of cokernel for every map is packaged);
    no [Subgroup]-of-[Subgroup] calculus beyond what the second
    isomorphism theorem consumes; and no comparison with
    Instance/Ab/Character/Finite.v's decidable [Subgroup].

    NO UNIVERSAL-ARROW PACKAGING, and the reason is structural rather than
    a shortage of effort.  Theory/Universal/Element.v's
    [universal_element_arrow_subsumption] relates universal elements of a
    functor H to universal arrows exactly when H has the shape
    d ↦ Hom(c, S d) for a functor S.  [KillsFunctor N] does not: it is the
    SUBfunctor of Hom(G, −) cut out by the killing condition, and that
    condition mentions N, which is data attached to G rather than
    something a functor out of [Grp] supplies.  So the universal-ELEMENT
    reading is the one Mac Lane's §III.1 states and the only one taken
    here; no [AUniversalArrow] is claimed. *)

(** ** Subgroups and normal subgroups *)

(* A subgroup is a `≈`-saturated predicate containing the unit and closed
   under product and inverse.  Membership is [Type]-valued, following
   Instance/Grp/Epi.v's [GrpImage] and Instance/Ab/Character/Finite.v's
   [sg_mem]: the library's `≈` is itself [Type]-valued, so a [Prop]-valued
   membership could not be eliminated into a hom-setoid equation.

   There is deliberately NO decidability field, unlike
   Instance/Ab/Character/Finite.v:624, and nothing below decides
   membership. *)
Record Subgroup (G : GrpObject) := {
  sub_mem : carrier G → Type;

  (* (1) ≈-saturation *)
  sub_resp : ∀ a b : carrier G, a ≈ b → sub_mem a → sub_mem b;
  (* (2) the unit *)
  sub_unit : sub_mem (grp_unit G);
  (* (3) closure under product *)
  sub_mul : ∀ a b : carrier G,
    sub_mem a → sub_mem b → sub_mem (grp_mul G a b);
  (* (4) closure under inverse *)
  sub_inv : ∀ a : carrier G, sub_mem a → sub_mem (grp_inv G a)
}.

Arguments sub_mem {G} _ _.
Arguments sub_resp {G} _ _ _ _ _.
Arguments sub_unit {G} _.
Arguments sub_mul {G} _ _ _ _ _.
Arguments sub_inv {G} _ _ _.

(* A normal subgroup adds the fifth fact: closure under conjugation.  The
   five laws are exactly the five that Abelianization.v:71-81 names. *)
Record NormalSubgroup (G : GrpObject) := {
  ns_sub :> Subgroup G;

  (* (5) normality *)
  ns_conj : ∀ t a : carrier G, sub_mem ns_sub a →
    sub_mem ns_sub (grp_mul G (grp_mul G t a) (grp_inv G t))
}.

Arguments ns_sub {G} _.
Arguments ns_conj {G} _ _ _ _.

(* Saturation in the argument-implicit shape the proofs below want, so
   that they read like Abelianization.v's [inc_resp] applications. *)
Definition sub_at {G : GrpObject} (S : Subgroup G) {a b : carrier G}
  (Hab : a ≈ b) (Ha : sub_mem S a) : sub_mem S b := sub_resp S a b Hab Ha.

(** ** The subgroup as an object of Grp *)

(* The sigma carrier over membership, compared on elements -- the shape
   Instance/Grp.v:709's [Grp_kernel] and Instance/Grp/Center.v use, so the
   membership witness carries no equational weight. *)
Definition sub_carrier {G : GrpObject} (S : Subgroup G) : Type :=
  { a : carrier G & sub_mem S a }.

Program Definition SubgroupGrp {G : GrpObject} (S : Subgroup G) : GrpObject := {|
  grp_setoid := {| carrier := sub_carrier S
                 ; is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |} |};
  grp_unit := existT _ (grp_unit G) (sub_unit S);
  grp_mul := fun p q =>
    existT _ (grp_mul G (`1 p) (`1 q)) (sub_mul S _ _ (`2 p) (`2 q));
  grp_inv := fun p => existT _ (grp_inv G (`1 p)) (sub_inv S _ (`2 p))
|}.
Next Obligation. intros G S; equivalence; now transitivity (`1 y). Qed.
Next Obligation.
  intros G S a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G S a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_inv_l. Qed.

(* The inclusion of a subgroup: the first projection. *)
Program Definition sub_incl {G : GrpObject} (S : Subgroup G) :
  SubgroupGrp S ~{Grp}~> G := {|
  grp_map := {| morphism := fun p : sub_carrier S => `1 p |}
|}.
Next Obligation. intros G S a b Hab; exact Hab. Qed.
Next Obligation. intros G S; simpl; reflexivity. Qed.
Next Obligation. intros G S a b; simpl; reflexivity. Qed.

(* The inclusion is injective, hence monic in [Grp] by
   Instance/Grp.v's biconditional. *)
Lemma sub_incl_injective {G : GrpObject} (S : Subgroup G)
  (a b : carrier (SubgroupGrp S)) :
  grp_map (sub_incl S) a ≈ grp_map (sub_incl S) b → a ≈ b.
Proof. intro Hab; exact Hab. Qed.

Lemma sub_incl_monic {G : GrpObject} (S : Subgroup G) : Monic (sub_incl S).
Proof.
  apply (fst (Grp_injectivity_is_monic (sub_incl S))).
  apply sub_incl_injective.
Qed.

(** ** The quotient relation *)

(* a ~ b when a * b⁻¹ lies in N.  The orientation matches
   Instance/Grp/Abelianization.v:170's [abel_eq], which this generalizes. *)
Definition quot_rel {G : GrpObject} (N : Subgroup G) (a b : carrier G) : Type :=
  sub_mem N (grp_mul G a (grp_inv G b)).

Section QuotientRelation.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The finer relation implies the coarser one. *)
Lemma quot_rel_of_equiv (a b : carrier G) : a ≈ b → quot_rel N a b.
Proof.
  intro Hab; unfold quot_rel.
  apply (sub_at N (a := grp_unit G)); [| exact (sub_unit N) ].
  rewrite Hab.
  symmetry; apply (grp_mul_inv_r G).
Qed.

Lemma quot_rel_refl (a : carrier G) : quot_rel N a a.
Proof. apply quot_rel_of_equiv; reflexivity. Qed.

Lemma quot_rel_sym (a b : carrier G) : quot_rel N a b → quot_rel N b a.
Proof.
  unfold quot_rel; intro K.
  apply (sub_at N (a := grp_inv G (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    reflexivity.
  - exact (sub_inv N _ K).
Qed.

Lemma quot_rel_trans (a b c : carrier G) :
  quot_rel N a b → quot_rel N b c → quot_rel N a c.
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G (grp_mul G a (grp_inv G b))
                   (grp_mul G b (grp_inv G c)))).
  - rewrite (grp_mul_assoc G a (grp_inv G b)
               (grp_mul G b (grp_inv G c))).
    rewrite <- (grp_mul_assoc G (grp_inv G b) b (grp_inv G c)).
    rewrite (grp_mul_inv_l G b).
    rewrite (grp_mul_unit_l G (grp_inv G c)).
    reflexivity.
  - exact (sub_mul N _ _ K1 K2).
Qed.

(* Multiplication respects the relation.  This is the first of the two
   places where NORMALITY is spent: the correction term a * (b * b'⁻¹) * a⁻¹
   is a conjugate of a member. *)
Lemma quot_rel_mul (a a' b b' : carrier G) :
  quot_rel N a a' → quot_rel N b b' →
  quot_rel N (grp_mul G a b) (grp_mul G a' b').
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_mul G a (grp_mul G b (grp_inv G b')))
                      (grp_inv G a))
                   (grp_mul G a (grp_inv G a')))).
  - rewrite (grp_inv_mul G a' b').
    rewrite (grp_mul_assoc G
               (grp_mul G a (grp_mul G b (grp_inv G b')))
               (grp_inv G a) (grp_mul G a (grp_inv G a'))).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a (grp_inv G a')).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_l G (grp_inv G a')).
    rewrite (grp_mul_assoc G a (grp_mul G b (grp_inv G b'))
               (grp_inv G a')).
    rewrite (grp_mul_assoc G b (grp_inv G b') (grp_inv G a')).
    rewrite (grp_mul_assoc G a b
               (grp_mul G (grp_inv G b') (grp_inv G a'))).
    reflexivity.
  - exact (sub_mul N _ _ (ns_conj N a _ K2) K1).
Qed.

(* Inversion respects the relation; normality again. *)
Lemma quot_rel_inv (a a' : carrier G) :
  quot_rel N a a' → quot_rel N (grp_inv G a) (grp_inv G a').
Proof.
  unfold quot_rel; intros K.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_inv G a)
                      (grp_inv G (grp_mul G a (grp_inv G a'))))
                   (grp_inv G (grp_inv G a)))).
  - rewrite (grp_inv_mul G a (grp_inv G a')).
    rewrite (grp_inv_inv G a').
    rewrite (grp_inv_inv G a).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a' (grp_inv G a)).
    rewrite (grp_mul_assoc G (grp_mul G (grp_inv G a) a')
               (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_r G (grp_mul G (grp_inv G a) a')).
    reflexivity.
  - exact (ns_conj N (grp_inv G a) _ (sub_inv N _ K)).
Qed.

(* Membership IS congruence to the unit: the quotient relation at the unit
   is membership on the nose.  Both directions, and the forward one by
   [reflexivity] under the relation's own unfolding. *)
Lemma quot_rel_unit_iff (a : carrier G) :
  quot_rel N a (grp_unit G) ↔ sub_mem N a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G).
    apply (grp_mul_unit_r G).
  - apply (sub_at N (a := a)); [| exact K ].
    rewrite (grp_inv_unit G).
    symmetry; apply (grp_mul_unit_r G).
Qed.

End QuotientRelation.

(** ** The quotient group and its projection *)

Program Definition QuotientGrp {G : GrpObject} (N : NormalSubgroup G) :
  GrpObject := {|
  grp_setoid := {| carrier := carrier G
                 ; is_setoid := {| equiv := quot_rel N |} |};
  grp_unit := grp_unit G;
  grp_mul := grp_mul G;
  grp_inv := grp_inv G
|}.
Next Obligation.
  intros G N; equivalence.
  - apply quot_rel_refl.
  - now apply quot_rel_sym.
  - now apply (quot_rel_trans N x y).
Qed.
Next Obligation.
  intros G N a a' Ha b b' Hb; now apply quot_rel_mul.
Qed.
Next Obligation.
  intros G N a b c; apply quot_rel_of_equiv, grp_mul_assoc.
Qed.
Next Obligation.
  intros G N a; apply quot_rel_of_equiv, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G N a; apply quot_rel_of_equiv, grp_mul_inv_l.
Qed.

(* NO NOTATION for the quotient.  An unscoped infix [/] at level 40 would
   sit in the core scope and compete with the stdlib's scope-bound
   division notations in every file that imports this one; the tree's only
   other [/] notation, Instance/Field/Frac.v:429, is [Local] and prefix
   for exactly that kind of reason.  [QuotientGrp N] is written out. *)

(* The projection: the identity function, read from the fine setoid into
   the coarse one. *)
Program Definition quot_proj {G : GrpObject} (N : NormalSubgroup G) :
  G ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation. intros G N a b Hab; apply quot_rel_of_equiv, Hab. Qed.
Next Obligation. intros G N; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N a b; simpl; apply quot_rel_refl. Qed.

(* The projection kills N, which is the statement that gives the universal
   element below its element. *)
Lemma quot_proj_kills {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem N a → grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

(* Conversely, anything the projection kills lies in N: the projection's
   kernel is exactly N, as a biconditional rather than an inclusion. *)
Lemma quot_proj_kernel {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N) ↔ sub_mem N a.
Proof. exact (quot_rel_unit_iff N a). Qed.

(* The projection is surjective on elements -- indeed the identity -- and
   hence epic.  Recorded because the isomorphism-theorem chases in the
   sibling file cancel it on the right. *)
Lemma quot_proj_epic {G : GrpObject} (N : NormalSubgroup G) :
  Epic (quot_proj N).
Proof.
  constructor; intros K g h Hgh a.
  exact (Hgh a).
Qed.

(** ** The functor of homomorphisms killing N *)

(* Kills N K is the set of homomorphisms G -> K that send every member of
   N to the unit.  It is covariant in K by postcomposition, which is what
   makes ⟨G/N, p⟩ a universal element in Mac Lane's covariant sense rather
   than a representing object of a presheaf. *)
Definition Kills {G : GrpObject} (N : NormalSubgroup G) (K : GrpObject) : Type :=
  { h : G ~{Grp}~> K & ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K }.

(* Two members are compared by their underlying homomorphisms; the
   killing witness carries no equational weight, exactly as the membership
   witness does not in [sub_carrier]. *)
Program Definition Kills_Setoid {G : GrpObject} (N : NormalSubgroup G)
  (K : GrpObject) : Setoid (Kills N K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros G N K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q r Hpq Hqr; now transitivity (`1 q).
Qed.

Lemma Kills_post {G : GrpObject} (N : NormalSubgroup G) {K K' : GrpObject}
  (k : K ~{Grp}~> K') (p : Kills N K) (a : carrier G) :
  sub_mem N a → grp_map (k ∘ `1 p) a ≈ grp_unit K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (grp_map_unit k).
Qed.

Program Definition KillsFunctor {G : GrpObject} (N : NormalSubgroup G) :
  Grp ⟶ Sets := {|
  fobj := fun K => {| carrier := Kills N K ; is_setoid := Kills_Setoid N K |};
  fmap := fun K K' k =>
    {| morphism := fun p : Kills N K =>
         existT _ (k ∘ `1 p) (Kills_post N k p) |}
|}.
Next Obligation.
  intros G N K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros G N K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros G N K p a; simpl; reflexivity. Qed.
Next Obligation. intros G N K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism *)

Section Mediator.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).
Context {K : GrpObject}.
Context (p : Kills N K).

(* Descent: a homomorphism killing N cannot tell N-congruent elements
   apart.  From N (a * b⁻¹) one gets h a * (h b)⁻¹ ≈ e, and cancelling
   (h b)⁻¹ on the right gives h a ≈ h b.  This is the ONE computation the
   quotient's universal property costs. *)
Lemma kills_descends (a b : carrier G) :
  quot_rel N a b → grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  intro Hab.
  apply (grp_cancel_r K (grp_inv K (grp_map (`1 p) b))).
  rewrite (grp_mul_inv_r K (grp_map (`1 p) b)).
  rewrite <- (grp_map_inv (`1 p) b).
  rewrite <- (grp_map_mul (`1 p)).
  exact (`2 p _ Hab).
Qed.

Program Definition quot_med : QuotientGrp N ~{Grp}~> K := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp N) =>
                              grp_map (`1 p) a |}
|}.
Next Obligation. intros a b Hab; exact (kills_descends a b Hab). Qed.
Next Obligation. simpl; apply (grp_map_unit (`1 p)). Qed.
Next Obligation. intros a b; simpl; apply (grp_map_mul (`1 p)). Qed.

(* The mediator's defining triangle, at the level of the underlying
   homomorphisms: it holds by reflexivity, since the projection is the
   identity function. *)
Lemma quot_med_commutes : quot_med ∘ quot_proj N ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma quot_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_proj N ≈ `1 p) : quot_med ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments quot_med {G} N {K} p.

(** ** Mac Lane's construction 5: ⟨G/N, p⟩ is a universal element *)

(* The projection, packaged as an element of (Kills N)(G/N). *)
Definition quot_elem {G : GrpObject} (N : NormalSubgroup G) :
  Kills N (QuotientGrp N) :=
  existT _ (quot_proj N) (quot_proj_kills N).

(* Mac Lane, §III.1 construction 5.  Every homomorphism out of G that
   kills N is (Kills N u) applied to the projection, for a UNIQUE
   u : G/N -> K.  The class is #303's [AUniversalElement], used DIRECTLY:
   the class sits upstream of both of Theory/Universal/Element.v's routes
   to [Representable], so neither the Yoneda packaging nor the hand-built
   alternative to it is touched here.  Nothing below mentions
   [Yoneda_Lemma], [ue_yoneda_obj] or [universal_element_representation],
   so the universe restriction those carry (object, hom and proof
   universes identified) is not inherited. *)
Program Definition quot_universal_element {G : GrpObject}
  (N : NormalSubgroup G) : AUniversalElement (KillsFunctor N) (QuotientGrp N) := {|
  aue_elem := quot_elem N
|}.
Next Obligation.
  intros G N K x.
  unshelve refine {| unique_obj := quot_med N x |}.
  - exact (quot_med_commutes N x).
  - intros v Hv; simpl in *.
    exact (quot_med_unique N x v Hv).
Defined.

(* The universal element's underlying homomorphism IS the projection, by
   convertibility -- the [eq_refl] exception to the `≈` discipline, and
   the check that the packaging did not silently rebuild it. *)
Example quot_universal_elem_is_proj {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

(* And the mediator extracted from the class is the fixpoint-free direct
   one, again by convertibility. *)
Example quot_universal_med_is_quot_med {G : GrpObject} (N : NormalSubgroup G)
  {K : GrpObject} (x : Kills N K) :
  unique_obj (@aue_universal _ (KillsFunctor N) (QuotientGrp N)
                (quot_universal_element N) K x)
    = quot_med N x.
Proof. reflexivity. Qed.

(** ** Awodey Theorem 4.4: the homomorphism theorem, as a biconditional *)

(* N ⊆ ker h if and only if h factors uniquely through the projection.
   The forward direction is the universal property; the backward one is
   the observation that every member of N is projected to the unit, so a
   factorization forces h to kill N. *)
Theorem hom_theorem {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K) :
  (∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K)
    ↔ (∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : G ~{Grp}~> K =>
                         ∀ a : carrier G, sub_mem N a →
                           grp_map h a ≈ grp_unit K) h Hkill).
    unshelve refine {| unique_obj := quot_med N x |}.
    + exact (quot_med_commutes N x).
    + intros v Hv.
      exact (quot_med_unique N x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (grp_map u (grp_map (quot_proj N) a)).
    + symmetry; exact (Hu a).
    + transitivity (grp_map u (grp_unit (QuotientGrp N))).
      * apply proper_morphism.
        exact (quot_proj_kills N a Ha).
      * exact (grp_map_unit u).
Qed.

(* The two halves separately, in the shape a consumer applies. *)
Definition hom_theorem_factor {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  fst (hom_theorem N h) Hkill.

Definition hom_theorem_kills {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hfac : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h) :
  ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K :=
  snd (hom_theorem N h) Hfac.

(** ** The kernel of a homomorphism is a normal subgroup

    The transplant from #301.  Awodey's Theorem 4.4 opens with this
    clause, and it is what makes the isomorphism theorems in the sibling
    file able to quotient by a kernel at all. *)

Program Definition KernelNS {G K : GrpObject} (h : G ~{Grp}~> K) :
  NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => grp_map h a ≈ grp_unit K |}
|}.
Next Obligation.
  intros G K h a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation.
  intros G K h a b Ha Hb; simpl in *.
  rewrite (grp_map_mul h), Ha, Hb.
  apply (grp_mul_unit_l K).
Qed.
Next Obligation.
  intros G K h a Ha; simpl in *.
  rewrite (grp_map_inv h), Ha.
  apply (grp_inv_unit K).
Qed.
Next Obligation.
  intros G K h t a Ha; simpl in *.
  rewrite !(grp_map_mul h), (grp_map_inv h), Ha.
  rewrite (grp_mul_unit_r K).
  apply (grp_mul_inv_r K).
Qed.

(* Membership in the kernel subgroup IS the defining equation, by
   convertibility. *)
Example KernelNS_mem {G K : GrpObject} (h : G ~{Grp}~> K) (a : carrier G) :
  sub_mem (KernelNS h) a = (grp_map h a ≈ grp_unit K).
Proof. reflexivity. Qed.

(* The subgroup object of the kernel normal subgroup has the same carrier
   as Instance/Grp.v:729's [Grp_kernel], by convertibility. *)
Example KernelNS_carrier_is_Grp_kernel {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(** ** The degenerate normal subgroups, named and separated *)

(* The trivial normal subgroup {e}. *)
Program Definition TrivialNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => a ≈ grp_unit G |}
|}.
Next Obligation. intros G a b Hab Ha; simpl in *; now rewrite <- Hab. Qed.
Next Obligation. intros G; simpl; reflexivity. Qed.
Next Obligation.
  intros G a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros G a Ha; simpl in *.
  rewrite Ha; apply (grp_inv_unit G).
Qed.
Next Obligation.
  intros G t a Ha; simpl in *.
  rewrite Ha, (grp_mul_unit_r G).
  apply (grp_mul_inv_r G).
Qed.

(* The whole group, as a normal subgroup of itself. *)
Program Definition TotalNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun _ : carrier G => poly_unit |}
|}.
Next Obligation. intros G a b Hab Ha; exact ttt. Qed.
Next Obligation. intros G; exact ttt. Qed.
Next Obligation. intros G a b Ha Hb; exact ttt. Qed.
Next Obligation. intros G a Ha; exact ttt. Qed.
Next Obligation. intros G t a Ha; exact ttt. Qed.

(* Quotienting by the trivial subgroup changes nothing: the coarse
   relation coincides with `≈`, in both directions. *)
Lemma quot_trivial_iff (G : GrpObject) (a b : carrier G) :
  quot_rel (TrivialNS G) a b ↔ a ≈ b.
Proof.
  split.
  - intro K; simpl in K.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite K.
    symmetry; apply (grp_mul_inv_r G).
  - intro Hab; simpl.
    rewrite Hab; apply (grp_mul_inv_r G).
Qed.

(* Quotienting by the whole group collapses everything. *)
Lemma quot_total_collapses (G : GrpObject) (a b : carrier G) :
  quot_rel (TotalNS G) a b.
Proof. exact ttt. Qed.

(** ** Quotients by coextensive normal subgroups agree *)

(* Two normal subgroups with the same members give isomorphic quotients,
   the comparison being the identity function in both directions.  This is
   what lets a quotient by a kernel be renamed as a quotient by the
   subgroup that kernel computes to, without a transport. *)
Program Definition quot_congr {G : GrpObject} (N N' : NormalSubgroup G)
  (H1 : ∀ a : carrier G, sub_mem N a → sub_mem N' a)
  (H2 : ∀ a : carrier G, sub_mem N' a → sub_mem N a) :
  QuotientGrp N ≅[Grp] QuotientGrp N' := {|
  to := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N) => a |} |};
  from := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N') => a |} |}
|}.
Next Obligation. intros G N N' H1 H2 a b Hab; exact (H1 _ Hab). Qed.
Next Obligation. intros G N N' H1 H2; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N N' H1 H2 a b; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N N' H1 H2 a b Hab; exact (H2 _ Hab). Qed.
Next Obligation. intros G N N' H1 H2; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N N' H1 H2 a b; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N N' H1 H2 a; simpl; apply quot_rel_refl. Qed.
Next Obligation. intros G N N' H1 H2 a; simpl; apply quot_rel_refl. Qed.

(** ** Non-degeneracy over a nonabelian witness

    Everything above holds for all groups, so nothing yet shows the
    quotient does not collapse.  S3 (Instance/Grp/TwoFunctors.v:248, the
    semidirect presentation over the decidable carrier rot * bool) with
    its rotation subgroup A3 is the smallest witness with a PROPER
    nontrivial normal subgroup, and it is nonabelian, so the degeneracies
    that make conjugation inert (Instance/Grp/TwoFunctors.v:195's
    [Grp_conj_abelian]) are excluded by proof rather than by assumption. *)

(* A3, the rotations: the elements whose reflection component is false.
   S3's setoid IS propositional equality
   (Instance/Grp/TwoFunctors.v's [S3_equiv_is_eq]), so saturation is
   substitution and every closure law is a finite check. *)
Program Definition A3 : NormalSubgroup S3 := {|
  ns_sub := {| sub_mem := fun a : carrier S3 => snd a = false |}
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; reflexivity.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hc; simpl in *; subst.
  destruct i, j, b; reflexivity.
Qed.

(* A3 is PROPER: the reflection is not a rotation. *)
Lemma A3_proper : sub_mem A3 S3_s → False.
Proof. simpl; discriminate. Qed.

(* A3 is NONTRIVIAL: it contains a non-unit element. *)
Lemma A3_nontrivial : sub_mem A3 S3_r * (S3_r ≈ s3_unit → False).
Proof. split; [ reflexivity | discriminate ]. Qed.

(* Normality of A3 is not vacuous: conjugation in S3 genuinely moves
   elements ([S3_conj_s_nontrivial]), so [ns_conj] is doing work here
   rather than holding because conjugation is the identity. *)
Lemma A3_conjugation_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof. exact S3_conj_s_nontrivial. Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: the reflection stays apart from the
   unit in S3/A3. *)
Theorem S3_mod_A3_not_collapsed : quot_rel A3 S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(* Nor does the quotient projection identify the two generators, so
   S3/A3 has at least two elements. *)
Theorem S3_mod_A3_two_elements :
  grp_map (quot_proj A3) S3_s ≈ grp_map (quot_proj A3) s3_unit → False.
Proof. simpl; discriminate. Qed.

(* But it does collapse the rotations, so the projection is not injective
   -- the quotient is a genuine quotient and not a relabelling of S3. *)
Theorem S3_mod_A3_collapses_rotations :
  grp_map (quot_proj A3) S3_r ≈ grp_map (quot_proj A3) s3_unit.
Proof. reflexivity. Qed.

Theorem quot_proj_A3_not_injective :
  (∀ a b : carrier S3,
     grp_map (quot_proj A3) a ≈ grp_map (quot_proj A3) b → a ≈ b) → False.
Proof.
  intro Hinj.
  pose proof (Hinj S3_r s3_unit S3_mod_A3_collapses_rotations) as E.
  discriminate E.
Qed.

(* The two-element subgroup generated by the reflection: the elements with
   trivial rotation part.  It is a SUBGROUP but NOT a normal one, and both
   halves are proved -- so the sibling files have a witness at which the
   plain-[Subgroup] hypothesis of the second isomorphism theorem is not
   secretly a normal one, and at which the normal closure of a subgroup is
   strictly larger than the subgroup. *)
Program Definition S3_refl_sub : Subgroup S3 := {|
  sub_mem := fun a : carrier S3 => fst a = rot0
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; now destruct b.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; now destruct b. Qed.

Theorem S3_refl_sub_not_normal :
  (∀ t a : carrier S3, sub_mem S3_refl_sub a →
     sub_mem S3_refl_sub (grp_mul S3 (grp_mul S3 t a) (grp_inv S3 t)))
  → False.
Proof.
  intro Hn.
  pose proof (Hn S3_r S3_s (eq_refl : fst S3_s = rot0)) as E.
  simpl in E.
  discriminate E.
Qed.
