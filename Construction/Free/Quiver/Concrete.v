Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Quivers as a concrete category: the multi-sorted case *)

(* nLab:      https://ncatlab.org/nlab/show/quiver
   nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Example 1.6.19, printed p. 46
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.7, printed p. 26

   Riehl's Example 1.6.19 is the sharpest small illustration of what a chosen
   underlying-set functor is for.  A quiver has TWO sorts of element, vertices
   and arrows, and neither sort alone determines a quiver homomorphism:

     - the VERTEX functor is not faithful, because a homomorphism can move
       parallel edges around while fixing every vertex;
     - the ARROW functor is not faithful, because a homomorphism can permute
       isolated vertices while fixing every edge (there being none to move);
     - their DISJOINT UNION is faithful, so quivers are concrete after all.

   All three functors are built here over the in-tree quiver category
   `QuiverCategory` (Construction/Free/Quiver.v:358), whose objects are the
   `Quiver` records of that file (line 54): a node type together with an edge
   setoid `edges x y` for each ordered pair of nodes.  Since edges are indexed
   by their endpoints rather than carrying source/target maps, the "set of
   arrows" has to be assembled: [QArrow] below is the type of triples
   (source, target, edge), and [QArrow_Setoid] compares two such triples by an
   equality of endpoints together with an `≈` of edges moved along it.

     [QuiverVertices] : Q ↦ the nodes of Q             (not faithful)
     [QuiverArrows]   : Q ↦ the triples of Q           (not faithful)
     [QuiverElements] : Q ↦ nodes of Q ⊎ triples of Q  (faithful, see below)

   These are the first `Sets`-valued functors on quivers in the library.
   `QuiverCategory` is the only quiver category in the tree, and the only
   quiver-facing functors that existed before this file are
   Construction/Free/Quiver.v:412's `Forgetful : StrictCat ⟶ QuiverCategory`
   and :546's `FreeCatFunctor : QuiverCategory ⟶ StrictCat`, neither of which
   lands in `Sets`.  The quiver-building idiom used for the witnesses below,
   `Build_Quiver_Standard_Eq`, is the one Test/Issue138.v:87 already uses.

   Both negative results are genuine refutations, each witnessed by two
   PARALLEL homomorphisms exhibited explicitly and shown distinct in the
   hom-setoid of `QuiverCategory` — not merely written differently:

     [LoopQuiver]  one node, two parallel loops; the identity and the
       loop-swapping endomorphism agree on nodes, differ on edges
       ([QuiverVertices_not_Faithful]).
     [DiscQuiver]  two nodes, no edges; the identity and the node-swapping
       endomorphism agree on arrows (there are none), differ on nodes
       ([QuiverArrows_not_Faithful]).

   Scope of the positive half, disclosed
   -------------------------------------

   [QuiverElements] is proved faithful under one hypothesis on the target
   quiver: uniqueness of identity proofs for its node type ([NodeUIP]).
   Where that hypothesis enters is worth stating precisely.

   Equivalence of quiver homomorphisms in `QuiverCategory`
   (`QuiverHomomorphismEquivalence`) is a SIGMA type: `F ≈ G` consists of a
   family `node_equiv : ∀ x, F x = G x` TOGETHER WITH a coherence condition
   that quantifies over all edges and refers to that one chosen family.  From
   `fmap[QuiverElements] F ≈ fmap[QuiverElements] G` one recovers, on the node
   summand, a family `ne x : F x = G x`, and on the arrow summand, for each
   edge separately, its own pair of endpoint equalities.  Nothing in that
   hypothesis ties the per-edge equalities to the ones `ne` supplies, and this
   development found no way to replace one by the other short of [NodeUIP].
   With [NodeUIP] the replacement is immediate, and the proof goes through.

   Riehl's quivers have SETS of vertices, for which uniqueness of identity
   proofs holds; so [NodeUIP] is the hypothesis under which her example is
   being reproduced.  Accordingly the `Concrete` instance is delivered for the
   full subcategory (in the sense of Construction/Subcategory.v) of quivers
   satisfying it — [SetQuiverCat], built with that file's generic `Sub` —
   rather than for `QuiverCategory` itself, and BOTH negative
   results are reproved there ([SetQuiverVertices_not_Faithful],
   [SetQuiverArrows_not_Faithful]) so that all of Example 1.6.19 lives in one
   category.  Both witness quivers have node types with decidable equality
   (`poly_unit` and `bool`), so they are objects of [SetQuiverCat] by
   [NodeDecEq_NodeUIP], an axiom-free Hedberg step through
   `Eqdep_dec.UIP_dec` — the same device Construction/Quotient.v uses for
   `obj_uip`.

   An unrestricted `Concrete QuiverCategory` is therefore NOT claimed here,
   and the restriction is NOT a shortcut: the closing section of this file
   proves that `Faithful QuiverElements` IMPLIES UIP, so the hypothesis is
   forced rather than convenient. (The first commit said only that this was
   an obstruction to the proof rather than a refutation; an audit closed
   the loop, and its argument is integrated below.) Since UIP is
   independent of Rocq's logic, `Faithful QuiverElements` is not provable
   here, and concreteness of `QuiverCategory` VIA THIS FUNCTOR is
   unreachable axiom-free.

   Whether some OTHER functor to `Sets` concretizes `QuiverCategory` is
   still left open. No such functor is known to the author of this file,
   and there is a structural reason for pessimism — pointwise data over any
   carrier yields equalities one element at a time, whereas the target
   requires a single node family coherent with every edge at once — but no
   non-existence proof is offered.

   Obligation discipline: this file sets `Obligation Tactic := idtac`, so
   every proof below introduces its own variables and none depends on a
   Program-generated name. *)

#[local] Existing Instance edgeset.
#[local] Obligation Tactic := idtac.

(** ** Uniqueness of identity proofs on nodes *)

(* The hypothesis discussed in the header: the node type of `Q` is a set in
   the sense of uniqueness of identity proofs. *)
Definition NodeUIP (Q : Quiver) : Type :=
  ∀ (x y : @nodes Q) (p q : x = y), p = q.

(* Decidable node equality gives [NodeUIP] with no axiom, by Hedberg's theorem
   in the form `Eqdep_dec.UIP_dec`.  Construction/Quotient.v's `obj_uip` is
   the same step for the objects of a category. *)
Lemma NodeDecEq_NodeUIP (Q : Quiver)
      (dec : ∀ x y : @nodes Q, {x = y} + {x ≠ y}) : NodeUIP Q.
Proof.
  intros x y p q.
  exact (UIP_dec dec p q).
Qed.

(** ** The vertex functor *)

(* Q ↦ its node type, under Leibniz equality; a homomorphism ↦ its node map.
   Functoriality is immediate: hom-equivalence in `QuiverCategory` carries a
   family of node equalities as its first component. *)
Program Definition QuiverVertices : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier   := @nodes Q
                    ; is_setoid := {| equiv        := @eq (@nodes Q)
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun Q Q' F => {| morphism := @fnodes Q Q' F |}
|}.
Next Obligation. intros Q Q' F a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation.
  intros Q Q' F G HFG a.
  destruct HFG as [ne _].
  exact (ne a).
Qed.
Next Obligation. intros Q a; reflexivity. Qed.
Next Obligation. intros Q1 Q2 Q3 F G a; reflexivity. Qed.

(** ** The arrow functor *)

(* The arrows of a quiver, assembled from the endpoint-indexed edge families
   of Construction/Free/Quiver.v into a single type of triples. *)
Record QArrow (Q : Quiver) := {
  qsrc  : @nodes Q;
  qtgt  : @nodes Q;
  qedge : edges qsrc qtgt
}.

Arguments qsrc {Q} _.
Arguments qtgt {Q} _.
Arguments qedge {Q} _.

(* Move an edge along equalities of its two endpoints. *)
Definition qmove {Q : Quiver} {a a' b b' : @nodes Q}
           (p : a = a') (q : b = b') (e : edges a b) : edges a' b' :=
  Logic.transport (fun t => edges a' t) q
    (Logic.transport (fun s => edges s b) p e).

(* Two arrows are equivalent when their endpoints agree and, after moving the
   first edge onto the second's endpoints, the edges agree in the edge setoid.
   The endpoint comparison is `=` and not `≈` because Construction/Free/
   Quiver.v gives nodes no setoid structure of their own — only edges carry
   one; the edge comparison is `≈`, as the library's discipline requires. *)
Definition QArrow_equiv {Q : Quiver} (u v : QArrow Q) : Type :=
  { p : qsrc u = qsrc v &
  { q : qtgt u = qtgt v & qmove p q (qedge u) ≈ qedge v } }.

Lemma QArrow_equiv_refl {Q : Quiver} (u : QArrow Q) : QArrow_equiv u u.
Proof.
  destruct u as [a b e].
  exists eq_refl, eq_refl; simpl.
  reflexivity.
Qed.

Lemma QArrow_equiv_sym {Q : Quiver} (u v : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v u.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now symmetry.
Qed.

Lemma QArrow_equiv_trans {Q : Quiver} (u v w : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v w → QArrow_equiv u w.
Proof.
  destruct u as [a b e], v as [a' b' e'], w as [a'' b'' e''].
  intros [p [q Hq]] [p' [q' Hq']]; simpl in *.
  destruct p, q, p', q'; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now transitivity e'.
Qed.

#[export] Program Instance QArrow_Setoid (Q : Quiver) : Setoid (QArrow Q) := {|
  equiv := @QArrow_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - exact (@QArrow_equiv_refl Q).
  - exact (@QArrow_equiv_sym Q).
  - exact (@QArrow_equiv_trans Q).
Qed.

(* Introduction forms for the arrow setoid, so that no proof below has to see
   through the `≈` notation to reach the underlying sigma type. *)
Lemma QArrow_intro {Q : Quiver} (u v : QArrow Q)
      (p : qsrc u = qsrc v) (q : qtgt u = qtgt v) :
  qmove p q (qedge u) ≈ qedge v → u ≈ v.
Proof. intro H; exact (existT _ p (existT _ q H)). Qed.

(* The common case: the endpoints agree on the nose. *)
Lemma QArrow_intro_same {Q : Quiver} {a b : @nodes Q} (e e' : edges a b) :
  e ≈ e' →
  {| qsrc := a ; qtgt := b ; qedge := e |} ≈
  {| qsrc := a ; qtgt := b ; qedge := e' |}.
Proof. intro H; exact (existT _ eq_refl (existT _ eq_refl H)). Qed.

(* The coherence condition of `QuiverHomomorphismEquivalence`, restated as an
   equivalence of moved edges.  Both directions are proved by eliminating the
   two endpoint equalities, which is legitimate here because all four
   endpoints are universally quantified variables. *)
Lemma qmove_bridge {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g → qmove p q f ≈ g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

Lemma qmove_bridge_inv {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  qmove p q f ≈ g →
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

(* The action of a homomorphism on arrows. *)
Definition qarrow_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (u : QArrow Q) : QArrow Q' :=
  {| qsrc  := F (qsrc u)
   ; qtgt  := F (qtgt u)
   ; qedge := @fedgemap _ _ F _ _ (qedge u) |}.

(* The arrow map respects the arrow setoid. *)
Lemma qarrow_map_respects {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
      (u v : QArrow Q) : u ≈ v → qarrow_map F u ≈ qarrow_map F v.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  unfold qarrow_map; simpl.
  apply QArrow_intro_same.
  now apply (@fedgemap_respects _ _ F).
Qed.

(* Two homomorphisms that are equivalent agree on every arrow. *)
Lemma qarrow_map_agrees {Q Q' : Quiver} (F G : Q ~{QuiverCategory}~> Q')
      (HFG : F ≈ G) (u : QArrow Q) : qarrow_map F u ≈ qarrow_map G u.
Proof.
  destruct HFG as [ne coh].
  apply (QArrow_intro (qarrow_map F u) (qarrow_map G u)
                      (ne (qsrc u)) (ne (qtgt u))).
  apply qmove_bridge, coh.
Qed.

Program Definition QuiverArrows : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QArrow Q ; is_setoid := QArrow_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qarrow_map F |}
|}.
Next Obligation. intros Q Q' F u v Huv; now apply qarrow_map_respects. Qed.
Next Obligation. intros Q Q' F G HFG u; now apply qarrow_map_agrees. Qed.
Next Obligation. intros Q u; destruct u as [a b e]; reflexivity. Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G u; destruct u as [a b e]; reflexivity.
Qed.

(** ** The disjoint-union functor *)

(* Riehl's V ⊎ E: the elements of a quiver are its vertices and its arrows.
   Vertices and arrows are never identified with one another. *)
Definition QElt (Q : Quiver) : Type := (@nodes Q + QArrow Q)%type.

Definition QElt_equiv {Q : Quiver} (z w : QElt Q) : Type :=
  match z, w with
  | Datatypes.inl x, Datatypes.inl y => x = y
  | Datatypes.inr u, Datatypes.inr v => QArrow_equiv u v
  | _, _ => False
  end.

#[export] Program Instance QElt_Setoid (Q : Quiver) : Setoid (QElt Q) := {|
  equiv := @QElt_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - intros [x|u]; simpl.
    + reflexivity.
    + apply QArrow_equiv_refl.
  - intros [x|u] [y|v]; simpl; try contradiction.
    + intro Hxy; now symmetry.
    + apply QArrow_equiv_sym.
  - intros [x|u] [y|v] [z|w]; simpl; try contradiction.
    + intros H1 H2; now transitivity y.
    + apply QArrow_equiv_trans.
Qed.

Definition qelt_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (z : QElt Q) : QElt Q' :=
  match z with
  | Datatypes.inl x => Datatypes.inl (F x)
  | Datatypes.inr u => Datatypes.inr (qarrow_map F u)
  end.

Program Definition QuiverElements : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QElt Q ; is_setoid := QElt_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qelt_map F |}
|}.
Next Obligation.
  intros Q Q' F z w Hzw.
  destruct z as [n|u], w as [n'|v]; simpl in *; try contradiction.
  - now subst.
  - now apply qarrow_map_respects.
Qed.
Next Obligation.
  intros Q Q' F G HFG z.
  destruct z as [n|u]; simpl.
  - destruct HFG as [ne _]; exact (ne n).
  - now apply qarrow_map_agrees.
Qed.
Next Obligation.
  intros Q z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.

(* The positive half of Riehl's example, at the scope disclosed in the header:
   a quiver homomorphism is determined by its action on vertices and arrows
   together, once the target's node type satisfies uniqueness of identity
   proofs.  The node summand supplies the node family; the arrow summand
   supplies the coherence, after [NodeUIP] identifies its own endpoint
   equalities with the ones the node summand chose. *)
Theorem QuiverElements_faithful_under_NodeUIP
        {Q Q' : QuiverCategory} (uip : NodeUIP Q')
        (F G : Q ~{QuiverCategory}~> Q') :
  fmap[QuiverElements] F ≈ fmap[QuiverElements] G → F ≈ G.
Proof.
  intro H.
  (* The node family, read off the vertex summand. *)
  unshelve refine (existT _ (fun x => H (Datatypes.inl x)) _).
  intros x y f; simpl.
  (* The arrow summand at the arrow (x, y, f). *)
  pose proof (H (Datatypes.inr {| qsrc := x; qtgt := y; qedge := f |})) as Ha.
  simpl in Ha.
  destruct Ha as [ps [pt Hc]].
  (* [NodeUIP] replaces the arrow summand's endpoint equalities by the ones
     the vertex summand supplied. *)
  rewrite (uip _ _ ps (H (Datatypes.inl x))) in Hc.
  rewrite (uip _ _ pt (H (Datatypes.inl y))) in Hc.
  exact (qmove_bridge_inv _ _ _ _ Hc).
Qed.

(** ** Witness quivers, and the two negative results *)

(* One node carrying two parallel loops.  A homomorphism out of it is a choice
   of node and a map on the two loops, so the node data cannot see the loop
   data — this is what defeats the vertex functor. *)
Definition LoopQuiver : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => bool).

(* The loop-swapping endomorphism: identity on the single node, negation on
   the two loops. *)
Program Definition loop_swap : LoopQuiver ~{QuiverCategory}~> LoopQuiver := {|
  fnodes   := Datatypes.id;
  fedgemap := fun _ _ => negb
|}.

(* Transport along a constant type family is the identity.  The edge family of
   [LoopQuiver] is constant, so every transport appearing in its
   hom-equivalence disappears, whatever equality proof it is taken along. *)
Lemma transport_const {A B : Type} {a a' : A} (p : a = a') (b : B) :
  Logic.transport (fun _ : A => B) p b = b.
Proof. destruct p; reflexivity. Qed.

(* The identity and [loop_swap] are DISTINCT in the hom-setoid of
   `QuiverCategory`: whatever node equality is offered, the coherence
   condition would force `true = negb true`. *)
Lemma loop_swap_distinct :
  @id QuiverCategory LoopQuiver ≈ loop_swap → False.
Proof.
  intros [ne coh].
  specialize (coh ttt ttt true).
  simpl in coh.
  unfold Logic.transport_r in coh.
  rewrite !transport_const in coh.
  discriminate.
Qed.

(* [QArrow] and [QuiverArrows] are not degenerate: [LoopQuiver] has two
   arrows, distinct in [QArrow_Setoid].  Without this the arrow functor could
   be the constant empty functor and [QuiverArrows_not_Faithful] below would
   be uninformative. *)
Definition loop_arrow (b : bool) : QArrow LoopQuiver :=
  Build_QArrow LoopQuiver ttt ttt b.

Lemma LoopQuiver_arrows_distinct :
  QArrow_equiv (loop_arrow true) (loop_arrow false) → False.
Proof.
  intros [p [q Hq]].
  unfold qmove, loop_arrow in Hq; simpl in Hq.
  rewrite !transport_const in Hq.
  discriminate.
Qed.

(* Riehl's first negative: the vertex functor is not faithful.  The identity
   and [loop_swap] have the same node map. *)
Theorem QuiverVertices_not_Faithful : Faithful QuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  apply (fmap_inj (F:=QuiverVertices)).
  simpl; intro x.
  reflexivity.
Qed.

(* Two nodes and no edges.  A homomorphism out of it is a pair of nodes and no
   edge data at all — this is what defeats the arrow functor. *)
Definition DiscQuiver : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => Empty_set).

(* The node-swapping endomorphism of [DiscQuiver]. *)
Program Definition disc_swap : DiscQuiver ~{QuiverCategory}~> DiscQuiver := {|
  fnodes   := negb;
  fedgemap := fun _ _ => Datatypes.id
|}.

(* The identity and [disc_swap] are DISTINCT in the hom-setoid: any node
   family would have to prove `true = negb true`. *)
Lemma disc_swap_distinct :
  @id QuiverCategory DiscQuiver ≈ disc_swap → False.
Proof.
  intros [ne coh].
  pose proof (ne true) as Hne.
  simpl in Hne.
  discriminate.
Qed.

(* Riehl's second negative: the arrow functor is not faithful.  The identity
   and [disc_swap] have the same action on arrows, [DiscQuiver] having none. *)
Theorem QuiverArrows_not_Faithful : Faithful QuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  apply (fmap_inj (F:=QuiverArrows)).
  simpl; intros [a b e].
  destruct e.
Qed.

(** ** The full subcategory of set-quivers, and its concreteness *)

(* Quivers whose node type satisfies uniqueness of identity proofs — Riehl's
   quivers, whose vertices form a set.  Every morphism between two of them is
   retained ([SetQuivers_Full]), so this is a full subcategory in the sense of
   Construction/Subcategory.  [SetQuivers_Full] is recorded because a reader
   will want it, but no proof below consumes it: what the results actually
   rest on is that [Sub]'s hom-setoid is DEFINITIONALLY the base one, so no
   transfer lemma is needed.v.  Its objects are PAIRS of a quiver and a
   [NodeUIP] witness, so the object map of the inclusion forgets a proof
   component and injectivity of that map is NOT claimed; what is used below is
   only that the inclusion is faithful (and full, by [SetQuivers_Full]). *)
Program Definition SetQuivers : Subcategory QuiverCategory := {|
  sobj := NodeUIP;
  shom := fun _ _ _ _ _ => poly_unit
|}.
Next Obligation. intros; exact ttt. Qed.
Next Obligation. intros; exact ttt. Qed.

Definition SetQuiverCat : Category := Sub QuiverCategory SetQuivers.

Lemma SetQuivers_Full : Full QuiverCategory SetQuivers.
Proof. intros x y ox oy f; exact ttt. Qed.

(* The three functors, restricted along the inclusion. *)
Definition SetQuiverVertices : SetQuiverCat ⟶ Sets :=
  QuiverVertices ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverArrows : SetQuiverCat ⟶ Sets :=
  QuiverArrows ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverElements : SetQuiverCat ⟶ Sets :=
  QuiverElements ◯ Incl QuiverCategory SetQuivers.

(* Both witness quivers are set-quivers, by Hedberg from decidable node
   equality. *)
Lemma LoopQuiver_NodeUIP : NodeUIP LoopQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y; left; reflexivity.
Qed.

Lemma DiscQuiver_NodeUIP : NodeUIP DiscQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y;
    solve [ left; reflexivity | right; intro Hxy; discriminate ].
Qed.

Definition LoopSetQuiver : SetQuiverCat := (LoopQuiver; LoopQuiver_NodeUIP).
Definition DiscSetQuiver : SetQuiverCat := (DiscQuiver; DiscQuiver_NodeUIP).

(* The two negatives survive the restriction: the witnesses are set-quivers,
   so all of Example 1.6.19 takes place inside [SetQuiverCat]. *)
Theorem SetQuiverVertices_not_Faithful : Faithful SetQuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  exact (fmap_inj (F:=SetQuiverVertices)
                  (x:=LoopSetQuiver) (y:=LoopSetQuiver)
                  (id; ttt) (loop_swap; ttt) (fun n => eq_refl)).
Qed.

Theorem SetQuiverArrows_not_Faithful : Faithful SetQuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  unshelve refine (fmap_inj (F:=SetQuiverArrows)
                            (x:=DiscSetQuiver) (y:=DiscSetQuiver)
                            (id; ttt) (disc_swap; ttt) _).
  simpl; intros [a b e]; destruct e.
Qed.

(* The positive half, unconditionally on [SetQuiverCat]: the [NodeUIP] witness
   the theorem needs is carried by the target object. *)
#[export] Instance SetQuiverElements_Faithful : Faithful SetQuiverElements.
Proof.
  constructor; intros x y f g Hfg.
  exact (QuiverElements_faithful_under_NodeUIP `2 y `1 f `1 g Hfg).
Qed.

(* Riehl's Example 1.6.19: quivers are concrete, by way of the disjoint union
   of their vertices and their arrows.  Neither summand alone would do. *)
#[export] Instance SetQuiver_Concrete : Concrete SetQuiverCat := {|
  underlying          := SetQuiverElements;
  underlying_faithful := SetQuiverElements_Faithful
|}.

(* Non-vacuity of [SetQuiver_Concrete]: the hom-setoids it is injective on are
   not trivial.  [loop_swap_distinct] and [disc_swap_distinct] each exhibit
   two parallel morphisms that differ, and equivalence in [SetQuiverCat] is by
   definition equivalence of the underlying quiver homomorphisms. *)
Lemma SetQuiverCat_two_arrows :
  @id SetQuiverCat LoopSetQuiver ≈ (loop_swap; ttt) → False.
Proof. exact loop_swap_distinct. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The node-UIP hypothesis is necessary, not merely convenient *)

(* The restriction to `NodeUIP` above is forced. If the disjoint-union
   functor were faithful on ALL quivers, UIP would follow — so, UIP being
   independent of Rocq's logic, that faithfulness is not provable and
   `Concrete QuiverCategory` is unreachable through this functor.

   The witness is a single quiver whose edges record BOTH endpoints:
   over a node type N with a distinguished c, take `edges x y := (c = x) *
   (c = y)`. Two endomorphisms constant at c differ by transporting the
   edge along a loop. The disjoint-union functor identifies them, because
   on the arrow summand it is enough to supply the loop itself. But
   equality in `QuiverCategory` demands ONE shared node family coherent
   with every edge simultaneously, and a single loop cannot satisfy the
   source constraint and the target constraint at once unless it is
   trivial. That last step is [uip_key] below, isolated so the arithmetic
   is visible. *)

Lemma uip_transport_id {A} {c a : A} (p : c = a) :
  Logic.transport (fun s => c = s) p eq_refl = p.
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_l {A} {c : A} {K : Type} {a a2 : A}
      (p : a = a2) (u : c = a) (v : K) :
  Logic.transport (fun s => ((c = s) * K)%type) p (u, v)
  = (Logic.transport (fun s => c = s) p u, v).
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_r {A} {c : A} {K : Type} {b b2 : A}
      (q : b = b2) (u : K) (v : c = b) :
  Logic.transport (fun t => (K * (c = t))%type) q (u, v)
  = (u, Logic.transport (fun t => c = t) q v).
Proof. destruct q; reflexivity. Qed.

(* One shared loop cannot meet the source and the target constraint at
   once unless the loop it is compared against is trivial. *)
Lemma uip_key {A} {c : A} (shared loop : c = c) :
  Logic.transport (fun t : A => ((c = c) * (c = t))%type) shared
    (eq_refl, eq_refl)
  = Logic.transport (fun s : A => ((c = s) * (c = c))%type) (eq_sym shared)
      (Logic.transport (fun s : A => ((c = s) * (c = c))%type) loop
         (eq_refl, eq_refl))
  → loop = eq_refl.
Proof.
  rewrite (uip_transport_r (c:=c) (K:=(c=c)) shared eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) loop eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) (eq_sym shared)
                (Logic.transport (fun s => c = s) loop eq_refl) eq_refl).
  rewrite !uip_transport_id.
  intro H.
  pose proof (f_equal fst H) as H1.
  pose proof (f_equal snd H) as H2.
  simpl in H1, H2.
  rewrite H2 in H1.
  simpl in H1.
  exact (eq_sym H1).
Qed.

Section UIPNecessity.

Context (N : Set) (c : N) (loop : c = c).

(* The probe quiver: edges from x to y record proofs that c is BOTH x and
   y, so an edge constrains its two endpoints independently. *)
Definition UIPQuiver : Quiver :=
  Build_Quiver_Standard_Eq N (fun x y => ((c = x) * (c = y))%type).

Definition uip_edge_id : @edges UIPQuiver c c := (eq_refl, eq_refl).
Definition uip_edge_moved : @edges UIPQuiver c c :=
  @qmove UIPQuiver c c c c loop eq_refl uip_edge_id.

Program Definition uip_hom_id : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_id |}.
Program Definition uip_hom_moved : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_moved |}.

(* The disjoint-union functor cannot tell them apart. *)
Lemma uip_homs_agree_on_elements :
  fmap[QuiverElements] uip_hom_id ≈ fmap[QuiverElements] uip_hom_moved.
Proof.
  intro z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; simpl.
    exact (existT _ loop (existT _ eq_refl eq_refl)).
Qed.

(* But the quiver category equates them only when the loop is trivial. *)
Lemma uip_homs_equal_forces_trivial :
  uip_hom_id ≈ uip_hom_moved → loop = eq_refl.
Proof.
  intros [shared coh].
  specialize (coh c c (eq_refl, eq_refl)).
  simpl in coh.
  unfold Logic.transport_r, uip_edge_moved, qmove, uip_edge_id in coh;
    simpl in coh.
  exact (uip_key (shared c) loop coh).
Qed.

End UIPNecessity.

(* Hence the hypothesis under which [QuiverElements] was proved faithful is
   exactly what that faithfulness would give back. *)
Theorem faithful_QuiverElements_implies_UIP :
  Faithful QuiverElements →
  ∀ (N : Set) (c : N) (loop : c = c), loop = eq_refl.
Proof.
  intros HF N c loop.
  apply (uip_homs_equal_forces_trivial N c loop).
  apply (fmap_inj (F:=QuiverElements)).
  apply uip_homs_agree_on_elements.
Qed.
