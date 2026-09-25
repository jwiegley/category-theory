Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Complete.

Generalizable All Variables.

(** * Where completeness of spaces stops: [PTopCat], and [Top] below its
      homs *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
     that a small complete category is a preorder, consumed through
     Structure/Complete/Freyd.v; §V.9 Remark 1 as in the header of
     Instance/Top/Complete.v, whose completeness this file bounds.
   nLab: https://ncatlab.org/nlab/show/complete+small+category
   nLab: https://ncatlab.org/nlab/show/Top

   BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header):
   were a category with products indexed by its own arrow collection K to
   carry two distinct parallel arrows, the 2^K choices between them would
   give 2^K arrows into the K-fold power, more than the K arrows there are.
   Completeness in the book's sense is therefore a property of large
   categories, relative to the size of the shapes.  #455's Instance/Top/
   StoneCech/Refutations.v turned that into theorems about the Type-valued
   [Top] and [CompHaus], whose homs sit above their points, at every shape
   universe at or above the homs; this file runs the same argument against
   Instance/Top/Prop.v's [PTopCat@{o so}], whose homs sit AT the points'
   universe [o] and whose objects sit at [so], above it, and carries
   #455's forms over [Top] and [CompHaus] down to every shape universe
   above the points.  The two points of [PBool], [ppoint_true] and
   [ppoint_false] (Instance/Top/Subspace.v), are told apart by evaluation
   at the point ([pbool_eval_pt]), constructively.  Nothing here is an
   axiom: informative excluded middle ([IEM], Instance/Sets/Classifier/
   OneLevel.v) and decidable equality of spaces ([ObjDecEq],
   Construction/Quotient.v) are hypotheses, and under either an arrow
   index exists ([canonical_ArrowIndex], through Instance/Top/StoneCech/
   Refutations.v's [ObjDecEq_of_IEM]).

   NAMES.  The refutations here and in Instance/Top/Cocomplete/
   Refutations.v, the colimit dual, share one scheme, the same on both
   sides: [_Freyd] and [_Cantor_] name the ARGUMENT, the hypothesis suffix
   names the REACH, and [_below], on the limit side only, marks a form
   over [Top] or [CompHaus] that reaches below the hom universe [h].
     [_Freyd]           Freyd's argument from an arrow index
                        ([ArrowIndex]) at the shape (or index) universe
                        [s], the index being the hypothesis; nothing ties
                        [s] to the points' universe [o].
     [_ObjDecEq]        decidable equality of spaces ([ObjDecEq]), at
                        every [s] with [o < s], [o := Set] included.
     [_IEM]             informative excluded middle ([IEM]), at every [s]
                        with [o < s], [o := Set] included.
     [_IEM_canonical]   [IEM] through the canonical index of the category's
                        own objects, untransported: every [s] at or above
                        the object universe ([so] for [PTopCat@{o so}],
                        [h] for [Top@{h o}]).
     [_below_ObjDecEq], [_below_IEM]   (limit side, over [Top] and
                        [CompHaus]) the reach of [_ObjDecEq] and [_IEM]
                        (for products [o < s <= h], at the reading
                        [@{s s s h h h}]),
                        the shapes strictly between the points and the
                        homs included, set apart from the forms of the
                        same classes that stop at [h <= s]: #455's
                        [Top_not_complete_IEM] and
                        [CompHaus_not_complete_IEM_below], and
                        [Top_iprod_refuted_IEM_canonical] here.  The
                        colimit side has no form that stops at [h <= s],
                        and its [Top] forms carry the plain suffixes.
     [_Cantor_ObjDecEq], [_Cantor_IEM]   (colimit side only) Cantor's
                        argument under the same hypotheses and with the
                        same reach, but that the [ObjDecEq] form needs
                        [Set < o].
   Instance/Top/StoneCech/Refutations.v's [Top_not_complete],
   [Top_not_complete_IEM] and [CompHaus_not_complete_IEM_below] (#455)
   predate the scheme: the first is a [_Freyd] form, the second an
   [_IEM_canonical] one, and the third's [_below] means below the OBJECT
   universe [c] of [CompHaus], at [h <= s]; this file's
   [CompHaus_not_complete_below_IEM] is the form that reaches below the
   hom universe.

   WHAT IS HERE.  This is the [PTopCat] half of #1328's item 4 (re-run
   #455's refutations against the Prop-valued encoding), for limits, and
   the extension of #455's [Top] and [CompHaus] forms below the homs.
     - [PTop_not_complete_Freyd]: given an [ArrowIndex] of [PTopCat] at a
       shape universe [s], [Complete@{r s o so} PTopCat] is false.
       [PTop_not_complete_IEM_canonical]: under [IEM], every [s] with
       [so <= s], [canonical_ArrowIndex] indexing at the arrow collection,
       which sits at [so]; [PTop_not_complete_IEM] below subsumes it (its
       [o < s] follows from [so <= s]), and it stays as the untransported
       form.
     - [PTop_ArrowIndex_transport]: the objects and homs of
       [PTopCat@{o so1}] and [PTopCat@{o so2}] are the same [PTop@{o}] and
       [PMor@{o}], so an arrow index moves between them, with no equation
       in its block; through it, [PTop_not_complete_ObjDecEq] and
       [PTop_not_complete_IEM] refute completeness at EVERY shape universe
       strictly above the points, [o < s], the canonical index being built
       at [PTopCat@{o s}] and transported.  The colimit dual reuses it.
     - [PTop_no_ArrowIndex_below]: constructively, NO arrow index of
       [PTopCat@{o so}] exists at any universe [s <= o], by
       [PTop_not_complete_Freyd] against Instance/Top/Complete.v's
       [PTop_Complete]; [PTop_no_ArrowIndex_at_points] is its case
       [s = o], proved against the book's route [PTop_Complete_via_products]
       instead.
     - [PTop_iprod_refuted_IEM]: under [IEM], products indexed at any
       universe [s] strictly above the points are refuted with no
       equalizer involved, while Instance/Top/Complete.v's
       [PTop_HasIndexedProducts] builds them at every index universe at or
       below [o].
     - [Top_iprod_refuted_IEM_canonical]: under [IEM], the Type-valued
       [Top@{h o}] has no [HasIndexedProducts@{s s s s h h}] at any index
       universe [s] at or above its hom universe [h], which is also its
       object universe: the canonical index, untransported.
     - [top_rebuild] and [Top_ArrowIndex_transport]: a continuous map of
       [Top@{h1 o}] is rebuilt as one of [Top@{h2 o}], the same map of
       points with the continuity field eta-expanded, and through it an
       arrow index moves between the two hom universes; neither block
       carries an equation ([About]).  The eta-expansion is what keeps the
       two hom universes apart.  Written [continuity := continuity f], the
       field is passed through unexpanded, elaboration unifies
       [Continuous@{h1 o}] with [Continuous@{h2 o}] first-order, and the
       rebuild acquires the equation [h1 = h2] (read back by [About] under
       the binder [@{o h1 h2 | o < h1, o < h2 +}]); under
       [@{o h1 h2 | o < h1, h1 < h2 +}] it is refused ("Cannot enforce
       h1 = h2 because h1 < h2").  That equation is an artifact of the
       encoding, not a wall; Test/ProbeTopComplete458.v pins it as such
       (N29) beside the eta-expanded rebuild at [h1 < h2], accepted.
     - Through the transport, the canonical index being built at
       [Top@{s o}]: [Top_not_complete_below_ObjDecEq] and
       [Top_not_complete_below_IEM] refute [Complete@{r s h h} Top@{h o}]
       at every [s] with [o < s], the shapes strictly between the points
       and the homs included, the first at [o := Set] as well;
       [Top_iprod_refuted_below_IEM] refutes
       [HasIndexedProducts@{s s s h h h} Top@{h o}] under [IEM] at every
       [s] with [o < s <= h].  The fourth slot of [HasIndexedProducts]
       bounds its third, where these statements put the index universe
       [s], and its sixth, the homs ([About]: [u1 <= u2] and
       [u4 <= u2]), so this reading carries [s <= h] and
       [Top_iprod_refuted_IEM_canonical]'s reading [@{s s s s h h}]
       carries [h <= s]; the two meet at [s = h].
       [CompHaus_not_complete_below_IEM] is #455's
       [CompHaus_ArrowIndex_of_Top] applied to the transported index: it
       refutes [Complete@{r s h c} CompHaus] under [IEM] at every [s] with
       [o < s], below [h] included, at the instances of [CompHaus] that
       Instance/Top/StoneCech/Refutations.v's COVERAGE records for
       [CompHaus_not_complete_IEM_below] (the two blocks agree but for
       that constant's [h <= s], which is [o < s] here).

   THE BOUNDARY.  With Instance/Top/Complete.v: completeness of
   [PTopCat@{o so}] is provable at every shape universe [s <= o]
   ([PTop_Complete], with no hypothesis) and refuted under [IEM], or under
   [ObjDecEq], at every [s] with [o < s] ([PTop_not_complete_IEM],
   [PTop_not_complete_ObjDecEq]).  No shape universe lies between the
   two; without [IEM], [ObjDecEq] or an index nothing above the points is
   refuted (NOT DELIVERED).  Measured in the scratch file of
   Instance/Top/Complete.v's boundary paragraph: both refutations are
   accepted at an [s] with [o < s] and at [o := Set], and
   [PTop_not_complete_IEM] read at [Complete@{o o o so}] is refused
   ("Cannot enforce <1> = o because <1> < o", the generated universe
   written <1>).  The index side is sharp the same way: no arrow index at
   or below [o], constructively, while the proof of
   [PTop_not_complete_ObjDecEq] builds one at every [s] above it from
   [ObjDecEq] ([canonical_ArrowIndex] at [PTopCat@{o s}], transported).
   Over the Type-valued [Top@{h o}] completeness is refuted under [IEM],
   or under [ObjDecEq], at every [s] with [o < s], and at [s <= o] it is
   neither built nor refuted.  Measured in Test/ProbeTopComplete458.v:
   [Top_not_complete_below_IEM] and [CompHaus_not_complete_below_IEM]
   are accepted at an [s] with [o < s < h], and
   [Top_not_complete_below_ObjDecEq] at [o := Set];
   [Top_not_complete_below_IEM] read at [s := o], and
   [Top_iprod_refuted_below_IEM] read at the index universe [o], each by
   its universe instance, are refused ("Cannot enforce o < o because
   o = o"), and #455's
   [Top_not_complete_IEM] and
   [CompHaus_not_complete_IEM_below] read at an [s] with [o < s < h] are
   refused ("Cannot enforce <3> = h because <3> <= <2> < h", the
   generated universes numbered in order of appearance in the message).

   STRENGTHS.  Every theorem ends in [False].  [PTop_ArrowIndex_transport]
   and [Top_ArrowIndex_transport] are data whose decoding law is [≈] of
   arrows, [top_rebuild] is data, and the two [PTop_no_ArrowIndex_*] are
   [:=] terms ending in [False].  No proof ends [Defined].

   UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
   left out; [e] the level of [IEM], free.
     PTop_not_complete_Freyd@{r s o so} :
       ArrowIndex@{s so o} PTopCat@{o so} → ¬ Complete@{r s o so}
       (* o < so, s <= r, o <= r: nothing ties s to o *)
     PTop_not_complete_IEM_canonical@{e r s o so} :
       IEM@{e} → ¬ Complete@{r s o so}      (* so <= s, o <= s *)
     PTop_not_complete_ObjDecEq@{r s o so} :
       ObjDecEq PTopCat@{o so} → ¬ Complete@{r s o so}   (* o < s *)
     PTop_not_complete_IEM@{e r s o so} :
       IEM@{e} → ¬ Complete@{r s o so}      (* o < s *)
     PTop_no_ArrowIndex_below@{s o so u} :
       ¬ ArrowIndex@{s so o} PTopCat@{o so}  (* s <= o *)
     PTop_iprod_refuted_IEM@{e s o so} :
       IEM@{e} → ¬ HasIndexedProducts@{s s s s so o} PTopCat@{o so}
       (* o < s *)
     Top_iprod_refuted_IEM_canonical@{e s h o} :
       IEM@{e} → ¬ HasIndexedProducts@{s s s s h h} Top@{h o}
       (* o < h, h <= s *)
     top_rebuild@{o h1 h2} :
       ContinuousMorphism@{h1 o} X Y → ContinuousMorphism@{h2 o} X Y
       (* o < h1, o < h2: no equation *)
     Top_ArrowIndex_transport@{s o h1 h2} :
       ArrowIndex@{s h1 h1} Top@{h1 o} → ArrowIndex@{s h2 h2} Top@{h2 o}
       (* o < h1, o < h2: no equation *)
     Top_not_complete_below_ObjDecEq@{r s h o} :
       ObjDecEq Top@{h o} → ¬ Complete@{r s h h}   (* o < h, o < s *)
     Top_not_complete_below_IEM@{e r s h o} :
       IEM@{e} → ¬ Complete@{r s h h}       (* o < h, o < s *)
     Top_iprod_refuted_below_IEM@{e s h o} :
       IEM@{e} → ¬ HasIndexedProducts@{s s s h h h} Top@{h o}
       (* o < h, o < s, s <= h *)
     CompHaus_not_complete_below_IEM@{e r s c h o …} :
       IEM@{e} → ¬ Complete@{r s h c}  (* o < h, o < s, h <= c *)
   [CompHaus_not_complete_below_IEM] carries seven further universes, the
   slots of [CompHaus] and [Top] that #455's [CompHaus_not_complete] and
   [CompHaus_ArrowIndex_of_Top] leave free; its block, stdlib caps left
   out, is #455's [CompHaus_not_complete_IEM_below]'s with [h <= s]
   replaced by [o < s], constraint for constraint.  Over the [About]
   output of all 17 of this file's constants (its [Print Module]
   listing; it declares no obligation, record or inductive), [Set] occurs
   in 10 blocks and only as a strict lower bound on an object universe of
   [PTopCat]: [Set < so] in 9, [Set < s] in the three refutations that
   transport over [PTopCat] ([PTop_not_complete_ObjDecEq],
   [PTop_not_complete_IEM], [PTop_iprod_refuted_IEM]; the [PTopCat@{o s}]
   they build the index at) and [Set < so1], [Set < so2] in
   [PTop_ArrowIndex_transport]; none of the seven constants over [Top] and
   [CompHaus] mentions [Set], and no block carries an equation.

   ROUTE AND COST.  Closure 173 [Category.*] modules excluding this file
   ([Print Libraries]).  Instance/Top/StoneCech/Refutations.v, required
   for [ObjDecEq_of_IEM], [Top_not_complete], [CompHaus_not_complete] and
   [CompHaus_ArrowIndex_of_Top] rather than restating them, costs 28 at
   the margin (dropped alone: 145); Instance/Top/CompHaus.v, required for
   the name [CompHaus], costs nothing at the margin, since the first loads
   it; dropped together they cost 31 (142).

   NOT DELIVERED.  A refutation above the points with neither an index
   nor [IEM] nor [ObjDecEq]: thinness of a small complete category is not
   constructively provable (Structure/Complete/Freyd.v's header).  The
   colimit side (Instance/Top/Cocomplete/Refutations.v).  For the
   Type-valued [Top], completeness at shapes at or below the points,
   [s <= o], is neither built nor refuted (Instance/Top/Complete.v builds
   it over [PTopCat] only), and neither are its products at index
   universes at or below [o]; nor is [CompHaus]'s completeness there.
   This file has no counterpart of the colimit side's Cantor argument. *)

(** ** Evaluation at the point separates the two points of [PBool] *)

Definition pbool_eval_pt@{o so +| o < so +}
  (f : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) : bool :=
  pmap f ttt.

Lemma pbool_eval_pt_resp@{o so +| o < so +}
  (u v : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  u ≈ v → pbool_eval_pt u = pbool_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(** ** Freyd's core at an arbitrary arrow index *)

Theorem PTop_not_complete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (complete_iprod comp (fun _ : ai_index AI => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(* The canonical index of [PTopCat@{o so}] sits at [so]. *)
Theorem PTop_not_complete_IEM_canonical@{e r s o so +| o < so +} (E : IEM@{e})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (canonical_ArrowIndex (ObjDecEq_of_IEM E PTopCat@{o so})) comp).
Qed.

(* The objects and homs of [PTopCat@{o so1}] and [PTopCat@{o so2}] are the
   same [PTop@{o}] and [PMor@{o}], so an arrow index moves between them. *)
Definition PTop_ArrowIndex_transport@{s o so1 so2 +| o < so1, o < so2 +}
  (AI : ArrowIndex@{s so1 o} PTopCat@{o so1}) :
  ArrowIndex@{s so2 o} PTopCat@{o so2} :=
  @Build_ArrowIndex PTopCat@{o so2} (ai_index AI)
    (fun x y f => @ai_enc PTopCat@{o so1} AI x y f)
    (fun x y m d => @ai_dec PTopCat@{o so1} AI x y m d)
    (fun x y f d => @ai_dec_enc PTopCat@{o so1} AI x y f d).

(* Every shape universe strictly above the points: decidable equality of
   spaces, transported to the canonical index at [s]. *)
Theorem PTop_not_complete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DO : ObjDecEq PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DO : ObjDecEq PTopCat@{o s})))
           comp).
Qed.

Theorem PTop_not_complete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so}) comp).
Qed.

(** ** No arrow index at or below the points, constructively *)

Definition PTop_no_ArrowIndex_at_points@{o so +| o < so +}
  (AI : ArrowIndex@{o so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete_via_products.

Definition PTop_no_ArrowIndex_below@{s o so +| s <= o, o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete.

(** ** Products above the points *)

Theorem PTop_iprod_refuted_IEM@{e s o so +| o < so, o < s +}
  (E : IEM@{e})
  (HP : @HasIndexedProducts@{s s s s so o} PTopCat@{o so}) : False.
Proof.
  pose (AI := PTop_ArrowIndex_transport@{s o s so}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E PTopCat@{o so} : ObjDecEq PTopCat@{o s}))).
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(** ** The Type-valued [Top]: products at and above the hom universe *)

(* The canonical index of [Top@{h o}] sits at its object universe [h], and
   indexes at every [s] with [h <= s]. *)
Theorem Top_iprod_refuted_IEM_canonical@{e s h o +| o < h, h <= s +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s s h h} Top@{h o}) : False.
Proof.
  pose (AI := canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(** ** The Type-valued [Top]: an arrow index moves between hom universes *)

(* A continuous map of [Top@{h1 o}] rebuilt as one of [Top@{h2 o}]: the
   same map of points, and the continuity field eta-expanded.  Written
   [continuity := continuity f] instead, the field is passed through
   unexpanded, elaboration unifies [Continuous@{h1 o}] with
   [Continuous@{h2 o}] first-order, and the block acquires [h1 = h2]; the
   eta-expanded field carries no equation. *)
Definition top_rebuild@{o h1 h2 | o < h1, o < h2 +} {X Y : TopSpace@{o}}
  (f : ContinuousMorphism@{h1 o} X Y) : ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f;
     continuity := fun U HU => continuity f U HU |}.

(* The index never mentions a hom universe: encode and decode through the
   rebuild, both ways; the decoding law is pointwise. *)
Definition Top_ArrowIndex_transport@{s o h1 h2 | o < h1, o < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) :
  ArrowIndex@{s h2 h2} Top@{h2 o} :=
  @Build_ArrowIndex Top@{h2 o} (ai_index AI)
    (fun x y f => @ai_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f))
    (fun x y m d => top_rebuild@{o h1 h2}
                      (@ai_dec Top@{h1 o} AI x y m (top_rebuild@{o h2 h1} d)))
    (fun x y f d z => @ai_dec_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f)
                        (top_rebuild@{o h2 h1} d) z).

(* Every shape universe strictly above the points, the shapes below the
   homs included: the canonical index is built at [Top@{s o}] and
   transported to [Top@{h o}]. *)
Theorem Top_not_complete_below_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           comp).
Qed.

Theorem Top_not_complete_below_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete_below_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) comp).
Qed.

(* Products indexed strictly above the points and at or below the homs:
   the reading of [HasIndexedProducts] whose fourth slot is the hom
   universe. *)
Theorem Top_iprod_refuted_below_IEM@{e s h o +| o < h, o < s, s <= h +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s h h h} Top@{h o}) : False.
Proof.
  pose (AI := Top_ArrowIndex_transport@{s o s h}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* #455's [CompHaus_ArrowIndex_of_Top] after the transport: [Complete
   CompHaus] refuted under [IEM] at every shape universe strictly above
   the points, the shapes below the homs included. *)
Theorem CompHaus_not_complete_below_IEM@{e r s c h o +| o < h, o < s +}
  (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.
