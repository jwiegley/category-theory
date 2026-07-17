Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Pseudo double categories *)

(* nLab: https://ncatlab.org/nlab/show/double+category
   Wikipedia: https://en.wikipedia.org/wiki/Double_category

   A (pseudo) double category has a collection of objects, two kinds of
   morphism between them — STRICT vertical 1-cells (organised as an ordinary
   [Category], [dcat]) and WEAK horizontal 1-cells ([dhor]) — and, for every
   arrangement

        a --h--> b
        |        |
        u        v          (h : dhor a b top, k : dhor c d bottom,
        v        v           u : a ~> c left, v : b ~> d right)
        c --k--> d

   a setoid [dsq h u v k] of squares filling it. Vertical composition of
   squares ([dsq_vcomp]) and the vertical identity square ([dsq_vid]) are
   STRICT and satisfy the ordinary category laws; horizontal composition of
   1-cells ([dhcomp]) is only WEAKLY associative and unital, the coherence
   isomorphisms being invertible GLOBULAR squares (squares whose two vertical
   edges are identities). This is exactly the amount of weakening that lets
   the same class host both the double category of commuting squares of a
   category (Construction/Sq.v — where [dsq h u v k := k ∘ u ≈ v ∘ h] is a
   mere proposition, its setoid trivial, every law automatic) and the double
   category of cospans (Construction/Cospan/Double.v — where squares are
   apex-maps and horizontal composition is a chosen pushout, so [dsq] is
   genuinely proof-relevant and the coherence squares carry real content).

   The horizontal 1-cells live in a plain [Type], but a square's boundary
   mentions the vertical morphisms [u], [v], which are only ever compared up
   to [≈]. So the square family must cohere across [≈] on its boundary. That
   coherence is [dsq_coerce]: along proofs [eu : u ≈ u'], [ev : v ≈ v'] a map
   [dsq h u v k → dsq h u' v' k], proof-irrelevant ([dsq_coerce_id]) and
   functorial ([dsq_coerce_trans]). This is precisely the Phase 10 displayed
   [dtransport] pattern (Theory/Displayed.v) re-applied to the vertical
   boundary of a square: the strict vertical laws are then stated THROUGH
   [dsq_coerce], which absorbs boundary reassociations such as [u' ∘ id]
   versus [u], and the weak coherence laws are stated between globular squares
   after normalising their [id ∘ id] vertical boundaries back to [id].

   Design note (kept minimal so both models supply every field): [dsq] is NOT
   assumed proof-irrelevant beyond what [dsq_setoid] provides, so the cospan
   model — whose squares are not propositions — is admissible; and every
   coherence field is dischargeable in the commuting-squares model, where the
   square setoid identifies all inhabitants. The invertible globular squares
   ([dassoc], [dunit_left], [dunit_right]) are packaged as a forward square, a
   backward square, and the two round-trip identities (a sigma-of-squares),
   which the commuting-squares model produces from associativity/unit laws of
   the base and the cospan model produces from the pushout universal property;
   named accessors ([dassoc_to], [dassoc_from], ...) are provided below.

   SCOPE. This class is the coherence-only fragment of the literature's
   pseudo double category (Grandis–Paré), matching the work order's skeleton.
   Three standard components are deliberately not required as fields:
   (a) horizontal identity squares on general VERTICAL morphisms
       (1_u : dsq (dhid a) u u (dhid c)) together with their functoriality —
       the representability formulation of the vertical zigzag in
       Theory/DoubleCategory/Companion.v exists precisely because of this;
   (b) the unit half of interchange,
       dsq_hcomp (dsq_vid h) (dsq_vid h') ≈ dsq_vid (dhcomp h' h);
   (c) naturality in squares of [dassoc]/[dunit_left]/[dunit_right]
       (contrast the hassoc_natural/hunit_*_natural fields of
       Theory/Bicategory.v).
   Both in-tree instances (Construction/Sq.v, Construction/Cospan/Double.v)
   satisfy all three, so a later phase may add them as fields without
   breaking either model.

   Orientation note: [dassoc] runs right-bracketed to left-bracketed
   (h·(g·f) ⇒ (h·g)·f), the OPPOSITE of tensor_assoc (Structure/Monoidal.v)
   and hassoc (Theory/Bicategory.v); the triangle and pentagon below are the
   standard laws rearranged for that orientation. A future horizontal-
   bicategory bridge must swap to/from accordingly. *)

(* Where double categories come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/double+category
   nLab:  https://ncatlab.org/nlab/show/proarrow+equipment
   Paper: Ehresmann, "Catégories doubles et catégories structurées",
          C. R. Acad. Sci. Paris 256 (1963), 1198-1201
   Paper: Grandis, Paré, "Limits in double categories", Cahiers de
          Topologie et Géométrie Différentielle Catégoriques 40 (1999)
   Paper: Shulman, "Framed bicategories and monoidal fibrations", Theory
          and Applications of Categories 20 (2008), no. 18

   A double category is the two-dimensional structure that keeps two
   different kinds of 1-cell at once. Shulman states the split: in some
   bicategories the 1-cells are morphisms BETWEEN the objects, such as
   functors between categories, while in others they are objects OVER the
   objects, such as bimodules, spans, distributors, or parametrized spectra
   (Shulman, "Framed bicategories and monoidal fibrations", TAC 20 (2008)).
   A bicategory retains only one kind; a double category retains both — the
   strict "tight" maps as the vertical [Category] [dcat], the weak "loose"
   bridges as the horizontal 1-cells [dhor], the two glued by squares
   [dsq].

   The two directions are asymmetric by design. Composing functions is
   strictly associative, whereas composing bimodules by tensor over a ring,
   spans by pullback, or profunctors by a coend is associative only up to
   coherent isomorphism, since each composite is fixed by a universal
   construction. The structure housing both is therefore the PSEUDO double
   category — strict one way, weak the other — the shape of the class
   above: an ordinary [dcat] for the vertical maps against a weakly
   coherent [dhcomp] whose [dassoc], [dunit_left], and [dunit_right] are
   invertible globular squares.

   Charles Ehresmann introduced double categories in 1963, alongside the
   companion memoir "Catégories structurées" (Ann. Sci. École Norm. Sup. 80
   (1963), 349-426) on internal categories: a double category is precisely
   a category internal to Cat, the category of small categories. Marco
   Grandis and Robert Paré founded the modern theory of the pseudo (weak)
   case, from "Limits in double categories" (Cahiers 40 (1999)) on through
   adjoints and Kan extensions; nLab reports their strictification theorem,
   that every pseudo double category is equivalent to a strict one. The
   SCOPE note of the header names this Grandis–Paré lineage.

   Taming coherence is the recurring motivation. Assembling the plain
   bicategory of bimodules or spans forces one to corral the associativity
   and unit coherence of the tensor or pullback, and base change is
   functorial only up to isomorphism, so the bookkeeping multiplies.
   Shulman keeps the strict maps as a separate tight direction and treats
   base change nonalgebraically, through categorical fibrations, so a
   universal property discharges the coherence in place of hand-tracking. A
   double category in which every vertical arrow carries a companion and a
   conjoint is a framed bicategory (Shulman 2008), the recasting of Wood's
   proarrow equipments ("Abstract pro arrows I", Cahiers 23 (1982));
   Theory/DoubleCategory/Companion.v realizes that machinery here through
   the records [Companion] and [Conjoint].

   The utility spreads across fields. The motivating example is Prof —
   small categories, functors vertical, profunctors horizontal, natural
   transformations as squares — beside bimodules, spans, and distributors
   (nLab; Shulman 2008). Formal category theory takes equipments as the
   correct home for weighted limits, pointwise Kan extensions, and fully
   faithful maps, notions a bare 2-category does not capture correctly, and
   Grandis–Paré develop limits, adjoints, and Kan extensions natively at
   the double-category level. In applied category theory, open systems
   assemble into symmetric monoidal double categories via structured
   cospans (Baez, Courser, "Structured cospans", TAC 35 (2020)); the
   in-tree cospans double category is [Cospan_Double] of
   Construction/Cospan/Double.v.

   The computational reading is of two kinds. The commuting-squares model
   renders diagram chasing itself as a structure: in the double category
   [Sq] of Construction/Sq.v a square [dsq] h u v k is the proposition
   k ∘ u ≈ v ∘ h, so [Sq] is the ambient home of every naturality or
   commuting diagram and the [dinterchange] law is the pasting discipline
   that makes grid-shaped diagrams composable. The applied reading is
   dataflow and wiring: a structured cospan is an open system, horizontal
   composition plugs outputs into inputs by pushout, and the symmetric
   monoidal structure is parallel composition. Companions and conjoints
   give the two canonical ways to turn a tight map into a loose bridge — in
   [Sq] every morphism is its own companion ([Sq_companion]) while
   conjoints exist exactly for the isomorphisms ([Sq_conjoint_iso]). *)

Class DoubleCategory : Type := {
  (* Objects together with their STRICT vertical morphisms. *)
  dcat : Category;

  (* Horizontal 1-cells. *)
  dhor : dcat → dcat → Type;

  (* A square with horizontal top [h], bottom [k], left vertical [u], and
     right vertical [v]. *)
  dsq {a b c d : dcat} :
    dhor a b → (a ~{dcat}~> c) → (b ~{dcat}~> d) → dhor c d → Type;

  dsq_setoid {a b c d} {h u v k} : Setoid (@dsq a b c d h u v k);

  (* Boundary coherence: recast a square along [≈]-equal vertical edges.
     (Sq: the square is a proposition, so this is the identity map;
      Cospan: the apex map is unchanged, only its recorded boundary is.) *)
  dsq_coerce {a b c d} {h} {u u' : a ~{dcat}~> c} {v v' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (ev : v ≈ v') : dsq h u v k → dsq h u' v' k;

  dsq_coerce_respects {a b c d} {h} {u u' : a ~{dcat}~> c}
    {v v' : b ~{dcat}~> d} {k} (eu : u ≈ u') (ev : v ≈ v') :
    Proper (equiv ==> equiv) (@dsq_coerce a b c d h u u' v v' k eu ev);

  (* Proof-irrelevance of the boundary: coercing along a loop is the identity
     (Phase 10 [dtransport_id] style, stated with [≈] on squares). *)
  dsq_coerce_id {a b c d} {h} {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k}
    (eu : u ≈ u) (ev : v ≈ v) (s : dsq h u v k) :
    dsq_coerce eu ev s ≈ s;

  (* Coercions compose. *)
  dsq_coerce_trans {a b c d} {h}
    {u u' u'' : a ~{dcat}~> c} {v v' v'' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (eu' : u' ≈ u'') (ev : v ≈ v') (ev' : v' ≈ v'')
    (s : dsq h u v k) :
    dsq_coerce eu' ev' (dsq_coerce eu ev s)
      ≈ dsq_coerce (Equivalence_Transitive _ _ _ eu eu')
                   (Equivalence_Transitive _ _ _ ev ev') s;

  (* Vertical identity square on a horizontal 1-cell. *)
  dsq_vid {a b} (h : dhor a b) : dsq h id id h;

  (* Vertical pasting of squares. *)
  dsq_vcomp {a0 b0 a1 b1 a2 b2}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} :
    dsq h u v k → dsq k u' v' l → dsq h (u' ∘ u) (v' ∘ v) l;

  dsq_vcomp_respects {a0 b0 a1 b1 a2 b2}
    {h u v k u' v' l} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_vcomp a0 b0 a1 b1 a2 b2 h u v k u' v' l);

  (* STRICT vertical unit laws, through [dsq_coerce] to absorb [id ∘ u] / u. *)
  dsq_vid_left {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k)) ≈ s;

  dsq_vid_right {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s) ≈ s;

  (* STRICT vertical associativity, through [dsq_coerce]. *)
  dsq_vassoc {a0 b0 a1 b1 a2 b2 a3 b3}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} {u'' : a2 ~{dcat}~> a3} {v'' : b2 ~{dcat}~> b3}
    {m : dhor a3 b3}
    (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
    dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
      (dsq_vcomp (dsq_vcomp s t) r)
      ≈ dsq_vcomp s (dsq_vcomp t r);

  (* Horizontal identity 1-cell. *)
  dhid (a : dcat) : dhor a a;

  (* Horizontal composition of 1-cells (outer then inner, like [∘]). *)
  dhcomp {a b c : dcat} : dhor b c → dhor a b → dhor a c;

  (* Horizontal pasting of squares (sharing the middle vertical edge). *)
  dsq_hcomp {a b c a' b' c'}
    {h : dhor a b} {h' : dhor b c}
    {u : a ~{dcat}~> a'} {v : b ~{dcat}~> b'} {w : c ~{dcat}~> c'}
    {k : dhor a' b'} {k' : dhor b' c'} :
    dsq h u v k → dsq h' v w k' → dsq (dhcomp h' h) u w (dhcomp k' k);

  dsq_hcomp_respects {a b c a' b' c'} {h h' u v w k k'} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_hcomp a b c a' b' c' h h' u v w k k');

  (* Interchange: pasting a 2x2 grid vertically-then-horizontally agrees with
     horizontally-then-vertically. The two composites carry the SAME boundary
     ([dhcomp h2 h1] on top, [w1 ∘ u1] / [w3 ∘ u3] on the sides, [dhcomp k2 k1]
     below), so no [dsq_coerce] is required. *)
  dinterchange {a b c a' b' c' a'' b'' c''}
    {h1 : dhor a b} {h2 : dhor b c}
    {u1 : a ~{dcat}~> a'} {u2 : b ~{dcat}~> b'} {u3 : c ~{dcat}~> c'}
    {j1 : dhor a' b'} {j2 : dhor b' c'}
    {w1 : a' ~{dcat}~> a''} {w2 : b' ~{dcat}~> b''} {w3 : c' ~{dcat}~> c''}
    {k1 : dhor a'' b''} {k2 : dhor b'' c''}
    (s11 : dsq h1 u1 u2 j1) (s12 : dsq h2 u2 u3 j2)
    (s21 : dsq j1 w1 w2 k1) (s22 : dsq j2 w2 w3 k2) :
    dsq_vcomp (dsq_hcomp s11 s12) (dsq_hcomp s21 s22)
      ≈ dsq_hcomp (dsq_vcomp s11 s21) (dsq_vcomp s12 s22);

  (* Weak associator: an invertible globular square between the two
     bracketings of a horizontal composite (forward square, backward square,
     two round-trip identities normalised through [dsq_coerce]). *)
  dassoc {a b c d} (f : dhor a b) (g : dhor b c) (h : dhor c d) :
    { fwd : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f) &
    { bwd : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhcomp g f)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid (dhcomp (dhcomp h g) f)) } };

  (* Weak left unitor: [dhid b · h ≅ h] as an invertible globular square. *)
  dunit_left {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp (dhid b) h) id id h &
    { bwd : dsq h id id (dhcomp (dhid b) h) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp (dhid b) h))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (* Weak right unitor: [h · dhid a ≅ h] as an invertible globular square. *)
  dunit_right {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp h (dhid a)) id id h &
    { bwd : dsq h id id (dhcomp h (dhid a)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhid a)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (* Triangle coherence (square level): whiskering the left unitor equals the
     associator followed by whiskering the right unitor. *)
  dcoherence_triangle {a b c} (f : dhor a b) (k : dhor b c) :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (projT1 (dassoc f (dhid b) k))
                 (dsq_hcomp (dsq_vid f) (projT1 (dunit_right k))))
      ≈ dsq_hcomp (projT1 (dunit_left f)) (dsq_vid k);

  (* Pentagon coherence (square level): the two globular paths from
     [k · (h · (g · f))] to [((k · h) · g) · f] agree, their [id]-boundaries
     normalised through [dsq_coerce]. *)
  dcoherence_pentagon {a b c d e}
    (f : dhor a b) (g : dhor b c) (h : dhor c d) (k : dhor d e) :
    dsq_coerce (id_left (id ∘ id)) (id_left (id ∘ id))
      (dsq_vcomp (dsq_vcomp
          (dsq_hcomp (projT1 (dassoc f g h)) (dsq_vid k))
          (projT1 (dassoc f (dhcomp h g) k)))
        (dsq_hcomp (dsq_vid f) (projT1 (dassoc g h k))))
      ≈ dsq_vcomp (projT1 (dassoc (dhcomp g f) h k))
                  (projT1 (dassoc f g (dhcomp k h)))
}.

#[export] Existing Instance dsq_setoid.
#[export] Existing Instance dsq_coerce_respects.
#[export] Existing Instance dsq_vcomp_respects.
#[export] Existing Instance dsq_hcomp_respects.

(** ** Named accessors for the invertible globular squares. *)

Definition dassoc_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f)
  := projT1 (dassoc f g h).

Definition dassoc_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f))
  := projT1 (projT2 (dassoc f g h)).

Definition dunit_left_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp (dhid b) h) id id h
  := projT1 (dunit_left h).

Definition dunit_left_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp (dhid b) h)
  := projT1 (projT2 (dunit_left h)).

Definition dunit_right_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp h (dhid a)) id id h
  := projT1 (dunit_right h).

Definition dunit_right_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp h (dhid a))
  := projT1 (projT2 (dunit_right h)).

(* The round-trip identities, named after [iso_to_from]/[iso_from_to] of
   Theory/Isomorphism.v: [X_to_from] cancels at the codomain of [X_to] and
   [X_from_to] at its domain (vertical pasting [dsq_vcomp s t] is the
   composite "t after s"). *)

Definition dassoc_from_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_to f g h) (dassoc_from f g h))
    ≈ dsq_vid (dhcomp h (dhcomp g f))
  := fst (projT2 (projT2 (dassoc f g h))).

Definition dassoc_to_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_from f g h) (dassoc_to f g h))
    ≈ dsq_vid (dhcomp (dhcomp h g) f)
  := snd (projT2 (projT2 (dassoc f g h))).

Definition dunit_left_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_to h) (dunit_left_from h))
    ≈ dsq_vid (dhcomp (dhid b) h)
  := fst (projT2 (projT2 (dunit_left h))).

Definition dunit_left_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_from h) (dunit_left_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_left h))).

Definition dunit_right_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_to h) (dunit_right_from h))
    ≈ dsq_vid (dhcomp h (dhid a))
  := fst (projT2 (projT2 (dunit_right h))).

Definition dunit_right_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_from h) (dunit_right_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_right h))).

(** ** The derived coercion lemma pack

    Mirrors the [dtransport] pack of Theory/Displayed.v: consumers of the
    class spend their time reorienting and cancelling boundary coercions,
    and each step is one of the lemmas below. *)

Section DoubleCategoryLemmas.

Context {D : DoubleCategory}.

(* Coercing there and back again cancels (left orientation). *)
Lemma dsq_coerce_symm_l {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) :
  dsq_coerce (symmetry eu) (symmetry ev) (dsq_coerce eu ev s) ≈ s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* Coercing back and there again cancels (right orientation). *)
Lemma dsq_coerce_symm_r {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (t : dsq h u' v' k) :
  dsq_coerce eu ev (dsq_coerce (symmetry eu) (symmetry ev) t) ≈ t.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* Reorienting a coercion equation: a coercion may be moved to the other
   side of [≈] by inverting the proofs it rides on. *)
Lemma dsq_coerce_flip {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) (t : dsq h u' v' k) :
  dsq_coerce eu ev s ≈ t ↔ s ≈ dsq_coerce (symmetry eu) (symmetry ev) t.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply dsq_coerce_symm_l.
  - rewrite H.
    apply dsq_coerce_symm_r.
Qed.

(* Coercion does not depend on the proofs coerced along: the groupoid laws
   [dsq_coerce_id]/[dsq_coerce_trans] force any two parallel proof pairs to
   coerce identically. *)
Lemma dsq_coerce_proof_irrel {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu eu' : u ≈ u') (ev ev' : v ≈ v') (s : dsq h u v k) :
  dsq_coerce eu ev s ≈ dsq_coerce eu' ev' s.
Proof.
  apply (snd (dsq_coerce_flip eu ev s (dsq_coerce eu' ev' s))).
  symmetry; rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* [dsq_coerce_trans] with the composite proofs replaced by any proofs of
   the endpoints' relations. *)
Lemma dsq_coerce_trans_any {a b c d : dcat} {h : dhor a b}
  {u u' u'' : a ~> c} {v v' v'' : b ~> d} {k : dhor c d}
  (eu1 : u ≈ u') (eu2 : u' ≈ u'') (eu3 : u ≈ u'')
  (ev1 : v ≈ v') (ev2 : v' ≈ v'') (ev3 : v ≈ v'')
  (s : dsq h u v k) :
  dsq_coerce eu2 ev2 (dsq_coerce eu1 ev1 s) ≈ dsq_coerce eu3 ev3 s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_proof_irrel.
Qed.

(* The strict vertical laws along any proofs of the base laws: exactly the
   shape of the unit/associativity obligations of categories built from
   squares. *)
Lemma dsq_vid_left_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : id ∘ u ≈ u) (ev : id ∘ v ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp s (dsq_vid k)) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k))).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_left.
Qed.

Lemma dsq_vid_right_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : u ∘ id ≈ u) (ev : v ∘ id ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vid h) s) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_right.
Qed.

Lemma dsq_vassoc_any {a0 b0 a1 b1 a2 b2 a3 b3 : dcat}
  {h : dhor a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
  {k : dhor a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
  {l : dhor a2 b2} {u'' : a2 ~> a3} {v'' : b2 ~> b3}
  {m : dhor a3 b3}
  (eu : u'' ∘ (u' ∘ u) ≈ (u'' ∘ u') ∘ u)
  (ev : v'' ∘ (v' ∘ v) ≈ (v'' ∘ v') ∘ v)
  (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vcomp s t) r)
    ≈ dsq_vcomp s (dsq_vcomp t r).
Proof.
  transitivity
    (dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
                (dsq_vcomp (dsq_vcomp s t) r)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vassoc.
Qed.

End DoubleCategoryLemmas.
