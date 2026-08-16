Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.

From Coq Require Import Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Decategorifying the exponential laws: the groupoid of finite sets *)

(* nLab: https://ncatlab.org/nlab/show/decategorification
   nLab: https://ncatlab.org/nlab/show/categorification
   nLab: https://ncatlab.org/nlab/show/FinSet

   Riehl, "Category Theory in Context", §1.4 Example 1.4.11 (printed p. 29)
   reads the four exponential laws

       z^(x × y) ≅ (z^y)^x,           (y × z)^x ≅ y^x × z^x,
       x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

   in finite sets, and observes that on restricting to the GROUPOID of finite
   sets and bijections and applying the cardinality functor to the DISCRETE
   category of natural numbers, the four isomorphisms become the four
   arithmetic identities

       z^(xy) = (z^y)^x,   (yz)^x = y^x z^x,
       x(y+z) = xy + xz,   x^(y+z) = x^y x^z,

   so that the groupoid of finite sets is a categorification of ℕ.  The
   naturality half of the same example -- Mac Lane, "Categories for the
   Working Mathematician", 2nd ed., §II.5 Exercise 2 (printed p. 44) -- is
   Structure/Cartesian/Closed/Natural.v.

   ** What is and is not the content here

   The four identities below are, as arithmetic, entirely elementary: [lia]
   proves the third outright and the other three follow by induction with
   [Nat.pow_mul_r], [Nat.pow_mul_l], [Nat.mul_add_distr_l] and
   [Nat.pow_add_r].  NONE of that is used.  Each identity is obtained by
   applying [FinSet_skeletal] -- equivalently, the arrow action of
   [Card_FinSet] -- to the CATEGORICAL isomorphism at [FinSet], so the route
   is the content: the equation of numbers is the shadow cast by an
   isomorphism of finite sets, and the proof term contains no arithmetic
   induction at all.

   ** Why two cardinality functors

   [Card_Groupoid] is Riehl's functor as stated: its domain is the groupoid
   of genuinely SET-LIKE objects (Instance/FinSet/Skeleton.v's [Set_f], finite
   setoids each carrying a chosen counting) and its arrow action discards the
   bijection, keeping only the fact that one exists -- which is exactly what
   decategorification does.

   [Card_FinSet] is its skeletal shadow: [FinSet] has the naturals themselves
   as objects (Instance/FinSet.v), so the functor is the identity on objects
   and its arrow action is [FinSet_skeletal].  It is the one the four
   identities are read off, because at [FinSet] the product, coproduct and
   exponential objects ARE [*], [+] and [^] on [nat]
   (Instance/FinSet/Product.v, Instance/FinSet.v, Instance/FinSet/Closed.v).

   ** A note on [=] versus [≈]

   The library's standing rule is that morphisms are compared with [≈], never
   with [=].  Nothing below breaks it: every [=] here is between OBJECTS.
   [FinSet]'s objects are natural numbers, and the hom-sets of
   [DiscreteCat nat] (Instance/Discrete.v) are equality PROOFS between
   naturals compared by [Morphism_equality], i.e. by [eq] on those proofs.
   That is why every functor law below is an identity between two proofs of
   one equation of naturals, discharged by Hedberg's theorem in its standard
   library form [UIP_dec] applied to [Nat.eq_dec] -- a theorem, not an axiom,
   so the whole file stays closed under the global context. *)

(** ** The cardinality functor on the groupoid of finite sets *)

(* The arrow action ignores WHICH bijection it is given and retains only the
   equality of countings that its existence forces.  That is the
   decategorification: a groupoid whose hom-sets can be large is mapped onto
   a discrete category whose hom-sets are subsingletons. *)
Program Definition Card_Groupoid : Groupoid Set_f ⟶ DiscreteCat nat := {|
  fobj := setf_cardinality;
  fmap := fun A B i => setf_cardinality_iso_invariant A B i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(** ** The skeletal companion *)

(* On the skeleton the object action is the identity: [FinSet]'s objects are
   already the naturals, and the whole functor is [FinSet_skeletal] read as an
   arrow action. *)
Program Definition Card_FinSet : Groupoid FinSet ⟶ DiscreteCat nat := {|
  fobj := fun n => n;
  fmap := fun m n i => @FinSet_skeletal m n i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(* The object action is the identity on the nose. *)
Example Card_FinSet_identity_on_objects (n : FinSet) :
  fobj[Card_FinSet] n = n := eq_refl.

(** ** The four arithmetic identities, decategorified

    Each is the image under [Card_FinSet] of the corresponding categorical
    isomorphism, taken at [FinSet].  Orientations follow the in-tree object
    maps: [product_obj m n = (m * n)%nat] (Instance/FinSet/Product.v),
    [product_obj] of [FinSet_Cocartesian] -- the coproduct -- is
    [(m + n)%nat] (Instance/FinSet.v), and [exponent_obj m n = (n ^ m)%nat],
    so that [exponent_obj x z], displayed [z ^ x], is the object of functions
    FROM x (Instance/FinSet/Closed.v). *)

Definition nat_exp_prod_l (x y z : nat) : (z ^ (x * y))%nat = ((z ^ y) ^ x)%nat :=
  FinSet_skeletal (@exp_prod_l FinSet _ _ x y z).

Definition nat_exp_prod_r (x y z : nat) :
  ((y * z) ^ x)%nat = (y ^ x * z ^ x)%nat :=
  FinSet_skeletal (@exp_prod_r FinSet _ _ x y z).

Definition nat_prod_coprod_r (x y z : nat) :
  (x * (y + z))%nat = (x * y + x * z)%nat :=
  FinSet_skeletal (@prod_coprod_r FinSet _ _ _ x y z).

Definition nat_exp_coprod (x y z : nat) :
  (x ^ (y + z))%nat = (x ^ y * x ^ z)%nat :=
  FinSet_skeletal (@exp_coprod FinSet _ _ _ x y z).

(* Each identity IS the functor's action on the isomorphism; stated for one
   of the four, since [fmap[Card_FinSet]] is [FinSet_skeletal] by
   construction. *)
Example nat_exp_coprod_is_Card_image (x y z : nat) :
  nat_exp_coprod x y z = fmap[Card_FinSet] (@exp_coprod FinSet _ _ _ x y z)
  := eq_refl.

(** ** Naturality decategorifies to nothing

    [DiscreteCat nat] is THIN: any two parallel arrows agree, because its
    hom-sets are equality proofs between naturals and [Nat.eq_dec] makes those
    unique.  So every naturality square in the image of a cardinality functor
    commutes for free, and the four natural isomorphisms of
    Structure/Cartesian/Closed/Natural.v have no shadow downstairs at all:
    what survives decategorification is the equation, not its naturality. *)
Lemma DiscreteCat_nat_Thin : Thin (DiscreteCat nat).
Proof. intros x y f g; apply (UIP_dec PeanoNat.Nat.eq_dec). Qed.

Corollary Card_FinSet_squares_commute {m n : FinSet}
          (i j : m ~{Groupoid FinSet}~> n) :
  fmap[Card_FinSet] i ≈ fmap[Card_FinSet] j.
Proof. apply DiscreteCat_nat_Thin. Qed.

(** ** Sanity: the functors and the identities compute *)

(* [parity_two] (Instance/FinSet/Skeleton.v) is [nat] under equality of
   parity: an infinite carrier of cardinality 2. *)
Example card_groupoid_parity_two :
  fobj[Card_Groupoid] parity_two = 2%nat := eq_refl.

Example card_groupoid_incl_three :
  fobj[Card_Groupoid] (FinSet_Incl 3%nat) = 3%nat := eq_refl.

Example card_finset_five : fobj[Card_FinSet] 5%nat = 5%nat := eq_refl.

Example nat_exp_coprod_2_1_1 : (2 ^ (1 + 1))%nat = (2 ^ 1 * 2 ^ 1)%nat :=
  nat_exp_coprod 2%nat 1%nat 1%nat.

Example nat_exp_prod_l_2_3_2 : (2 ^ (3 * 2))%nat = ((2 ^ 2) ^ 3)%nat :=
  nat_exp_prod_l 3%nat 2%nat 2%nat.

Example nat_prod_coprod_r_4_2_3 : (4 * (2 + 3))%nat = (4 * 2 + 4 * 3)%nat :=
  nat_prod_coprod_r 4%nat 2%nat 3%nat.

Example nat_exp_prod_r_2_3_4 : ((3 * 4) ^ 2)%nat = (3 ^ 2 * 4 ^ 2)%nat :=
  nat_exp_prod_r 2%nat 3%nat 4%nat.
