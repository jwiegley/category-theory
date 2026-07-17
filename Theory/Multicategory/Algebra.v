Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Theory.Multicategory.
Require Import Category.Theory.Multicategory.Functor.
Require Import Category.Theory.Multicategory.Endomorphism.
Require Import Category.Theory.Multicategory.Operad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.

From Coq Require Import Lists.List.
From Coq Require Import Logic.Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(** * Operad algebras *)

(* nLab: https://ncatlab.org/nlab/show/algebra+over+an+operad

   An algebra for an operad [O] on an object [X] of a cartesian category is
   exactly a multifunctor from the underlying one-object multicategory of
   [O] to the endomorphism operad [EndOperad X] of
   Theory/Multicategory/Endomorphism.v.  That IS the definition here
   ([OperadAlgebra]), so the classical universal property of the
   endomorphism operad — "an O-algebra structure on X is a map of operads
   O ⟶ End(X)" — holds definitionally ([OperadAlgebra_is_MultiFunctor]).

   THE CONVENIENCE CONSTRUCTOR.  The object map of such a multifunctor is
   forced (the colour type of [EndOperad X] is [poly_unit]), so an algebra
   is determined by its ACTION MAPS [ohom O n → (pow X n ~> X)] together
   with identity/composition/symmetry preservation restated at the arity
   accessors of Theory/Multicategory/Operad.v ([OperadAction]);
   [Build_OperadAlgebra] assembles the full multifunctor, discharging the
   boundary bookkeeping once and for all.  The target-object casts ride on
   axiom-free UIP for the operad's colour type ([operad_obj_UIP]: the
   colour type is propositionally [poly_unit], and UIP transports along
   type equality by [destruct]; the [poly_unit] end is Hedberg via
   [UIP_dec], as in the [UIP_nat] use of
   Theory/Multicategory/Endomorphism.v).

   THE CATEGORY OF ALGEBRAS.  Morphisms of algebras are carrier maps
   intertwining the actions at every arity, with the finite-power
   functoriality [pow_map]; the bundled category [OperadAlgebras] follows
   the first-projection idiom of Construction/FAlg.v.

   THE COMMUTATIVE OPERAD.  [Comm] is the terminal operad: one operation
   in every arity ([mhom Γ c := poly_unit], trivial setoid).  Its algebras
   in [Sets] are commutative monoids in both directions (a full
   categorical equivalence is not claimed; see the bundled note below):
   [Comm_algebra_to_CMon] (binary action + nullary action, with
   associativity/commutativity/unit extracted from the multifunctor laws
   at concrete contexts) and [CMon_to_Comm_algebra] (n-fold sums via the
   convenience constructor), bundled as [Comm_algebra_CMon]. *)

(** ** The transparent length kit *)

Fixpoint map_length_t {A B : Type} (f : A → B) (l : list A) :
  length (map f l) = length l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal S (map_length_t f t)
  end.

Fixpoint repeat_length_t {A : Type} (x : A) (n : nat) :
  length (repeat x n) = n :=
  match n with
  | O => eq_refl
  | S k => f_equal S (repeat_length_t x k)
  end.

Definition len_map_repeat {A B : Type} (φ : A → B) (x : A) (n : nat) :
  length (map φ (repeat x n)) = n :=
  eq_trans (map_length_t φ (repeat x n)) (repeat_length_t x n).

(* The length of a permutation witness's two boundary lists agree; a
   transparent Fixpoint so that concrete witnesses compute. *)
Fixpoint tperm_length {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  length Γ = length Δ :=
  match p with
  | tperm_nil => eq_refl
  | tperm_skip x q => f_equal S (tperm_length q)
  | tperm_swap x y l => eq_refl
  | tperm_trans q r => eq_trans (tperm_length q) (tperm_length r)
  end.

(** ** UIP for the colour type of an operad

    The colour type is propositionally [poly_unit] ([operad_one]), and UIP
    transports backwards along a type equality by [destruct]; on
    [poly_unit] itself, equality is decidable, so Hedberg ([UIP_dec],
    axiom-free) applies. *)

Lemma operad_obj_UIP (O : Operad) (x y : @mobj (operad_multi O))
  (e1 e2 : x = y) : e1 = e2.
Proof.
  destruct O as [M e]; simpl in *.
  unfold IsOperad in e.
  revert x y e1 e2.
  rewrite e.
  intros.
  apply UIP_dec.
  intros a b.
  destruct a, b.
  now left.
Qed.

(** ** Operad algebras as multifunctors *)

Definition OperadAlgebra (O : Operad) {C : Category}
  `{@Cartesian C} `{@Terminal C} (X : C) : Type :=
  MultiFunctor (operad_multi O) (EndOperad X).

(* The universal property of the endomorphism operad, definitionally: an
   O-algebra structure on X IS a map of multicategories into End(X). *)
Definition OperadAlgebra_is_MultiFunctor (O : Operad) {C : Category}
  `{@Cartesian C} `{@Terminal C} (X : C) :
  OperadAlgebra O X = MultiFunctor (operad_multi O) (EndOperad X) :=
  eq_refl.

(** ** The convenience constructor *)

Section Build.

Context (O : Operad).
Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (X : C).

Local Notation MO := (operad_multi O).
Local Notation pt := (operad_pt O).

(* The forced object map: the colour type of [EndOperad X] is
   [poly_unit]. *)
Definition oalg_obj : @mobj MO → poly_unit := λ _, ttt.

(* The canonical boundary witness: every context is a repeat of the point,
   at the arity that the image context reports. *)
Definition oalg_ctx (Γ : list (@mobj MO)) :
  Γ = repeat pt (length (map oalg_obj Γ)) :=
  eq_trans (all_repeat O Γ)
           (f_equal (repeat pt) (eq_sym (map_length_t oalg_obj Γ))).

(* An operad action: the action maps at every arity, respecting [≈], with
   the three preservation laws restated at the accessor level of
   Theory/Multicategory/Operad.v.  The symmetry law conjugates the
   permutation action of the endomorphism operad by the reindexing casts
   normalising [length (map oalg_obj (repeat pt n))] to [n]. *)
Record OperadAction : Type := {
  oact (n : nat) : ohom O n → (pow X n ~> X);

  oact_respects (n : nat) : Proper (equiv ==> equiv) (oact n);

  oact_id : oact 1 (oid O) ≈ exl;

  oact_comp (i j n : nat) (f : ohom O (i + S j)) (g : ohom O n) :
    oact (i + (n + j))%nat (ocomp O f g)
      ≈ oact (i + S j)%nat f ∘ graft X i n j (oact n g);

  oact_sym (n : nat) (p : tperm (repeat pt n) (repeat pt n))
    (f : ohom O n) :
    oact n (osym O p f)
      ≈ oact n f
          ∘ pow_cast X (len_map_repeat oalg_obj pt n)
          ∘ perm_act X (perm_map oalg_obj p)
          ∘ pow_cast X (eq_sym (len_map_repeat oalg_obj pt n))
}.

#[local] Instance oact_proper (a : OperadAction) (n : nat) :
  Proper (equiv ==> equiv) (oact a n) := oact_respects a n.

(* Target-object casts collapse on loops, by UIP for the colour type. *)
Lemma mtarget_loop {Γ : list (@mobj MO)} (e : pt = pt)
  (f : @mhom MO Γ pt) :
  mtarget_cast e f ≈ f.
Proof.
  rewrite (operad_obj_UIP O _ _ e eq_refl).
  reflexivity.
Qed.

(* Moving an action across a reindexing of its arity. *)
Lemma oact_cast (a : OperadAction) {m n : nat} (e : m = n)
  (h : ohom O m) :
  oact a n (mcast (f_equal (repeat pt) e) h)
    ≈ oact a m h ∘ pow_cast X (eq_sym e).
Proof.
  destruct e; simpl.
  rewrite (mcast_id eq_refl h).
  now rewrite id_right.
Qed.

(* The reindexing move along ANY boundary proof between repeat contexts. *)
Lemma oact_cast_any (a : OperadAction) {m n : nat} (e : n = m)
  (E : repeat pt m = repeat pt n) (h : ohom O m) :
  oact a n (mcast E h) ≈ oact a m h ∘ pow_cast X e.
Proof.
  rewrite (mcast_proof_irrel E (f_equal (repeat pt) (eq_sym e)) h).
  rewrite oact_cast.
  now rewrite (pow_cast_irrel X (eq_sym (eq_sym e)) e).
Qed.

(* Conjugating a graft by reindexing casts on all three block sizes. *)
Lemma graft_cast {m m' d d' k k' : nat}
  (em : m = m') (ed : d = d') (ek : k = k')
  (E1 : (m + (d + k))%nat = (m' + (d' + k'))%nat)
  (E2 : (m' + S k')%nat = (m + S k)%nat)
  (v : pow X d' ~> X) :
  graft X m d k (v ∘ pow_cast X ed)
    ≈ pow_cast X E2 ∘ graft X m' d' k' v ∘ pow_cast X E1.
Proof.
  destruct em, ed, ek.
  rewrite (pow_cast_refl X E1), (pow_cast_refl X E2).
  rewrite id_right, id_left.
  apply graft_respects.
  rewrite (pow_cast_refl X eq_refl).
  now rewrite id_right.
Qed.

Local Obligation Tactic := idtac.

(* Assembling the full multifunctor from the action maps: the object map
   is forced, the multimorphism map recasts every context to its repeat
   form and every target to the point, and the three multifunctor laws
   are discharged from the accessor-level laws by the cast calculus. *)
Program Definition Build_OperadAlgebra (α : OperadAction) :
  OperadAlgebra O X := {|
  mf_obj := oalg_obj;
  mf_map := λ Γ c f,
    oact α (length (map oalg_obj Γ))
      (mtarget_cast (operad_obj_contr O c) (mcast (oalg_ctx Γ) f))
|}.
Next Obligation.
  intros α Γ c.
  proper.
  now rewrite X0.
Qed.
Next Obligation.
  intros α a.
  pose proof (operad_obj_contr O a) as Ha; subst a.
  rewrite mtarget_loop.
  rewrite (mcast_id (oalg_ctx [pt]) (mid pt)).
  apply oact_id.
Qed.
Next Obligation.
  intros α Γ1 Γ2 Δ b c f g ez es.
  (* Collapse the slot/target objects and the contexts to repeat form. *)
  pose proof (operad_obj_contr O b) as Hb; subst b.
  pose proof (operad_obj_contr O c) as Hc; subst c.
  pose proof (all_repeat O Γ1) as H1;
  set (n1 := length Γ1) in H1; clearbody n1.
  pose proof (all_repeat O Γ2) as H2;
  set (n2 := length Γ2) in H2; clearbody n2.
  pose proof (all_repeat O Δ) as HD;
  set (nd := length Δ) in HD; clearbody nd.
  subst Γ1 Γ2 Δ.
  rewrite !mtarget_loop.
  (* The unzipped operation and its round trip. *)
  set (F := mcast (eq_sym (orep_zip O n1 n2)) f).
  assert (Hf : mcast (orep_zip O n1 n2) F ≈ f) by apply mcast_symm_r.
  clearbody F.
  (* The left side through the operadic composition. *)
  assert (HL : mcomp f g
                 ≈ mcast (eq_sym (orep_splice O n1 nd n2)) (ocomp O F g)).
  { unfold ocomp.
    rewrite Hf.
    now rewrite mcast_symm_l. }
  rewrite HL.
  rewrite <- Hf.
  rewrite !mcast_trans.
  (* Canonical nat-level boundary equations. *)
  assert (HS : length (map oalg_obj
                 (repeat pt n1 ++ repeat pt nd ++ repeat pt n2))
                 = (n1 + (nd + n2))%nat)
    by (rewrite map_length_t, !len_app; now rewrite !repeat_length_t).
  assert (HF : length (map oalg_obj (repeat pt n1 ++ pt :: repeat pt n2))
                 = (n1 + S n2)%nat)
    by (rewrite map_length_t, len_app; simpl;
        now rewrite !repeat_length_t).
  assert (HDl : length (map oalg_obj (repeat pt nd)) = nd)
    by apply len_map_repeat.
  assert (Hm : length (map oalg_obj (repeat pt n1)) = n1)
    by apply len_map_repeat.
  assert (Hk : length (map oalg_obj (repeat pt n2)) = n2)
    by apply len_map_repeat.
  (* Reindex all three actions to their canonical arities. *)
  rewrite (oact_cast_any α HS).
  rewrite (oact_cast_any α HF).
  rewrite (oact_cast_any α HDl).
  rewrite oact_comp.
  (* Unfold the endomorphism side and settle the cast algebra. *)
  cbn [mcast mcomp EndOperad].
  unfold End_mcast, End_mcomp.
  rewrite (graft_cast Hm HDl Hk
             (f_equal2 Nat.add Hm (f_equal2 Nat.add HDl Hk))
             (eq_sym (f_equal2 Nat.add Hm (f_equal S Hk)))
             (oact α nd g)).
  rewrite <- !comp_assoc.
  rewrite !pow_cast_fuse'.
  rewrite !pow_cast_fuse.
  rewrite pow_cast_refl, id_left.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  apply pow_cast_irrel.
Qed.
Next Obligation.
  intros α Γ Δ c p f.
  pose proof (operad_obj_contr O c) as Hc; subst c.
  pose proof (all_repeat O Γ) as HG;
  set (n := length Γ) in HG; clearbody n.
  pose proof (all_repeat O Δ) as HDl;
  set (n' := length Δ) in HDl; clearbody n'.
  subst Γ Δ.
  pose proof (tperm_length p) as Hnn.
  rewrite !repeat_length_t in Hnn.
  subst n'.
  rewrite !mtarget_loop.
  rewrite !(oact_cast_any α (len_map_repeat oalg_obj pt n)).
  rewrite (oact_sym α n p f).
  cbn [msym EndOperad].
  unfold End_msym.
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse.
  rewrite pow_cast_refl, id_right.
  reflexivity.
Qed.

End Build.

(** ** The category of O-algebras

    Following the [FAlgHom] idiom of Construction/FAlg.v: a morphism of
    algebras is a carrier map intertwining the actions at every arity,
    through the functorial action [pow_map] on finite powers. *)

Section Algebras.

Context (O : Operad).
Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* The arity-n action of an algebra, at the canonical power. *)
Definition alg_act {X : C} (A : OperadAlgebra O X) (n : nat)
  (o : ohom O n) : pow X n ~> X :=
  mf_map A o
    ∘ pow_cast X (eq_sym (len_map_repeat (mf_obj A) (operad_pt O) n)).

(* Sanity: the convenience constructor does not scramble the action — at
   every arity the assembled multifunctor's action IS the input action,
   the boundary casts fusing away. *)
#[local] Instance alg_oact_proper {X : C} (α : OperadAction O X) (n : nat) :
  Proper (equiv ==> equiv) (oact O X α n) := oact_respects O X α n.

Lemma alg_act_Build {X : C} (α : OperadAction O X) (n : nat)
  (o : ohom O n) :
  alg_act (Build_OperadAlgebra O X α) n o ≈ oact O X α n o.
Proof.
  unfold alg_act; simpl.
  rewrite mtarget_loop.
  rewrite (oact_cast_any O X α
             (len_map_repeat (oalg_obj O) (operad_pt O) n)
             (oalg_ctx O (repeat (operad_pt O) n)) o).
  rewrite <- comp_assoc.
  rewrite pow_cast_fuse.
  rewrite pow_cast_refl.
  now rewrite id_right.
Qed.

(* The action of a carrier map on finite powers. *)
Fixpoint pow_map {x y : C} (h : x ~> y) (n : nat) :
  pow x n ~> pow y n :=
  match n as m return ((pow x m ~> pow y m) : Type) with
  (* the section variable [O] shadows the [nat] constructor in patterns *)
  | 0%nat => @id C (pow x 0)
  | S k => Cartesian.split h (pow_map h k)  (* [List.split] shadows *)
  end.

Lemma pow_map_id {x : C} (n : nat) : pow_map (id[x]) n ≈ id.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn.
    apply split_id.
Qed.

Lemma pow_map_comp {x y z : C} (h2 : y ~> z) (h1 : x ~> y) (n : nat) :
  pow_map (h2 ∘ h1) n ≈ pow_map h2 n ∘ pow_map h1 n.
Proof.
  induction n; simpl.
  - now rewrite id_left.
  - rewrite IHn.
    symmetry; apply split_comp.
Qed.

(* An algebra morphism: a carrier map intertwining the actions. *)
Class OperadAlgebraHom {X Y : C}
  (A : OperadAlgebra O X) (B : OperadAlgebra O Y) := {
  oalg_hom : X ~> Y;
  oalg_commutes (n : nat) (o : ohom O n) :
    oalg_hom ∘ alg_act A n o ≈ alg_act B n o ∘ pow_map oalg_hom n
}.

End Algebras.

Arguments oalg_hom {O C H H0 X Y A B} _.
Arguments oalg_commutes {O C H H0 X Y A B} _ n o.

(* The category of O-algebras in C.

       objects: pairs of a carrier and an algebra structure
        arrows: action-intertwining carrier maps
      identity: the identity carrier map
   composition: composition of carrier maps, pasting the squares *)
Program Definition OperadAlgebras (O : Operad) (C : Category)
  `{@Cartesian C} `{@Terminal C} : Category := {|
  obj     := ∃ X : C, OperadAlgebra O X;
  hom     := λ x y, OperadAlgebraHom O (`2 x) (`2 y);
  homset  := λ _ _, {| equiv := λ f g, oalg_hom f ≈ oalg_hom g |};
  id      := λ _, {| oalg_hom := id |};
  compose := λ _ _ _ f g, {| oalg_hom := oalg_hom f ∘ oalg_hom g |}
|}.
Next Obligation.
  rewrite id_left.
  rewrite pow_map_id.
  now rewrite id_right.
Qed.
Next Obligation.
  rewrite pow_map_comp.
  rewrite <- comp_assoc.
  rewrite (oalg_commutes g).
  rewrite !comp_assoc.
  now rewrite (oalg_commutes f).
Qed.

(** ** The commutative operad

    The terminal operad: exactly one operation in every arity, with the
    trivial setoid on each multimorphism carrier.  Every law holds
    trivially. *)

Program Definition Comm_Multi : Multicategory := {|
  mobj := poly_unit;
  mhom := λ _ _, poly_unit;
  mhomset := λ _ _, {| equiv := λ _ _, True |};
  mcast := λ _ _ _ _ f, f;
  mid := λ _, ttt;
  mcomp := λ _ _ _ _ _ _ _, ttt;
  msym := λ _ _ _ _ f, f
|}.

Definition Comm : Operad := {|
  operad_multi := Comm_Multi;
  operad_one := eq_refl
|}.

(** ** Comm-algebras in Sets are commutative monoids

    Forward direction.  The binary and nullary actions of a Comm-algebra
    furnish the operation and unit; associativity comes from the two ways
    of splicing the binary operation into itself ([mf_comp] at concrete
    contexts), commutativity from the symmetric action at the swap
    witness ([mf_sym]), and the unit law from [mf_comp] against the
    nullary operation combined with [mf_id].  Everything is definitional
    in [Sets], so each law is an instance of the corresponding
    multifunctor law evaluated at a point. *)

Section CommToCMon.

Context {X : Sets}.
Context (A : OperadAlgebra Comm X).

(* The distinguished actions at concrete arities. *)
Definition comm_mu : pow X 2 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt; ttt]) (c:=ttt) ttt.

Definition comm_eps : pow X 0 ~{Sets}~> X :=
  mf_map A (Γ:=[]) (c:=ttt) ttt.

Definition comm_u1 : pow X 1 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt]) (c:=ttt) ttt.

Definition comm_t3 : pow X 3 ~{Sets}~> X :=
  mf_map A (Γ:=[ttt; ttt; ttt]) (c:=ttt) ttt.

(* The unary action is the projection: [mf_id] at the point. *)
Lemma comm_u1_id (a : X) (u : poly_unit) : comm_u1 (a, u) ≈ a.
Proof. exact (mf_id A ttt (a, u)). Qed.

(* Commutativity: [mf_sym] at the swap witness. *)
Lemma comm_mu_comm (a b : X) (u : poly_unit) :
  comm_mu (a, (b, u)) ≈ comm_mu (b, (a, u)).
Proof. exact (mf_sym A (tperm_swap ttt ttt []) ttt (a, (b, u))). Qed.

(* Associativity, left splice: the slot before the passive input. *)
Lemma comm_assoc_l (a b c : X) (u : poly_unit) :
  comm_t3 (a, (b, (c, u))) ≈ comm_mu (comm_mu (a, (b, ttt)), (c, u)).
Proof.
  exact (mf_comp A (Γ1:=[]) (Γ2:=[ttt]) (Δ:=[ttt; ttt]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, (b, (c, u)))).
Qed.

(* Associativity, right splice: the slot after the passive input. *)
Lemma comm_assoc_r (a b c : X) (u : poly_unit) :
  comm_t3 (a, (b, (c, u))) ≈ comm_mu (a, (comm_mu (b, (c, ttt)), u)).
Proof.
  exact (mf_comp A (Γ1:=[ttt]) (Γ2:=[]) (Δ:=[ttt; ttt]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, (b, (c, u)))).
Qed.

(* The unit law: splicing the nullary operation into the binary one. *)
Lemma comm_unit_l (a : X) (u : poly_unit) :
  comm_u1 (a, u) ≈ comm_mu (comm_eps ttt, (a, u)).
Proof.
  exact (mf_comp A (Γ1:=[]) (Γ2:=[ttt]) (Δ:=[]) (b:=ttt) (c:=ttt)
           ttt ttt eq_refl eq_refl (a, u)).
Qed.

Local Obligation Tactic := idtac.

Program Definition Comm_algebra_to_CMon : CMonObject := {|
  cmon_setoid := X;
  cmon_zero := comm_eps ttt;
  cmon_plus := λ a b, comm_mu (a, (b, ttt))
|}.
Next Obligation.
  intros a a' Ha b b' Hb.
  exact (proper_morphism comm_mu (a, (b, ttt)) (a', (b', ttt))
           (Ha, (Hb, eq_refl))).
Qed.
Next Obligation.
  intros a b c; simpl.
  rewrite <- (comm_assoc_l a b c ttt).
  apply (comm_assoc_r a b c ttt).
Qed.
Next Obligation.
  intros a b; simpl.
  apply (comm_mu_comm a b ttt).
Qed.
Next Obligation.
  intros a; simpl.
  rewrite <- (comm_unit_l a ttt).
  apply (comm_u1_id a ttt).
Qed.

End CommToCMon.

(** ** Commutative monoids are Comm-algebras

    Converse direction, through the convenience constructor: the arity-n
    action is the n-fold sum, identity/composition/symmetry preservation
    are the unit law, the fold-of-a-graft computation, and invariance of
    sums under permutation (associativity + commutativity). *)

Section CMonToComm.

Context (M : CMonObject).

(* The n-fold sum on the underlying carrier. *)
Fixpoint nfold_fn (n : nat) :
  carrier (pow (C:=Sets) (cmon_setoid M) n) → carrier (cmon_setoid M) :=
  match n with
  | 0%nat => λ _, cmon_zero M
  | S k => λ p, cmon_plus M (fst p) (nfold_fn k (snd p))
  end.

Lemma nfold_fn_proper (n : nat) : Proper (equiv ==> equiv) (nfold_fn n).
Proof.
  induction n; simpl.
  - repeat intro.
    reflexivity.
  - intros [a r] [a' r'] [Ha Hr]; simpl.
    apply cmon_plus_respects.
    + exact Ha.
    + now apply IHn.
Qed.

Definition nfold (n : nat) :
  pow (C:=Sets) (cmon_setoid M) n ~{Sets}~> cmon_setoid M := {|
  morphism := nfold_fn n;
  proper_morphism := nfold_fn_proper n
|}.

(* Folding is invariant under boundary reindexing. *)
Lemma nfold_cast {m n : nat} (e : m = n) :
  nfold n ∘ pow_cast (C:=Sets) (cmon_setoid M) e ≈ nfold m.
Proof.
  destruct e.
  intro x; simpl.
  reflexivity.
Qed.

(* Folding a split context sums the two blocks. *)
Lemma nfold_split (d k : nat)
  (x : carrier (pow (C:=Sets) (cmon_setoid M) (d + k))) :
  nfold (d + k) x
    ≈ cmon_plus M
        (nfold d (fst (pow_split (C:=Sets) (cmon_setoid M) d k x)))
        (nfold k (snd (pow_split (C:=Sets) (cmon_setoid M) d k x))).
Proof.
  generalize dependent x.
  induction d as [|d IHd]; intro x; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - destruct x as [a x']; simpl.
    rewrite (IHd x').
    symmetry; apply cmon_plus_assoc.
Qed.

(* Folding through a graft folds the spliced block first. *)
Lemma nfold_graft (m d k : nat) :
  nfold (m + (d + k))
    ≈ nfold (m + S k) ∘ graft (C:=Sets) (cmon_setoid M) m d k (nfold d).
Proof.
  induction m as [|m IHm]; intro x; simpl.
  - apply nfold_split.
  - destruct x as [a x']; simpl.
    apply cmon_plus_respects.
    + reflexivity.
    + apply (IHm x').
Qed.

(* Folds are invariant under the permutation action: associativity and
   commutativity, by induction on the witness. *)
Lemma nfold_perm {Γ Δ : list poly_unit} (q : tperm Γ Δ) :
  nfold (length Γ) ∘ perm_act (C:=Sets) (cmon_setoid M) q ≈ nfold (length Δ).
Proof.
  induction q as [| x Γ0 Δ0 q IH | x y l | Γ0 Δ0 Λ q IHq r IHr].
  - intro z; simpl.
    reflexivity.
  - intros [a v]; simpl.
    apply cmon_plus_respects.
    + reflexivity.
    + apply (IH v).
  - intros [a [b v]]; simpl.
    rewrite <- cmon_plus_assoc.
    rewrite (cmon_plus_comm M b a).
    now rewrite cmon_plus_assoc.
  - intro z; simpl.
    etransitivity.
    + apply (IHq (perm_act (C:=Sets) (cmon_setoid M) r z)).
    + apply (IHr z).
Qed.

Local Obligation Tactic := idtac.

Program Definition CMon_Comm_action :
  OperadAction (C:=Sets) Comm (cmon_setoid M) := {|
  oact := λ n _, nfold n
|}.
Next Obligation.
  intros n f g Hfg.
  reflexivity.
Qed.
Next Obligation.
  intros [a u]; simpl.
  apply cmon_plus_zero_r.
Qed.
Next Obligation.
  intros i j n f g.
  apply nfold_graft.
Qed.
Next Obligation.
  intros n p f.
  rewrite (nfold_cast (len_map_repeat (oalg_obj Comm) (operad_pt Comm) n)).
  rewrite (nfold_perm (perm_map (oalg_obj Comm) p)).
  rewrite (nfold_cast
             (eq_sym (len_map_repeat (oalg_obj Comm) (operad_pt Comm) n))).
  reflexivity.
Qed.

Definition CMon_to_Comm_algebra : OperadAlgebra (C:=Sets) Comm (cmon_setoid M) :=
  Build_OperadAlgebra (C:=Sets) Comm (cmon_setoid M) CMon_Comm_action.

End CMonToComm.

(** ** The two directions, bundled

    The named Comm/CMon connection: a Comm-algebra in [Sets] yields a
    commutative monoid on its carrier, and every commutative monoid
    carries a Comm-algebra structure.  (The checklist row asks for the
    two directions; a full categorical equivalence is not claimed
    here.) *)

Definition Comm_algebra_CMon :
  (∀ (X : Sets) (A : OperadAlgebra Comm X), CMonObject)
  * (∀ M : CMonObject, OperadAlgebra (C:=Sets) Comm (cmon_setoid M)) :=
  (λ X A, @Comm_algebra_to_CMon X A, λ M, CMon_to_Comm_algebra M).
