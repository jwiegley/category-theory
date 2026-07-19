Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Multifunctors *)

(* nLab: https://ncatlab.org/nlab/show/multicategory
   Wikipedia: https://en.wikipedia.org/wiki/Multicategory

   A multifunctor [F : M ⟶ N] between multicategories sends objects to
   objects and a multimorphism [f : mhom Γ c] to
   [mf_map f : mhom (map mf_obj Γ) (mf_obj c)], preserving identities,
   single-slot composition, and the symmetric-group action.

   BOUNDARY CASTS.  As in Theory/Multicategory.v, the preservation laws
   relate multimorphisms whose source lists are PROPOSITIONALLY but not
   definitionally equal: [map φ (Γ1 ++ b :: Γ2)] versus
   [map φ Γ1 ++ φ b :: map φ Γ2], and [map φ Γ1 ++ map φ Δ ++ map φ Γ2]
   versus [map φ (Γ1 ++ Δ ++ Γ2)].  Lists of objects are Type-level
   object data, so [=] on them is sanctioned; the laws recast along
   [mcast] and are quantified over ANY proofs of their boundary
   equations (the [_any] style of Theory/Multicategory.v), with the
   transparent [mf_eq_*] kit below providing canonical witnesses.

   TRANSPARENT LIST KIT.  The stdlib proofs [map_id]/[map_app]/[map_map]
   are opaque; the instance proofs below (identity and composite
   multifunctors) need the boundary equations to COMPUTE on list
   constructors, so transparent Fixpoint versions [map_id_t]/[map_app_t]
   /[map_map_t]/[map_ext_t] are defined here.

   PERMUTATION ACTION.  The symmetry-preservation law is
   witness-relevant in the permutation, and the class action is indexed
   by the Type-valued [tperm] of Theory/Multicategory.v, so the image of
   a witness under the object map is the structural [perm_map], a
   Fixpoint that computes on each constructor.  Comparing the witnesses
   that arise for the identity and composite multifunctors requires
   transporting a witness along list equalities ([pcast]) and the
   commutation lemmas [pcast_skip]/[pcast_swap]/[pcast_ptrans]; the
   equalities proven between witnesses are [=] on Type-level witness
   data, never on multimorphisms. *)

(** ** The transparent list kit *)

Section ListKit.

Context {A B C : Type}.

Fixpoint map_id_t (l : list A) : map (fun x => x) l = l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons x) (map_id_t t)
  end.

Fixpoint map_app_t (f : A → B) (l l' : list A) :
  map f (l ++ l') = map f l ++ map f l' :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons (f x)) (map_app_t f t l')
  end.

Fixpoint map_map_t (f : A → B) (g : B → C) (l : list A) :
  map g (map f l) = map (fun x => g (f x)) l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons (g (f x))) (map_map_t f g t)
  end.

Fixpoint map_ext_t (f g : A → B) (H : ∀ a, f a = g a) (l : list A) :
  map f l = map g l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal2 cons (H x) (map_ext_t f g H t)
  end.

End ListKit.

(** ** The multifunctor boundary-equation kit *)

Section BoundaryKit.

Context {A B : Type}.
Context (φ : A → B).

(** The image of a slot zipper is a slot zipper: [map φ (b :: Γ2)]
    computes, so this is [map_app_t] up to conversion. *)
Definition mf_eq_slot (Γ1 Γ2 : list A) (b : A) :
  map φ (Γ1 ++ b :: Γ2) = map φ Γ1 ++ φ b :: map φ Γ2 :=
  map_app_t φ Γ1 (b :: Γ2).

(** The image of a spliced context, reassembled blockwise. *)
Definition mf_eq_splice (Γ1 Δ Γ2 : list A) :
  map φ Γ1 ++ map φ Δ ++ map φ Γ2 = map φ (Γ1 ++ Δ ++ Γ2) :=
  eq_sym (eq_trans (map_app_t φ Γ1 (Δ ++ Γ2))
                   (f_equal (app (map φ Γ1)) (map_app_t φ Δ Γ2))).

End BoundaryKit.

(** ** The transparent permutation image and its transport calculus *)

(** The structural image of a permutation witness under a function.
    Being a Fixpoint, it computes on each constructor, which the
    identity/composite multifunctor proofs below rely on. *)
Fixpoint perm_map {A B : Type} (φ : A → B) {Γ Δ : list A}
  (p : tperm Γ Δ) : tperm (map φ Γ) (map φ Δ) :=
  match p in tperm Γ0 Δ0
        return tperm (map φ Γ0) (map φ Δ0) with
  | tperm_nil => tperm_nil
  | tperm_skip x q => tperm_skip (φ x) (perm_map φ q)
  | tperm_swap x y l => tperm_swap (φ x) (φ y) (map φ l)
  | tperm_trans q r => tperm_trans (perm_map φ q) (perm_map φ r)
  end.

(** Transport of a permutation witness along equalities of its endpoint
    lists (Type-level object data). *)
Definition pcast {A : Type} {Γ Γ' Δ Δ' : list A}
  (e1 : Γ = Γ') (e2 : Δ = Δ') (p : tperm Γ Δ) :
  tperm Γ' Δ' :=
  match e2 with
  | eq_refl => match e1 with eq_refl => p end
  end.

(** [pcast] commutes with [tperm_skip]. *)
Lemma pcast_skip {A : Type} {a b c d : list A} (e1 : a = b) (e2 : c = d)
  (x : A) (p : tperm a c) :
  pcast (f_equal (cons x) e1) (f_equal (cons x) e2) (tperm_skip x p)
    = tperm_skip x (pcast e1 e2 p).
Proof. destruct e1, e2; reflexivity. Qed.

(** [pcast] commutes with [tperm_swap]. *)
Lemma pcast_swap {A : Type} {a b : list A} (e : a = b) (x y : A) :
  pcast (f_equal (cons y) (f_equal (cons x) e))
        (f_equal (cons x) (f_equal (cons y) e)) (tperm_swap x y a)
    = tperm_swap x y b.
Proof. destruct e; reflexivity. Qed.

(** [pcast] commutes with [tperm_trans]. *)
Lemma pcast_ptrans {A : Type} {a a' b b' c c' : list A}
  (e1 : a = a') (e2 : b = b') (e3 : c = c')
  (p : tperm a b) (q : tperm b c) :
  pcast e1 e3 (tperm_trans p q)
    = tperm_trans (pcast e1 e2 p) (pcast e2 e3 q).
Proof. destruct e1, e2, e3; reflexivity. Qed.

(** [eq_sym] slides under [f_equal]. *)
Lemma eq_sym_f_equal {A B : Type} (h : A → B) {a b : A} (e : a = b) :
  eq_sym (f_equal h e) = f_equal h (eq_sym e).
Proof. destruct e; reflexivity. Qed.

(** The identity function's permutation image is the original witness,
    transported along [map_id_t].  Everything on both sides computes on
    list/permutation constructors, so the induction goes through with
    no identification of equality proofs.  [tperm] lives in [Type], so
    its dependent induction principle [tperm_rect] comes for free. *)
Lemma perm_map_id {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  pcast (map_id_t Γ) (map_id_t Δ) (perm_map (fun x => x) p) = p.
Proof.
  induction p as [| x l l' p IH | x y l | l l' l'' p IHp q IHq]; simpl.
  - reflexivity.
  - now rewrite pcast_skip, IH.
  - now rewrite pcast_swap.
  - now rewrite (pcast_ptrans _ (map_id_t l') _), IHp, IHq.
Qed.

(** The permutation image of a composite function is the composite of
    the images, transported along [map_map_t]. *)
Lemma perm_map_comp {A B C : Type} (f : A → B) (g : B → C)
  {Γ Δ : list A} (p : tperm Γ Δ) :
  pcast (map_map_t f g Γ) (map_map_t f g Δ) (perm_map g (perm_map f p))
    = perm_map (fun x => g (f x)) p.
Proof.
  induction p as [| x l l' p IH | x y l | l l' l'' p IHp q IHq]; simpl.
  - reflexivity.
  - now rewrite pcast_skip, IH.
  - now rewrite pcast_swap.
  - now rewrite (pcast_ptrans _ (map_map_t f g l') _), IHp, IHq.
Qed.

(** ** Transport lemmas in a multicategory

    Boundary casts commute with everything in sight.  Each lemma is
    quantified over equalities with variable endpoints, so the proof is
    a [destruct] of the equality followed by [mcast_id] — no UIP
    anywhere. *)

Section MulticategoryTransport.

Context {M : Multicategory}.

(** Recasting the TARGET object of a multimorphism along a
    propositional equality of objects (Type-level object data).  Unlike
    [mcast] this needs no groupoid-law fields: every use below carries
    its equality proof as data, so only functoriality along
    [eq_refl]/[eq_sym]/[eq_trans] is ever needed, and those hold by
    [destruct]. *)
Definition mtarget_cast {Γ : list mobj} {c c' : mobj} (e : c = c') :
  mhom Γ c → mhom Γ c' :=
  match e with eq_refl => fun f => f end.

#[export] Instance mtarget_cast_respects {Γ c c'} (e : c = c') :
  Proper (equiv ==> equiv) (@mtarget_cast Γ c c' e).
Proof. destruct e; repeat intro; assumption. Qed.

Lemma mtarget_cast_trans {Γ : list mobj} {c c' c'' : mobj}
  (e : c = c') (e' : c' = c'') (f : mhom Γ c) :
  mtarget_cast e' (mtarget_cast e f) ≈ mtarget_cast (eq_trans e e') f.
Proof. destruct e, e'; reflexivity. Qed.

Lemma mtarget_cast_symm {Γ : list mobj} {c c' : mobj}
  (e : c = c') (f : mhom Γ c) :
  mtarget_cast (eq_sym e) (mtarget_cast e f) ≈ f.
Proof. destruct e; reflexivity. Qed.

(** Source and target casts commute. *)
Lemma mcast_mtarget_cast {Γ Γ' : list mobj} {c c' : mobj}
  (e : Γ = Γ') (e' : c = c') (f : mhom Γ c) :
  mcast e (mtarget_cast e' f) ≈ mtarget_cast e' (mcast e f).
Proof. destruct e'; reflexivity. Qed.

(** Splicing commutes with blockwise recasting of the boundary: casts
    on both arguments of [mcomp] fuse into one cast on the composite.
    The zipper/splice equalities [ez]/[es] are ANY proofs; the blockwise
    equalities [e1]/[e2]/[ed] guarantee they exist. *)
Lemma mcomp_cast_zipper {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list mobj} {b c : mobj}
  (e1 : Γ1 = Γ1') (e2 : Γ2 = Γ2') (ed : Δ = Δ')
  (ez : Γ1 ++ b :: Γ2 = Γ1' ++ b :: Γ2')
  (es : Γ1 ++ Δ ++ Γ2 = Γ1' ++ Δ' ++ Γ2')
  (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
  mcomp (mcast ez f) (mcast ed g) ≈ mcast es (mcomp f g).
Proof.
  destruct e1, e2, ed.
  now rewrite !mcast_id.
Qed.

(** The symmetric-group action commutes with boundary casts: acting by
    a transported permutation on a recast multimorphism is the recast of
    the original action. *)
Lemma msym_pcast {Γ Γ' Δ Δ' : list mobj} {c : mobj}
  (e1 : Γ = Γ') (e2 : Δ = Δ') (p : tperm Γ Δ) (f : mhom Γ c) :
  msym (pcast e1 e2 p) (mcast e1 f) ≈ mcast e2 (msym p f).
Proof.
  destruct e1, e2; simpl.
  now rewrite !mcast_id.
Qed.

End MulticategoryTransport.

(** ** The class *)

Class MultiFunctor (M N : Multicategory) : Type := {
  (* The object map. *)
  mf_obj : @mobj M → @mobj N;

  (* The multimorphism map: sources go through [map mf_obj]. *)
  mf_map {Γ : list (@mobj M)} {c : @mobj M} :
    mhom Γ c → mhom (map mf_obj Γ) (mf_obj c);

  mf_map_respects {Γ c} : Proper (equiv ==> equiv) (@mf_map Γ c);

  (* Identities are preserved on the nose: [map mf_obj [a]] computes to
     [[mf_obj a]], so no cast is needed. *)
  mf_id (a : @mobj M) : mf_map (mid a) ≈ mid (mf_obj a);

  (* Splicing is preserved, up to the boundary casts putting the image
     of the zipper in zipper form ([ez]) and reassembling the image of
     the spliced context ([es]).  Quantified over ANY proofs of the two
     boundary equations (witnesses: [mf_eq_slot], [mf_eq_splice]),
     following the [_any] law style of Theory/Multicategory.v. *)
  mf_comp {Γ1 Γ2 Δ : list (@mobj M)} {b c : @mobj M}
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b)
    (ez : map mf_obj (Γ1 ++ b :: Γ2)
            = map mf_obj Γ1 ++ mf_obj b :: map mf_obj Γ2)
    (es : map mf_obj Γ1 ++ map mf_obj Δ ++ map mf_obj Γ2
            = map mf_obj (Γ1 ++ Δ ++ Γ2)) :
    mf_map (mcomp f g) ≈ mcast es (mcomp (mcast ez (mf_map f)) (mf_map g));

  (* The symmetric-group action is preserved along the transparent
     permutation image [perm_map]. *)
  mf_sym {Γ Δ : list (@mobj M)} {c : @mobj M}
    (p : tperm Γ Δ) (f : mhom Γ c) :
    mf_map (msym p f) ≈ msym (perm_map mf_obj p) (mf_map f)
}.

#[export] Existing Instance mf_map_respects.

Arguments mf_obj {M N} _ _.
Arguments mf_map {M N} _ {Γ c} _.
Arguments mf_id {M N} _ a.
Arguments mf_comp {M N} _ {Γ1 Γ2 Δ b c} f g ez es.
Arguments mf_sym {M N} _ {Γ Δ c} p f.

(** The composition law at the canonical kit witnesses. *)
Corollary mf_comp_kit {M N : Multicategory} (F : MultiFunctor M N)
  {Γ1 Γ2 Δ : list (@mobj M)} {b c : @mobj M}
  (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
  mf_map F (mcomp f g)
    ≈ mcast (mf_eq_splice (mf_obj F) Γ1 Δ Γ2)
        (mcomp (mcast (mf_eq_slot (mf_obj F) Γ1 Γ2 b) (mf_map F f))
               (mf_map F g)).
Proof. apply mf_comp. Qed.

(** A multifunctor commutes with boundary casts: the image of a recast
    multimorphism is the recast image, along the [f_equal] image of the
    boundary equality. *)
Lemma mf_map_cast {M N : Multicategory} (F : MultiFunctor M N)
  {Γ Γ' : list (@mobj M)} {c : @mobj M} (e : Γ = Γ') (f : mhom Γ c) :
  mf_map F (mcast e f) ≈ mcast (f_equal (map (mf_obj F)) e) (mf_map F f).
Proof.
  destruct e; simpl.
  now rewrite !mcast_id.
Qed.

(** ** The setoid of multifunctors

    Two parallel multifunctors are equivalent when their object maps
    agree pointwise (Type-level object data, so [=] is sanctioned) and,
    modulo the source/target recasting that this agreement induces,
    their multimorphism maps agree up to [≈].  The witness [eobj] is
    carried as DATA in a sigma — the pattern of the [Hobj]-conjugated
    uniqueness statements of Construction/ColouredPROP/Universal.v —
    so the equivalence laws never compare equality proofs, only
    compose them. *)

Definition mf_equiv {M N : Multicategory} (F G : MultiFunctor M N) : Type :=
  { eobj : ∀ a : @mobj M, mf_obj F a = mf_obj G a
  & ∀ (Γ : list (@mobj M)) (c : @mobj M) (f : mhom Γ c),
      mcast (map_ext_t _ _ eobj Γ)
        (mtarget_cast (eobj c) (mf_map F f)) ≈ mf_map G f }.

Lemma mf_equiv_refl {M N : Multicategory} (F : MultiFunctor M N) :
  mf_equiv F F.
Proof.
  exists (fun _ => eq_refl); intros; simpl.
  apply mcast_id.
Qed.

Lemma mf_equiv_sym {M N : Multicategory} (F G : MultiFunctor M N) :
  mf_equiv F G → mf_equiv G F.
Proof.
  intros [eobj eh].
  exists (fun a => eq_sym (eobj a)); intros Γ c f.
  rewrite <- (eh Γ c f).
  rewrite !mcast_mtarget_cast.
  rewrite mtarget_cast_trans.
  rewrite (eq_trans_sym_inv_r (eobj c)); simpl.
  rewrite mcast_trans.
  apply mcast_id.
Qed.

Lemma mf_equiv_trans {M N : Multicategory} (F G H : MultiFunctor M N) :
  mf_equiv F G → mf_equiv G H → mf_equiv F H.
Proof.
  intros [e1 h1] [e2 h2].
  exists (fun a => eq_trans (e1 a) (e2 a)); intros Γ c f.
  rewrite <- (h2 Γ c f).
  rewrite <- (h1 Γ c f).
  rewrite !mcast_mtarget_cast.
  rewrite mtarget_cast_trans.
  rewrite mcast_trans.
  now rewrite (mcast_proof_irrel
                 (map_ext_t _ _ (fun a => eq_trans (e1 a) (e2 a)) Γ)
                 (eq_trans (map_ext_t _ _ e1 Γ) (map_ext_t _ _ e2 Γ))).
Qed.

#[export] Program Instance MultiFunctor_Setoid {M N : Multicategory} :
  Setoid (MultiFunctor M N) := {|
  equiv := mf_equiv
|}.
Next Obligation.
  equivalence.
  - apply mf_equiv_refl.
  - now apply mf_equiv_sym.
  - now apply mf_equiv_trans with y.
Qed.

(** ** The identity multifunctor

    The object map is the identity, but [map (fun a => a) Γ] is only
    propositionally equal to [Γ], so the multimorphism map recasts along
    the transparent [map_id_t]. *)

Local Obligation Tactic := intros; cbv beta.

Program Definition MultiId (M : Multicategory) : MultiFunctor M M := {|
  mf_obj := fun a => a;
  mf_map := fun Γ c f => mcast (eq_sym (map_id_t Γ)) f
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  apply mcast_id.
Qed.
Next Obligation.
  rewrite mcast_trans.
  rewrite (mcomp_cast_zipper
             (eq_sym (map_id_t Γ1)) (eq_sym (map_id_t Γ2))
             (eq_sym (map_id_t Δ)) _
             (f_equal2 (@app _) (eq_sym (map_id_t Γ1))
                (f_equal2 (@app _) (eq_sym (map_id_t Δ))
                   (eq_sym (map_id_t Γ2))))).
  rewrite mcast_trans.
  apply mcast_proof_irrel.
Qed.
Next Obligation.
  assert (Hq : msym (pcast (map_id_t Γ) (map_id_t Δ) (perm_map (fun a => a) p))
                 (mcast (map_id_t Γ) (mcast (eq_sym (map_id_t Γ)) f))
               ≈ mcast (map_id_t Δ)
                   (msym (perm_map (fun a => a) p)
                      (mcast (eq_sym (map_id_t Γ)) f)))
    by apply msym_pcast.
  rewrite perm_map_id in Hq.
  rewrite mcast_symm_r in Hq.
  rewrite Hq.
  apply mcast_symm_l.
Qed.

(** ** Composition of multifunctors

    Objects compose on the nose; the multimorphism map recasts along the
    transparent [map_map_t] to move between [map (mf_obj G) (map
    (mf_obj F) Γ)] and [map (fun a => mf_obj G (mf_obj F a)) Γ]. *)

Program Definition MultiCompose {M N O : Multicategory}
  (G : MultiFunctor N O) (F : MultiFunctor M N) : MultiFunctor M O := {|
  mf_obj := fun a => mf_obj G (mf_obj F a);
  mf_map := fun Γ c f =>
    mcast (map_map_t (mf_obj F) (mf_obj G) Γ) (mf_map G (mf_map F f))
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  rewrite (mf_id F a).
  rewrite (mf_id G (mf_obj F a)).
  apply mcast_id.
Qed.
Next Obligation.
  (* Normalize the left-hand side: push the image of the splice through
     [G], collecting all boundary casts. *)
  rewrite (mf_comp_kit F f g).
  rewrite (mf_map_cast G).
  rewrite (mf_comp_kit G).
  rewrite (mf_map_cast G).
  rewrite !mcast_trans.
  (* Split the right-hand side's inner cast at the [G ∘ F]-image zipper
     and commute the blockwise casts out of the splice. *)
  rewrite <- (mcast_trans_any
                (eq_trans
                   (f_equal (map (mf_obj G)) (mf_eq_slot (mf_obj F) Γ1 Γ2 b))
                   (mf_eq_slot (mf_obj G)
                      (map (mf_obj F) Γ1) (map (mf_obj F) Γ2) (mf_obj F b)))
                (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Γ1)
                   (f_equal (cons (mf_obj G (mf_obj F b)))
                      (map_map_t (mf_obj F) (mf_obj G) Γ2)))).
  rewrite (mcomp_cast_zipper
             (map_map_t (mf_obj F) (mf_obj G) Γ1)
             (map_map_t (mf_obj F) (mf_obj G) Γ2)
             (map_map_t (mf_obj F) (mf_obj G) Δ) _
             (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Γ1)
                (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Δ)
                   (map_map_t (mf_obj F) (mf_obj G) Γ2)))).
  rewrite !mcast_trans.
  apply mcast_proof_irrel.
Qed.
Next Obligation.
  rewrite (mf_sym F p f).
  rewrite (mf_sym G).
  rewrite <- (perm_map_comp (mf_obj F) (mf_obj G) p).
  symmetry; apply msym_pcast.
Qed.

(** ** The evident laws, up to the multifunctor setoid *)

Lemma MultiCompose_id_left {M N : Multicategory} (F : MultiFunctor M N) :
  MultiCompose (MultiId N) F ≈ F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite !mcast_trans.
  apply mcast_id.
Qed.

Lemma MultiCompose_id_right {M N : Multicategory} (F : MultiFunctor M N) :
  MultiCompose F (MultiId M) ≈ F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite (mf_map_cast F).
  rewrite !mcast_trans.
  apply mcast_id.
Qed.

Lemma MultiCompose_assoc {M N O P : Multicategory}
  (H : MultiFunctor O P) (G : MultiFunctor N O) (F : MultiFunctor M N) :
  MultiCompose H (MultiCompose G F) ≈ MultiCompose (MultiCompose H G) F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite (mf_map_cast H).
  rewrite !mcast_trans.
  apply mcast_proof_irrel.
Qed.
