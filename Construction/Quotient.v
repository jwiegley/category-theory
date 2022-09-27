Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Coq.Relations.Relation_Definitions.
Require Import Category.Theory.Functor.

Section Quotient.
  Universes o h p.
  Context (C : Category@{o h p}).
  Context (R : ∀ x y : C, crelation (hom x y)).

  Inductive R' : forall x y : C, crelation (hom x y) :=
  | extendsR x y : forall f g : hom x y, f ≈ g -> R' _ _ f g
  | trans x y : forall f g h: hom x y, R' _ _ f g -> R' _ _ g h -> R' _ _ f h
  | sym x y : forall f g : hom x y, R' _ _ f g -> R' _ _ g f
  | refl x y : forall f : hom x y, R' _ _ f f
  | leftcomp x y z : forall f : hom y z, forall g h : hom x y,
      R' _ _ g h -> R' _ _ (f ∘ g) (f ∘ h)
  | rightcomp x y z : forall f : hom x y, forall g h : hom y z,
      R' _ _ g h -> R' _ _ (g ∘ f) (h ∘ f).
  Arguments R' {x y}.
  Arguments trans {x y}.
  Arguments sym {x y}.
  Arguments refl {x y}.
  Arguments leftcomp {x y z}.
  Arguments rightcomp {x y z}.
  
  Program Definition Equiv_R' x y : Setoid (hom x y) :=
    {| Setoid.equiv := R';
      Setoid.setoid_equiv := {| Equivalence_Reflexive := fun f => refl f;
                                Equivalence_Transitive := fun f g h => trans f g h;
                                Equivalence_Symmetric := fun f g => sym f g
                             |}
    |}.

  Program Definition Quotient : Category := {|
    obj := @obj C;
    hom := @hom C;
    id := @id C;                                         
    homset := fun x y => Equiv_R' x y;
    compose := @compose C
  |}.
  
  Next Obligation.
    intros g1 g2 ? f1 f2 ?;
    assert (t : (R' (g1 ∘ f1) (g1 ∘ f2))) by (now apply leftcomp);
      now (apply (trans _ _ _ t), rightcomp).  Qed.
  Next Obligation. apply (trans _ f); [ now apply extendsR, id_left | now apply refl]. Qed.
  Next Obligation. apply (trans _ f); [ now apply extendsR, id_right | now apply refl]. Qed.
  Next Obligation. apply extendsR, comp_assoc. Qed.
  Next Obligation. apply extendsR, comp_assoc_sym. Qed.  
End Quotient.

Program Definition InducedFunctor
  (C D: Category) (R : ∀ x y : C, relation (hom x y)) (F : @Functor C D)
  (p : ∀ (c c' : C) (f g : hom c c'), R c c' f g -> fmap f ≈ fmap g) :
  @Functor (Quotient C) D :=  {| fobj := @fobj _ _ F; fmap := @fmap _ _ F |}.
Next Obligation.
  intros f g Rfg; induction Rfg as
    [ ? ? ? ? f_equiv_g 
    | ? ? ? ? ? ? Ff_equiv_Fg ? Fg_equiv_Fh | | | | ].
  { exact (fmap_respects _ _ _ _ f_equiv_g). }
  { exact (Equivalence_Transitive _ _ _  Ff_equiv_Fg Fg_equiv_Fh). }
  { now apply Equivalence_Symmetric. }
  { now apply Equivalence_Reflexive. }
  { 
    apply (Equivalence_Transitive _ ((fmap f) ∘ (fmap g)));
      [ exact (fmap_comp _ _) | ].
    apply (Equivalence_Transitive _ ((fmap f) ∘ (fmap h)));
      [ | apply Equivalence_Symmetric ; now apply (fmap_comp _ _)  ].
    apply compose_respects; cat. }
  { apply (Equivalence_Transitive _ ((fmap g) ∘ (fmap f)));
      [ exact (fmap_comp _ _) | ].
    apply (Equivalence_Transitive _ ((fmap h) ∘ (fmap f)));
      [ | apply Equivalence_Symmetric ; now apply (fmap_comp _ _)  ].
    apply compose_respects; cat. }
  Qed.
Next Obligation. apply fmap_comp. Qed.
