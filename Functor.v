Require Export Hask.Category.

Open Scope category_scope.

Set Universe Polymorphism.
Generalizable All Variables.

Class Functor (C : Category) (D : Category) :=
{ fobj : C → D
; fmap : ∀ {X Y : C}, (X ~> Y) → (fobj X ~> fobj Y)

; functor_id_law : ∀ {X : C}, fmap (id (A := X)) = id
; functor_compose_law : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Y),
    fmap f ∘ fmap g = fmap (f ∘ g)
}.

Notation "C ⟶ D" := (Functor C D) (at level 90, right associativity).

(* Functors used as functions will map objects of categories, similar to the
   way type constructors behave in Haskell. *)
Coercion fobj : Functor >-> Funclass.

Definition fun_compose
  {C : Category} {D : Category} {E : Category}
  (F : Functor D E) (G : Functor C D) : Functor C E.
  apply Build_Functor with
    (fobj := fun x => fobj (fobj x))
    (fmap := fun _ _ f => fmap (fmap f)).
  - intros.
    rewrite functor_id_law.
    apply functor_id_law.
  - intros.
    rewrite functor_compose_law.
    rewrite functor_compose_law.
    reflexivity.
Defined.

Lemma fun_irrelevance `(C : Category) `(D : Category)
  : ∀ (a : C → D)
      (f g : ∀ {X Y : C}, (X ~> Y) → (a X ~> a Y))
      i i' c c',
  @f = @g ->
  {| fobj := @a
   ; fmap := @f
   ; functor_id_law      := i
   ; functor_compose_law := c |} =
  {| fobj := @a
   ; fmap := @g
   ; functor_id_law      := i'
   ; functor_compose_law := c' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(* The Identity [Functor] *)

Definition Id `(C : Category) : Functor C C.
  apply Build_Functor with
    (fobj := fun X => X)
    (fmap := fun X X f => f); crush.
Defined.

(** [Cat] is the category whose morphisms are functors betwen categories. *)

Section Hidden.

Program Instance Cat : Category :=
{ ob      := Category
; hom     := @Functor
; id      := @Id
; compose := @fun_compose
}.
Obligation 1.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 2.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  extensionality g.
  reflexivity.
Defined.
Obligation 3.
  unfold fun_compose.
  destruct f.
  apply fun_irrelevance.
  extensionality e.
  extensionality f.
  reflexivity.
Defined.

Program Instance One : Category := {
    ob      := unit;
    hom     := fun _ _ => unit;
    id      := fun _ => tt;
    compose := fun _ _ _ _ _ => tt
}.
Obligation 1. destruct f. reflexivity. Qed.
Obligation 2. destruct f. reflexivity. Qed.

Program Instance Fini `(C : Category) : C ⟶ One := {
    fobj    := fun _ => tt;
    fmap    := fun _ _ _ => id
}.

Program Instance Zero : Category := {
    ob      := Empty_set;
    hom     := fun _ _ => Empty_set
}.
Obligation 3.
    unfold Zero_obligation_1.
    unfold Zero_obligation_2.
    destruct A.
Defined.

Program Instance Init `(C : Category) : Zero ⟶ C.
Obligation 1. destruct C. crush. Defined.
Obligation 2.
  unfold Init_obligation_1.
  destruct C. crush.
Defined.
Obligation 3.
  unfold Zero_obligation_1.
  unfold Init_obligation_1.
  unfold Init_obligation_2.
  destruct C. crush.
Defined.
Obligation 4.
  unfold Init_obligation_2.
  unfold Zero_obligation_2.
  destruct C. crush.
Qed.

Class HasInitial (C : Category) :=
{ init_obj    : C
; init_mor    : ∀ {X}, init_obj ~> X
; initial_law : ∀ {X} (f g : init_obj ~> X), f = g
}.

Program Instance Cat_HasInitial : HasInitial Cat := {
    init_obj := Zero;
    init_mor := Init
}.
Obligation 1.
  induction f as [F].
  induction g as [G].
  assert (F = G).
    extensionality e.
    crush.
  replace F with G. subst.
  assert (fmap0 = fmap1).
    extensionality e.
    extensionality f.
    extensionality g.
    crush.
  apply fun_irrelevance.
  assumption.
Qed.

Class HasTerminal (C : Category) :=
{ term_obj     : C
; term_mor     : ∀ {X}, X ~> term_obj
; terminal_law : ∀ {X} (f g : X ~> term_obj), f = g
}.

Program Instance Cat_HasTerminal : HasTerminal Cat := {
    term_obj := One;
    term_mor := Fini
}.
Obligation 1.
  destruct f as [F].
  destruct g as [G].
  assert (F = G).
    extensionality e.
    crush.
  replace F with G. subst.
  assert (fmap0 = fmap1).
    extensionality e.
    extensionality f.
    extensionality g.
    crush.
  apply fun_irrelevance.
  assumption.
Qed.

End Hidden.

Class Natural `(F : @Functor C D) `(G : @Functor C D) :=
{ transport  : ∀ {X}, F X ~> G X
; naturality : ∀ {X Y} (f : X ~> Y),
    fmap f ∘ transport = transport ∘ fmap f
}.

Notation "transport/ N" := (@transport _ _ _ _ N _) (at level 44).
Notation "F ⟾ G" := (Natural F G) (at level 90, right associativity).

(* Natural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion transport : Natural >-> Funclass.

Definition nat_identity `{F : Functor} : Natural F F.
  apply Build_Natural with (transport := fun _ => id).
  intros.
  rewrite right_identity.
  rewrite left_identity.
  reflexivity.
Defined.

Definition nat_compose
  `{F : @Functor C D} `{G : @Functor C D} `{K : @Functor C D}
  (f : Natural G K) (g : Natural F G) : Natural F K.
  apply Build_Natural
    with (transport := fun X =>
           @transport C D G K f X ∘ @transport C D F G g X).
  intros.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.

Lemma nat_irrelevance
  `(C : Category) `(D : Category) `(F : @Functor C D) `(G : @Functor C D)
  : ∀ (f g : ∀ {X}, F X ~> G X) n n',
  @f = @g ->
  {| transport := @f; naturality := n |} =
  {| transport := @g; naturality := n' |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
Qed.

(* Nat is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Instance Nat (C : Category) (D : Category) : Category :=
{ ob      := Functor C D
; hom     := @Natural C D
; id      := @nat_identity C D
; compose := fun _ _ _ => nat_compose
}.
Proof.
  - (* right_identity *)
    intros.
    destruct f.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite right_identity.
    reflexivity.
  - (* left_identity *)
    intros.
    destruct f.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite left_identity.
    reflexivity.
  - (* comp_assoc *)
    intros.
    destruct f.
    destruct g.
    destruct h.
    apply nat_irrelevance.
    extensionality a.
    unfold nat_identity, nat_compose.
    simpl. rewrite <- comp_assoc.
    reflexivity.
Defined.

Notation "[ C , D ]" := (Nat C D) (at level 90, right associativity).

Definition Copresheaves (C : Category) := [C, Sets].
Definition Presheaves   (C : Category) := [C^op, Sets].

(*
Bifunctors can be curried:

  C × D ⟶ E   -->  C ⟶ [D, E]
  ~~~
  (C, D) -> E  -->  C -> D -> E

Where ~~~ should be read as "Morally equivalent to".

Note: We do not need to define Bifunctors as a separate class, since they can
be derived from functors mapping to a category of functors.  So in the
following two definitions, [P] is effectively our bifunctor.

The trick to [bimap] is that both the [Functor] instances we need (for [fmap]
and [fmap1]), and the [Natural] instance, can be found in the category of
functors we're mapping to by applying [P].
*)

Definition fmap1 `{P : C ⟶ [D, E]} {A : C} `(f : X ~{D}~> Y) :
  P A X ~{E}~> P A Y := fmap f.

Definition bimap `{P : C ⟶ [D, E]} {X W : C} {Y Z : D} (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  P X Y ~{E}~> P W Z := let N := @fmap _ _ P _ _ f in transport/N ∘ fmap1 g.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (unop f).

Definition dimap `{P : C^op ⟶ [D, E]} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P W Y ~{E}~> P X Z := bimap (unop f) g.

Program Instance Hom `(C : Category) : C^op ⟶ [C, Sets] :=
{ fobj := fun X =>
  {| fobj := @hom C X
   ; fmap := @compose C X
   |}
; fmap := fun _ _ f => {| transport := fun X g => g ∘ unop f |}
}.
Obligation 1. intros. extensionality e. crush. Defined.
Obligation 2. intros. extensionality e. crush. Defined.
Obligation 3. extensionality e. crush. Defined.
Obligation 4.
  unfold nat_identity.
  apply nat_irrelevance.
  extensionality e.
  extensionality f.
  unfold unop.
  rewrite right_identity.
  auto.
Defined.
Obligation 5.
  unfold nat_compose, nat_identity.
  apply nat_irrelevance.
  extensionality e.
  simpl.
  unfold unop.
  extensionality h.
  crush.
Defined.

Coercion Hom : Category >-> Functor.

(** This is the Yoneda embedding. *)
(* jww (2014-08-10): It should be possible to get rid of Hom here, but the
   coercion isn't firing. *)
Program Instance Yoneda `(C : Category) : C ⟶ [C^op, Sets] := Hom (C^op).
Obligation 1. apply op_involutive. Defined.

Program Instance YonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C^op}
    : @Isomorphism Sets (C A ⟾ F) (F A).
Obligation 1.
  intros.
  destruct X.
  apply transport0.
  simpl.
  destruct C.
  crush.
Defined.
Obligation 2.
  intros.
  simpl.
  pose (@fmap C Sets F A).
  apply Build_Natural with (transport := fun Y φ => h Y φ X).
  intros.
  inversion F. simpl.
  extensionality e.
  unfold h.
  rewrite <- functor_compose_law.
  crush.
Defined.
Obligation 3.
  extensionality e.
  pose (f := fun (_ : unit) => e).
  destruct C.
  destruct F. simpl.
  rewrite functor_id_law0.
  crush.
Qed.
Obligation 4.
  extensionality e.
  destruct e.
  simpl.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct C.
  destruct F.
  simpl.
  assert (fmap0 A f g (transport0 A (id A)) =
          (fmap0 A f g ∘ transport0 A) (id A)).
    crush. rewrite H. clear H.
  rewrite naturality0.
  crush.
Qed.

Class FullyFaithful `(F : @Functor C D) :=
{ unfmap : ∀ {X Y : C}, (F X ~> F Y) → (X ~> Y)
}.

Program Instance Hom_Faithful (C : Category) : FullyFaithful C :=
{ unfmap := fun _ _ f => (transport/f) id
}.

(*
Program Instance Hom_Faithful_Co (C : Category) {A : C} : FullyFaithful (C A).
Obligation 1.
  destruct C. crush.
  clear left_identity.
  clear right_identity.
  clear comp_assoc.
  specialize (compose X A Y).
  apply compose in X0.
    assumption.
Abort.
*)

(** ** Opposite functor[edit]

Every functor [F: C ⟶ D] induces the opposite functor [F^op]: [C^op ⟶ D^op],
where [C^op] and [D^op] are the opposite categories to [C] and [D].  By
definition, [F^op] maps objects and morphisms identically to [F].

*)

Program Instance Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op := {
    fobj := @fobj C D F;
    fmap := fun X Y f => @fmap C D F Y X (op f)
}.
Obligation 1. unfold op. apply functor_id_law. Qed.
Obligation 2. unfold op. apply functor_compose_law. Qed.

(* jww (2014-08-10): Until I figure out how to make C^op^op implicitly unify
   with C, I need a way of undoing the action of Opposite_Functor. *)

Program Instance Reverse_Opposite_Functor `(F : C^op ⟶ D^op) : C ⟶ D := {
    fobj := @fobj _ _ F;
    fmap := fun X Y f => unop (@fmap _ _ F Y X f)
}.
Obligation 1.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_id_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e X). auto.
Qed.
Obligation 2.
  unfold unop.
  unfold fmap. simpl.
  pose (@functor_compose_law _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e Z Y X g f).
  auto.
Qed.

(* Definition Coerce_Functor `(F : C ⟶ D) := Opposite_Functor F. *)

(* Coercion Coerce_Functor : Functor >-> Functor. *)

Lemma op_functor_involutive `(F : Functor)
  : Reverse_Opposite_Functor (Opposite_Functor F) = F.
Proof.
  unfold Reverse_Opposite_Functor.
  unfold Opposite_Functor.
  destruct F.
  apply fun_irrelevance.
  auto.
Qed.
