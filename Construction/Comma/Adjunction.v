From Ltac2 Require Ltac2.
From Ltac2 Require Import Notations.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Definition whisker_equiv
           {C D E : Category}
           (φ  : C ⟶ D)
           (ψ  : D ⟶ C)
           (πC : C ⟶ E)
           (πD : D ⟶ E)
           (η  : Id ⟹ ψ ◯ φ)
           (μ  : Id ⟹ φ ◯ ψ)
           (κ  : πC ⟹ πD ◯ φ)
           (θ  : πD ⟹ πC ◯ ψ) :=
  to (nat_α _ _ _) ∙ πC ⊳ η ∙ from (nat_λ _) ≈ (θ ⊲ φ) ∙ κ ∧
  to (nat_α _ _ _) ∙ πD ⊳ μ ∙ from (nat_λ _) ≈ (κ ⊲ ψ) ∙ θ.

Section AdjunctionComma.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
   : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
   1x → k in B ↓ p that is universal from i to k."

   Lawvere's own statement of the theorem, from his thesis (page 40):

   "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
   is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
   and a map φ : B ~> A in B such that for every object A′ ∈ |A| and every
   map x : B ~> A′ in B, there exists a unique map y : A ~> A′ in A such that
   x = φ(yf) in B." *)

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Definition πD := comma_proj1.
Definition πC := comma_proj2.

#[local] Notation "⟨πD,πC⟩" := comma_proj (at level 100).

Record lawvere_equiv := {
  lawvere_iso : F ↓ Id[C] ≅[Cat] Id[D] ↓ G;

  φ := to lawvere_iso;
  ψ := from lawvere_iso;

  η x := from (`1 (iso_from_to lawvere_iso) x);
  μ x := from (`1 (iso_to_from lawvere_iso) x);

  projF : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ◯ φ;
  projG : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ◯ ψ;

  κ := `1 projF;
  θ := `1 projG;

  σ : @whisker_equiv
        (F ↓ Id[C]) (Id[D] ↓ G) (D ∏ C)
        (to lawvere_iso) (from lawvere_iso)
        comma_proj comma_proj
        (from (equiv_iso (iso_from_to lawvere_iso)))
        (from (equiv_iso (iso_to_from lawvere_iso)))
        (to (equiv_iso projF))
        (to (equiv_iso projG));

  lawvere_to {a b} (f : F a ~> b) : a ~> G b :=
    let o := ((a, b); f) in
    fmap[G] (snd (from (κ o))) ∘ `2 (φ o) ∘ fst (to (κ o));

  lawvere_from {a b} (g : a ~> G b) : F a ~> b :=
    let o := ((a, b); g) in
    snd (from (θ o)) ∘ `2 (ψ o) ∘ fmap[F] (fst (to (θ o)));

  φ' {a b} (f : F a ~> b) := lawvere_to f;
  ψ' {a b} (g : a ~> G b) := lawvere_from g
}.

Context `(E : lawvere_equiv).

Lemma η_θ_κ : ∀ x, `1 (η E x) ≈ θ E (φ E x) ∘ κ E x.
Proof.
  intros.
  pose proof (σ E).
  destruct X as [X _].
  specialize (X x); simpl in X.
  unfold equiv_iso, η, κ, θ, φ in *.
  destruct (iso_from_to (lawvere_iso E)), (projG E), (projF E).
  destruct X; split.
  - simpl in e2 |- *.
    refine (transitivity _ e2);
    refine (transitivity _ (symmetry (id_right _)));
    refine (transitivity _ (symmetry (id_left _)));
    reflexivity.
  - simpl in e3 |- *.
    refine (transitivity _ e3).
    refine (transitivity _ (symmetry (id_right _)));
    refine (transitivity _ (symmetry (id_left _)));
    reflexivity.
Qed.

Lemma μ_κ_θ : ∀ x, `1 (μ E x) ≈ κ E (ψ E x) ∘ θ E x.
Proof.
  intros.
  pose proof (σ E).
  destruct X as [_ X].
  specialize (X x); simpl in X.
  unfold equiv_iso, μ, κ, θ, ψ in *.
  destruct (iso_to_from (lawvere_iso E)), (projG E), (projF E).
  destruct X; split.
  - simpl in e2 |- *.
    refine (transitivity _ e2);
    refine (transitivity _ (symmetry (id_right _)));
    refine (transitivity _ (symmetry (id_left _)));
    reflexivity.
  - simpl in e3 |- *.
    refine (transitivity _ e3).
    refine (transitivity _ (symmetry (id_right _)));
    refine (transitivity _ (symmetry (id_left _)));
    reflexivity.
Qed.

(* Intended usage : To select a subterm of the goal, 
   supply a SetPattern (an ordinary "pattern" with only holes but no metavariables) or
   a SetInPattern (a pattern with one metavariable ?z, ?z will be the thing which is 
   selected.
 *)
Ltac2 Type pattern_type := [ SetPattern_ntimes ( (Init.unit -> Init.constr) * Init.int )
                           | SetPatternRepeat (Init.unit -> Init.constr)
                           | SetInPattern_ntimes (Init.pattern * Init.int)
                           | SetInPatternRepeat (Init.pattern) ].
Ltac2 only_in_goal := { Std.on_hyps := Init.Some [] ; Std.on_concl := Std.AllOccurrences }.

(* progress_in_goal is like progress, but it only succeeds 
   if there is a change on the RHS of the sequent; 
   whereas "progress" succeeds if there is a change 
   in either the goals or hypotheses. *)

Ltac2 progress_in_goal tac :=
  let old_goal := Control.goal() in
  ( tac() ;
    if Constr.equal old_goal (Control.goal()) then
      Control.zero (Init.Tactic_failure
                      (Init.Some (Message.of_string "No change in goal"))) else () ).

(* strictset accepts an identifier and a thunked term. It tries to "set identifier := term."
   If the goal is unchanged, it raises an exception. *)
Ltac2 strictset ident term :=
  progress_in_goal 
  (fun () => Std.set Init.false (fun () => (Init.Some ident, term() ))
          { Std.on_hyps := Init.Some [] ; Std.on_concl := Std.AllOccurrences }).

Ltac2 rec hide_SetPattern_ntimes thunk n :=
  if (Int.lt n 0) then Control.zero (Control.throw(
      Init.Tactic_failure (Init.Some (Message.of_string "Pattern asked to repeat < 0 times"))))
  else if (Int.equal n 0) then []
  else let h := Fresh.in_goal @tmpvar in 
       (strictset h thunk); h :: (hide_SetPattern_ntimes thunk (Int.sub n 1)).
                               
(* This function should accept as input a pattern list. 
   It should go through them one by one and "set" each item in the list. 
   It should return a list of identifiers corresponding to the terms that 
   were successfully set.
 *)
Ltac2 hide_draft1 pattern_list :=
  match pattern_list with
  | [] => []
  | hhead :: ttail =>
      match head with
      | SetPattern_ntimes tthunk nat =>
          if (n < 0) then
            
          else if (n = 0) then []
          else 
      end
  end
  

Ltac2 rec hide pattern_list tac := 
  match pattern_list with
  | [] => tac ()
  | head :: tail =>
      match head with
      | SetPattern p =>
          let h := Fresh.in_goal @tempvar in
          (Std.set
             Init.false
             (fun () => (Init.Some h, p ()))
             { Std.on_hyps := Init.Some [] ;
               Std.on_concl := Std.AllOccurrences });
           hide tail tac;
          Std.unfold ((Std.VarRef h, Std.AllOccurrences) :: []) only_in_goal;
          Std.clear (h :: [])
      | SetInPattern p =>
          let subterm_stream := (fun () => Pattern.matches_subterm p (Control.goal ())) in
          let rec traverse_thunk subtermlist :=
            match Control.case subtermlist with
            | Init.Val pair => let (subtermlist', c_p) := pair in
               let (_ , list_pairs) := subtermlist' in
                 match list_pairs with
                 | [] => Control.throw (
                             (Init.Tactic_failure (Init.Some (Message.of_string
                              "Patterns are required to have at least one metavariable."))))
                 | occ_head :: occ_tail  => let (_ , subterm) := occ_head in
                   if (Constr.is_var subterm) then
                     traverse_thunk
                         (fun () => c_p
                                    (Init.Tactic_failure (Init.Some (Message.of_string
                                     "Variable, skipping this pattern match."))))
                   else (
                   let h := Fresh.in_goal @tempvar in (
                   let try_set :=
                    (fun () => progress_in_goal
                                 (fun () => Std.set Init.false
                                              (fun () => (Init.Some h, subterm))
                                              only_in_goal)) in (
                   match Control.case try_set with
                   | Init.Val _ => hide tail tac;
                                  Std.unfold
                                  ((Std.VarRef h, Std.AllOccurrences) :: []) only_in_goal;
                                  Std.clear (h :: [])
                   | Init.Err e =>
                       traverse_thunk
                         (fun () => c_p
                                    (Init.Tactic_failure (Init.Some (Message.of_string
                                     "set failed to modify the goal."))))
                   end)))
                 end
            | Init.Err e => ()
            end in traverse_thunk subterm_stream
      end
  end.

(** hide1 accepts a pattern p which is expected to have a single metavariable, i.e.
      pat:(compose _ _ ?z).

      subterm_stream is a thunk of type context * ((ident * constr) list), where the
      constr "term" is the subterm matched by ?z.
      
      If "term" is not a variable, we "set (H := term)", where H is a fresh variable name.
      If "term" is a variable, or if "set H := term" fails to progress, we raise an
      exception to the thunk subterm_stream, which responds by returning the next subterm
      of the goal matching the p. We repeat this recursively until we either successfully
      set a variable in the goal or exhaust all subterms.
 *)

Ltac2 hide1 p :=
  let subterm_stream := fun () => Pattern.matches_subterm p (Control.goal ()) in
  let rec traverse_thunk' thunk :=
  match Control.case thunk with
  | Init.Val pair => 
      let (a , c_p ) := pair in (* c_p - exception hander in 
                                    continuation-passing style *)
      let ( ctx , id_constr_list) := a in
      match id_constr_list with
      | [] =>
          Control.zero Init.No_value (* The list shouldn't be empty, if you put in a
                                       pattern with 1 quantifier you should get a
                                       list with one element. *)
      | x :: xs =>
          let (ident, term) := x in
          (if Constr.is_var term then
             traverse_thunk' (fun () => c_p Init.Not_found)
          else
              let h := Fresh.in_goal @tempvar in
              let try_set := (fun () => progress_in_goal
                                     (fun () =>
                                        Std.set Init.false
                                          (fun () => (Init.Some h, term)) only_in_goal)) in
              match Control.case try_set with
              | Init.Val pair => let (a, _) := pair in a
              | Init.Err e => traverse_thunk' (fun () => c_p e) 
              end)
      end  
  | Init.Err e => fail
  end in traverse_thunk' subterm_stream.

Theorem ψ_φ_equiv :
  ∀ x, snd (from (κ E x))
         ∘ snd (from (θ E (φ E x)))
         ∘ `2 (ψ E (φ E x))
         ∘ fmap[F] (fst (to (θ E (φ E x))))
         ∘ fmap[F] (fst (to (κ E x)))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f |- *.
  set (j1 := from (κ E _));
    set (j2 := (from (θ E _)));
    change (snd j1 ∘ snd j2) with (snd (j1 ∘ j2));
    unfold j2, j1; clear j1 j2.
  (* time(rewrite <- ! comp_assoc). *)
  (* Tactic call ran for 0.474 secs (0.472u,0.s) (success) *)
  (*  Each pattern corresponds to a subterm of the goal which will be 
      "hidden" from the tactic. 
      Equivalent to:
      set (j1 := snd _);
      set (J2 := snd _);
      set (j3 := fmap[F] _);
      set (j4 := fmap[F] _);
      match goal with 
      | [ |- context[@compose _ ?z]] => set (j5 := z)
      end ;
      match goal with 
      | [ |- context[@compose _ ?z]] => set (j6 := z)
      end ;
      rewrite <- ! comp_assoc;
      ...
      unfold j3; clear j3;
      unfold j2; clear j2;
      unfold j1; clear j1  *)
  time(ltac2:(hide (  
      SetPattern (fun () => '(snd _)) ::
      SetPattern (fun () => '(`2 _)) ::
      SetPattern (fun () => '(fmap[F] _)) ::
      SetPattern (fun () => '(fmap[F] _)) ::
      SetInPattern pat:(@compose _ ?z) ::
      SetInPattern pat:(@compose _ ?z) ::
      SetInPattern pat:(@compose _ ?z) ::                            
                         []) (fun () => ltac1:(rewrite <- ! comp_assoc)))).

  (* Tactic call ran for 0.069 secs (0.069u,0.s) (success) *)


  (* I am trying to workshop a design pattern for doing this kind of 
     thing efficiently. This is what I have come up with so far. *)
  (* First, get the equation you are rewriting with in the context. *)
  match goal with
  | |- context[ fmap[F] ?f1' ∘ fmap[F] ?g1' ] =>
      set(f1 := f1'); set (g1 := g1');
      assert (M := fmap_comp f1 g1); symmetry in M
  end.
  (* Then, we make sure that LHS of the equation M is bound to the 
     same variable as the term we want to rewrite. This ensures that no 
     simplifications we make to the goal will prevent the rewrite from succeeding
     because it can no longer identify the terms we wanted to rewrite.

     The "context" operator in the goal helps us in the event that "set" is unable to 
     capture both the LHS of M and the term to be rewritten. 
     "set" does not perform any unification afaik, so we have to unify them
     explicitly with "change."
 *)
  match goal with 
  | [h : ?a ≈ ?b |- context[(`2 _) ∘ ?c ]] => set (j1 := a) in *; change c with j1; revert h
  end.
  (* Now we can focus on simplifying the goal. *)
  (* The idea is to think through the Proper hints and replace by a variable any
     dependency which is only a parameter to the Proper hint and serves no role in the
     resolution algorithm.  
     Here is a (not comprehensive) list of examples of type
     information which usually plays no role in the Proper typeclass resolution.
     
     1. in the rule p ≈ q => fst A B p, A and B are irrelevant to the pattern match, and
     if A and B are complicated we can replace them both by variables to improve the
     performance of the typeclass resolution.
     2. in the rules f ≈ f' -> @compose A B C f g ≈ @compose A B C f' g and
                     g ≈ g' -> @compose A B C f g ≈ @compose A B C f' g,
                A, B, C are irrelevant to the pattern match.
     3. in functor composition,  F ≈ F' -> @Compose C D E F G ≈ @Compose C D E F' G,
                the categories are parameters and can be opaqued.
     4. In general the details of the equivalences _themselves_ cannot be opaqued, i.e.,
        if one has p : equiv A S f g where S is a setoid structure on A, opaquing
        S would probably make little difference to the runtime because the resolution
        algorithm would have to unfold it anyway to see what the equivalence relation is.
        *However*, if the type A = A(p,q) is parametric in some p, q 
        and the setoid structure is also parametric in p, q, it might be possible to 
        opaque the parameters p, q. Example, in the hint  
        fmap_respects c d : forall f, g : hom c d, f ≈ g -> F f ≈ F g,
        it would be possible to opaque the arguments c and d without the typeclass
        resolution algorithm getting held up by this.
        Thus we can safely call 
        ltac2:(hide1 pat:(@homset ?A)) - opaque the category
        ltac2:(hide1 pat:(@homset _ ?A)) - opaque the domain
        ltac2:(hide1 pat:(@homset _ _ ?A)) - opaque the codomain.
     5. Another example of 4, by the definition of prod_setoid, if f ≈ f' and g ≈ g'
        then (f, f') ≈ (g, g'). 
        But the types of f,g and f' g' need not be fed to the typeclass resolution algorithm
        concretely, just the setoid structures. The type of f and g can be opaqued, i.e.,
        ltac2:(hide1 pat:(@prod_setoid ?A))
        ltac2:(hide1 pat:(@prod_setoid _ ?B))
     6. In fmap, the domain and codomain of the source morphism can be opaqued. 
     7. As a general rule if all objects are fixed, and the computation is only on
        morphisms, then we can opaque the objects. Thus
        ltac2:(hide1 pat:(@hom _ ?c)) 
        ltac2:(hide1 pat:(@hom _ _ ?d)) 
     A possible future direction might be to assemble a list of such parameters which are 
     unlikely to play a role in typeclass resolution and write an automated script that
     "opaques" all terms in the goal which seem irrelevant to the rewrite.
   *)
  time(ltac2:(hide(
      SetPattern(fun () => '(fmap[F] _)) ::
      SetPattern(fun () => '(snd _)) ::  
      SetPattern(fun () => '(snd _)) ::  
      SetPattern(fun () => '(`2 _))   ::
      SetInPattern pat:(@compose _ ?a) ::
      SetInPattern pat:(@compose _ _ ?a) ::
      SetInPattern pat:(@homset _ _ ?a) ::
                         []) (fun () => ltac1:(intro M; rewrite M; clear M)))).
  (* 0.049 secs *)
  unfold f1, g1, j1; clear f1 g1 j1.

  (* 0.15 secs *)
  set (j1 := θ E (fobj[φ E] ((a,b);f))); set (j2 := κ E ((a, b); f));
       change ((fst _ ∘ fst _)) with (fst (j1 ∘ j2));
       unfold j2, j1; clear j1 j2.

  (* Original tactic call ran for 0.846 secs (0.848u,0.s) (success) *)
  (*    rewrite <- η_θ_κ. *)

  (* Another instance of this technique / pattern. *)
  assert (M := η_θ_κ ((a, b); f)).
  match goal with
  | [ h : ?a ≈ ?b |- context[ fst ?c ] ] =>
      set (j1 := a) in *; set (j2 := b) in * ; change c with j2; revert M
  end.
  time(ltac2:(hide(
     SetInPattern pat:( _ -> ?a ∘ _ ≈ f) ::
     SetPattern (fun () => '(`2 _)) ::
     SetInPattern pat:(@hom _ ?a) ::
     SetInPattern pat:(@hom _ ?a) ::
     SetInPattern pat:(@hom _ ?a) ::
     SetInPattern pat:(@hom _ ?a) ::
     SetInPattern pat:(@hom _ ?a) ::
     SetInPattern pat:(@hom _ _ ?a) ::
     SetInPattern pat:(@hom _ _ ?a) ::
     SetInPattern pat:(@hom _ _ ?a) ::                                
     SetInPattern pat:(@hom _ _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) :: 
     SetInPattern pat:(@compose _ _ ?a) :: 
     SetInPattern pat:(@prod_setoid _ ?a) :: 
     SetInPattern pat:(@prod_setoid _ _ ?a) ::
     []) (fun () => intro M; rewrite <- M; clear M))).
  (* It is clear that this process could be more automated,
     for example by giving an option to repeating "hide" for each
     pattern application until it fails and new variables cannot be introduced. *)
  unfold j1, j2; clear j1 j2.

  (* We will repeat this for each rewrite step in the proof. *)

  time(assert (M := (`2 (η E ((a, b); f)))); simpl in M;
    match goal with
  | [h : ?a ≈ ?b |- context[(snd _) ∘ ?c ≈ f] ] =>
      set (j1 := a) in *; set (j2 := b) in *; change c with j1
  end;
  ltac2:(hide (
     SetInPattern pat:(?a ∘ _) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
                        []) (fun () => ltac1:(rewrite  M; clear M)));
  unfold j1, j2; clear).

  
 assert (M := η_θ_κ ((a, b); f));
  match goal with
  | [ h : ?a ≈ ?b |- _ ∘ (snd ?c ∘ _) ≈ f ] =>
      set (j1 := a) in *; set (j2 := b) in *; change c with j1; revert M
  end;
    ltac2:(hide(
     SetInPattern pat:( _ → ?a ∘ _ ≈ _) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
     SetInPattern pat:(@compose _ _ _ ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd _ ?b) ::
     SetInPattern pat:(@snd _ ?b) ::
     SetInPattern pat:(@hom _ ?b) ::
     SetInPattern pat:(@hom _ _ ?b) ::
     SetInPattern pat:(@prod_setoid ?a) ::
     SetInPattern pat:(@prod_setoid _ ?b) ::
     []) (fun () => ltac1:(intro M; rewrite M; clear M)));
  unfold j1, j2; clear j1 j2. 

   time(ltac2:(hide(
           SetPattern (fun () => '(snd _)) ::
           SetPattern (fun () => '(snd _)) ::
           SetPattern (fun () => '(snd _)) ::
           SetInPattern pat:(@compose _ ?a) ::
             [] ) (fun () => ltac1:(rewrite comp_assoc)))).

   change (snd ((κ E _)⁻¹ ∘ (θ E (φ E _))⁻¹) ∘ snd _) with
    (snd ( (κ E ((a, b); f))⁻¹ ∘ (θ E (fobj[φ E] ((a, b); f)))⁻¹ ∘
             (θ E (fobj[φ E] ((a, b); f)) ∘ κ E ((a, b); f)))).


   match goal with
   | [ |- context[?f1' ∘ ?f2' ∘ ?f3'] ] =>
       set (f1 := f1'); set (f2 := f2'); set (f3 := f3');
       assert (M := comp_assoc f1 f2 f3); revert M;
       set (j2 := f1 ∘ f2 ∘ f3) in *
   end;
   ltac2:(hide(
      SetInPattern pat:(@snd _ ?a) ::   
      SetInPattern pat:(@snd _ ?a) ::   
      SetInPattern pat:(@compose ?a) :: 
      SetInPattern pat:(@compose _ ?a) :: 
      SetInPattern pat:(@compose _ _ ?a) ::
      SetInPattern pat:(@compose _ _ ?a) ::
                         []) (fun () => ltac1:(intro M; rewrite <- M; clear M)));
   unfold j2, f3, f2, f1; clear.

   match goal with
   | [ |- context[_ ∘ (?f1' ∘ (?f2' ∘ ?f3'))] ] =>
       set (f1 := f1'); set (f2 := f2'); set (f3 := f3')
   end; 
   assert (M := comp_assoc f1 f2 f3);
   set (j1 := f1 ∘ (f2 ∘ f3)) in *;
   match goal with
   | [ h : ?a ≈ ?b |- snd (_ ∘ ?x) ∘ f ≈ f ] =>  change x with j1
   end;
   revert M;
     ltac2:(hide(
          SetPattern (fun () => '(from _)) ::
          SetInPattern pat:(@snd ?a) ::
          SetInPattern pat:(@snd ?a) ::
          SetInPattern pat:(@snd _ ?b) ::
          SetInPattern pat:(@snd _ ?b) ::
          SetInPattern pat:(@compose ?c) ::
          SetInPattern pat:(@compose _ ?c) ::
          SetInPattern pat:(@compose _ ?c) ::
          SetInPattern pat:(@compose _ ?c) ::
          SetInPattern pat:(@compose _ _ ?c) ::
          SetInPattern pat:(@compose _ _ ?c) ::
                             []) (fun () => ltac1:(intro M; rewrite M; clear M)));
          unfold f1, f2, f3, j1; clear.

  match goal with
  | [ |- context[from ?f1' ∘ to ?f1'] ] => set (f1 := f1')
  end.
  assert (M := iso_from_to f1).
  match goal with
  | [ h : ?a ≈ ?b |- _ ] =>  set (j1 := a) in *
  end.
  revert M.

  ltac2:(hide(
     SetInPattern pat:(snd (?a ∘ _)  ∘ _) ::
     SetInPattern pat:(snd (_ ∘ (_ ∘ ?b))) ::
     SetInPattern pat:(@compose ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd _ ?a) ::
     []) (fun () => ltac1:(intro M; rewrite M; clear M)));
    unfold j1, f1; clear j1 f1.

  match goal with
  | [ |- context[ id ∘ ?f1' ] ] =>
      assert (M := id_left f1'); set (f1 := f1') in *; set (j1 := id ∘ f1) in *
  end;
  match goal with
  | [ |- snd (_ ∘ ?a) ∘ _ ≈ _ ] => change a with j1
  end;
  revert M;
    ltac2:(hide(
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd _ ?a) ::
     SetInPattern pat:(@compose ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     SetInPattern pat:(@compose _ _ ?a) ::
     []) (fun () => ltac1:(intro M; rewrite M; clear M)));
     unfold j1, f1; clear j1 f1.

  match goal with
  | [ |- context[from ?f1' ∘ to ?f1'] ] => set (f1 := f1')
  end.
  assert (M := iso_from_to f1).
  match goal with
  | [ h : ?a ≈ ?b |- _ ] =>  set (j1 := a) in *
  end.
  revert M.
  ltac2:(hide(
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd ?a) ::
     SetInPattern pat:(@snd _ ?a) ::
     SetInPattern pat:(@snd _ ?a) ::
     SetInPattern pat:(@compose _ ?a) ::
     []) (fun () => ltac1:(intro M; rewrite M; clear M)));
     unfold j1, f1; clear j1 f1.
  simpl.
  exact (id_left f).
Qed.

Theorem φ_ψ_equiv :
  ∀ x, fmap[G] (snd (from (θ E x)))
         ∘ fmap[G] (snd (from (κ E (ψ E x))))
         ∘ `2 (φ E (ψ E x))
         ∘ fst (to (κ E (ψ E x)))
         ∘ fst (to (θ E x))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f |- *.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _ (θ E ((a, b); f))⁻¹ (κ E (ψ E _))⁻¹).
  rewrite <- !comp_assoc.
  rewrite (fst_comp _ _ _ (κ E (ψ E _)) (θ E ((a, b); f))).
  rewrite <- μ_κ_θ.
  rewrite (`2 (μ E ((a, b); f))).
  rewrite μ_κ_θ.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _
             ((θ E _)⁻¹ ∘ (κ E (ψ E _))⁻¹)
             (κ E (ψ E _) ∘ θ E ((a, b); f))).
  rewrite <- comp_assoc.
  rewrite (comp_assoc (κ E (ψ E ((a, b); f)))⁻¹ _).
  rewrite iso_from_to, id_left.
  now rewrite iso_from_to; cat.
Qed.

Program Instance to_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (φ E).
Next Obligation.
  proper.
  construct.
  - exact (fmap[φ E] (to X)).
  - exact (fmap[φ E] (from X)).
  - exact (iso_to_from (@fobj_iso _ _ (φ E) _ _ X)).
  - exact (iso_from_to (@fobj_iso _ _ (φ E) _ _ X)).
Qed.

Program Instance from_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (ψ E).
Next Obligation.
  proper.
  construct.
  - exact (fmap[ψ E] (to X)).
  - exact (fmap[ψ E] (from X)).
  - exact (iso_to_from (@fobj_iso _ _ (ψ E) _ _ X)).
  - exact (iso_from_to (@fobj_iso _ _ (ψ E) _ _ X)).
Qed.

Program Instance lawvere_to_Proper {a b} :
  Proper (equiv ==> equiv) (@φ' E a b).
Next Obligation.
  proper.
  unfold φ', lawvere_to.
  given (ff : ((a, b); x) ~{ F ↓ Id[C] }~> ((a, b); y)). {
    now refine ((id, id); _); abstract cat.
  }
  spose (`2 (projF E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  symmetry.
  rewrite <- id_right.
  rewrite H1; clear H1.
  comp_right.
  rewrite <- !comp_assoc.
  Set Printing All.
  
  rewrite (comp_assoc (fst _) _).
  spose (iso_to_from (κ E ((a, b); y))) as H0.
  destruct H0 as [H3 _].
  unfold κ in H3.
  rewrite H3; clear H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_left (snd _)).
  rewrite H2; clear H2.
  rewrite !fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap (snd (to (κ E ((a, b); x)))))).
  rewrite <- fmap_comp.
  spose (iso_to_from (κ E ((a, b); x))) as H0.
  destruct H0 as [_ H4].
  rewrite H4; clear H4.
  rewrite fmap_id, id_left.
  remember (fmap[to (lawvere_iso E)] _) as o.
  destruct o.
  symmetry.
  apply e.
Qed.

Program Instance lawvere_from_Proper {a b} :
  Proper (equiv ==> equiv) (@ψ' E a b).
Next Obligation.
  proper.
  unfold ψ', lawvere_from.
  spose (θ E) as H.
  given (ff : ((a, b); x) ~{ Id[D] ↓ G }~> ((a, b); y)). {
    now refine ((id, id); _); abstract cat.
  }
  spose (`2 (projG E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  rewrite <- id_left.
  rewrite H2; clear H2.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E ((a, b); x)))) (snd _)).
  spose (iso_to_from (θ E ((a, b); x))) as H0.
  destruct H0 as [_ H3].
  rewrite H3; clear H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_right (fst _)).
  rewrite H1; clear H1.
  rewrite comp_assoc.
  spose (iso_to_from (θ E ((a, b); y))) as H0.
  destruct H0 as [H4 _].
  rewrite comp_assoc.
  rewrite H4; clear H4.
  rewrite !fmap_comp.
  comp_right.
  rewrite fmap_id, id_right.
  remember (fmap[from (lawvere_iso E)] _) as o.
  destruct o.
  apply e.
Qed.

Ltac pair_comp :=
  match goal with
  | [ |- context[@fst _ _ ?F ∘ @fst _ _ ?G] ] =>
    rewrite (@fst_comp _ _ _ _ _ F G)
  | [ |- context[@snd _ _ ?F ∘ @snd _ _ ?G] ] =>
    rewrite (@snd_comp _ _ _ _ _ F G)
  end.

Arguments φ' l {_ _} _.
Arguments ψ' l {_ _} _.

Lemma lawvere_iso_to {a b} (f : F a ~> b) :
  φ E ((a, b); f) ≅ ((a, b); φ' E f).
Proof.
  construct.
  - exists (from (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite <- !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl fst;
       now rewrite id_right).
  - exists (to (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite !comp_assoc;
       rewrite <- !fmap_comp;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite fmap_id, id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

Lemma lawvere_iso_from {a b} (g : a ~> G b) :
  ψ E ((a, b); g) ≅ ((a, b); ψ' E g).
Proof.
  construct.
  - exists (from (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
      rewrite <- !comp_assoc;
      rewrite <- !fmap_comp;
      pair_comp;
      rewrite iso_to_from;
      simpl fst;
      now rewrite fmap_id, id_right).
  - exists (to (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
       rewrite !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

Lemma lawvere_iso_from_to {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f)) ≅ ((a, b); ψ' E (φ' E f)).
Proof.
  refine (iso_compose (lawvere_iso_from (φ' E f)) _).
  apply fobj_iso.
  now apply lawvere_iso_to.
Qed.

Definition lawvere_iso_to_from {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g)) ≅ ((a, b); φ' E (ψ' E g)).
Proof.
  refine (iso_compose (lawvere_iso_to (ψ' E g)) _).
  apply fobj_iso.
  now apply lawvere_iso_from.
Qed.

Definition lawvere_to_from_iso {a b} (g : a ~> G b) :
  ((a, b); φ' E (ψ' E g)) ≅[Id[D] ↓ G] ((a, b); g) :=
  iso_compose (`1 (iso_to_from (lawvere_iso E)) ((a, b); g))
              (iso_sym (@lawvere_iso_to_from _ _ g)).

Definition lawvere_from_to_iso {a b} (f : F a ~> b) :
  ((a, b); ψ' E (φ' E f)) ≅[F ↓ Id[C]] ((a, b); f) :=
  iso_compose (`1 (iso_from_to (lawvere_iso E)) ((a, b); f))
              (iso_sym (@lawvere_iso_from_to _ _ f)).

Lemma lawvere_to_functorial {a b} (f : F a ~{C}~> b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  φ' E (j ∘ f ∘ fmap[F] i) ≈ fmap[G] j ∘ φ' E f ∘ i.
Proof.
  (* φ'(j ∘ f ∘ Fi) = φ'(j ∘ f) ∘ i *)

  given (Fi : ((a', b'); j ∘ f ∘ fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)). {
    now refine ((i, id); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (j ∘ f ∘ fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', b'); j ∘ f ∘ fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_left in H.
  rewrite <- H.
  clear Fi H.

  (*                = G(j ∘ f) ∘ φ'(Fi) *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)). {
    now refine ((i, j ∘ f); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite H.
  clear Fi H.

  (*                = Gj ∘ Gf ∘ φ'(Fi) *)

  rewrite fmap_comp.

  (*                = Gj ∘ φ'(f) ∘ i *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b); f)). {
    now refine ((i, f); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to f)
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b); f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- comp_assoc.
  rewrite <- H.
  now cat.
Qed.

Lemma lawvere_from_functorial {a b} (g : a ~{D}~> G b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ ψ' E g ∘ fmap[F] i ≈ ψ' E (fmap[G] j ∘ g ∘ i).
Proof.
  (* ψ'(Gj ∘ g ∘ i) = j ∘ ψ'(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((a', b'); fmap[G] j ∘ g ∘ i)). {
    now refine ((id, j); _); simpl; abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j ∘ g ∘ i))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((a', b'); fmap[G] j ∘ g ∘ i) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_right in H.
  rewrite H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ F(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)). {
    now refine ((g ∘ i, j); _); simpl; abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ Fg ∘ Fi *)

  rewrite fmap_comp.

  (*                = Gj ∘ ψ'(f) ∘ i *)

  given (Gj : ((a, b); g) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)). {
    now refine ((g, j); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g)))) as H.
  spose (`2 (projG E) ((a, b); g) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  now cat.
Qed.

Lemma surjective_tripleF (p : obj[F ↓ Id[C]]) :
  ((fst `1 p, snd `1 p); `2 p) = p.
Proof.
  destruct p; simpl; simpl_eq.
  destruct x; reflexivity.
Qed.

Lemma surjective_tripleG (p : obj[Id[D] ↓ G]) :
  ((fst `1 p, snd `1 p); `2 p) = p.
Proof.
  destruct p; simpl_eq.
  destruct x; reflexivity.
Qed.

Lemma expand_φ_ψ {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g))
    ≈
  φ E
    ((fst `1 ((lawvere_iso E)⁻¹ ((a, b); g)),
      snd `1 ((lawvere_iso E)⁻¹ ((a, b); g)));
       `2 ((lawvere_iso E)⁻¹ ((a, b); g))).
Proof. now rewrite surjective_tripleF. Qed.

Lemma expand_ψ_φ {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f))
    ≈
  ψ E
    ((fst `1 (φ E ((a, b); f)),
      snd `1 (φ E ((a, b); f)));
       `2 (φ E ((a, b); f))).
Proof. now rewrite surjective_tripleG. Qed.

(** Given that:

      π₁((A,B);f) = (A,B)
        = π₁(φ((A,B);f)) = π₁(φ((A,B);f))       [projF, projG]
      φ((A,B);f) ≅ ((A,B);φ'(f))                [lawvere_iso_to]
      ψ((A,B);f) ≅ ((A,B);ψ'(f))                [lawvere_iso_from]
      φ(ψ(f)) ≈ f and ψ(φ(f)) ≈ f               [lawvere_iso]

    it follows that:

      φ'(ψ'(f)) ≈ f and ψ'(φ'(f)) ≈ f *)

Lemma lawvere_to_from {a b} (g : a ~> G b) : φ' E (ψ' E g) ≈ g.
Proof.
  intros.
  unfold φ', ψ'.
  pose proof (@lawvere_to_functorial
                _ _ (`2 (fobj[(lawvere_iso E)⁻¹] ((a, b); g)))
                a b
                (fst (to (`1 (projG E) ((a, b); g))))
                (snd (`1 (projG E) ((a, b); g))⁻¹)) as X.
  etransitivity.
  - now apply X.
  - clear X.
    symmetry.
    etransitivity.
    + spose (φ_ψ_equiv ((a, b); g)) as X1.
      symmetry in X1.
      now apply X1.
    + apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      spose (surjective_tripleF (ψ E ((a, b); g))) as X2.
      unfold ψ in *.
      simpl.
      rewrite <- X2.
      solve [ reflexivity           (* works in >=8.12 *)
            | simpl;                (* needed for <8.11 *)
              unfold lawvere_to, θ, κ, ψ;
              rewrite !comp_assoc;
              reflexivity
            ].
Qed.

Lemma lawvere_from_to {a b} (f : F a ~> b) : ψ' E (φ' E f) ≈ f.
Proof.
  intros.
  unfold φ', ψ'.
  pose proof (@lawvere_from_functorial
                _ _ (`2 (fobj[to (lawvere_iso E)] ((a, b); f)))
                a b
                (fst (to (`1 (projF E) ((a, b); f))))
                (snd (`1 (projF E) ((a, b); f))⁻¹)) as X.
  etransitivity.
  - symmetry.
    now apply X.
  - clear X.
    symmetry.
    etransitivity.
    + spose (ψ_φ_equiv ((a, b); f)) as X1.
      symmetry in X1.
      now apply X1.
    + unfold θ, κ, ψ.
      apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      spose (surjective_tripleG (φ E ((a, b); f))) as X2.
      unfold φ in *.
      simpl.
      rewrite <- X2.
      solve [ reflexivity           (* works in >=8.12 *)
            | simpl;                (* needed for <8.11 *)
              unfold lawvere_to, θ, κ, ψ;
              rewrite !comp_assoc;
              reflexivity
            ].
Qed.

Program Instance lawvere_morph_iso {a b} : F a ~> b ≊ a ~> G b := {
  to   := {| morphism := φ' E; proper_morphism := lawvere_to_Proper |};
  from := {| morphism := ψ' E; proper_morphism := lawvere_from_Proper |};
  iso_to_from := lawvere_to_from;
  iso_from_to := lawvere_from_to
}.

Corollary lawvere_to_morph_iso_functorial {a b} (f : F a ~{C}~> b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  to lawvere_morph_iso (j ∘ f ∘ fmap[F] i)
    ≈ fmap[G] j ∘ to lawvere_morph_iso f ∘ i.
Proof. now apply lawvere_to_functorial. Qed.

Corollary lawvere_from_morph_iso_functorial {a b} (g : a ~{D}~> G b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ from lawvere_morph_iso g ∘ fmap[F] i
    ≈ from lawvere_morph_iso (fmap[G] j ∘ g ∘ i).
Proof. now apply lawvere_from_functorial. Qed.

Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun x : D => ((x, F x); id[F x]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ reflexivity | apply fmap_comp ]. Qed.

Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun x : C => ((G x, x); id[G x]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ apply fmap_comp | reflexivity ]. Qed.

Definition lawvere_eqv_unit {a} : a ~{ D }~> G (F a) :=
  to lawvere_morph_iso (`2 (Left_Functor a)).

Definition lawvere_eqv_counit {a} : F (G a) ~{ C }~> a :=
  from lawvere_morph_iso (`2 (Right_Functor a)).

Lemma lawvere_eqv_counit_fmap_unit {a} :
  lawvere_eqv_counit ∘ fmap[F] lawvere_eqv_unit ≈ id[F a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- id_left.
  rewrite comp_assoc.
  rewrite lawvere_from_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_left.
  now sapply (iso_from_to (@lawvere_morph_iso a (F a))).
Qed.

Lemma lawvere_eqv_fmap_counit_unit {a} :
  fmap[G] lawvere_eqv_counit ∘ lawvere_eqv_unit ≈ id[G a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- (id_right (to lawvere_morph_iso _)).
  rewrite comp_assoc.
  rewrite <- lawvere_to_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_right.
  now sapply (iso_to_from (@lawvere_morph_iso (G a) a)).
Qed.

Lemma Left_Functoriality
      x y (f : comma_proj (Left_Functor x) ~> comma_proj (Left_Functor y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (κ E (Left_Functor x))⁻¹)
         ∘ `2 (φ E (Left_Functor x))
         ∘ fst (to (κ E (Left_Functor x))))
    ≈ fmap[G] (snd (κ E (Left_Functor y))⁻¹)
        ∘ `2 (φ E (Left_Functor y))
        ∘ fst (to (κ E (Left_Functor y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff : (Left_Functor x) ~{ F ↓ Id[C] }~> (Left_Functor y)). {
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  }
  destruct (`2 (projF E) (Left_Functor x) (Left_Functor y) ff).
  srewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (κ E (Left_Functor x)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (κ E (Left_Functor x)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  spose (`2 (fmap[φ E] ff)) as X.
  rewrite !comp_assoc.
  rewrite <- X.
  comp_left.
  srewrite e.
  comp_right.
  rewrite (fst (iso_to_from (κ E (Left_Functor y)))).
  rewrite id_left.
  reflexivity.
Qed.

Lemma Right_Functoriality
      x y (f : comma_proj (Right_Functor x) ~> comma_proj (Right_Functor y)) :
  snd f ∘ (snd (θ E (Right_Functor x))⁻¹
        ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor x))
        ∘ fmap[F] (fst (to (θ E (Right_Functor x)))))
  ≈ snd (θ E (Right_Functor y))⁻¹
      ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor y))
      ∘ fmap[F] (fst (to (θ E (Right_Functor y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff : (Right_Functor x) ~{ Id[D] ↓ G }~> (Right_Functor y)). {
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  }
  destruct (`2 (projG E) (Right_Functor x) (Right_Functor y) ff).
  symmetry.
  srewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (θ E (Right_Functor y)))).
  rewrite id_left.
  symmetry.
  srewrite e0.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E (Right_Functor x))))).
  rewrite (snd (iso_to_from (θ E (Right_Functor x)))).
  rewrite id_left.
  rewrite fmap_comp.
  comp_right.
  symmetry.
  apply (`2 (fmap[ψ E] ff)).
Qed.

Program Definition lawvere_eqv_unit_transform : Id ⟹ G ◯ F := {|
  transform := @lawvere_eqv_unit;
  naturality := fun x y f =>
    Left_Functoriality x y (f, fmap[F] f);
  naturality_sym := fun x y f =>
    symmetry (Left_Functoriality x y (f, fmap[F] f))
|}.

Program Definition lawvere_eqv_counit_transform : F ◯ G ⟹ Id := {|
  transform := @lawvere_eqv_counit;
  naturality := fun x y f =>
    Right_Functoriality x y (fmap[G] f, f);
  naturality_sym := fun x y f =>
    symmetry (Right_Functoriality x y (fmap[G] f, f))
|}.

Program Definition Comma_Functor_F_Id_Id_G (H : F ⊣ G) :
  (F ↓ Id[C]) ⟶ (Id[D] ↓ G) := {|
  fobj := fun x => (``x; to adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- to_adj_nat_r;
  rewrite <- X;
  rewrite <- to_adj_nat_l;
  reflexivity.
Qed.

Program Definition Comma_Functor_Id_G_F_Id (H : F ⊣ G) :
  (Id[D] ↓ G) ⟶ (F ↓ Id[C]) := {|
  fobj := fun x => (``x; from adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- from_adj_nat_r;
  rewrite <- X;
  rewrite <- from_adj_nat_l;
  reflexivity.
Qed.

Program Instance Comma_F_Id_Id_G_Iso (H : F ⊣ G) :
  (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G) := {
  to   := Comma_Functor_F_Id_Id_G H;
  from := Comma_Functor_Id_G_F_Id H
}.
Next Obligation.
  constructive.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.
Next Obligation.
  constructive.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.

End AdjunctionComma.

Theorem Adjunction_Comma `{F : D ⟶ C} `{G : C ⟶ D} :
  F ⊣ G  ↔  @lawvere_equiv _ _ F G.
Proof.
  split; intros H. {
    unshelve refine {| lawvere_iso := Comma_F_Id_Id_G_Iso H |}.
    - unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - unfold whisker_equiv.
      split; intros; simpl; intros; cat.
  }

  apply Adjunction_from_Transform.

  exact (Build_Adjunction_Transform
           (@lawvere_eqv_unit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_fmap_unit _ _ _ _ H)
           (@lawvere_eqv_fmap_counit_unit _ _ _ _ H)).
Qed.
