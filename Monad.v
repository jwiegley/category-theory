Require Import Lib.
Require Export Adjunction.
Require Export Closed.

Section Monad.

Context `{C : Category}.
Context `{D : Category}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.
Context `{F ⊣ U}.

Class Monad := {
  join {a} : U (F (U (F a))) ~> U (F a) := fmap counit
}.

End Monad.

Definition monad_map `{C : Category} `{D : Category}
           `{F : D ⟶ C} `{U : C ⟶ D} `{J : F ⊣ U}
           `{M : @Monad _ _ F U J} {X} := U (F X).

Arguments monad_map {_ _ _ _ _} M X /.

Coercion monad_map : Monad >-> Funclass.

Section MonadLib.

Context `{C : Category}.
Context `{D : Category}.
Context `{A : @Cartesian D}.
Context `{@Closed D A}.
Context `{F : D ⟶ C}.
Context `{U : C ⟶ D}.
Context `{J : F ⊣ U}.
Context `{M : @Monad _ _ F U J}.

Program Definition bind {a b : D} : M a × M b ^ a ~> M b :=
  uncurry _.
Obligation 1.
  destruct M.
Admitted.

End MonadLib.
