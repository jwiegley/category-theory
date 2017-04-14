Class Applicative := {
  pure {a} : a ~> M a;
  ap {a b} : M (b ^ a) ~> M b ^ M a
    where "f <*> g" := (ap f g)
}.
