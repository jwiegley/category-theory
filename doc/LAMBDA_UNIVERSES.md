# Smaller Equations signatures in the lambda calculus (#1404)

`Sub_EqDec` decides equality for a substitution between two environments. Both environments and the substitutions live in `Set`. Nevertheless, at `88a811e7a813c13bc9abbb6b6febe5fe53ce61c9`, its inferred public universe instance has 5,375 slots on released Rocq/Corelib 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2. The 5,450 reported in the original issue was measured on another compiler; it is not this baseline.

The change is in `Instance/Lambda/Ty.v`, **not** the substitution decision. `Ty` is unindexed; both its no-confusion relations return `Prop`. `Set Universe Minimization ToSet` around `Derive NoConfusion NoConfusionHom for Ty` eliminates internal levels before later derivations can inherit them. The original library setting is restored before `Derive Subterm EqDec for Ty`. No file disables universe polymorphism. The two no-confusion relations now have zero bound slots (formerly two and one); the types of the relations and packages still mention `Ty`, not an arbitrary carrier whose universe could vary. `Ty`, `Var`, `Exp` and `Sub` still return `Set` with empty polymorphic headers. `Sub_EqDec` remains polymorphic and closed; its header shrinks to **975 slots**, its printed constraint block from **3,743 to 2,703** constraints. This is a reduction, not an assertion that all remaining levels are necessary.

## Census

For each of the baseline's 34 `Derive` and `Equations` sentences in the registered Lambda files, compile the source prefix just before and just after the sentence (close enclosing sections in both). Compare the top-level heads in `Print Module` on those two prefixes. Query the names added by the command against the *complete* module, with `Set Printing Universes` and `Set Printing All`. This attributes 456 distinct module heads to those commands, including generated obligations, graph inductives and elimination schemes. It counts module members, not unnamed subterms or constructors nested inside an inductive entry. For example, `Sub_eqdec` and `Sub_EqDec` count separately. A slot is one identifier in the outer `@{...}` header, not every occurrence in its type. A constraint is a printed `<`, `<=` or `=` edge in the following universe block, not a transitively implied edge. Each column sums over declarations, not globally distinct levels.

| File under `Instance/Lambda/` | Heads | Baseline slots | Revised slots | Baseline edges | Revised edges |
|---|---:|---:|---:|---:|---:|
| Eval | 210 | 26,285 | 5,653 | 20,221 | 14,501 |
| Exp | 30 | 8,728 | 1,684 | 6,215 | 4,573 |
| Full | 51 | 346 | 150 | 227 | 171 |
| Log | 24 | 144 | 144 | 70 | 70 |
| Multi | 3 | 9 | 9 | 6 | 6 |
| Ren | 47 | 563 | 143 | 667 | 547 |
| Sem | 17 | 29 | 29 | 80 | 80 |
| Step | 3 | 3 | 3 | 3 | 3 |
| Sub | 46 | 10,808 | 2,008 | 7,576 | 5,496 |
| Ty | 22 | 79 | 9 | 24 | 8 |
| Value | 3 | 3 | 3 | 0 | 0 |
| **Total** | **456** | **46,997** | **9,835** | **35,089** | **25,455** |

Including the other top-level module members and `.glob` declarations (among them the explicitly declared constructors), 803 qualified names were queried in the 16 modules `Instance/Lambda.v` and `Instance/Lambda/*.v`. All 803 `Print Assumptions` answers are unchanged; 756 say `Closed under the global context`. In particular, closure of the decision does not imply closure of `Lambda_Closed`. Across all 1,179 original registered `.glob` files there are 1,439 direct reference rows to these 803 names, including 91 to the generated module heads. None carries an explicit positional universe instance. The unresolved lexical short-name matches for `Closed@{...}` and `Sub@{...}` were in comments on cartesian closure and subcategories, not positional clients of the Lambda library.

## Why not make the decisions monomorphic?

A trial that made **only** `Derive EqDec` monomorphic for `Ty`, `Var`, `Exp`, `Ren` and `Sub` reduced `Sub_EqDec` to zero slots and built every Lambda module. It also introduced global universe constraints. After jointly importing `Category.Instance.Lambda`, `Category.Instance.Lambda.Norm`, `Category.Instance.Lambda.Example` and `Category.Instance.Lambda.Sound`, `Print Universes` showed new paths from `list.u0` and `NoConfusion.NoConfusion_list.u0` to both `eq.u0` and `Constants.eq_sig_pack.u0`. The accepted change leaves that joint import's entire `Print Universes` output byte-identical to baseline.

Another trial minimized all five bundled derivations without disabling polymorphism. It shrank `Sub_EqDec` to one slot but also specialized signature domains such as `Ren_sig`'s sigma universe to `Set`. Even an unannotated application accepting a higher-universe sigma did not expose that change. `Test/Issue1404.v` therefore **supplies** a level strictly above `Set` to `Ty_direct_subterm_sig` and `Ren_sig`. The original and accepted versions admit both instances; the broader treatment no longer has the corresponding positional slot. The same test checks seven `eq_refl` computations (including positive and negative type equality, renamings and substitutions) and jointly uses the decisions, semantics and cartesian closure.

## Product sizes and build costs

These measurements are for the 16 baseline Lambda modules, not a whole-library build. For each run, seed a new directory with byte-verified compiled products of the same 41 non-Lambda prerequisites, no Lambda products. Compile all 16 serially with `coqc -q -R . Category` in the locked shell, choosing the lexicographically first ready file from the `coqdep` graph. Compare identical sources except for the `Ty` derivation change. There were no other registered reverse dependents at the baseline. Input preparation and result queries are outside the timed loop. OS caches were not flushed; measurements are not cold-cache estimates. The order below puts each variant first once. Summed per-file wall time measures the individual compiler invocations; CPU sums user and system child times, while elapsed includes loop overhead.

| Run order | Sum of `.vo` bytes | Sum wall (s) | CPU (s) | Elapsed (s) |
|---|---:|---:|---:|---:|
| Revised A | 3,539,433 | 11.29 | 11.10 | 11.31 |
| Baseline A | 5,023,753 | 15.70 | 15.41 | 15.72 |
| Baseline B | 5,023,753 | 16.07 | 15.91 | 16.08 |
| Revised B | 3,539,433 | 11.13 | 10.98 | 11.14 |

The size saving repeats exactly: **1,484,320 bytes** across these 16 products. Timing is host- and load-dependent; those four runs are not a projected speedup for the whole library. To inspect the motivating constant on either tree, in the release shell after building, run:

```coq
Require Import Category.Lib Category.Instance.Lambda.Sub.
Set Printing Universes. Set Printing All.
About Category.Instance.Lambda.Sub.Sub_EqDec.
Print Assumptions Category.Instance.Lambda.Sub.Sub_EqDec.
```
