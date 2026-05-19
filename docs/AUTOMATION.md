# Tactic and hint-database reference

A one-page contract for the library's exported proof automation.
Downstream projects can rely on these names and behaviours as stable
across non-major versions; conversely, anything not listed below is
considered internal to the library and may change without notice.

## Tactics

Most tactics live in `Lib/Tactics.v` (loaded transitively by
`Require Import Category.Lib.`, which is itself the first import of
every library file).

**Exception:** `Ltac normal` is defined in `Functor/Bifunctor.v:129` —
NOT in `Lib/Tactics.v`. To use `normal` in your own code, write
`Require Import Category.Functor.Bifunctor.` explicitly.

| Tactic        | Arity      | Purpose                                                       | Closes / progresses        | Stability     |
|---------------|------------|---------------------------------------------------------------|----------------------------|---------------|
| `cat`         | no-arg     | Standard simplification for category-law goals: `simplify` + `autorewrite with categories` + `auto with category_laws` + `try reflexivity`. | Most equational `≈` goals at the morphism level. | Stable        |
| `cat_simpl`   | no-arg     | More aggressive: `program_simpl`, `autounfold`, then dispatch to `equivalence` / `proper` / `respectful` discharges and finally `cat`. Bound as the default `Obligation Tactic` library-wide. | All standard `Program` obligations. | Stable        |
| `proper`      | no-arg     | Discharge a `Proper _ _` goal. `repeat intro; simpl; try cat; intuition`. | Most `Proper`/`respectful` instances. | Stable        |
| `equivalence` | no-arg     | Discharge a `Equivalence` goal. `constructor; repeat intro; simpl; try cat; intuition; auto with *`. | Most setoid `Equivalence` proofs. | Stable        |
| `construct`   | no-arg     | `unshelve econstructor; simpl; intros` — build a record value, leaving each field as a subgoal. | Record-introduction step. | Stable        |
| `normal`      | no-arg     | Bring a composition chain into a canonical right-associated form. Defined in `Functor/Bifunctor.v` (NOT `Lib/Tactics.v`). | Composition normalisation. | Stable        |
| `simplify`    | no-arg     | Library's structural-tactic preamble used inside `cat` / `cat_simpl`. | Match-and-split goals.    | Internal*     |
| `inv`         | hypothesis | `inversion H; subst; try clear H`.                            | Hypothesis destruction.     | Stable        |
| `spose F as X` | term + ident | `pose proof F as X; simpl in X` — bring `F` into the context simplified. | Lemma instantiation step.   | Stable        |
| `sapply F`    | term       | Cb-simplified `apply F`.                                       | Lemma application.          | Stable        |
| `srewrite F`  | term       | Cb-simplified `rewrite F`.                                     | Lemma-driven rewrite.       | Stable        |
| `srewrite_r F` | term      | Cb-simplified `rewrite <- F`.                                  | Reverse-direction rewrite.  | Stable        |
| `isomorphism` | no-arg     | Solver for `_ ≅ _` goals (see `Theory/Isomorphism.v:149`).     | Iso construction.           | Stable        |

`*` "Internal" means we keep the API working but downstream code
should prefer the higher-level wrappers `cat` / `cat_simpl`.

## Hint databases

| Database         | Contents                                                                                          | Defined in                              |
|------------------|---------------------------------------------------------------------------------------------------|------------------------------------------|
| `categories`     | Rewrite rules for category laws: `id_left`, `id_right`, `comp_assoc` (right-associated direction only, to normalise; the forward direction would loop), `fmap_id`, etc. | `Theory/Category.v`, `Lib/Tactics2.v`   |
| `category_laws`  | `Hint Extern` resolutions for `Reflexive`/`Symmetric`/`Transitive`/`Proper`/`equiv`.              | `Lib/Tactics.v`                          |
| `core`           | Standard Coq + library-installed extensions for `Equivalence`/`Proper`/`Reflexive`/`Symmetric`/`Transitive`. | `Lib/Tactics.v` (via `Hint Extern 1`). |

Both `cat` and `cat_simpl` consult `categories` (via `autorewrite`) and
`category_laws` (via `auto`).

## Recommended downstream conventions

If you depend on this library and want to add your own automation:

1. **Don't pollute `categories`.** Reserve it for the library's
   category-law identities. Use your own prefixed databases
   (`mylib_kernels`, `mylib_rewrite_specs`, etc.).
2. **Wrap, don't replace, `cat` / `cat_simpl`.** A downstream
   `solve_mylib` tactic should typically end with `; cat` or
   `; cat_simpl` to fall through to the library's primitive automation.
3. **Don't fight the library's `Obligation Tactic`.** The library
   sets `#[global] Obligation Tactic := cat_simpl.` in `Lib/Tactics.v`.
   Inside your own files, set `#[local] Obligation Tactic := …` if you
   need a different default — never `#[global]`.
4. **Avoid `Set Default Proof Using "All"` in files with heavy
   typeclass contexts.** This forces every proof term to capture every
   in-scope section variable, which makes proof terms enormous and can
   trigger memory blow-ups in typeclass-rich code (e.g. anything
   touching `Hypergraph`).
5. **Prefer flat projections over deep nests.** Use `scfa_mu (scfa X)`
   rather than `@mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _
   (@scfa_commutative _ _ _ (scfa X))))`. The flat projections are
   provided exactly to keep goal states readable.

## What `cat` will NOT do

- Solve goals that require non-trivial categorical structure
  reasoning (e.g. Frobenius, hypergraph-specific spider laws). For
  those use the lemmas in `Structure/Monoidal/Hypergraph/Spider.v`
  directly.
- Compute monoidal coherence (associator / unitor) cancellations
  beyond what's registered in `categories`. For strict-monoidal
  reductions, this is currently a manual step.
- Solve goals where the algebra is hidden behind opaque
  `Program`-generated `existT` packagings — unfold them first with
  `cbn` or `simpl`.

## When in doubt

`cat_simpl` is the highest-power closer the library exports. If
`cat_simpl` doesn't progress, the next thing to try is a manual
`spose` of the relevant lemma followed by a small `rewrite` chain.

## Stability promise

The tactics listed above will continue to exist with the same surface
syntax in all future releases of this library. Their *implementation*
may strengthen (we may make `cat` smarter); we will not remove or
rename them. If a future tactic supersedes one of these, the old name
will become a `Tactic Notation` alias for the new one.
