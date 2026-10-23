# Positional universe instances in refusal probes

`Fail` accepts **any** error. A stale positional universe instance can turn
an intended conversion or universe refusal into an unrelated arity error.
Issue #1380 guards against that false green.

For a constant with elaboration-added universes, every positional instance
inside a `Fail` needs a same-file, same-constant, same-arity eager positive
twin outside **every** `Fail`. Prefer dropping the positional instance when
a type ascription or declaration binder expresses exactly the same constraints.
Never drop load-bearing universe identifications merely to satisfy lint.

## Compiler-backed enforcement

Run `make probe-arity-check` in the declared Nix environment. This is a
**fresh build gate**, not a timestamp check over existing checkout products:

1. Copy `_CoqProject` and its registered sources into a new private directory.
   No checkout `.vo`, `.glob`, generated makefile or dependency file is copied.
2. Rebuild every registered source with the selected compiler in full `.vo`
   mode, using `-q` and the project's `-R . Category` mapping. Inherited make
   targets, jobserver state, quick-mode and compiler overrides are discarded;
   the declared library-selection environment is retained.
3. Validate source digests and logical-module headers in fresh `.glob` files.
   Each instance must have an exact-span direct global reference, not a
   notation occurrence, local variable, absent reference or ambiguous span.
4. Replay relevant **whole files** with read-only `About` queries immediately
   before candidate controls and negatives, under their original logical
   module names. Compare canonical identities as well as reference metadata,
   exact spelling, arity and conservative resolution epochs. Short `.glob`
   paths alone can omit nested modules; they are not canonical identities.
5. Verify source/policy stability and retain the source/product fingerprints,
   compiler version/configuration, selected library environment, logs and
   canonical-name outputs with the result. There is no cache/reuse mode and
   no lexical fallback counted as semantic success.

The guard checks all constant instances, not only those classified as having
extra universes. `Type@{u}` is a sort annotation; a declaration's `f@{u ...}`
binds universes. Neither is a constant use-site instance. Missing, stale,
swapped or ambiguous compiler artifacts fail closed.

`PROBE_ARITY_JOBS` selects build parallelism (default 2, maximum 16).
`PROBE_ARITY_WORK_DIR` selects a **nonexistent**, preferably external evidence
directory; otherwise a fresh directory under `TMPDIR` is retained. The inner
build uses generated `Makefile.coq` directly, never the outer `lint`/`check`
targets, so there is no recursive guard/build cycle.

`make probe-arity-unit` runs fast scanner/metadata tests only. The optional
`--syntax-only` CLI mode is a weaker preflight and explicitly says so; neither
certifies the semantic rule. `make probe-arity-coq-selftest` also runs real
compiler regressions, including false-green fixtures and repaired companions.
Set `PROBE_ARITY_TEST_EVIDENCE` to a fresh external directory to retain their
sources, build receipts and stripped error logs.

Both `lint` and `check`, and the pre-commit hook, run the semantic gate.
Nix CI's `probe-arity-check` and `build` checks share the default package,
whose check phase runs the semantic gate and compiler self-tests. The separate
Nix `probe-arity-unit` check needs Python only. Python and compiler dependencies
are declared in the relevant Nix development/check environments.

## What counts as a twin

A candidate positive twin is an **explicit-`@` bare Check**, for example:

```coq
Check @SAFT_cover_wp@{_ _ _ _ _ _ _ _ _ _ _ _}.
```

Parentheses around that same bare term are accepted. Fresh `_` slots avoid
identifying existing named universes. These checks add no proof constants and
do not replace the substantive positive controls already in the probes.

**Correction to the initial implementation:** plain `Check F@{...}.` is NOT
accepted. Notation can erase that entire lexical form, even when it looks
bare. Explicit `@` on positives alone is not sufficient either: a negative
`F@{...}` under a scope can expand to another constant. Fresh direct-reference
metadata and canonical-name queries are therefore required on both sides.
Delayed/caught tactics, unchosen tactic branches, notation bodies and erased
arguments likewise do not supply eager controls.

The lexer honors strings, including doubled quotes, **inside nested comments**
as Coq does. Quoted comment delimiters cannot manufacture a control or hide a
live negative. Declaration binders are distinguished from uses. Modules,
imports, notation, proof/obligation steps, resets, generated-name declarations
and unknown commands separate conservative epochs. Ordinary declaration reuse
requires current compiler identities, including when imported Program Mode
generates auxiliaries whose names were not written in the declaration.

A short target also written bare elsewhere in its negative might be bound
there, including through binding notation. Unqualified references inside
`ltac:`/`ltac2:` quotations or non-term refusal commands are also unresolved.
Qualification can remove this ambiguity, but is **not** by itself proof
against notation capture: the compiler evidence is still required.

## References not reached after an earlier refusal

Eight entries in `scripts/probe_arity_unreached.json` enumerate uses whose
`.glob` references are absent because an earlier binder or declared result
type fails. This is not a missing-reference waiver:

- The source use must have protected explicit-`@`, fully canonical syntax,
  with the configured declaration, constant and exact arity.
- A fresh whole-file strip must produce a universe refusal **before** that
  use, not a syntax, lookup or arity error.
- Extracted protected references are compiled against the freshly rebuilt
  library. Their direct references and canonical identities must agree with
  the whole-file query replay. They still need an eager twin in the source.
- Missing references outside this mechanism fail closed. Changed or unused
  configuration entries fail; normal twin exceptions cannot suppress absent
  compiler evidence.

The eight uses are in `p452_n4_binder_collapsed`,
`p453_n8_shapes_below_homs`, `p465c_C8_carrier_below` and
`p465c_C8a_proof_below`. Their named universe instances are preserved. The
qualification/explicit-`@` repairs were compared in formable whole-file copies:
relax `so < h` to `h <= so` for the first two, and replace the failing strict
carrier/proof inequality with `a = c, p = c` for the latter two. Before/after
functions agree by `eq_refl` on ordinary Rocq and the saved stand-in. Those
relaxations are measurements only, never changes to the source negatives.

## Exceptions and refusal measurements

`scripts/probe_arity_exceptions.json` is an explicit, initially empty twin
allowlist. Entries require a file, constant, exact arity, reason and evidence
that no twin is needed. No wildcard constants/arities, malformed field types,
duplicates, unused or out-of-project entries. It does not waive missing
compiler artifacts or canonical identities.

Strip one `Fail` at a time in a **whole-file copy** when measuring refusal
kinds. Preserve imports, controls and fixtures; passing the original `Fail`
alone proves nothing about its cause. The guard is not certification of every
refusal kind, nor a general Coq parser. New syntax may need explicit support.

The N6 regression instruments the current whole `Test/ProbeSAFT453.v`: H4
(#1379) removed the fragile instance, so the test explicitly injects one,
retains a twelve-slot twin, rejects thirteen slots and accepts twelve. It
does not pretend the historical N6 still exists on this branch.
