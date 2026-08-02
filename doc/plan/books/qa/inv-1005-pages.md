# INV-1005 — page range for Riehl §5.5 Theorem 5.5.9 / Lemma 5.5.10 (Decision 6.1)

**Verdict:** the PDF range in #1005 is right; the **printed** range is short by one page.
Correct: **printed pp. 206–208, PDF pp. 226–228.**

**Direct answer to the question asked:** *No* — the **lemma** (Lemma 5.5.10) does **not**
run onto printed p. 208. It ends on printed p. 207. What runs onto printed p. 208 is the
**Proof of Theorem 5.5.9**, which #1005 also cites (`riehl:5.5:thm9`). So #1005's printed
range must be extended to 208 — but for the theorem, not the lemma. The premise implied by
the question ("the lemma runs onto 208, consistent with #1006/#1007") is false as stated;
the conclusion (extend to 208) is nevertheless correct for a different reason.

## Method

`pdftoppm -r 150 -png` on `/Users/johnw/Desktop/riehl-category-theory-in-context.pdf`,
PDF pages 224–232, read **as images**; text layer (`pdftotext -layout`) used only as a
cross-check. Every claim below is something visible on the rendered page.

## What I saw, page by page

Running-folio offset confirmed on all four pages: printed = PDF − 20.

**PDF p. 226 — folio `206` printed top-left**, running head `5. MONADS AND THEIR ALGEBRAS`.
Contains, in order: Example 5.5.7 clauses (iii) and (iv) (the page *opens* mid-list with
"(iii) If C has coproducts and J is small, then Exercise 5.5.v demonstrates…"); the PTT/CTT/VTT
prose paragraph; `Proposition 5.5.8` with its three clauses and the one-line
"Proof. Exercise 5.5.iii. □"; then

> `Theorem 5.5.9 (Paré). The contravariant power set functor P : Set^op → Set is monadic.`

and its "argument presented here, due to Paré [Par74]" paragraph; then

> `Lemma 5.5.10. For any pullback diagram of monomorphisms of sets, as displayed on the left,`

with the two-square display, closing the page body at

> `the right hand square commutes.`

Footnotes 14 ("Triple" is an antiquated synonym for "monad.") and 15 (reflexive pair) at the foot.
**No proof of either result appears on this page.**

**PDF p. 227 — folio `207` printed top-right**, running head `5.5. RECOGNIZING CATEGORIES OF ALGEBRAS`.
Opens with `Proof. For any X ∈ PB′, consider a commutative rectangle` — this is the proof of
**Lemma 5.5.10**, and it **closes with □ about one-third down this page**, at
"By Exercise 3.1.vi, these conditions are equivalent. □". Then the Exercise-4.6.vi corollary
paragraph (`PA →^{f_*} PB →^{f^{-1}} PA` "is the identity"), then

> `Proof of Theorem 5.5.9. We apply Proposition 5.5.8.`

which runs to the bottom of the page, ending mid-argument at
"is a split coequalizer diagram, proving (ii)." — **no □ on this page for the theorem.**

**PDF p. 228 — folio `208` printed top-left**, running head `5. MONADS AND THEIR ALGEBRAS`.
**Opens with the continuation of the Theorem 5.5.9 proof**: "To show (iii), note that P is
faithful: given a parallel pair f, g : A ⇒ B, the composites …", and the proof **terminates with
□** at "Proposition 5.5.8 now implies that the contravariant power set functor is monadic. □".
Immediately below: the bold heading `Exercises.`, then Exercises 5.5.i, 5.5.ii, 5.5.iii, 5.5.iv,
**5.5.v** (with clauses (i)–(iv), the `LanF(j) := ∐_{x∈J} ∐_{J(x,j)} Fx` display), **5.5.vi**
(entire, ending "Challenge: describe the left adjoint (or see Theorem 6.2.1)."), and the opening
of **5.5.vii** including its `N^op --I--> L` square.

**PDF p. 229 — folio `209` printed top-right**, running head
`5.6. LIMITS AND COLIMITS IN CATEGORIES OF ALGEBRAS`. Exercise 5.5.vii clause (i), the interleaved
**Lawvere theory** prose definition, clause (ii); then §5.6 begins.

## Consequences for the three issues

| item | correct printed | correct PDF | current issue text | status |
|---|---|---|---|---|
| Lemma 5.5.10 (stmt + proof) | 206–207 | 226–227 | — | — |
| Theorem 5.5.9 (stmt + proof) | 206–208 | 226–228 | — | — |
| **#1005** (cites *both*) | **206–208** | **226–228** | `printed pp. 206–207, PDF pp. 226–228` | printed range wrong |
| #1006, Ex. 5.5.v–vi | 208 | 228 | `printed p. 208, PDF p. 228` | **correct** |
| #1007, Ex. 5.5.vii + defn | 208–209 | 228–229 | `printed pp. 208–209, PDF pp. 228–229` | **correct** |

#1005's printed and PDF ranges were internally inconsistent (206–207 is 226–227, not 226–228).
The PDF side was the accurate one.

## The exact one-substring edit for #1005

Warning: the issue body uses **U+2013 EN DASH**, not ASCII hyphen, in both ranges
(verified with `cat -A`: `printed pp. 206M-bM-^@M-^S207, PDF pp. 226M-bM-^@M-^S228`).
An edit keyed on `206-207` with a hyphen will not match. The substring below occurs
**exactly once** in the body (`grep -o` count = 1; the literal `206` occurs once in the
whole body), on line 2, the `## Source` line.

Find:

```
printed pp. 206–207, PDF pp. 226–228
```

Replace with:

```
printed pp. 206–208, PDF pp. 226–228
```

(Single character changes: `207` → `208` in the printed range. The PDF range is already correct
and must not be touched.)

For the record, the full unedited line 2 is:

> `Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §5.5 Theorem 5.5.9 and Lemma 5.5.10 (printed pp. 206–207, PDF pp. 226–228). Items: \`riehl:5.5:thm9\`, \`riehl:5.5:lem10\`.`

## Incidental (outside the question, no edit requested or applied)

#1006's second paragraph reads:

> `This issue also formalizes clause (iii) of §5.5 Example 5.5.7 (printed p. 205, PDF pp. 225–226)`

Same off-by-one shape: printed p. 205 is PDF p. 225 alone, so `printed p. 205, PDF pp. 225–226`
is internally inconsistent. On the page images, Example 5.5.7's heading and clauses (i)–(ii) are
at the foot of printed 205 / PDF 225, and **clause (iii) — the clause #1006 actually names — sits
entirely at the top of printed 206 / PDF 226.** So either `printed pp. 205–206, PDF pp. 225–226`
(the whole example) or `printed p. 206, PDF p. 226` (clause (iii) alone) would be right. Flagged
for the coordinator; I did not touch #1006.

## Confidence

High. Both the rendered images and the text layer agree, the printed folios are legible on all
four pages, and each proof's □ terminator was located visually.
