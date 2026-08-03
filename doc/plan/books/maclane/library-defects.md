# Library defects surfaced during the MacLane catalog campaign

These are in-tree defects (comments contradicting code, stale/garbled
pointers, headers claiming unbuilt results) found by the coverage/verify
agents while classifying items — NOT missing-theory catalog gaps. Recorded
here so they are not lost; most are cosmetic/doc-level. Filing them as
GitHub issues is a maintainer call (they are not "coverage-gap" items).
Where a defect naturally belonged to a filed coverage-gap issue, it was
folded into that issue's Definition of Done instead (noted below).

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| 1 | Instance/Adjoints.v:32-36, :82-83 | Header + comment claim the LEFT adjoint is the "forward" direction, but `adj_morphism` (:84-88) has `free_functor : D ⟶ C` / `forgetful_functor : C ⟶ D`, so arrows run along the RIGHT adjoint. `Adjoints` is Mac Lane's Adj with the opposite direction convention, mis-described. | Folded into issue **#395** (DoD item). |
| 2 | Construction/Comma/Limit.v:17, :33, :120; Construction/Comma.v:99-100 | Header prose and section titles claim `comma_proj2` "creates the limits", but the file proves only existence/lifting (`comma_ump` at :222 is the ordinary terminal-cone UMP); the creation uniqueness/reflection clause is neither stated nor proved, and — unlike Beck.v:52-60 — no disclosure of the gap. | Folded into issue **#438** ("The comma projection creates limits"), which asks for exactly the missing creation statement. |
| 3 | Instance/Omega.v:13 | Garbled cross-reference in the header: `Adámek's initial-algebra chain [Instance ... Construction/Chain.v] is indexed` — the bracketed token `[Instance ... ` is a leftover/broken pointer; intended reference is `[Chain]` in Construction/Chain.v (where `Chain : Omega ⟶ C` is defined, :64). Cosmetic, but a broken pointer in a header the CLAUDE.md reading protocol tells readers to consult first. | **No coverage-gap home** — recorded here only. Trivial doc fix. |
| 4 | Structure/Equalizer.v:78-92 (esp. :89) | Header essay concludes ":89 — \"Both arguments run in this library\"", but the first argument (all finite limits from products + equalizers, Mac Lane V.2 Thm 1) is genuinely NOT in-tree — that is precisely the gap issue **#416** exists to close. Over-claim. | Folded into issue **#416** (DoD widened to cite the whole :78-92 essay, not just :80). |
| 6 | Structure/Monoidal/Braided.v:131 (+ header :22-24) | The comment on the `braid` field says "beta : x ⊗ y **≅** y ⊗ x, natural in both arguments" (≅ = natural ISO), but the field at :132 is `braid {x y} : x ⨂ y **~>** y ⨂ x` — a bare morphism, NOT an isomorphism. Comment contradicts code, and materially: the ~>/≅ gap is exactly why `BraidedMonoidal` admits non-invertible pre-braidings (invertibility is not derivable from the two hexagons), which is what makes MacLane XI.1:def2 PARTIAL. | Folded into issue **#606** (XI.1 braiding, DoD item: "correct the misleading ≅ comment to match whatever the field ends up being"). LIBRARY-DEFECT channel worked end-to-end (verifier→drafter placed→reported). |
| 5 | Construction/Enriched.v:107 | Background essay names "the hand-built Ab-enriched example of Structure/Preadditive.v and Structure/Additive.v", but Preadditive.v is explicitly **CMon-enriched, NOT Ab-enriched** (its own header :20-21: negatives deliberately not demanded); only Additive.v (pneg) supplies the negatives for an Ab-enrichment. Prose imprecision, not a code contradiction; found twice (two VIII.2 verifiers). | **No coverage-gap home** — recorded here only (minor doc fix: qualify the sentence to attribute Ab-enrichment to Additive alone). |

Chapter IV also surfaced two accurate-but-unproved prose claims (not folded,
worded correctly in the issues that cite them): Construction/Slice.v:88-90
("Σ_f ⊣ f^* recorded in the header" — true, it is in prose) and
Instance/Fun.v:104-106 (functor-category cartesian *closure* stated in prose
with only the cartesian case proved). And one genuine false claim:
Structure/Pullback.v:129-130 says the slice base-change adjunction is built in
Construction/Slice/Pullback.v, but that code is commented out AND mis-oriented
— surfaced in issue **#387**.
