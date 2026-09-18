# External PR draft — JSP-001021 (TheJustinSunPrize/awards)

**Target file:** `problems/catalog-1001-1022.md` → the `## JSP-001021` table.

**What to change:**
- Replace the `Lean proof` row (`No` → `Yes`, with the evidence below).
- **Add** an `Attribution basis` row (it is currently absent from this entry).

**Status: final.** Public evidence repo: `https://github.com/wangweiqi388/jsp-001021-transitive-subtournament`,
branch `master`. The 40-char commit SHA in the rows below is pinned to the current proof commit.

Co-signature (recorded in `formalization.yaml`):
- Formalizer (primary): 王玮琪 (WangWeiqi, GitHub: wangweiqi388)
- Co-formalizer: WorkBuddy (AI assistant)

---

## New / changed rows (paste into the JSP-001021 table)

```
| Lean proof | Yes — Lean 4.34.0 formalization: theorem `JustinSunPrize.transitiveSubtournament` in `TransitiveSubtournament.lean` (single file, only `import Init`, no mathlib). Repo: https://github.com/wangweiqi388/jsp-001021-transitive-subtournament · branch `master` · commit `4bec001e239b72f9e66edf58b9eef4658718fb85`. Build: `lean TransitiveSubtournament.lean` (exit 0). Axiom audit: `[propext, Quot.sound]` (no `sorry`/`sorryAx`). Formalizer: 王玮琪 (WangWeiqi, GitHub: wangweiqi388). Independent Python check: `verify_transitive.py` (all pass). |
| Attribution basis | Lean formalization credit follows `formalization.yaml` (role: Formalizer, 王玮琪 (WangWeiqi, GitHub: wangweiqi388)). Lean attribution source: https://github.com/wangweiqi388/jsp-001021-transitive-subtournament (commit `4bec001e239b72f9e66edf58b9eef4658718fb85`, file `TransitiveSubtournament.lean`, theorem `JustinSunPrize.transitiveSubtournament`). The formalized result is the Erdős–Moser (1964) lower bound `≥ ⌈log₂(n+1)⌉`; the exact value f(n) remains open (Reid–Parker 1970 disproved the equality conjecture). |
```

`Current status` stays `Solved` (Erdős–Moser 1964) — do not change it.
`Eligible to claim` is updated by maintainers after merge/review (screening flag).

---

## Notes for the maintainer

- Scope: this formalization proves the **lower bound** (the problem statement).
  It does **not** claim f(n) = ⌈log₂(n+1)⌉ for every n (that is an open problem).
- No mathlib: the proof uses only Lean core `Init`. The `library` field in any
  verification record must reference the Lean 4.34.0 core toolchain, not mathlib.
- Independent verification: `verify_transitive.py` exhaustively checks n = 1..6,
  runs the constructive algorithm on 2000 random tournaments per n = 1..40, and
  verifies tight examples at n = 3, 4, 7.
- Do not paste Lean source into this repo; reference only (per CONTRIBUTING.md).
