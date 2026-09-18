# JSP-001021 — Lean 4 formalization of the Erdős–Moser lower bound

> **Theorem (JSP-001021, Erdős–Moser 1964).** Every tournament on `n`
> vertices contains a transitive subtournament of size at least
> `⌈log₂(n+1)⌉`.
>
> Formalized in Lean 4 as a single self-contained file using only the core
> library `Init` (no mathlib). Zero `sorry` / `admit`.

## Files

| File | Purpose |
| --- | --- |
| `TransitiveSubtournament.lean` | The formal proof — theorem `JustinSunPrize.transitiveSubtournament`. |
| `verify_transitive.py` | Independent Python check of the bound + tight examples (n = 3, 4, 7). |
| `JSP-001021_证明.md` | Human-readable proof and award-rule notes (Chinese). |
| `formalization.yaml` | Lean credit / role record (Formalizer and Co-formalizer named). |
| `catalog_submission.md` | Draft text for the external PR to the award catalog. |
| `.gitignore` | Ignores build artifacts (`.lake/`). |

## Build & verify (Lean 4.34.0)

No external dependencies beyond Lean core `Init`.

```sh
lean TransitiveSubtournament.lean        # exit code 0  ⇒  proof checks
```

Axiom audit (from inside the file or a check file):

```lean
#print axioms JustinSunPrize.transitiveSubtournament
-- => [propext, Quot.sound]
```

Only the two core Lean axioms `propext` and `Quot.sound` appear — there is
**no `sorryAx`** and no `choice`. The proof is fully constructive.

## Independent Python check

```sh
python verify_transitive.py
```

Prints `OK` / `✅` for: (A) exhaustive n = 1..6 over all tournaments,
(B) the constructive greedy algorithm on 2000 random tournaments for each
n = 1..40, (C) tight examples at n = 3, 4, 7.

## Submitting to TheJustinSunPrize/awards (external PR)

1. Push this repository to a **public** host. Note the **branch** and the
   **full 40-character commit SHA**.
2. Fork `TheJustinSunPrize/awards`; edit `problems/catalog-1001-1022.md`,
   the `## JSP-001021` table.
3. Set `Lean proof: Yes` with: repo URL + branch + 40-char commit SHA +
   theorem name `JustinSunPrize.transitiveSubtournament` + this build line
   + your name.
4. **Add** an `Attribution basis` row crediting the Formalizer (see
   `formalization.yaml` / `catalog_submission.md`).
5. Do **not** commit Lean source / binaries into the award repo — only
   reference text and links.
6. Open the PR; maintainers review (source reachable, pinned version,
   attribution, theorem scope).

`Eligible to claim` flips to `Yes` only after the PR merges and review
passes — it is a screening flag, not a payout right. See
`catalog_submission.md` for the exact text to paste, and
`JSP-001021_证明.md` §4 for the verified official rules.
