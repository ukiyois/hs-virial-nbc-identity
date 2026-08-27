# Hard-sphere Mayer NBC volume identity

This repository contains a Lean 4 and Mathlib formalization of the exact
no-broken-circuit (NBC) volume identity for hard-sphere Mayer cluster
integrals.

## Main result

For natural numbers `k` and `d` with `2 <= k`, the checked theorem
`PalomarHS.main_result` proves

```text
(k.factorial : Real) * |hardSphereBk|
  = sum over spanning trees T of hardSphereNBCVolumeFlat T
```

The proof covers the finite graph cancellation, the measurable NBC-region
decomposition, the anchored product-Lebesgue configuration space, and the
explicit measure-preserving identification with flat Euclidean coordinates.

## Repository layout

- `Challenge.lean`: independently readable statement surface.
- `Solution.lean`: proved declaration used by Comparator.
- `lean/`: substantive graph, matroid, Mayer, and hard-sphere development.
- `comparator.json`: Challenge/Solution declaration configuration.
- `formalization.yaml`: structured provenance, scope, and automation metadata.
- `tex/nbc_identity.tex`: human-readable mathematical account and proof architecture.

Lean source and the Lean kernel are authoritative for the formal proof. The TeX
file is explanatory and is not a replacement for the checked Lean proof.

## Verification

From the repository root:

```text
lake exe cache get
lake build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory tex tex/nbc_identity.tex
```

`Challenge.lean` intentionally contains a statement-only `sorry`; the
substantive proof development and `Solution.lean` contain no unresolved proof
holes or project-specific axioms. The permitted Lean axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope

The primary measure is the product of Euclidean Lebesgue measures on the
anchored configuration space `Fin (k - 1) -> EuclideanSpace Real (Fin d)`.
`HardSphereMeasure.lean` proves the explicit measure-preserving transport to
`EuclideanSpace Real (Fin ((k - 1) * d))`. The formal statement also includes
the natural-number case `d = 0`. It does not claim strict positivity,
additional sign-alternation results, convergence bounds, or freezing
consequences.

The NBC convention is deletion of the lexicographically largest edge from a
circuit. The upstream fact records use a different smallest-edge convention;
the convention change is stated explicitly in `formalization.yaml`.

## Provenance

`ukiyois` supplied the graph-theoretic/NBC research direction, problem framing,
scope decisions, and repository maintenance. The Lean proof was implemented
through AI-assisted OpenCode sessions, principally using DeepSeek-V4-Flash and
GLM-5.3-Flash; some runs exposed only the anonymous provider alias `ox-alpha`.
The current handoff also includes work done with `openai/gpt-5.6-luna`.

The repository is licensed under Apache-2.0. The Palomar submission target is
https://github.com/ukiyois/hs-virial-nbc-identity; submission uses a public,
immutable commit SHA and the form at https://submit.palomar-registry.org/.
