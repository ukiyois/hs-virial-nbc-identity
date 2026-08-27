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

## Relation to prior work

The finite graph identity is part of the classical broken-circuit and
chromatic-polynomial literature. Whitney's broken-circuit expansion, Tutte's
spanning-tree formulation, and the later broken-circuit-complex treatment by
Brylawski explain the graph-side cancellation and its Tutte specialization.
The connected-graph expansion of a Mayer coefficient is standard statistical
mechanics background going back to Mayer, with rigorous convergence treatments
by Penrose and Ruelle.

The tree-graph literature is related but addresses a different statement.
Penrose's 1967 tree-graph identity and the minimum-spanning-tree partition of
Procacci--Yuhjtman rewrite or bound connected graph sums; Lebowitz--Penrose
derive virial convergence bounds from such estimates. Ree--Hoover use a
different modified-graph representation for hard-sphere virial coefficients.
Those works are comparison sources, not imported proof terms, and this
repository does not claim their convergence or phase-transition conclusions.

## Contribution and distinction

The contribution is the exact identity for the continuous hard-sphere Mayer
integral, together with its kernel-checked Lean formalization. The finite
broken-circuit cancellation, the connected Mayer expansion, and the
product-to-flat coordinate change are not claimed as new in isolation. They are
classical or standard ingredients, explicitly separated from the theorem's
central bridge.

It is incomplete to reduce the result to a direct specialization and
recombination of a classical finite broken-circuit/Mayer cancellation followed
by a routine coordinate change. The overlap graph is a function of the
continuous hard-sphere configuration, so the finite cancellation is applied
pointwise while the active graph changes with the configuration. The proof then
turns the pointwise NBC count into measurable tree-owned regions and an exact
finite sum of their volumes. This is an exact identity, not an unsigned
majorant or a convergence bound.

The conventional coordinate transformation is deliberately not presented as a
novel contribution. Its role is fidelity: the theorem is first proved for the
anchored product-Lebesgue space and then transported explicitly to the usual
flat Euclidean presentation. The main mathematical significance is preserving
the Mayer cancellation as a nonnegative geometric decomposition instead of
discarding it through absolute values; the main formal significance is that the
entire discrete-to-continuous-to-measure chain is checked by the Lean kernel.

| Aspect | Prior work | This repository |
| --- | --- | --- |
| Finite NBC/Tutte cancellation | Classical finite graph/matroid identity | Re-proved and connected to the analytic statement; not claimed new alone |
| Mayer/tree-graph methods | Connected sums are expanded, rewritten, or bounded | Exact NBC-region volume equality, not a bound |
| Hard-sphere geometry | Standard overlap and configuration-space ingredients | Configuration-dependent overlap graph and measurable tree-owned regions are linked pointwise to the integral |
| Coordinates | Ordinary Euclidean/product-coordinate identifications | Explicit measure-preserving bridge for fidelity; not a novelty claim |
| Verification | Mathematical literature statements | Full discrete, measurable, integrable, and measure-transport chain checked in Lean |

The recorded prior-work search did not identify an exact prior statement of this
continuous hard-sphere NBC-region volume identity. That is a bounded search
result, not an absolute priority claim; the statements above identify precisely
which parts are classical and where the submitted theorem differs. The theorem
still does not claim strict positivity, convergence bounds, or phase-transition
consequences.

Selected references:

- J. E. Mayer, "The Statistical Mechanics of Condensing Systems. I," *Journal of Chemical Physics* 5(1) (1937), 67-73. DOI: `10.1063/1.1749933`.
- O. Penrose, "Convergence of Fugacity Expansions for Fluids and Lattice Gases," *Journal of Mathematical Physics* 4(10) (1963), 1312-1320. DOI: `10.1063/1.1703906`.
- D. Ruelle, "Correlation Functions of Classical Gases," *Annals of Physics* 25(1) (1963), 109-120. DOI: `10.1016/0003-4916(63)90336-1`.
- O. Penrose, "Two Inequalities for Classical and Quantum Systems of Particles with Hard Cores," *Physics Letters* 11(3) (1964), 224-226. DOI: `10.1016/0031-9163(64)90418-4`.
- J. L. Lebowitz and O. Penrose, "Convergence of Virial Expansions," *Journal of Mathematical Physics* 5(7) (1964), 841-847. DOI: `10.1063/1.1704186`.
- O. Penrose, "Convergence of Fugacity Expansions for Classical Systems," in A. Bak (ed.), *Statistical Mechanics: Foundations and Applications* (Benjamin, 1967), p. 101.
- H. Whitney, "A Logical Expansion in Mathematics," *Bulletin of the American Mathematical Society* 38(8) (1932), 572-579. DOI: `10.1090/S0002-9904-1932-05460-X`.
- W. T. Tutte, "A Contribution to the Theory of Chromatic Polynomials," *Canadian Journal of Mathematics* 6 (1954), 80-91. DOI: `10.4153/CJM-1954-010-9`.
- H. H. Crapo, "The Tutte Polynomial," *Aequationes Mathematicae* 3 (1969), 211-229. DOI: `10.1007/BF01817442`.
- T. Brylawski, "The Broken-Circuit Complex," *Transactions of the American Mathematical Society* 234(2) (1977), 417-433. DOI: `10.1090/S0002-9947-1977-0468931-6`.
- F. H. Ree and W. G. Hoover, "Seventh Virial Coefficients for Hard Spheres and Hard Disks," *Journal of Chemical Physics* 46(11) (1967), 4181-4197. DOI: `10.1063/1.1840521`.
- A. Procacci and S. A. Yuhjtman, "Convergence of Mayer and Virial Expansions and the Penrose Tree-Graph Identity," *Letters in Mathematical Physics* 107(1) (2017), 31-46; preprint arXiv:1508.07379. DOI: `10.1007/s11005-016-0918-7`.

## Provenance

`ukiyois` supplied the graph-theoretic/NBC research direction, problem framing,
scope decisions, and repository maintenance. The Lean proof was implemented
through AI-assisted OpenCode sessions. DeepSeek-V4-Flash was used under its own
model label. At the time of the relevant runs, GLM-5.3-Flash had not been
publicly released; OpenCode exposed that free GLM route under the alias
`ox-alpha`. That alias refers only to the GLM route, not to DeepSeek. The
current handoff also includes work done with `openai/gpt-5.6-luna`.

The repository is licensed under Apache-2.0. The Palomar submission target is
https://github.com/ukiyois/hs-virial-nbc-identity; submission uses a public,
immutable commit SHA and the form at https://submit.palomar-registry.org/.
