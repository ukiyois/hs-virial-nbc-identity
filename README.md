# Hard-sphere Mayer NBC identity and fork-packing volume bound

This repository contains a kernel-checked Lean 4 and Mathlib development of
the hard-sphere Mayer NBC identity together with an explicit three-dimensional
geometric upper bound for every tree-owned NBC region.

## Main results

The principal geometric theorem is the checked declaration
`PalomarHS.nbc_region_real_volume_le_fork_factor`.  For every spanning tree
`T` on `k` vertices, it proves

```text
Vol(NBC_T) <= (17 / 32) ^ hardSphereNu T * hardSphereKappa ^ (k - 1)
```

Here `hardSphereKappa` is the volume of the unit ball in three-dimensional
position space, and `hardSphereNu T` is the maximum cardinality of a packing of
pairwise vertex-disjoint, order-compatible forks in `T`.  A formal fork is an
ordered triple `(a,b,c)` with `a < b < c` and tree edges `{a,b}` and `{a,c}`;
`a` is the center and `b,c` are the two leaves higher than it in the `Fin k`
label order.  Each packed order-compatible fork contributes an explicit factor
`17/32` to the base tree bound `Vol(NBC_T) <= hardSphereKappa ^ (k - 1)`.

The factor is obtained from an attachment-aware, measure-preserving block
factorization.  Each packed order-compatible fork contributes two oriented
relative-position coordinates constrained to the separated-pair region, whose
exact volume is
`(17/32) * hardSphereKappa ^ 2`; all remaining tree-difference coordinates lie
in unit balls.  The construction handles the orientation of each tree edge
and the unused coordinates simultaneously, rather than applying independent
pair estimates to overlapping variables.

The exact identity remains the global structural theorem.  The checked
declaration `PalomarHS.main_result` proves

```text
(k.factorial : Real) * |hardSphereBk|
  = sum over spanning trees T of hardSphereNBCVolumeFlat T
```

It converts the signed Mayer graph integral into a finite sum of nonnegative
NBC-region volumes.  The exact identity supplies the decomposition; the
fork-packing theorem supplies the stronger per-tree geometric estimate.  The
current Comparator configuration checks both `PalomarHS.main_result` and
`PalomarHS.nbc_region_real_volume_le_fork_factor`; both declarations are stated
independently in `Challenge.lean` and proved in `Solution.lean`.

The proof chain covers finite broken-circuit cancellation, the
configuration-dependent overlap graph, measurable NBC regions, anchored
product-Lebesgue configuration space, explicit tree-difference coordinates,
the attachment-aware fork packing, and the measure-preserving transport to
flat Euclidean coordinates.

## Repository layout

- `Challenge.lean`: independently readable statement surface.
- `Solution.lean`: proved declarations used by Comparator.
- `lean/`: substantive graph, matroid, Mayer, and hard-sphere development.
- `lean/HardSphereCompound.lean`: checked fork packing and avoidance interface.
- `lean/HardSphereTreeDifference.lean`: checked tree difference coordinates,
  base volume bound, and separated-block interfaces.
- `lean/HardSphereGeometry.lean`: checked lens and separated-pair calculations.
- `lean/HardSphereForkPackingCoordinates.lean`: checked oriented fork-packing
  coordinates, measure-preserving block factorization, and the `17/32` bound.
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

The comparator surface in `Challenge.lean` intentionally contains
statement-only `sorry` holes for the selected declarations; the substantive
proof development and `Solution.lean` contain no unresolved proof holes or
project-specific axioms. The permitted Lean axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope

The exact NBC identity is formalized for natural numbers `k` and `d` with
`2 <= k`, on the anchored configuration space
`Fin (k - 1) -> EuclideanSpace Real (Fin d)`.  The explicit
measure-preserving transport to `EuclideanSpace Real (Fin ((k - 1) * d))` is
proved in `HardSphereMeasure.lean`.

The fork-packing upper bound is the dimension-three specialization: for every
tree `T`, it bounds the corresponding NBC region by
`(17/32) ^ hardSphereNu T * hardSphereKappa ^ (k - 1)`.  Its proof uses the
exact separated-pair volume and a simultaneous coordinate factorization.  The
packing counted by `hardSphereNu T` consists of order-compatible triples
`(a,b,c)` with `a < b < c`, center `a`, leaves `b,c`, and tree edges `{a,b}` and
`{a,c}`.  The formal natural-number parameter also includes the degenerate
`d = 0` identity case.  The development does not claim strict positivity of `b_k`, a complete
sign-alternation theorem, convergence bounds, or freezing consequences.

The NBC convention is deletion of the lexicographically largest edge from a
circuit. The upstream fact records use a different smallest-edge convention;
the convention change is stated explicitly in `formalization.yaml`.

## Relation to prior work

Prior work on broken circuits, chromatic polynomials, and spanning trees
provides the discrete comparison context. Whitney's broken-circuit expansion,
Tutte's spanning-tree formulation, and Brylawski's broken-circuit-complex
treatment describe the graph-side cancellation and its Tutte specialization.
The connected-graph expansion of a Mayer coefficient and the convergence
results of Penrose and Ruelle provide the statistical-mechanics comparison
context.

The tree-graph literature is related but addresses a different statement.
Penrose's 1967 tree-graph identity and the minimum-spanning-tree partition of
Procacci--Yuhjtman rewrite or bound connected graph sums; Lebowitz--Penrose
derive virial convergence bounds from such estimates. Ree--Hoover use a
different modified-graph representation for hard-sphere virial coefficients.
Those works provide comparison context; their convergence and phase-transition
conclusions are separate results and are not formalized by this theorem.

## Contribution and distinction

The central contribution is the combination of an exact NBC volume identity
with an attachment-aware compound-fork estimate.  The identity turns the
configuration-dependent signed Mayer sum into a finite sum of nonnegative
tree-owned volumes.  The geometric layer then exploits pairwise disjoint,
order-compatible forks inside each tree to obtain the explicit multiplicative
suppression
`(17/32) ^ hardSphereNu T`.

The decisive geometric step is a simultaneous, orientation-aware coordinate
factorization: two coordinates per packed fork form a separated pair, while
the complementary coordinates remain in unit balls.  The resulting product
measure statement is transported by an explicit measure-preserving map and
checked by the Lean kernel.  This retains the structure of the NBC
decomposition instead of replacing it with an unsigned global majorant.

The finite broken-circuit cancellation, connected Mayer expansion, and
product-to-flat coordinate map are supporting components of the checked
construction.  The formalized contribution is the complete
pointwise-to-measurable-volume bridge together with the verified fork-packing
geometry and its quantitative per-tree bound.

| Aspect | Prior work | This repository |
| --- | --- | --- |
| Finite NBC/Tutte cancellation | Prior finite graph/matroid results | Re-proved and connected to the analytic statement |
| Mayer/tree-graph methods | Connected sums are expanded, rewritten, or bounded | Exact NBC-region volume equality |
| Hard-sphere geometry | Existing overlap and configuration-space results | Configuration-dependent overlap graph and measurable tree-owned regions are linked pointwise to the integral |
| Coordinates | Ordinary Euclidean/product-coordinate identifications | Explicit measure-preserving bridge in the checked theorem |
| Fork geometry | Separated-pair and fork exclusions | Attachment-aware factorization for order-compatible forks and the `17/32` per-fork volume bound |
| Verification | Mathematical literature statements | Full discrete, measurable, integrable, and measure-transport chain checked in Lean |

The recorded prior-work search did not identify an exact prior statement of this
continuous hard-sphere NBC-region volume identity or this fork-packing
specialization. That is a bounded search result, not an absolute priority
claim; the statements above identify precisely which parts come from prior work
and where the submitted development differs. The formalized results currently
comprise the exact identity and the explicit dimension-three fork-packing upper
bound. Strict positivity, convergence bounds, and phase-transition consequences
are separate targets.

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
