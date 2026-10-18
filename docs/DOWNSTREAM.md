# Quillen and R5Lab integration

This document preserves the initial downstream migration census and transition
contract. Its source revisions and counts are historical, rather than a current
inventory or a claim that downstream packages have not adopted Aglib. The
[recorded cache rollout](CACHING.md#recorded-initial-rollout) already includes a
Quillen consumer with an Aglib dependency. The inspected R5Lab checkout at
`959fb044206b188c9b7cd66404b2b37b84fad8b0` also declares Aglib
`25c37780264f0da94f5bb6bd31cc089d26f2da80` and Quillen
`db5f75ff068fe14b605a5b4fe2dd5bc67fb773dc` in its `lean/lakefile.toml`
and manifest. Those dependency declarations do not establish completion of all
consumer migrations or downstream checks. Curve, projective-line, K/G/Q/S and
other applications keep their downstream owners.

## Dependency and release order

Imports should follow this dependency graph:

```mermaid
flowchart TD
  R5Lab --> Quillen
  R5Lab --> Aglib
  Quillen --> Aglib
  Aglib --> Mathlib
```

Migrate Quillen first, then R5Lab. Pin a verified Aglib commit, retain Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and update each Lake manifest through its dependency workflow. The initial census recorded R5Lab pinning Quillen `83629578a3d70787d41ec631f5234af8758716af`, while its inspected Quillen source was `189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Moving R5Lab to the migrated Quillen commit is an explicit dependency update requiring application verification.

Aglib and Quillen are public; R5Lab is private. Quillen can resolve its Aglib dependency without private repository credentials. Pin the verified published Aglib revision before publishing Quillen's dependency switch, then pin that Quillen revision in R5Lab.

## Inspected scope

These are source-import counts at R5Lab
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3` and the historical Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905` selection, using the [migration records](migration/latest-quillen.json), [module map](module-map.json) and [namespace map](namespace-map.json). Import dependence does not assert that every imported declaration is referenced.

| Package | Extracted source owners | Retained direct consumers | Important boundary |
| --- | --- | --- | --- |
| Quillen | 272 source modules, mapped to 283 Aglib destinations | 310 implementation files and 23 positive-test modules | 222 whole-source replacement candidates; 50 mixed sources retain declarations or applications |
| R5Lab | 123 extraction entries from 100 source modules | 131 local modules importing extracted R5Lab or Quillen owners | Curve, finite-etale, Grayson, Quillen and elliptic applications remain in R5Lab |

Quillen's retained transitive implementation closure contains 2613 files. For R5Lab's extracted owners alone, another 680 local modules are reached transitively. The exact replacement set must follow declaration correspondence, rather than treating these counts as file-deletion lists.

## Transition contract

- Keep one implementation of every migrated general declaration, in Aglib. Entirely transferred owners may temporarily import precise Aglib leaves. Mixed owners remove only the transferred declarations and keep their application remainder.
- Native objects and instances must be shared. In particular, replace Quillen's old exact structures/functors with `CategoryTheory.ExactCategory` objects, and use the canonical scheme module, coherent and invertible-sheaf objects. Do not recreate structures, quotient relations or registered instances to preserve an old spelling.
- Refactor retained consumers to precise Aglib imports and native names. Transparent abbreviations or theorem aliases may stage a batch with exact types, universes and premises, but remove them and vacated general source modules once their consumers are migrated. A type abbreviation alone does not recreate old projection, method or theorem namespaces.
- Preserve modern public imports and intended reduction visibility. Keep adapters in the original consumer packages; Aglib must not import them.
- Preserve actual theorem hypotheses and identify retained family inputs. Pass a proved Aglib supplier where one is available, as for proper finiteness and smooth differential rank; retain still-unsupplied premises under the [interface boundary](INTERFACES.md).

## Quillen batches

1. Add the pinned Aglib dependency. Pilot `Quillen/CategoryTheory/ExactCategory/Basic.lean` and a real immediate consumer such as `Quillen/KTheory/Basic.lean`. Make QCategory, KSpace and K use the canonical exact structure.
2. Continue through exact functors, subcategories and small models. Retain Q-compatible functors, Q/K maps and their laws in mixed files. Migrate independent ring, module and ordinary homology leaves alongside this chain.
3. Switch general sheaf, quasicoherent and cohomology producers. Keep finite-type quasicoherence separate from the locally Noetherian coherent specialization. Retain G groups and G maps in the application files, using the canonical lower functors.
4. Replace general cuts inside perfect-complex, projective-line and Waldhausen files at their recorded declaration ranges. Preserve strict/perfect K maps, cylinder applications and other retained content.
5. Update remaining imports and names, remove unused adapters, and regenerate aggregates with Quillen's own generator. Validate the changed `Quillen` and `QuillenTest` closure and real affected application clients, retaining compatible evidence for unchanged modules.

## R5Lab batches

1. Pin Aglib and the verified migrated Quillen commit together. The historical census found 45 distinct direct Quillen imports outside the extraction map; do not infer removal of that dependency from the extraction map alone.
2. Switch independent ring/length/descent and homology/sheaf leaves first. Preserve the application part of Grayson `Cycle/LocalLength.lean`.
3. Switch geometry foundations: Base/FScheme, generic curve-container predicates, stalks, etale/smooth/normal properties, field extensions, rank and Picard prerequisites. Keep the remaining contents of mixed `PointedCover`, `Core`, `Genus`, `Degree/Basic` and `SmoothIntegral` owners.
4. Follow the actual dependency graph for cohomology and differentials. Structure-sheaf results require Base/FScheme; relative cohomology requires `Degree/SheafRank`; generic differentials depend on cohomological pullback. A family-wide geometry-before-cohomology ordering is insufficient. Replace only the general blocks in `CurveEuler.lean`.
5. Update retained consumers: curve Picard/degree/Riemann-Roch, finite-etale descent, arithmetic surfaces, Grayson/Quillen applications, elliptic scalar extension and the elliptic-integral essays. Keep their mathematical scope in R5Lab and preserve existing user work.

## Acceptance and publication

Use isolated adaptation branches or worktrees. For each batch, compile the changed producers and the actual affected application-consumer closure, using matching retained evidence where available. Check canonical type/instance identity, maps and retained premises; inspect the actual diagnostics before introducing compatibility names.

Reconcile required production/test, source-enrollment, style, axiom/control and
standalone-consumer coverage for each combined package snapshot. Preserve
compatible evidence and check actual gaps incrementally; finishing a migration
or publishing does not require blanket builds. Use bounded exact-module replay
where the owning workflow requires additional replay. Prune obsolete owned
module facets while preserving compatible current outputs, so stale compiled
modules cannot mask missing imports. Record pre-existing failures separately
from migration regressions.

Downstream package changes and publication are separate from Aglib's completed first extraction. No downstream build or migration acceptance is claimed by the static census above.
