# Etale cohomology module and namespace migration

This change moves the scheme-specific small-etale cohomology family from
`AlgebraicGeometry/Cohomology/` to the sibling
`AlgebraicGeometry/EtaleCohomology/`, and renames its scheme declaration
namespace. The migration is based on Aglib
`d1994587faf05aad9ef3f39500a21c58d5a8f7ec`.

The [family guide](../Aglib/AlgebraicGeometry/EtaleCohomology/README.md) owns
current objects and hypotheses. The machine-readable
[module and namespace map](migration/etale-cohomology-layout.json) contains
all 65 exact module substitutions and the namespace-prefix change. It is the
input for downstream retargeting; no substring-wide replacement of every
`Cohomology` or `Etale` owner is appropriate.

## Import changes

| Old module prefix | New module prefix | Leaves |
| --- | --- | --- |
| `Aglib.AlgebraicGeometry.Cohomology.EtaleH1` excluding its nested Kummer leaves | `Aglib.AlgebraicGeometry.EtaleCohomology.H1` | 48 |
| `Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer` | `Aglib.AlgebraicGeometry.EtaleCohomology.Kummer` | 7 |
| `Aglib.AlgebraicGeometry.Cohomology.Kummer` | `Aglib.AlgebraicGeometry.EtaleCohomology.Kummer` | 3 |
| `Aglib.AlgebraicGeometry.Cohomology.FiniteLocallyConstant` | `Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant` | 7 |

For example:

```lean
-- Before
import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Pullback

-- After
import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback
```

The exact map handles nested Kummer first and avoids a duplicated
`EtaleEtaleCohomology` prefix. No old-path import shims are retained. Generic
`GroupCohomology/Kummer`, ring theory, finite-etale geometry and Zariski/module
cohomology keep their own module roots.

## Declaration changes

The namespace prefix changes uniformly:

```text
AlgebraicGeometry.Scheme.EtaleH1
  -> AlgebraicGeometry.Scheme.EtaleCohomology
```

There is no additional `H1` declaration subnamespace. For instance, the new
module `Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback` exports
`AlgebraicGeometry.Scheme.EtaleCohomology.h1Pullback`. Declaration suffixes,
including `H1Etale`, `AbelianSheaf`, `inverseImage`, `FiniteCoefficient`,
`TatePointed` and `TateCoefficients`, retain their names and mathematical
meaning below this prefix. No aliases in the old scheme namespace remain.

Update qualified uses and `open` statements, including short uses such as
`Scheme.EtaleH1` or `EtaleH1` inside the scheme namespace. Import searches alone
miss namespace-only consumers. Leave historical source paths, provenance and
quoted earlier-version evidence intact.

Other native object namespaces retain their identity. In particular, the
Kummer leaves extending `GroupCohomology.Kummer` and finite representation
leaves extending `Scheme.FiniteEtale.SheafDescent` keep those namespaces.

## Mathematical and internal compatibility boundary

The moved implementations remain the same actual Mathlib sites, sheaves, Ext
groups, coefficients, canonical maps and comparison morphisms. Universes,
positivity, invertibility, finite/local-triviality conditions, markings and
explicit comparison inputs are preserved. This relocation is not a new proof
of a previously assumed geometric comparison or of proper base change.

All actual Aglib source and in-package test references are retargeted, including
namespace-only consumers. Public aggregate imports are regenerated/retargeted
through the native enrollment tools. Existing library and test modules remain
consumers of the one canonical implementation.

## Handoff to Quillen, Motivic and R5Lab sessions

This task changes Aglib internally. Quillen, Motivic and R5Lab sources,
dependency pins and manifests are deliberately left to their owning sessions.
Those packages can keep building against their existing Aglib revisions until
they adopt the migration commit. This guide is not a downstream acceptance or
upgrade claim.

When adopting the migration:

1. Select the Aglib revision containing this change and reconcile the library's
   actual Lake dependency resolution. Retain Lean 4.34.1 and Mathlib
   `d13f23b723b8a846827a245b89c10fc7d3f11612` unless a separate upgrade is
   intended. Refresh the consumer's manifest through its own workflow.
2. Apply exact `module_changes` from the JSON map to import tokens, then the
   namespace-prefix change to live declaration references. Do not rewrite
   historical provenance or every occurrence of the word cohomology.
3. Include qualified namespace-only uses and local candidate extensions.
   Reconcile declarations extending a migrated native type with that type's
   new namespace; do not recreate a parallel implementation or blanket aliases.
4. Update affected library aggregates and relevant examples/manifests using
   that repository's own generator. Quillen's committed example manifest also
   contains an Aglib pin. Manifest maintenance does not itself request a
   separate example-client build.
5. Run the consumer's ordinary affected build/lint/in-package test batch,
   reusing compatible caches and successful evidence. Additional kernel replay,
   trust/client chains and blanket rebuilding do not follow from this move.

At the prior inspected standalone snapshots, Quillen and Motivic each depended
on Aglib and neither on the other. Their updates can therefore be prepared
independently once an Aglib migration revision is selected. Recheck actual
current pins in those sessions. R5Lab directly consumes all three libraries,
so its eventual integration must reconcile the selected Aglib, Quillen and
Motivic revisions together. No current downstream import census is inferred
from that historical dependency observation.

For a quick triage before using the exact map:

```sh
rg -n 'Cohomology\.(EtaleH1|Kummer|FiniteLocallyConstant)|Scheme\.EtaleH1' \
  --glob '*.lean' SOURCE_ROOT
```

This search is not a complete parser or a proof that no shorter namespace use
remains. The owning session should inspect its actual import graph and compiler
diagnostics. Existing unrelated work and dirty dependency updates must be
preserved.

## Validation scope

Migration validation uses the changed implementation graph, required affected
consumers and relevant AglibTest modules, plus native batch lint and applicable
source/document checks. Passing results are reused after repairs. Compile
aggregation only consumes already available unrelated artifacts; a missing
cache does not authorize an unrelated whole-library rebuild. No downstream
repository validation or new mathematical theorem is part of this change.
The affected batch passed for 128 targets, including
`AglibTest.FundamentalGroup`, `GroupBaseChange`, `RelativeCurveFoundations` and
`RootGroupGeometry`. Both changed aggregate modules built successfully. The
complete production `Aglib` environment passed native builtin lint and the
unmodified Batteries driver; selected text-style lint passed for 116 changed
modules. The exact Lean-source digest and coverage are in the JSON map.

Full-test-environment lint was not run and is excluded by the user's explicit
task scope. It is not an outstanding completion condition for this migration.
The four affected test modules above already passed, and that evidence is
retained. No further AglibTest environment preparation or test compilation is
required by this phase. Earlier test-entry/cache readiness observations remain
separate infrastructure facts and are not recorded as a passing test-umbrella
lint result.
