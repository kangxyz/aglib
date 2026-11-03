# Canonical split providers at the production import boundary

## Observed failure

The completed-source integration added the split projective twist coefficient
providers `Coefficients.Model` and `Coefficients.Sections`, while the existing
`Coefficients` parent still contained the full implementation. The selected
leaf graph compiled, but the normal `Aglib` production build failed while
importing both forms through `Aglib.AlgebraicGeometry`. Its first diagnostic
reported that the environment already contained
`AlgebraicGeometry.Scheme.Cohomology.twistingFiniteCechHomologyZeroSectionsIso._proof_2`
from `Coefficients.Sections`.

The reported auxiliary name came from a duplicated declaration family. The
parent repeated 39 named commands from the split providers, including fourteen
model, instance and map definitions. The parent also contained three original
coefficient-naturality theorems absent from those providers.

## Repair and retained mathematics

The parent now imports and reexports the canonical Model and Sections
providers. It retains only the three independent original naturality theorems.
Their attributes, statements and proof bodies are copied verbatim. The local
derived-category instances use the same existing standard values exported by
Model. All fourteen model/instance/map definitions in the split providers have
identical types and defining bodies modulo whitespace to the old parent.
No public constructor, map, universe or mathematical premise is replaced.

The [coefficient API](../../../../Aglib/AlgebraicGeometry/Cohomology/Projective/TwistCohomology/Coefficients.md)
records the native owners and the degree bound applying to the derived
comparison. [Source identities](source-identity.json) retain the baseline,
pins, constructor comparison, original naturality block hashes and exact
before/after parent identities. The [source delta](source-delta.diff) records
the complete parent change.

## Native evidence and scope

[Native compiler evidence](compiler-evidence.json) preserves the failed and
successful production-build resource records, actual failed import invocation
and all four production frontends in the repair run. The failed build had
2157 successful frontends and one failed aggregate import. The warm retry
compiled the repaired parent, both aggregate roots and one separate EOF-only
source adjustment; all four frontends succeeded. Existing successful artifacts
were retained.

These observations establish the production import repair and reuse of the
canonical providers. The differently scoped runs give no controlled cold-build
speedup or attribution of proof checking costs. Normal package tests, lint and
axiom checking retain their own evidence.

## Reusable procedure

When a parent and new split providers enter the same production root, compare
their declarations before editing a reported generated auxiliary name. Keep
one implementation of each constructor and law. Let the parent reuse the
shared providers and retain only its independent original laws, preserving
the supplied models and actual maps. Continue the ordinary production-root
build with compatible artifacts; that root exercises coexistence of the
providers without adding a separate client or replay procedure.

## Placement follow-up, 2026-11-03

The earlier repair and its evidence above describe that historical source. A later invalidation review restored the original `Coefficients` parent byte-for-byte to pre-integration main `1b737dca122694a54850316097a7ee87ddcbaead`. The new Model and Sections modules are thin imports of that parent. The parent retains the 39 original named declarations and three naturality laws, with one canonical implementation. This reverses the earlier import direction and avoids changing the stable parent solely to introduce duplicate split providers.

The candidate remains uncommitted; the earlier warm production retry does not establish its current build, lint, axiom audit, or shared-main invalidation cost. See the [placement follow-up](../../placement-edits-in-widely-imported-modules.md#surface-resolution-invalidation-follow-up-2026-11-03) for the compared graphs and pending checks.
