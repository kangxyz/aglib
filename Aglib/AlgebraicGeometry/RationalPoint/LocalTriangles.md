# LocalTriangles

The namespace is `Scheme.RationalPoint`. For source parameters `F, p, o, ho`,
put `q := (⟨p, o, ho⟩ : RationalPoint F X)` in the existing native structure.
This is the exact replacement for the source `actualOrigin` constructor; no
second rational-point structure or constructor alias is created.
`localScheme`, `localMap` and `closedMap` use the actual origin stalk and section
evaluation. `closedTriangle` recovers the given section. `genericMap` and
`genericTriangle` require integrality and recover the scheme's actual
generic-point arrow. The level-unit theorem retains characteristic zero and
a nonzero natural level and applies to every actual codimension-one stalk.

Source basis: `f8a3314ddecffcada2ec721d26d56a937bed9690`.

- Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.RationalSection`.
  SHA-256: `eb2e49d19b97fba8abdedcfb7966f3c83a2b22d4ade66d40e1398f9ac94f8213`.
  Selected source ranges: `[[15, 58]]`.
  - `actualOrigin` → `(⟨p, o, ho⟩ : AlgebraicGeometry.Scheme.RationalPoint F X)`.
  - `level_isUnit_at` → `AlgebraicGeometry.Scheme.RationalPoint.level_isUnit_at`.
  - `originLocalScheme` → `AlgebraicGeometry.Scheme.RationalPoint.localScheme`.
  - `originLocalMap` → `AlgebraicGeometry.Scheme.RationalPoint.localMap`.
  - `originClosedMap` → `AlgebraicGeometry.Scheme.RationalPoint.closedMap`.
  - `originClosedTriangle` → `AlgebraicGeometry.Scheme.RationalPoint.closedTriangle`.
  - `originGenericMap` → `AlgebraicGeometry.Scheme.RationalPoint.genericMap`.
  - `originGenericTriangle` → `AlgebraicGeometry.Scheme.RationalPoint.genericTriangle`.

Compiler and native-client evidence, provider hashes and complete correspondence
are recorded in the assigned packet-2 scratch return. No existing provider,
family README, facade or published release file is modified.
