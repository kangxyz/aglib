# Independent ordinary review: constant cyclic cohomology core v3

**Verdict: accepted mathematically for fixed v3, retaining the accepted v1 proof review and checking the affected v2/v3 correspondence.** No mathematical gap was found. This continuation does not assign formal status or claim fresh native coverage.

The current identity is `versions/v3/manifest.json` under `migration/implementation/constant-cyclic-cohomology-core-staging`, SHA-256 `0333a8553899e7d86723fe9d0e1316fcc05b4347242b998f90fd18501ce0c18f`. Its exact seven-file vector is recorded in the JSON. Fixed afterimages and live sources match it. Native HEAD remains provenance `54d6974ace11bf7d197aa925cb8cade86db8a24f`. The earlier complete proof review was on the actual fixed v1 four-file vector; that vector and the prior execution boundary are retained separately in the JSON.

The affected changes check as follows:

- **v1 → v2:** the generic file only adds `omit [HasSheafify J AddCommGrpCat.{a}] in` before `cyclicCoefficient_shortExact`. That premise is genuinely unused by native `ShortExact.map_of_exact`; removing it changes no proof or map. The cohomology theorems retain their original sheafification and Ext premises. The current generic hash is `510e0282ff85b01ee8a48b2f36cf79fffbc8311ecaa10495543a32561736fcc6`.
- **v2 → v3:** the original documented `ConstantFinite.value` and `ConstantFinite.coefficient` alias block is copied literally into the new `H1/ConstantFinite/Coefficient` leaf. The FQN, universe order, section variables, native value lift, coefficient RHS and local `hasSheafifyLarge` are the same. Its block hash is `59fd8a88d854c1c4736a11083f50d764baa64f0ffbea556a1f0a817bd065a87d`. Removing exactly that block from the old `Basic` and adding the leaf's public import gives the current `Basic` byte-for-byte. Its remaining geometric definitions, statements and proofs are exact.
- `ConstantRestriction` changes only its public import from geometric `ConstantFinite.Basic` to the coefficient leaf. `CyclicCoefficientSequence` changes only its former `ConstantRestriction` import to that leaf. The concrete functor and all three instances, including both native ULifts, are unchanged. `CyclicVanishing` and `ArtinSchreier` retain their exact reviewed v1 hashes.

The public import boundary intentionally changes: `Sequence` no longer brings in `ConstantRestriction` through its former public import, and `ConstantRestriction` no longer brings in the geometric `ConstantFinite.Basic` reexports. `Basic` still publicly reexports the relocated aliases through the leaf. This preserves the owned mathematical objects, maps and public statements; it does **not** preserve the entire incidental export set. The supplied v3 header-routing evidence records the pure coefficient/cyclic routes without `Class`; geometric `Basic` keeps its genuine geometry. This is routing evidence only, with no timing or compiler-success inference.

The following v1 mathematical conclusions remain accepted on the corresponding unchanged proofs:

1. `cyclicCoefficient_shortExact` maps the actual native multiplication/reduction sequence under the one specified exact additive functor.
2. `cyclicPrimePower_vanishing` proves the full induction for any positive base, including the actual `ZMod 1` zero case.
3. `cyclic_vanishing_of_prime_divisors` proves the full strong induction for every positive order using its actual prime divisors and the same mapped sequence.
4. `cyclicPrimePower_cohomology_finite` proves the full induction from genuine finite base cohomology. Its successor uses the native same-degree `H.map` exact pair and `Exact.ab_finite`, without assuming cohomology surjectivity.
5. The concrete proper Artin–Schreier endpoint still proves its finite prime-field base through proper structure-cohomology finiteness and the literal Frobenius-fixed comparison, transports it by the original cyclic/prime-field iso, and invokes the generic induction. The entire endpoint has the same reviewed hash; no invertibility or perfectness premise has appeared.

The retained hypotheses and universe boundaries remain one additive `F : AddCommGrpCat.{0} ⥤ Sheaf J AddCommGrpCat.{a}` preserving finite limits and colimits; independent site-object/Hom/value/Ext worlds `c/v/a/e`; native `Sheaf.H`, its original Ext postcomposition maps, and the specified genuine vanishing/finite base cases. There is no new coefficient/cohomology model, geometric premise or desired induction law. The bare mapped-short-exact theorem now needs no `HasSheafify` premise.

Only existing generic compilation coverage is retained: `remote-1b73ac9d1f7845368dc41326884a1dc4`, source `052123e1b54f8aa4339b28e1294f545ca1e0b8802b1aa954fa0944386d3b9f82`, input `510e...`, Lean 4.34.1. The actual generic frontend (wrapper 884350/compiler 884352) finished with exit 0; the shared run exited 1 because of other packets, with group closed and no input drift. This does not establish the concrete or relocated v3 modules. The earlier active v1 run is not relabeled as this evidence. No compilation, lint, tests, audit or replay was started for the continuation.

No earlier mathematical conclusion is retracted. The report's source identity and import-boundary description are updated to v3; unchanged proof coverage is retained rather than recreated. Remaining native evidence, broader geometric conclusions, formal status and independent writing acceptance remain with their actual owners.

