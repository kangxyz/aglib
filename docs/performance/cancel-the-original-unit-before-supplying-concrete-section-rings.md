> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#cancel-the-original-unit-before-supplying-concrete-section-rings) · [Context](original-context.md) · [Case index](README.md) · [Previous record](evaluate-original-geometric-stalk-units-through-typed-projections.md) · [Next record](normal-constants-typed-kan-extension-comparison.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Cancel the original unit before supplying concrete section rings

The first `Scheme.ArtinSchreier.rootOpen_appTop_root` proof in
[KernelCover](../../Aglib/AlgebraicGeometry/EtaleCohomology/ArtinSchreier/KernelCover.lean)
mapped the original equation `e_i * b = i.val * e_i` through
`U_i.ι.appTop.hom`, cancelled the restricted idempotent unit, and simplified
the multiplication and natural casts in the concrete section rings.
At Lean 4.34.1 and the pinned Mathlib revision, run
`remote-32232dd2146848e1ba4d655ad98a274b`, source
`e7ecf61bc6628ee7ad781c6dd9c997db73b20420158791c19e05866f13aa79b6`,
exhausted 200000 heartbeats at `whnf` in that final theorem. Earlier declarations
had no diagnostics, but this failed invocation supplied no accepted module
artifact.

The retained private `map_eq_natCast_of_unit_factor` proves the same cancellation
over variable commutative rings, with a fully typed `RingHom`, original factor,
original root, natural number, mapped-unit proof, and original product equation
as explicit inputs. The geometric theorem then supplies the actual rings
`Γ(X, ⊤)` and `Γ(U_i.toScheme, ⊤)` and the literal `U_i.ι.appTop.hom`.
The original cover, unit, restriction map, public equation and mathematical
hypotheses are preserved, including the empty-scheme case.

Run `remote-3cbd553cb8a54250bb5bbaf0a8853ef3`, source
`8be7fe3ea0623ffa7ec897114394ce3989cf43e16abe0a122cdab1d2f4f8e50a`,
accepted the exact KernelCover leaf in 3.7 seconds with no diagnostics and the
standard heartbeat budget. Native resource ceilings were unchanged. This
records a validated proof-boundary repair without isolating a compiler cause
or measuring a matched speedup. The actual Artin--Schreier short-exact consumer
subsequently compiled in `remote-fdafdc1ba6484130bfca42898e69d458`;
that consumer is outside the leaf-only timing claim.


