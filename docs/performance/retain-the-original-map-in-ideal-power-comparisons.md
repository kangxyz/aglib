> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-the-original-map-in-ideal-power-comparisons) · [Context](original-context.md) · [Case index](README.md) · [Previous record](preserve-module-types-in-finite-normalization.md) · [Next record](retain-native-localization-structures.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Retain the original map in ideal-power comparisons

The completed-base quotient comparison in
[FiniteTypeLocalComparison](../../Aglib/RingTheory/AdicCompletion/FiniteTypeLocalComparison.lean)
originally normalized the native tensor `includeRight` from an `AlgHom`
through its `RingHom`, then rewrote `Ideal.map_coe`. The power-equivalence
declaration reached the default 200000-heartbeat `whnf` limit. The repair
uses `Ideal.map_pow` directly with the original `includeRight`, keeping the
same map in both the quotient producer and its consumers. Surjectivity is
composed with the existing exact quotient-map equation.

Candidate `dd06f3c14eb726e5444c61f03d616292541abc7132e81144d51e05e25819b3cb`
failed in native run `remote-68314ede6d02463d9b66ea5eb8be5993`. Repaired
source `4f11e3612242ef6443f0e5bcdefea7c194a7354f740bafaa1d31967f1d672cb0`
passed the complete quotient-comparison module in 10 seconds in
`remote-a32421a12426431ab6a42af7a2bda5a6`. Maps, hypotheses and budgets are
unchanged. This covers the compatible quotient comparisons; localization,
completed local rings and scheme stalk comparisons remain separate consumers.
The observations establish removal of the tested timeout, without a
controlled speedup or general attribution of compiler cost.

