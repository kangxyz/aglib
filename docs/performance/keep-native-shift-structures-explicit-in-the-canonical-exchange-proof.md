> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-native-shift-structures-explicit-in-the-canonical-exchange-proof) · [Context](original-context.md) · [Case index](README.md) · [Previous record](pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof.md) · [Next record](keep-the-original-universal-exchange-test-at-a-shared-data-head.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Keep native shift structures explicit in the canonical exchange proof

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
The ordinary 200000-heartbeat declaration budget and native instance-search
budget were retained. These are existing scoped compilation observations,
not benchmarks or an additional verification cycle.

The failed `ExchangeShift` source
`6e394111247e039aa7b488409081d13fff411dfa39b55a5612a04c27e2ec00ea`
was compiled in `remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`.
After building the original derived inverse-image comparisons, direct
instance search for `NatTrans.CommShift` on their concrete two-factor and
three-factor isomorphism chains exhausted 200000 heartbeats at `whnf` or
`isDefEq`. The same leaf also exposed a separate actual coherence mismatch
in its identity-on-complexes comparison and a missing import of the existing
bounded-below quasi-isomorphism shift instance.

The effective repair has three parts.

1. The original degreewise identity comparison is postcomposed with the
   fully faithful native complex inclusion. Its displayed chain includes
   both the right unitor and the final inverse left unitor. The latter
   retains the target functor as `Id ⋙ inclusion`, with its actual composite
   `CommShift` structure, rather than identifying only the underlying
   functor with `inclusion`. The original chain components remain identities.
2. The existing `CochainComplexPlus.QuasiIsoShift` provider is imported;
   no new shift-stability premise is assumed.
3. Private typed `isoTrans_commShift` and `isoChain_commShift` prove the
   native composition law over variable functors and their supplied native
   shift structures. The concrete inverse-image comparison and original
   square supply those same factors to these regular proof heads. This
   avoids asking instance search to reconstruct the expanded geometric
   comparison chain. It does not choose another shift structure or another
   inverse-image square.

The original derived-adjunction unit is shown shift-compatible through its
original unit factorization. Its two right-derived units and original
degreewise adjunction unit are retained. Only the exact left functor's unit
is inverted; the nonexact right-derived unit is not cancelled. The original
adjunction mate consequently has the original canonical shift compatibility.
There is no additional public scheme hypothesis.

After the performance repair, `remote-5343d4769a9c40948d7108ee21f8548d`
reported only four ordinary elaboration errors, with no remaining timeout.
These were repaired by using `NatTrans.ext` followed by `funext K` instead
of allowing `ext K` to descend to the full-subcategory morphism's underlying
`.hom`, and by naming the two original `derivedImageAdjunction` compatibility
facts at their exact types. `remote-3daf87dbe5e24b0dab8cb23955db4394` then
reported only a local-let normalization and an associativity equality;
explicitly unfolding that local `Q` and applying `Category.assoc` closed them.
Neither intermediate failed invocation is claimed as a successful provider.

Complete validated leaf source:
`19875b7f834ee4099fcc6d1a3d87e7d96f7dc3fff57a9900a4e2171060072534`.
Run `remote-aa4f8a36498e4ef3a3da29f4fab9b1cb`, source snapshot
`00847f07b44899f9f17b527183df7bcfa0ce7a173f0703df630ea87c6c01de2a`,
compiled `ExchangeShift` successfully in 6.1 seconds. That two-frontend batch
**failed overall** at the separate upper `AllModuleCoefficients` parser
error, so the evidence covers the complete shift provider only. It is not
whole-family or proper-base-change closure evidence.

The actual logs and receipts are preserved in this task's `remote-runs/`
directory. This note diagnoses the successful typed coherence boundary,
not a Lean compiler defect or an asserted performance ratio.

