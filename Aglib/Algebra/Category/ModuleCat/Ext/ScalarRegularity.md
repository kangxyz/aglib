# Scalar regularity on Ext

`ModuleCat.isSMulRegular_ext_of_subsingleton_quotSMulTop` takes a commutative
ring `S`, the actual modules `M N : ModuleCat S`, a scalar `a : S` regular
on `M`, and a natural degree `q`. If
`Ext (ModuleCat.of S (QuotSMulTop a M)) N q` is zero, the same scalar is
regular on `Ext M N q` with its native `S`-module structure.

The source quotient is the original `QuotSMulTop a M`. The proof uses
`M.smulShortComplex a` and the short exactness supplied by the given
regularity of `a` on `M`. In its contravariant Ext sequence, a class killed
by precomposition with the original scalar endomorphism comes from Ext
of that quotient. The latter group is zero by hypothesis.

The equality between this precomposition and scalar multiplication is
proved using `Ext.mk₀_smul`, `Ext.smul_comp`, and `Ext.mk₀_id_comp`.
Thus the argument retains the original maps and native action. It uses
`Ext.contravariant_sequence_exact₂`, with no connecting-map sign or trace
choice. The statement includes degree zero.

There are no local, Noetherian, finite, projective or free hypotheses on
the ring or modules. The source uses the installed standard-size
`Ext.{u}` for `ModuleCat.{u} S`, where `S : Type u`.

The current consumer is regularity of the actual normal-surface canonical
stalk. That consumer must still derive the quotient-Ext vanishing from its
genuine local geometry and transport this result through the original
stalk comparisons. This module supplies neither canonical-module
regularity as an assumption nor the later surface-to-curve canonical
restriction or counit comparison.
