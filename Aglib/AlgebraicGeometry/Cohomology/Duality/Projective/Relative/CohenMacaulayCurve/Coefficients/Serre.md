# Original line-coefficient curve Serre duality

[Serre.lean](Serre.lean) keeps the actual field `k`, specified module
`V : ModuleCat k`, closed embedding `j : C ⟶ ProjectiveSpace k ι`, structural
scalar map `cmCurveSerreScalar k ι j`, and native Ext/cohomology objects.
The canonical module is exactly
`cmCurveCoefficientCanonicalModule k ι j n V`, the own degree `(n : ℤ)-1`
homology of the original closed right adjoint applied to the actual ambient
coefficient of `tilde V`.

The conditions are `[Module.Finite k V]`, `Module.finrank k V = 1`,
`e : ι ≃ Fin (n+1)`, `1 ≤ n`, and the original closed-stalk parameter
condition: at every closed point there is a stalk element in the maximal
ideal, regular on that stalk, whose principal ideal has maximal radical.
The source may be nonreduced over an arbitrary field. A source module `F`
is coherent in the native `affineLocallyFiniteType C F` sense.

`cmCurveCoefficientSerreDuality` gives, for natural `r ≤ 1`, the linear
equivalence

    Ext_C^r(F, W_C(V)) ≃ₗ[k] (H^(1-r)(C,F) →ₗ[k] V).

Its forward-map theorem is literal equality with
`cmCurveCoefficientSerreCohomologyAddEquiv`. This additive comparison is the
same six original maps: own-homology purity input, original relative
closed-embedding Serre map at `tilde V`, original affine derived Hom,
native single reindex, native injective-target homology, and original
resolution-section transport with the native tilde/global-sections
coefficient isomorphism. The index is genuinely `r+(n-1)` with the explicit
lower bound on `n`; no integer degree is silently truncated.

The proof upgrades the actual additive comparison by proving its equality
with the positive Yoneda pairing and the same coefficient-valued trace.
`cmCurveCoefficientSerreCohomologyAddEquiv_pairing` is the original-class
anchor. Its proof uses the original derived Serre composition, the proved
affine structural evaluation, and the existing original structural-unit
class. Compatibility and perfection are conclusions, not new hypotheses.
The unsigned native Ext product and installed shifts remain in the source
and Yoneda laws. `cmCurveCoefficientSerreDuality_precomp` uses the original
sheaf-cohomology map; `cmCurveCoefficientSerreDuality_zero` states the
consumer formula `D_F^0(a) = τ_V ∘ H¹(a)` for an actual morphism `a : F ⟶ W`.

`cmCurveCoefficientSerreTrace` is the actual linear map `H¹(W) → V` obtained
from the same original Serre arrow, precomposed with the original structural
derived unit and evaluated on the original section one. It does not orient
`V` as `k`. `cmCurveCoefficientSerreDuality_one` proves the same degree-one
comparison evaluates at structural one to this trace. If the genuine map
`cmCurveSerreStructuralH0Map k ι j` is bijective, the same trace is bijective
and `cmCurveCoefficientSerreTraceEquiv` packages it without changing its
forward map. Evaluation of `Hom_k(H⁰(O_C),V)` uses the honest structural map;
no basis of `V` or `H¹(O_C)=0` condition is used.

The standard native Ext universe is explicit as `u+1`; the coefficient is
`ModuleCat.{u} k` and the original cohomology carrier is in `u+1`. No change
of universe or assumed definitional identification is inserted.

The focused [affine provider](Serre/Affine.md) contains the arbitrary-module
coefficient normalization and structural-unit comparison. It has no finite,
rank-one or CM assumption. The parent uses the existing coefficient
concentration and generic native single/shift machinery; it does not
recreate their implementations.

Native status: complete authored source candidate, awaiting the principal's
ordinary incremental compiler graph. The older unit-coefficient passes do
not supply V-valued coverage. Curve generation, the hyperplane and degree
adapters, coefficient base change, and the surface/RDP continuation retain
their separate implementation boundaries.
