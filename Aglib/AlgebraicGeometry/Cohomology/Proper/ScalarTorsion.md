# Uniform scalar torsion on original proper birational models

This module bounds scalar torsion on the original cohomology of proper
birational models using the actual scalar cokernel, total divisor and
normalization maps described below.

`exists_uniform_structureH1_scalarTorsion_length_bound` states that, for a
normal Noetherian Nagata local domain `A` of dimension two and a nonzero
`a : A`, there is `N : ℕ` such that the original `a`-torsion in `H¹(X,O_X)`
has length over `A` at most `N` for every supplied proper dominant morphism
`f : X ⟶ Spec A` from a normal integral scheme whose original function-field
map is an isomorphism. The action on the literal `Sheaf.H` is always induced
by `f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom`.

The source also exposes the explicit bound
`structureH1_scalarTorsion_length_le_normalizationColength`. For any nonzero
`c` in the maximal ideal, it bounds original `c`-torsion by the length of
`B / range(A → B)`, where `C = A/(c)` and
`B = integralClosure C (FractionRing C)`. This inequality does not itself
require that `C` be reduced. Reducedness is used to make this fixed colength
finite when the final theorem chooses `c` from the reduced-principal-cover
theorem.

The construction retains the following maps and equations.

1. The original scalar cokernel of `c : O_X → O_X` is identified with the
   pushforward of `O_Z` for the literal total divisor
   `Z = X ×[Spec A] Spec C`. Its quotient projection becomes the original
   structure-module map of the closed immersion `Z → X`.
2. A parameter `g` satisfies `radical(c,g) = maximalIdeal A`. The image of
   `g` is a non-zero-divisor in `C`, by the height-one associated-prime
   theorem for a principal quotient of a normal domain. The proper
   birational map is an isomorphism over `D(g)`. The actual pullback square
   identifies the punctured total divisor with `Spec C_g`, preserving its
   projection to `Spec C`.
3. Proper coherent H⁰ finiteness makes the original structural map
   `C → Γ(Z,O_Z)` finite. Original restriction, the preceding chart, and the
   canonical injection `C_g → FractionRing C` therefore give a map
   `Γ(Z,O_Z) →ₐ[C] B`. Each image is integral because the source algebra is
   finite. No injectivity of this map on all global sections is asserted.
4. Its composite with the original scalar-cokernel comparison is `A`-linear.
   The actual structural base-change square proves the original constants
   equation. Injectivity of `C_g → FractionRing C` proves that comparison-zero
   implies zero under the original presheaf restriction to the puncture.
5. `structureH1_puncturedPresheafRestriction_injective_of_isNagata` transports
   the existing V1 geometric injection to precisely the presheaf map used by
   `Exact/KernelLength`. That existing diagram theorem yields the displayed
   colength bound. Nagata finite normalization and original-base normalization
   colength make it finite for reduced `C`. The reduced-principal cover
   gives `a ∣ c^r`; the length inequality for torsion by powers gives
   the final bound `r * length_A(B / range(A → B))`. Units have bound zero.

The theorem imposes no source dimension, projectivity or regularity condition,
no complete-base or coefficient-field condition, and no resolution-existence
premise. The total divisor is not replaced by a proper transform. No finite
proper-transform theorem or equality `C_g = FractionRing C` is used.
This construction needs no new GF2 or source-dimension calculation. The reused
V1 theorem still depends transitively on GF2.

The lower public theorem `structuralCoefficients_finite_of_proper` only needs
a proper morphism over a Noetherian affine base. The full comparison uses the
existing geometric and algebraic suppliers, including the original V1 theorem,
`Exact/KernelLength`, `LocalRing/ReducedPrincipalCover`, `Length/Torsion`,
`Nagata/Normalization`, and `IntegralClosure/Colength`.
