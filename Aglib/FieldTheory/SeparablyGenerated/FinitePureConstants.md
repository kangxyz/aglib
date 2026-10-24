# Finite purely inseparable constants

This companion records the finite-constant field input to the
[J-2 criterion](../../RingTheory/Excellent/J2Criterion.md). The Lean file
constructs the constants, retains the actual compositum interfaces, and
identifies the original tensor map's range and kernel.

## Statement and fixed input

Let `k`, `K`, and `Ω` be fields, with compatible inclusions `k → K → Ω`,
where `Ω` is perfect and `K/k` is finitely generated. No
perfectness or finiteness of a p-basis of `k` is assumed. There exists a
subfield `E ⊂ Ω` containing the given image of `k` such that:

1. `E/k` is finite and purely inseparable.
2. The literal compositum `N = E · image(K) ⊂ Ω` is separably generated over `E`.
3. With the original inclusion `K → Ω` factored through `N`, `N/K` is finite
   and purely inseparable.
4. The multiplication map `K ⊗[k] E → Ω` has image `N` and kernel its
   nilradical. Consequently its reduced quotient is this same field `N`.

The J-2 application takes `Ω = AlgebraicClosure K`, with the original
`k`-action induced through `K`. The native theorem only requires perfectness
of `Ω`. Algebraicity of all of `Ω/k` is neither assumed nor generally true.
The consumer is the field step in Stacks 07PC used by the general-surface
J-2 argument.

## Finite coefficient descent

Let `P` and `M` be subfields of a field `Ω` containing `k`. Every element of
their compositum `PM` belongs to `k(c)M` for some finite set `c ⊂ P`.
Indeed an expression formed by field operations uses only finitely many
elements of `P`; elements from `M` may all be retained. Taking the union of
the finite sets gives one such `c` for any finite family of elements.

Now suppose `x ∈ Ω` is separable algebraic over `PM`. Its minimal polynomial
has finitely many coefficients, each in `PM`. Choose one finite `c ⊂ P`
containing enough constants to express all these coefficients over `M`.
The same polynomial is then a polynomial over `k(c)M`. It is still separable:
separability of a polynomial over a field is reflected by extension of its
coefficient field. It still vanishes at the same ambient element `x`.
The minimal polynomial over `k(c)M` divides it, so `x` is separable over
`k(c)M`. This proves the precise finite-descent assertion without presuming
that arbitrary inseparability data are finite.

The Lean declarations `exists_finset_left_of_mem_sup`,
`exists_finset_left_of_finset_mem_sup`,
`isSeparable_of_minpoly_coeff_mem`, and
`exists_finset_left_of_isSeparable_sup` encode these assertions with actual
intermediate fields of `Ω`. Their use of `IsSeparable` concerns algebraic
elements over the field containing the transcendence parameters.

## Construction of the constants

Inside the given `Ω`, let `P` be the relative perfect closure of `k`.
In positive characteristic p it consists of elements whose p-power of some
order is in `k`; in characteristic zero it equals `k`. The field `P` is
perfect because `Ω` is perfect, and `P/k` is purely inseparable.

Choose field generators `a₁,…,aₘ` of `K/k`, viewed through the original
embedding in `Ω`, and set `L = PK = P(a₁,…,aₘ)`. The finite-generation
theorem over a perfect field gives a finite separating transcendence basis
`t₁,…,tᵣ` of `L/P`. Thus the `tᵢ` are algebraically independent over `P`,
and `L/P(t₁,…,tᵣ)` is finite separable algebraic.

Apply finite compositum support to the `tᵢ ∈ PK`. It gives a finite set
`c₀ ⊂ P` such that every `tᵢ` lies in `k(c₀)K`. For each generator `aⱼ`,
apply the preceding separable-descent assertion with the two fields `P`
and `k(t₁,…,tᵣ)`. This gives a finite `cⱼ ⊂ P` such that `aⱼ` is separable
algebraic over `k(cⱼ)(t₁,…,tᵣ)`.

Let `c` be the union of these finitely many finite sets and put `E = k(c)`.
Since every element of `c` is purely inseparable algebraic over `k`, the
extension `E/k` is finite and purely inseparable. The field
`N = EK = E(a₁,…,aₘ)` contains all `tᵢ`. Each `aⱼ` remains separable
algebraic over the larger field `E(t₁,…,tᵣ)`, because separability of an
algebraic element is preserved on enlarging the base field. Therefore
`N/E(t₁,…,tᵣ)` is finite separable algebraic. The `tᵢ` remain algebraically
independent over `E ⊂ P`, so they form a separating transcendence basis
of `N/E`.

All choices were made inside the original `Ω`, and all field operations
use its operations. In particular the map `K → N → Ω` is the original map.
Writing `E = k(c₁,…,cₛ)` also gives `N = K(c₁,…,cₛ)`. Each `cᵢ` is purely
inseparable over `K`, using the same power equation over `k ⊂ K`.
Consequently `N/K` is finite and purely inseparable. This completes the
mathematical construction.

## Tensor image and the model fraction field

Let `μ : K ⊗[k] E → Ω` send `a ⊗ b` to the product of the two specified
images. Its image is a finite-dimensional `K`-algebra, since `E/k` is
finite, and it is a domain as a subring of `Ω`. It is a field: multiplication
by a nonzero element is an injective endomorphism of a finite-dimensional
`K`-space and therefore surjective. Its image contains `K` and `E` and is
contained in their compositum, hence equals `N`.

In positive characteristic choose one exponent q = pⁿ that sends all of
`E` into `k`; such an exponent exists by choosing a finite field-generating
set of the finite purely inseparable extension. For any tensor element z,
the Frobenius identity shows `z^q ∈ K ⊗ 1`. If `μ(z) = 0`, the injectivity
of the original `K → Ω` forces `z^q = 0`. Conversely every nilpotent is
killed by a map to a field. Thus `ker μ` is the nilradical. In characteristic
zero `E = k`, so the same conclusion holds directly. Neither argument
replaces the specified map by an unrelated embedding.

For the J-2 consumer, suppose domain maps `S → Ω` and `D' → Ω` have fraction
fields equal to the specified images of `K` and `E`. Let `S'` be the image
of `S ⊗_R D' → Ω`. The smallest subfield of `Ω` containing `S'` contains
both `S` and `D'`, hence both of their fraction fields. Conversely `S'`
lies in `N`. Therefore this smallest subfield is exactly `N`, and the
fraction-field map of `S'` identifies its fraction field with this `N`.
This statement depends on the actual commuting maps and on the asserted
fraction-field properties of `S` and `D'`; it does not supply those
properties for an arbitrary replacement model.

## Primary source correspondence

[Stacks Lemma 10.45.3, tag 030R](https://stacks.math.columbia.edu/tag/030R)
has precisely the finite-generation hypothesis and permits the actual
compositum and reduced tensor product. Its word “separable” has the general
meaning in [Definition 10.42.1, tag 030O](https://stacks.math.columbia.edu/tag/030O).
For a finitely generated extension it gives the separating basis required
above. It must not be translated as `Algebra.IsSeparable E N`.

The source route uses [Lemma 10.42.4, tag 04KM](https://stacks.math.columbia.edu/tag/04KM),
then [tag 030X](https://stacks.math.columbia.edu/tag/030X) and restriction
in [tag 030P](https://stacks.math.columbia.edu/tag/030P). The current proof
of 04KM refers to the generalized separable-polynomial clause (2) of
[tag 031V](https://stacks.math.columbia.edu/tag/031V). The section's 2013
correction discusses why minimal-polynomial irreducibility after base
change cannot be presumed. The current clause (2) avoids that presumption.
The recorded source correspondence uses the corrected statement and proof
inspected on 2026-10-24. The linked historical commit was not checked.
This source correspondence is distinct from the native Lean construction.

## Native interface and consumer boundary

`Algebra.FinitePureConstants.exists_constants` assumes fields `k`, `K`, and
`Ω`, the three given algebra structures with `IsScalarTower k K Ω`,
`Algebra.EssFiniteType k K`, and `PerfectField Ω`. The fields may lie in
different universes. Perfectness is required only of the ambient field,
so the theorem applies to the specified `AlgebraicClosure K` with arbitrary
imperfect `k`. It returns an actual `E : IntermediateField k Ω` with
`FiniteDimensional k E`, `IsPurelyInseparable k E`, and
`Algebra.IsSeparablyGenerated E (compositum k K Ω E)`.

The `compositum` is exactly
`IntermediateField.adjoin E (Set.range (algebraMap K Ω))`.
`originalMap` factors the original `K → Ω` through this field, and
`originalAlgebra` installs that same map as its `K`-action.
`original_isScalarTower` and `ambient_isScalarTower` give the corresponding
commuting towers. `compositum_le_iff` gives the least-field property;
`compositumSwap` identifies this same embedded field with `K(E)` while
preserving its original `K`-action.

After installing the returned finiteness and pure-inseparability witnesses,
`compositum_finiteDimensional` and `compositum_isPurelyInseparable` give
the finite purely inseparable extension `N/K` under `originalAlgebra`.
The original field's essential finite type composes with this finite
extension and then extends scalars to give `Algebra.EssFiniteType E N`.

`tensorMap` is the specified multiplication map `K ⊗[k] E → Ω`.
`tensorMap_range` identifies its image with the literal compositum as a
`k`-subalgebra, using algebraicity of `E/k`. `tensorMap_ker` identifies its
kernel with the nilradical, using pure inseparability of `E/k`.

The proof uses Mathlib's relative perfect closure and perfect-field
separating-basis theorem, then the finite coefficient lemmas above.
`HasAmbientSeparatingFinset` retains the actual ambient inclusion while
transporting the basis. Its finite-subtype range equalities are proved
before forming coefficient fields, and separability witnesses are
transported explicitly along those equalities.

These statements supply the field input to 07PC. The J-2 consumer constructs
the actual integral and tensor-image ring models, proves their finiteness
properties, and applies the fraction-field comparison under the explicit
model premises stated above.
