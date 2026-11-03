# The actual differential-trace cokernel and its generic rank inputs

Source: [Cokernel.lean](Cokernel.lean).

Retain the original normal Noetherian domain A, its fraction field K,
the finite purely inseparable degree-p extension L/K, and the displayed
coefficient ring Λ and scalar towers. Put B=integralClosure A L. For
positive degree r=n+1, the map is the original
`integralClosureTraceTranspose`, with target

```text
H = Hom_A(B, Hom_A(Hom_A(exteriorPower A r Ω_(A/Λ), A), A)).
```

The raw base exterior module and B are finite over A. No finiteness or
reflexivity of the raw source is assumed. The two original duals are finite
by Noetherianity, and then the original Hom from finite B is finite. Thus
H and the actual quotient H/range(c_B) are finite.

The actual generic-bijectivity theorem for c_B supplies surjectivity through
its original exterior and Hom localization maps. The native equivalence
with `LocalizedModule.map` transfers this to the canonical localization of
the same map. Localization of the actual cokernel is therefore zero.
Every cokernel element is killed by a nonzero denominator. The finite
torsion annihilator theorem combines finitely many such denominators into
one fixed s≠0 with

```text
s • x = 0  for every x in H/range(c_B).
```

Equivalently every original target value has an original source preimage
after multiplication by s. This statement makes no linear choice of
preimages. It does not introduce a generic isomorphism or trace-membership
oracle: generic surjectivity is derived from the actual differential trace.

The generic data can be supplied in either of two concrete forms:

* `finrank_K Ω_(K/Λ)=n+1` and the original `D_(K/Λ)(a)≠0`;
* equal actual dimensions `finrank_K Ω_(K/Λ)=finrank_L Ω_(L/Λ)=n+1`.

In the second case, the original Kähler presentation proves da≠0. If da
were zero, its decomposition would add one free direction and make the
upper dimension n+2. For nonzero da, extend that original vector to a
K-basis and put it last. The basis determinant shows that the actual top
wedge η∧da is nonzero. Quotient rank, actual scalar extension and the existing
Kähler decomposition give the upper rank. Native exterior dimensions then
give the two generic lines consumed by the original transpose theorem.

All basis choices occur over the original generic fields. No integral
wedge is required to generate the coefficient bidual, and no scalar in A
is assumed a unit. These arguments include characteristic 2 without an
invertible factorial or 2. They impose no absolute finite-p-rank condition.

The displayed relative rank conditions require their own applicable source.
The separating differential-basis theorem applies through a rational
fraction field and a separable field extension; a purely inseparable
extension of the fraction field of a different expanded base requires its
own rank argument. Pure degree p alone does not imply da≠0 relative to an
arbitrary fixed Λ.

Sheaf and reflexive-source assembly, native coinduction packaging,
proper/global trace identification, and geometric H1 bounds are separate
consumers of this algebraic result.

The direct `..._coker_of_basis` entrance retains a positive finite basis of
Ω(A/Λ) and nonzero integral df. Its generic rank and nonzero differential
are proved by unchanged-base fraction localization. The raw exterior finite
instance is derived inside this endpoint from the supplied finite basis via
`finite_exterior_of_basis`, rather than imposed as an additional hypothesis.

## Integral basis consumer

`exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_basis`
derives the finiteness of the actual exterior module from its input basis using
`finite_exterior_of_basis`; it does not require that finiteness separately.
The underlying trace derives finite presentation over the Noetherian ring and
localizes the same exterior module over the same coefficient ring.
`exists_singleSeries_fraction_basis` supplies a positive-rank integral basis
for a non-pth-power formal series over the expanded coefficient series ring.
Writing its positive rank as `n + 1` supplies this consumer's basis;
`finrank_fraction_of_basis` and `fraction_D_ne_zero_of_basis` then derive the
two generic differential inputs without replacing the coefficient base.
The normalization finiteness, original degree-p field presentation, and normal
Noetherian domain hypotheses remain genuine geometric inputs.

The literal cokernel conclusion is packaged by
`LinearMap.HasNonzeroCokernelAnnihilator`, whose definition is exactly
`∃ s ≠ 0, ∀ x : V ⧸ f.range, s • x = 0`. This is a proposition about
Mathlib's original quotient, not another quotient realization. It lets the
native quotient module dictionary be fixed at the abstract linear-map boundary.
The basis endpoint also exports
`exists_nonzero_smul_mem_range_integralClosureTraceTranspose_of_basis`, deriving
one fixed nonzero original-ring scalar with every target functional in the
image after multiplication. Neither endpoint requires a B-action on the bidual.

Direct consumers: [RingTheory/Kaehler/PureDegreePTrace/CompleteRegularEntrance](CompleteRegularEntrance.md).
