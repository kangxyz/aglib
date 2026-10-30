# Curve cohomology and restriction

This family uses original `Sheaf.H` and the literal closed fibre to prove
all-degree finite-constant restriction surjectivity for finite schemes over
the native projective line of a strictly henselian local ring. Coefficients
have value universe `u+1`; source and target Ext universes remain independent.

[GenericDirectImageDivisibility](GenericDirectImageDivisibility.lean) retains
independent source and target Ext universes for the original generic
direct-image scalar bijectivity theorem; its ordinary cohomological statement
requires no derived-category model.

## Strictly local endpoint

[StrictlyLocalComparison](StrictlyLocalComparison.lean) proves
`finite_projectiveLine_constantRestriction_surjective`. For a commutative
henselian local ring `R` with separably closed residue field, finite
`f : Y ⟶ ProjectiveLine.projectiveP1 R`, finite abelian `A : Type u`
and every `q : ℕ`, the original map

```lean
constantRestriction A
  (pullback.fst (f ≫ ProjectiveLine.structureMap R)
    (LocalRing.residueSpecMap R)) q
```

is surjective. It is original cohomological pullback followed by the native
constant-coefficient transport. The endpoint adds no Noetherian, excellence,
completeness, flatness, finite-presentation, normality, reducedness, smoothness
or coefficient-order premise. H0/H1 are the existing bijections; higher
injectivity is not asserted. [The module guide](StrictlyLocalComparison.md)
records the exact hypotheses and proof route.

## Reusable inputs

| Sources | Actual contribution |
| --- | --- |
| [ConstantRestriction](ConstantRestriction.lean), [LowDegree](LowDegree.lean) | The original constant-coefficient map and its H0/H1 normalization. |
| [ResidueFiber](ResidueFiber.lean), [ResidueFiberDimension](ResidueFiberDimension.lean) | The literal finite closed fibre maps to the residue-field projective line and is a proper finite-type scheme of dimension at most one, including empty and nonreduced fibres. |
| [CoefficientNaturality](CoefficientNaturality.lean), [SplitCoefficients](SplitCoefficients.lean), [PrimePowerReduction](PrimePowerReduction.lean) | Original coefficient squares and actual finite-abelian primary decompositions, including exponent-zero factors. |
| [PrimeToCharacteristicVanishing](PrimeToCharacteristicVanishing.lean) | For finite-type dimension-at-most-one schemes over a separably closed field and a positive invertible level: original multiplicative power bijectivity in degrees at least two, Picard-boundary surjectivity, and root vanishing above degree two. [The guide](PrimeToCharacteristicVanishing.md) retains all conditions. |
| [PrimeToCharacteristicDegreeTwo](PrimeToCharacteristicDegreeTwo.lean) | Actual Picard lifting, the original Kummer square and constructed henselian root coordinates combine with that boundary theorem. |
| [CharacteristicPrimaryGeometry](CharacteristicPrimaryGeometry.lean) | The actual arbitrary-quasicoherent comparison, original scalar/Frobenius maps and Artin–Schreier give the characteristic-primary target vanishing used by the final comparison. |
| [GenericArtin](GenericArtin.lean), [FiniteClosedSupport](FiniteClosedSupport.lean) | Actual component-generic Artinian local rings and original finite-support coefficients; local rings are retained before the legitimate root-coefficient residue comparisons. [Finite support](FiniteClosedSupport.md) records its maps and arbitrary-coefficient acyclicity. |

The [quasicoherent family](../QuasiCoherent/README.md) owns affine acyclicity
and global Zariski comparison. The [field family](../Fields/README.md) owns
original field cohomology, finite-monodromy reduction and arbitrary purely
inseparable root comparison. Artin–Schreier is used on the characteristic-p
fibre, without asserting such a sequence on a mixed-characteristic total
scheme. Root coordinates are constructed rather than supplied as markings.

The stated curve module is mathematically complete. General torsion proper
base change, its proper-surjective descent and the unbounded six-operation
assembly remain separate work.
