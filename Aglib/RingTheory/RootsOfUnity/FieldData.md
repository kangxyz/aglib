# Finite root data and residue adapters

The additional native leaves preserve the actual roots-of-unity groups and maps.

- `CharacterCompatibility.lean` proves compatibility of the existing finite
  cyclotomic characters with `ZMod.castHom` at divisible nonzero levels in
  characteristic zero.
- `FiniteData.lean` and `PrimeUnits.lean` store the original prime root, root-minus-one
  unit, and prime unit. Lifting needs both value and inverse in an injective
  map's range. The stored units preserve exact prime order under specialization.
- `PrimeToCharacteristic.lean` constructs primitive roots and proves cardinality
  for nonzero levels nonzero in the field; characteristic zero is not required.
- `NativeEmbedding.lean` is the integer-linear restriction of the existing
  `RootCoordinates.rootEmbeddingLinear`, with its primitive-root and actual
  Galois-restriction equations.
- `DVR.lean` lifts positive-level fraction-field roots to genuine DVR units and
  reduces them. It uses the native integer order and angular component.
- `IntegralClosureResidue.lean` uses the actual integral closure and a specified
  maximal prime above the closed point. Root reduction and residue lifting are
  bijective when the level is invertible in the DVR.
- `Specialization.lean` uses the actual complete nonarchimedean residual-Galois
  construction. Positivity and residue-level invertibility give the root
  equivalence, primitivity, action, reduction, and inclusion formulas. Its
  global transport is the existing chosen closure embedding. The chosen residue
  closure equivalence remains visible; choice-independence is not claimed.

The early `Valuation.ResidualGalois` supplier does not import the late
specialization leaf. Existing root carriers, finite characters, closure maps,
and fundamental-group modules remain their canonical providers.
