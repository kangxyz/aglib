# Finite etale algebra maps and torsors

These leaves use actual finite etale algebras and their canonical tensor generic
fibers. They introduce no scheme objects.

- [GenericMaps](GenericMaps.lean) places normalization and generic-map extension
  in `Algebra.FiniteEtale.GenericMaps`. An integrally closed base with its
  specified fraction field gives full faithfulness for supplied finite etale
  models; these helpers do not require Noetherianity. Coactions and transporter
  maps extend on those same models. Tensor
  base-change maps are the existing
  `Algebra.TensorProduct.BaseChange` constructions.
- [TorsorExtension](TorsorExtension.lean) uses
  `Algebra.FiniteEtale.TorsorExtension.OriginalTorsorData`: an actual coaction,
  nontrivial generic algebra, and bijective transporter. Under the displayed
  model hypotheses it derives faithful flatness, coaction laws, and transporter
  bijectivity, with the canonical original-algebra generic square.
  Its literal-normalization specialization still requires finite etaleness of
  the normalization.
- [TensorHopf](TensorHopf.lean) identifies the scalar-extended Mathlib Hopf
  counit and comultiplication with these same base-change maps.
- [TorsorPoints](TorsorPoints.lean) derives coefficient-point transitivity from
  the bijective transporter. Coefficient fixedness and one common fixed point
  then imply fixedness of every point.
- [CoefficientInertia](CoefficientInertia.lean) proves that literal inertia
  fixes every point of a finite etale coefficient algebra. It reuses
  `Algebra.FormallyUnramified.eq_of_comp_residue_eq`; completeness, perfect
  residue, and a coefficient fixedness premise are unnecessary.
- [TorsorCocycle](TorsorCocycle.lean) constructs a continuous cocycle from the
  supplied coaction, transporter, point, coefficient mark, and its compatibility
  equations. The class is independent of the point. Zero restriction to an
  actual subgroup gives a fixed point. Continuity comes through the discrete
  algebra-point space; the coefficient topology itself may be nondiscrete.
- [TorsorCoordinates](TorsorCoordinates.lean) packages the specified coefficient
  coordinates and specializes the cocycle and fixed-point results to literal
  inertia. The coefficient topology, action, continuity, and all coordinate
  equations remain explicit. The lower extraction works for the inertia of a
  specified ideal. Reverse-normalization consumers separately supply their
  DVR, closure, prime/lies-over, and finite etale coefficient hypotheses.

The current consumers are normalization torsors and finite-coefficient
cohomology. These constructions do not supply arbitrary torsors, a categorical
group structure from counit/comultiplication alone, or an identification with an
external etale or Galois cohomology class. Reverse-normalization endpoints and
their scheme interpretations belong to the algebraic-geometry consumer.

The source cohort is R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Each leaf records its exact source identity. The lower point supplier is the
generic algebra slice of `Normalization.TorsorInertia`.
