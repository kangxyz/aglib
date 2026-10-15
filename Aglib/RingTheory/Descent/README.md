# Effective descent of actual algebras

Import `Aglib.RingTheory.Descent.Basic` for `Algebra.Descent.Datum`: a multiplicative coaction with actual counit and coassociativity. `Datum.invariants` is its equalizer subalgebra, and `Datum.baseChange` is the actual reconstruction map.

`Datum.baseChangeEquiv` requires flatness of the scalar extension. [Canonical](Canonical.lean) gives recovery of an arbitrary original algebra from its canonical datum under faithful flatness. [Morphisms](Morphisms.lean) constructs actual invariant algebra maps, proves reconstruction naturality and transports finite/etale properties under their stated faithful-flat hypotheses. [Overlap](Overlap.lean) converts normalized tensor-overlap isomorphisms satisfying the cocycle equation into coaction data.

[Nilpotent](Nilpotent.lean) constructs formally etale descent data by actual nilpotent lifting. [PurelyInseparable](PurelyInseparable/README.md) applies this to finite purely inseparable field extensions and arbitrary affine base algebras; [FieldOfDefinition](FieldOfDefinition/README.md) builds finite-stage algebra models.

The lower overlap/equalizer results live in [TensorProduct](../TensorProduct/README.md). The internal consumers are canonical recovery, invariant morphisms and finite-field property transport. Source module paths, rather than original application names, identify the focused imports.
