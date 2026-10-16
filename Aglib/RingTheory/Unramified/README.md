# Rigidity of unramified algebra maps

[Rigidity](Rigidity.lean) extends the native `Algebra.FormallyUnramified` API. Its local-target theorem `eq_of_comp_residue_eq` states that two algebra maps from an essentially finite-type formally unramified algebra into any commutative local target are equal when their actual `IsLocalRing.residue` maps agree pointwise. The local target may have zero divisors; no domain, reducedness, Noetherianity or nilpotence hypothesis is added.

`eq_of_comp_residue_eq_of_mem_subalgebra` applies to maps into a common ambient commutative algebra whose values lie in a specified local subalgebra. It retains the given membership proofs, compares the actual residue classes of those subtype values, and uses the actual `codRestrict` maps.

The local proof evaluates the finitely generated idempotent diagonal ideal through the tensor-product lift of the two maps. Residue equality puts the evaluated idempotent in the maximal ideal. Its complement is a unit, so the idempotent vanishes and the maps agree. Essential finite type and formal unramifiedness are both retained.

The existing `eq_of_comp_mkQ_eq` has its original statement and proof: `R`, `A` and `B` are commutative rings in independent universes with their supplied `R`-algebra structures; `A` is essentially of finite type and formally unramified, `B` is a domain, and `Q` is prime. Equality modulo the actual `Ideal.Quotient.mk Q` gives equality of the maps. Its tensor-separator proof uses cancellation in the domain. No Noetherian hypothesis or nilpotence condition on `Q` is imposed. Mathlib's nilpotent-ideal `ext` and `lift_unique` remain separate APIs.

The precise import is `Aglib.RingTheory.Unramified.Rigidity`; its direct lower imports are `Mathlib.RingTheory.Unramified.Finite` and `Mathlib.RingTheory.LocalRing.ResidueField.Basic`. Original DVR-inertia and point-specialization consumers remain downstream. The existing isolated `AglibTest.UnramifiedRigidity` client covers the domain/prime statement with independent ring universes.
