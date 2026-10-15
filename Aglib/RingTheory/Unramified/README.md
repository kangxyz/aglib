# Rigidity of unramified algebra maps

[Rigidity](Rigidity.lean) extends the native `Algebra.FormallyUnramified` API with
`eq_of_comp_mkQ_eq`. Let `R`, `A` and `B` be commutative rings in independent
universes, with the supplied `R`-algebra structures. If `A` is essentially of
finite type and formally unramified over `R`, `B` is a domain, and `Q` is a
prime ideal of `B`, then two actual algebra maps `A →ₐ[R] B` are equal whenever
their reductions by the actual `Ideal.Quotient.mk Q` agree on every element.

The proof uses Mathlib's tensor separator for an essentially finite-type
formally unramified algebra. Its image under the two maps is nonzero because
the maps agree modulo `Q`; cancellation in the domain gives equality. No
Noetherian hypothesis or nilpotence condition on `Q` is imposed. Mathlib's
existing nilpotent-ideal `ext` and `lift_unique` results remain separate APIs.

The precise import is `Aglib.RingTheory.Unramified.Rigidity`; its only lower
import is `Mathlib.RingTheory.Unramified.Finite`. The original R5 DVR-inertia
consumer remains downstream, together with its application hypotheses. The
isolated `AglibTest.UnramifiedRigidity` client checks this field-free statement
with independent ring universes.
