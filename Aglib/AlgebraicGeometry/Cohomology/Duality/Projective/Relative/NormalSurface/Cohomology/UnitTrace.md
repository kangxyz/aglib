# Original canonical H0, dual unit and section trace

[UnitTrace.lean](UnitTrace.lean) identifies the actual TwoLayer dual unit on
canonical degree-zero cohomology with the existing chosen-embedding trace
on its literal section. The actual A-linear cohomology equivalence and the
original A-linear unitMap give the cohomology-side map. The output carries
native coinduction, with scalar action by multiplication on the original
argument of the functional.

The inputs retain the original closed embedding over R, the integral normal
scheme X of dimension at most two, the original canonical object and its
homology-normalized reconstruction, the actual structural triangle through
g:X→Spec A, the actual generic field finiteness, and the supplied native
resolutions IX and IR. The ring map sigma:R→A is finite, injective and local;
R is regular local of dimension two and A is a normal Noetherian local
domain of dimension two. The finite-normal theorem discharges
restricted projectivity inside the proofs. The canonical module is not
assumed invertible.

The first normalization is geometric. Original Ext zero maps to its actual
section under Sheaf.H.equiv0. The same canonical reconstruction and native
zero shifts identify the degree-zero source with the section lift.
The original degree-zero Serre map and affine derived-sections comparison
then give `normalSurfaceCohomologyModel_zero_phi0`. That equation keeps the
actual source-factor isomorphisms, Q of the coefficient zero shift, and the
original IR.ι' augmentation visible.

The second normalization uses the original unit. The structural
chain augmentation represents the literal moduleDerivedStructureUnit.
`normalSurfaceDerivedDualHomologyIso_unit` applies native dual-model
naturality to that actual square. Original coinduction/source-single
naturality and the lower coefficient leaf identify its functional in Ext
zero. The same augmentation and zero-shift comparisons cancel, giving
`normalSurfaceDualUnit_model` for the original eta_A and its actual P
source factors. This equation is proved, not received as an input.

The original geometric and algebraic comparisons have the same intermediate
model target. Their original additive inverse cancellation, followed by
these two normalizations, identifies the original unit functional with
existing normalSurfaceSectionsPhi0. The already normalized section
trace/unit equation then proves
`normalSurfaceCohomologyDual_unit_trace`. The theorem
`normalSurfaceCohomologyDual_unit_trace_evaluation` evaluates that same
functional at a and obtains the original base trace of a times the literal
canonical section.

No alternative coefficient, source model, A-to-R ring map, transported
scalar action, whole-derived-sections linearity premise, desired-unit
predicate, or trace-compatibility assumption is introduced. The old
counit and augmentation remain those of the existing chosen-embedding
construction. This leaf proves a normalization for that embedding and
asserts no embedding-independent proper/finite trace identity.

The Ext-zero class equation retains the actual derived universes and
homology carriers. The original canonical and affine zero-shift equations
use typed isomorphisms and composition identities. The final functional
comparison uses the original single-functor preimage, and evaluation uses
the literal module-section carrier with its original A-action.

The coefficient calculation precedes geometric specialization: the original
module chain map computes the Ext-zero class through the coefficient
augmentation. The geometric dual-unit theorem pastes that coefficient
equation with the structural-unit naturality square. Zero-shift cancellation
and bounded-below preimages retain their actual source and target objects.

The chosen-embedding Grauert–Riemenschneider H1 vanishing theorem is
independent of these degree-zero trace normalizations. This module concerns
the exact original unit/section-trace identity.
