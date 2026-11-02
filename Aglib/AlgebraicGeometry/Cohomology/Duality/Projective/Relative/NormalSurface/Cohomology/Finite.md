# Canonical sections over a finite cover

[Finite.lean](Finite.lean) constructs the degree-zero comparison

    Hom_X(pi_* O_Y, omega_X) ≃+ Gamma(Y, omega_Y)

from the original coherent-source Serre maps and the actual affine
direct-image comparison. It retains the original source endomorphisms,
structural units, coefficient maps and base traces.

## Inputs and canonical objects

The base R is a regular local domain. The finite map pi:Y→X is the actual
geometric map. The integral normal schemes X and Y have dimension at most
two and genuine closed projective embeddings over R, with their actual
index identifications, dominant base maps and finite generic function-field
maps. Their embedding composites satisfy the original commuting triangle.
The canonical modules are literally the existing
`normalSurfaceCanonicalModule` objects for those embeddings.

The intended geometric application has X regular proper birational over
the original two-dimensional regular local base and Y finite over X. The
comparison uses the stated normal-surface interfaces and requires no
invertibility of the upstairs canonical module.

## Original coherent-source comparison

`normalSurfaceFiniteCoherentSerreMap` sends a native M→omega_X through the
homology-normalized canonical shift, the original closed-embedding Serre
map, its native target normalization, the bounded-below inclusion and the
original affine derived-sections map. Coherence proves bijectivity of that
same forward map. The structure-source specialization is exactly the
existing normalized section Serre map.

For M=pi_*O_Y, finite-morphism pushforward supplies coherence. The actual
`moduleDerivedGlobalSectionsAffineSingleIso` identifies RΓ_X(pi_*O_Y)
with RΓ_Y(O_Y). The equality between their original scalar maps is derived
from the commuting scheme triangle. `normalSurfaceFiniteCanonicalSectionsEquiv`
composes these comparisons to produce the displayed additive equivalence.
Its source-endomorphism theorem retains each ordinary map O_Y→O_Y, so
later scalar multiplication uses the original coefficient action.

## Units, trace and coefficient factorization

The affine coefficient-unit theorem and literal structural section map
prove the actual equation

    eta_X ; RΓ_X(u_pi) ; c.hom = eta_Y,

where u_pi:O_X→pi_*O_Y is the original structure-module unit and c is the
actual affine comparison. Original Serre source naturality then proves
compatibility of the constructed section with these units.

`normalSurfaceFiniteCanonicalSectionsEquiv_trace` evaluates the resulting
native scalar arrow at one and proves

    Tr_Y(E_fin(f)) = Tr_X(section(u_pi ; f)).

Both traces are exactly `normalSurfaceSectionsTraceBase` for the given
embeddings. The source-endomorphism version preserves the inserted
ordinary coefficient map on O_Y explicitly.

`normalSurfaceFiniteCanonicalSectionsEquiv_trace_coefficient` applies this
equation to actual maps pi_*O_Y→L_X→omega_X. It retains L_X as its own
sheaf and the actual map to the canonical module. The input need not
identify those two sheaves.

## Geometric application boundary

For the geometric trace application, the height-one differential construction supplies
the map into L_X. The corrected one-pole construction supplies L_X→omega_X
through the original proper transposition and canonical composition,
retaining its actual counit equation and the original base coefficient
comparison. The remaining ordinary differential-functional identification
must use those maps. Generic comparison can identify ordinary section
maps or functionals into torsionfree targets; the derived equations in
this module are proved separately from the native unit and Serre laws.

This comparison does not construct a general finite exceptional inverse
image, supply embedding independence, substitute field trace for the
differential functional, or supply the remaining geometric trace identification. The actual embeddings
remain geometric inputs for the intended diagram.

## Full coherent upstairs coefficients

`normalSurfaceFiniteCanonicalHomEquiv` supplies

    Hom_X(pi_*M, omega_X) ≃+ Hom_Y(M, omega_Y)

for any actual affine-locally finite-type quasicoherent upstairs coefficient M.
The finite pushforward's coherence is derived, not supplied. Its forward map is
EX followed by the original affine source-Hom transport and EY.inverse; the
normalization theorem states `c.hom ; EY(E_fin(f)) = EX(f)` for that same c.
The geometric, generic-finiteness and structural-triangle inputs are unchanged.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Cohomology/ProperTranspose](ProperTranspose.md).
