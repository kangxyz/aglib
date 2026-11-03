# Conditional original point-blowup canonical evaluation

Source: [PointBlowupGeneration.lean](PointBlowupGeneration.lean).

Import:
`Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.PointBlowupGeneration`.

## Exact conclusion and one conditional input

`normalSurfacePointBlowupCanonicalPullback_epi_of_exceptional_generation`
proves epimorphy of the existing `ordinaryTracePullback b τ`, where `b` is
`RegularPoint.pointBlowdown P x` and `τ` is the existing
`normalSurfaceProperCanonicalTrace` formed from the supplied original global
projective embeddings. Neither map is replaced by a new construction.

Its only generation input is the literal proposition
`Epi (globalSectionsEval (i* (a* ω_Z)))`. Here `a` is the original
`stalkBlowupComparison P x hx` and `i` the full exceptional closed immersion
of the original maximal-ideal blowup of `S = P.presheaf.stalk x`.
There is no reduced exceptional scheme or separately chosen local canonical
module. Generation of this actual coefficient over the original residue field
remains an input to the conditional theorem. Nonregularity is not needed for this conditional theorem;
it will be used to supply the first-power lower bound when the generation
input is discharged.

## Genuine geometric hypotheses

- One original regular local domain `R` of dimension two and one original
  integral locally Noetherian `P`, with closed point `x` of stalk dimension two.
- The same actual ordinary point-blowup source is integral, and both original
  schemes have normal stalks and the honest dimension-at-most-two bounds.
- The centre stalk is genuinely Nagata and satisfies the existing universal
  `NormalModificationH1Vanishing` proposition. It is not assumed complete,
  finite over `R`, Gorenstein, or canonically framed.
- Actual global closed projective embeddings of `P` and its point blowup over
  `R`, their dominant structural maps, original blowdown triangle, finite
  coordinate identifications and original generic-image finiteness witnesses.
- The original `R`-algebra structure on `P.residueField x`, with its literal
  structural residue triangle. Finiteness of this residue is derived inside
  the existing localized coefficient supplier from properness of the original
  structural map. No finite `R → S` premise is introduced.

These normality, integrality, dimension and embedding fields are the existing
canonical-trace telescope, not newly asserted resolution hypotheses. The
eventual unconditional application must derive them from the accepted
original geometry before applying this conditional bridge.

## Proof and unique suppliers

1. The actual blowdown is proper by the native blowup theorem. The accepted
   `DerivedUnit` endpoint uses rationality of the SAME centre stalk and the
   honest source dimension bound to prove the SAME derived unit invertible.
2. `Trace.IsIso` then proves the existing proper canonical trace invertible.
   The standard derived choices remain the existing ones.
3. `Trace.Generation` makes the original local-spectrum pullback of the
   inverse-trace adjoint surjective on sections, through the actual Cartesian
   square, flat base change mate and counit.
4. `LocalizedExceptionalCanonicalVanishing` supplies the literal exceptional
   restriction-unit section lifting for this very `a*ω_Z`. Its accepted
   Cartier restriction, mono and all-power vanishing are reused unchanged.
5. `Generators.Restriction` combines these two surjectivities with the one
   actual exceptional-generation input to prove the original fibre row epi.
6. Canonical finite presentation and actual pullback give finite type of the
   original cokernel. Existing proper-local support detection promotes the
   fibre epi to epi on the original local blowup.
7. On the actual inverse image of the complement of `{x}`, the same blowdown
   restricts to an isomorphism. The existing original trace base-change formula
   expresses the restricted row as isomorphisms and the original counit; the
   latter is invertible along that isomorphism.
8. Accepted `Modules.Locality.PointLocalization` combines these literal local
   and away pullbacks to give epimorphy of the original global row.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupFrame](PointBlowupFrame.md).
