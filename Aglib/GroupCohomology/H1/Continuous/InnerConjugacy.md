# Inner conjugacy on continuous first cohomology

`InnerConjugacy.lean` uses `GroupCohomology.ContinuousH1.InnerConjugacy` and preserves the source family's actual maps.

Inner conjugation on the group, together with the inverse action on coefficients, changes a
continuous cocycle by the explicit principal cocycle of -(g⁻¹ • c(g)). The action and group
operations have their stated continuity hypotheses. This proves identity of the resulting map
on the actual continuous H1 quotient.

Source: `R5Lab.Aglib.GroupCohomology.H1.InnerConjugacy`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7a0e28f3f63a56979b8c06d362956695198ffeb969e72a42536a324b64ceb75d`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
