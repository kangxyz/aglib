# Original degree-zero coefficient and unit normalization

[UnitNormalization.lean](UnitNormalization.lean) retains the native regular
source, coinduced coefficient, supplied R-resolution and its original
augmentation. For the original finite injective local map `sigma : R → A`,
R is regular local of dimension two and A is a normal Noetherian local
domain of dimension two. The actual finite-normal theorem supplies the
restricted projectivity used by the TwoLayer coefficient comparison.

The class calculation starts from the original cycle projection. Exact
scalar restriction and the native Hom comparison carry the same cochain
to its actual cocycle class. Evaluation at one sends the original
coinduced regular augmentation to the original functional followed by
the supplied coefficient augmentation. The existing Hom-to-Ext map
cancels that augmentation and its native zero shift. The resulting
`coinducedRegularHomologyZeroIso_ext_zero` identifies the degree-zero
normalization with the original R-linear functional.

`TwoLayerDual.unitNormalization_eq_regularHomologyZeroIso` derives the
original TwoLayer normalization from the same augmentation. It applies
homology to `coinducedRegularHomAugmentation_evaluation` and cancels
those same isomorphisms. The original single-model comparison is kept
explicitly. `TwoLayerDual.unitNormalization_ext_zero` composes this
identity with the cocycle/Ext calculation on every actual dual class.

No A-to-R ring map, transported A-action, replacement coefficient,
independent compatibility equation or projectivity premise is introduced.
The coefficient's action remains multiplication on the original argument
of its functional. The geometric unit and section trace are consumers
in the separate surface extension; this leaf asserts no embedding-independent
trace statement.

The mapped cycles, homology objects and projection arrows are fixed before
commuting-square composition. The original functional is constructed through
the ModuleCat Hom equivalence, with its value recorded by an application
theorem. The single coefficient component is calculated before evaluating
the original coinduction action at one.

The zero-shift proof distinguishes `CategoryTheory.shiftFunctorZero'` from
the cochain-specific construction and proves the `mk0` equation before
specialization. The Ext comparison uses the original cocycle equation and
the original isomorphism/linear-equivalence constructor identity.

The chosen-embedding Grauert–Riemenschneider theorem proves H1 vanishing of
the literal canonical module under its complete-local, birational and
closed-embedding hypotheses. Its proof uses the degree-one comparison and
residue obstruction independently of this degree-zero normalization.
That vanishing alone does not imply the trace normalization or embedding
independence.

The cycle inclusion uses the original comparison equation and inverse-
isomorphism cancellation. The zero-shift calculation exposes the underlying
shifted cochain, applies its component formula, and uses the inverse
equality-transport identity.

The class-to-Ext proof applies an identity for the original three linear
equivalences. Functor/augmentation cancellation is proved before supplying
the original homology class, source/target isomorphisms and Ext coordinates.
The coefficient, augmentation and scalar action remain the original ones.
