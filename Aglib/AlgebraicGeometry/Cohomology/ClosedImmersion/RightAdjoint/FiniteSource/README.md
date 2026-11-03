# Finite quotient sources in closed-adjoint homology

[Stalk](Stalk.lean) starts with the original quotient immersion
`Spec(R/I) → Spec R`, a quasicoherent ambient coefficient, its supplied
injective resolution and an actual quotient-spectrum point.
It identifies the original closed-adjoint homology stalk with native Ext
over the ambient stalk, retaining the quotient stalk's original scalar
map and coefficient germ. The affine Ext comparisons keep their
Noetherian and selected-Ext hypotheses. The raw section-to-stalk
coefficient map is defined for every ambient module sheaf.

[OpenNaturality](OpenNaturality.lean) gives coefficient naturality of the
installed open-homology comparison in every integer degree.
[ResolutionNaturality](ResolutionNaturality.lean) retains an actual
injective-resolution lift in the original model comparison; this abstract
naturality needs no Noetherianity or quasicoherence.
Its quotient-counit specialization uses a Noetherian affine ring and
quasicoherent coefficients.

Present consumers include [Original derived closed-adjoint homology](Derived.md).
