# Regular open subsets of semilocal normal surfaces

`PrimeSpectrum.regularLocus` uses the actual prime localizations. The file proves
that regularity is stable under generalization, and that a domain's generic point
is regular. It introduces `IsJ0Ring` as Noetherianity together with a nonempty
open subset of that locus. For a Noetherian domain this is equivalent to the
existence of a nonzero element whose away localization is a regular ring.

For a normal Noetherian domain of dimension at most two, every nonmaximal prime
has height at most one. Its localization is a field or a DVR and is therefore
regular. If `MaximalSpectrum R` is finite, the singular locus is a finite set of
closed points, so its complement is open and contains the generic point. This
proves `IsJ0Ring.of_isIntegrallyClosed_of_dimLE_two` without assuming openness.

`Module.Finite.maximalSpectrum_finite_of_finite_base` supplies semilocality for
finite algebras over a semilocal base. Maximal ideals contract to maximal ideals
and inject into the finite union of the spectra of the actual residue fibres.
Those fibres are finite dimensional over fields and hence Artinian.

[J2Criterion](J2Criterion.md) uses this J-0 theorem for the finite normal
models of the actual prime quotients in
[Stacks Lemma 15.48.6 (07PC)](https://stacks.math.columbia.edu/tag/07PC).
That consumer supplies the prime-quotient spreading and J-0 to J-1 steps,
then uses [finite purely inseparable constants](../../FieldTheory/SeparablyGenerated/FinitePureConstants.md)
to obtain J-2 for semilocal Nagata rings of dimension at most two.
The present regular-locus theorem alone does not assert J-2 for an
arbitrary Nagata ring.
