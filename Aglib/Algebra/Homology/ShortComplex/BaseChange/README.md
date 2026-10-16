# Pointwise canonical homology base change

[The parent leaf](../BaseChange.lean) proves
`ShortComplex.lTensor_cycles_exact_of_epi_homologyBaseChangeMap`.
Surjectivity of the original scalar-extension homology mate forces
exactness of the actual cycle inclusion and outgoing differential after
tensoring with that algebra. This uses coefficient naturality of the
unchanged adjunction mate; no flatness or finiteness is assumed.

[Projective](Projective.lean) proves
`ModuleCat.homologyBaseChangeMap_isIso_of_projective_cokernel` for every
ring map. Projectivity of the final term and the original outgoing
cokernel suffices. The first two terms need not be finite or projective.
The native generalized inverse supplies pointwise kernel preservation;
the left adjoint is not assumed exact.

[Local](Local.lean) proves
`ShortComplex.epi_residue_homologyBaseChangeMap_iff_free_cokernel` over a
commutative local ring. For a finite middle term and finite flat final
term, the original residue-field homology mate is surjective exactly when
the original outgoing cokernel is free. The first term need not be
finite, and Noetherianity is not assumed.
`homologyBaseChangeMap_isIso_of_epi_residue` then proves the original mate
invertible after every ring map, including nonflat maps and target rings
in a larger universe. Its explicit maximum-universe arguments retain the
native extension/restriction adjunction's carrier bound.

[LocalFreeness](LocalFreeness.lean) adds
`free_homology_iff_free_opcycles_of_epi_residue`. Under the original
residue-field surjectivity condition, the actual homology is a retract of
the finite opcycles and hence is finite. It is free exactly when those
opcycles are free. The proof uses the original right-homology-data arrow
and native projectivity comparisons, retaining the same weak hypotheses.

The [cochain specialization](../../CochainComplex/BaseChangeCriterion.lean)
identifies these opcycles with the actual outgoing cokernel in the
predecessor degree. It gives the usual adjacent-degree residue-surjectivity
criterion for freeness of original homology. No bound on the complex is
required. External public consumers cover independent universes and all
integer degrees; axiom inspection reports only the standard three axioms.

These are degreewise algebraic criteria on the actual native short complex.
A geometric application must identify its original cohomology and
base-change maps with those of an actual universal complex; these lower
results alone do not discharge a proper or Grauert theorem family.

[Grauert](Grauert.lean) proves the constant-dimension local criterion over
a reduced local ring. The original two cokernel fibre dimensions become
locally constant because they are upper semicontinuous and their sum is
locally constant. Reducedness then makes the two finite cokernels free;
original homology is free and its unchanged native mate is invertible
after every ring map. A finite middle and a finite flat final term suffice,
with no Noetherianity or first-term finiteness. The global numerical
cokernel-dimension implication does not require reducedness or locality.
The [cochain interface](../../CochainComplex/Grauert.lean) and its actual
projective-cohomology consumer retain these same objects and maps.

[Grauert/Global](Grauert/Global.lean) removes the local-ring assumption:
over a reduced ring, local constancy of the native fibre-homology dimension
makes the original homology projective and its original mate invertible
after every ring map. The first term is finite, the middle term finitely
presented, and the final term finite projective; boundedness and
Noetherianity are not required.

[Locus](Locus.lean) supplies a basic-open neighbourhood of every point in
the original outgoing cokernel's free locus. After localization there,
the unchanged native homology mate is invertible for every further ring
map, including target rings in an independent universe. A finite middle
term and finitely presented projective final term suffice. Identification
of this locus with original residue-field surjectivity remains a separate
normalization step.
