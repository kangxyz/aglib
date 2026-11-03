# Exact residue-point kernel ideals on affine neighbourhoods

`ResiduePoint.lean` compares the native ideal sheaf
`(X.fromSpecResidueField x).ker` with the original affine chart prime at x.
`fromSpecResidueField_ker_ideal` gives exact ideal equality on every actual
affine open containing x. It does not replace the ideal by its radical or
prove only equality of supports.

Quasi-compactness of the original point morphism is proved locally from its
singleton source; it is not a supplied assumption or a new global instance.
Native `Hom.ker_apply` first exposes the actual section-map kernel. The
original restriction from sections on the preimage to sections on the whole
residue-field spectrum is explicitly an isomorphism of rings. Its underlying
injectivity compares the app and appLE kernels without identifying their
section carriers silently. The whole original residue-point section law
then removes only the injective canonical `Gamma(Spec)` comparison and uses
the already proved original evaluation kernel.

`fromSpecResidueField_ker_ideal_basicOpen` restricts this same ideal along the
native section restriction to an actual principal open. It is a thin use of
`IdealSheafData.map_ideal_basicOpen`; the principal open may be empty. Keeping
x in that open is a separate nonmembership condition for the later regular
pair neighbourhood.

Neither theorem requires x closed, X Noetherian, regularity, a dimension
bound, a domain, a field of definition, or a finite-type structure morphism.
The universe and all original scheme, residue, germ and restriction maps
are retained. No alternative ideal-sheaf or field implementation is created.

The complete native owner passed as exact source `910a2687` in own189:
2.0 s leaf, 5.8024 s total, 2538 jobs, exit 0 with no aggregate guard and
the owned process group gone. The preceding own188 failed only the two
reported proposition-local `letI` style checks; the accepted source uses
`let` for those same proofs, with all mathematical statements and maps
unchanged. PointSections eadd and the original FibreIdempotents owner 2ac8
separately passed in own187 and own190.

The actual affine-centre blowup specialization, transport of the accepted
Away regular pair to actual section rings, and global one-pole construction
remain separate consumers, not conclusions of this file.
