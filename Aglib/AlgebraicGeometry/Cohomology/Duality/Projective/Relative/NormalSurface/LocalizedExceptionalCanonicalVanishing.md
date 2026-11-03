# Localized original canonical coefficients

Source: [LocalizedExceptionalCanonicalVanishing.lean](LocalizedExceptionalCanonicalVanishing.lean).

This leaf retains the original global canonical module and the original
local-spectrum point-blowup comparison. Its first source batch derives residue
finiteness from an actual proper-model triangle, localness of the original
residue algebra map, and scalar regularity/Cartier monicity of the actual
pulled-back global coefficient through the native stalk-ring isomorphisms.

The scalar-extension unit and geometric pullback-stalk isomorphism are the
existing native maps. No later local ring is assumed finite over the original
base. No canonical module is rebuilt using a projective embedding over that
later local ring.

The actual restriction assembly uses the original local exceptional scheme as
the Cartier source in the global surface. The original centre-fibre isomorphism
and identity-base ideal comparison identify its ideal; native pullback composition
and flat ideal pullback identify the positive local exceptional twist. Closed
stalk dimension is transported through the same actual stalk-ring isomorphism.
The coefficient line is the original derived residue coefficient line.

The final source theorem retains normality/local Noetherianity of the original
model, its proper structural map, the actual original residue algebra triangle,
and the global canonical embedding/dominance/generic finiteness data. It derives
finite presentation, Cartier monicity and the actual restriction isomorphism,
then invokes the single coefficient descent implementation for all ideal powers
and the literal restriction-unit section lift.

The final proof spells the actual stalk residue quotient with syntax-only
notation. A local type-let for that same carrier caused native auxiliary
extraction to generalize the algebra carrier independently; the ordinary kernel
rejected that candidate. Removing the type-let retained the original field and
algebra structures, and the normal production kernel accepted the full theorem.
No proof-checking bypass or budget increase was used.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupGeneration](Trace/PointBlowupGeneration.md).
