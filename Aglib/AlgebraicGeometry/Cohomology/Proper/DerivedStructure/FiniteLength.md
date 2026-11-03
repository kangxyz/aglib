# Finite length of the original structural derived H1

`Scheme.Cohomology.moduleDerivedStructure_homologyOne_finiteLength_of_proper_birational_surface`
applies to an integral scheme with an original proper dominant map to Spec A,
where A is a normal Noetherian local domain of dimension two and the original
function-field map is invertible. It concludes finite A-length of the actual
first homology of `moduleDerivedStructure` for the original structural section
map `f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom`.

The proof uses the codimension-one birational isomorphism criterion to obtain
an isomorphism over the original punctured spectrum. Proper cohomology then
has finite length, and the existing linear comparison for the supplied
structure-sheaf injective resolution identifies it with the same derived
homology module. No model, coefficient or scalar action is replaced.

Completeness, Nagata hypotheses, normality of the source, a projective embedding
and canonical duality are not required. The standard derived-category universe
is u+1 over the original module category in universe u. The supplied resolution
is computational data only; the theorem's output is the original native derived
object. The chosen-embedding GR consumer reuses this one extracted body.
