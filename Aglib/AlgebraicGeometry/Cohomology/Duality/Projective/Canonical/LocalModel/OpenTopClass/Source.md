# Original source-model comparison on every open

The source-isomorphism comparison retains the original closed-adjoint model on
the supplied resolution J, its actual cochain map, and the original affine
homology counit on every open. No exactness of global sections on arbitrary
sheaves or invertibility of a counit is assumed.

The private open-complex counit comparison uses the accepted
`HomologicalComplex.homologyMap_twoStage_square` with its original cochain
square and native homology-adjunction equation. It does not introduce another
homology transport. The now-unused private counit-naturality copy is removed;
all public declarations and the final every-open section proof are unchanged.

The previous exact source produced native kernel-memory errors at the private
open-complex theorem and the later public section theorem under a scoped
lower-memory diagnostic. The later error was not attributed independently to
the section proof after the private failure. The generic private prefixes then
checked with only private-module diagnostic lints; a strict final-proof probe
localized the remaining conversion to the original public exact application.
The final caller now instantiates the existing helper at the original bundled
B and C, retaining the same ring-equivalence map rather than re-inferring
CommRingCat.of carriers. Exact source 59885306 passed its full selected native
check in graph77 (123 seconds, normal limits). The actual downstream source
presentation received its first separate diagnostics; no global flat gluing
or arbitrary-field generation is asserted here.
