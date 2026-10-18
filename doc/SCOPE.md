# Mathematical scope

Aglib develops general algebraic geometry and related mathematics. Its remit includes general scheme, sheaf, cohomological and derived theory, together with the commutative algebra, category theory and homological algebra that support it. A result may belong here independently of whether Quillen or R5Lab currently consumes it. A statement's complete hypotheses, objects and dependencies determine its owner, including when it was extracted from a curve or K-theory source.

## Migration criterion

Select existing general theory by its actual mathematical interface, not by its
source directory, its present consumer, or how easily its imports can be moved.
Noetherian, qcqs, proper, smooth, flat, finite-presentation and intrinsic local
Cartier hypotheses are normal general-theory conditions. They do not turn a
result into a curve or K-theory application. General coherent and perfect-complex
theory, derived categories, descent, normalization and relevant algebraic and
homological foundations are within scope.

If a general producer imports a downstream helper, isolate the necessary general
helper closure. Split mixed files by declaration. An exact existing Mathlib or
Aglib interface should be reused, with consumers retargeted and duplicate
implementations removed. A stronger statement needing a new proof is a separate
obligation; a migration ledger must not count it as already implemented.

Standard functorial geometric constructions are eligible independently of their
current applications. This includes spectra of polynomial/Laurent algebras and
an algebraic simplex family over arbitrary coefficient rings. Intrinsic curve,
genus, degree, Riemann--Roch, nodal-resolution and arithmetic endpoints remain
downstream in this migration. K/G/Q/S, spectrum and Waldhausen/K-map models remain
downstream even when parameterized by arbitrary schemes. Their general geometric,
exact and homological prerequisites are selected independently.

A requested source-tree review records every file's disposition: migrate, split,
reuse upstream, retain an application, or aggregate. Preserve exact source hashes,
selected statements and the mathematical reason. Unreviewed or unresolved rows
remain open; completing a dependency-selected subset does not establish that all
in-scope general theory in the source library has been migrated. A definition or
conditional interface is recorded separately from a theorem supplying it.

## Mathematical families

The ring layer contains actual algebra descent data/equalizers, finite-field models, nilpotent purely inseparable overlaps, integral closedness, regular-local parameters/domain/normality, prime heights, tensor-domain results, support, prime filtrations, localized length and scalar Euler expressions. Its generic scalar homology, fraction and filtration prerequisites sit in their own lower subjects; the multiplicity layer consumes them.

The categorical and algebraic layers contain selected exact structures, exact functors, abelian full subcategories, small models, finite modules, scalar restriction/localization, supplied injective resolutions, Ext-map comparison and first-quadrant total complexes. Topological sheaves and generic site Cech interfaces lie below scheme-specialized cohomology.

The geometric module layer distinguishes ambient structure-module sheaves, quasicoherent sheaves, finite type, finite presentation, finite local freeness, coherent sheaves under local Noetherianity, invertible sheaves and differential sheaves. It preserves actual restriction, pullback, pushforward, stalk, tensor, support and base-change maps. A property of a sheaf and an abelian/exact structure on its full category have separate hypotheses.

Scheme geometry includes schemes over fields, actual stalks, normal components, geometric connectedness, group objects, finite-surjective geometric-point lifting, finite-etale covers and their field-valued fibres, etale neighborhoods and smooth regularity/dimension in arbitrary relative dimension. Ordinary Picard groups are isomorphism classes of actual rank-one module sheaves. Differential sheaves are sheafified Kahler differentials with their universal derivations.

Scheme cohomology uses actual Zariski `Sheaf.H`, with structural scalar actions, canonical functoriality, injective/flasque and affine comparisons, Cech comparison, finite-support cohomology, long exact sequences and Noetherian dimension vanishing. Proved suppliers include qcqs flat base change over arbitrary bases and proper coherent finiteness over locally Noetherian targets. Coherent relatively flat coefficients on proper morphisms over Noetherian affine bases have a universal finite-projective model, with the original ordinary base-change maps and a strict-perfect derived direct-image comparison. Projective-space duality includes field-linear complementary degrees and the original derived Serre comparison over Noetherian rings. General proper duality and direct images of arbitrary perfect coefficients remain separate targets. General topology/site results remain in their lower owners; generic long exactness is distinct from low-degree Euler/dimension consequences.

The current migration boundary is general theory. Specialized curve and projective-line applications, degree and point counts, genus, divisors/curve degree maps, Riemann–Roch, curve-specific Euler/product formulae, K-theory, G-theory, Q/S constructions and spectra remain downstream. General perfect-complex theory belongs here; Waldhausen/K-theory models of those complexes remain downstream. Generic prerequisites extracted from an application introduce no production import of that application. The ordinary Picard group supplies neither Picard-scheme representability nor a curve-degree map.

The structural perfect-complex family uses actual cochain complexes of scheme modules and Mathlib's native derived category. Strict perfection means globally bounded terms that are finite locally free; local perfection uses local derived isomorphisms to such strict models. Their chain categories, local models, strict restriction, inherited exactness and strict shift/cone closure are available over arbitrary schemes. They do not assert a global strict model on every scheme or identify a chain category with its derived localization. Locally perfect complexes have quasicoherent homology and local homology bounds without assuming termwise quasicoherence of the original complex. A single global homology interval additionally requires `CompactSpace X`; it is not a global term bound or strictification.

Field-linear results keep their field-scheme structure. The arbitrary-base relative evaluation and module-base-change maps do not generalize every field-linear theorem to arbitrary base rings. [INTERFACES.md](INTERFACES.md) distinguishes legacy family predicates with proved suppliers, including proper finiteness and smooth differential rank, from the still-unsupplied full arbitrary-base `LocalFreeCohomologyBaseChange` family. Each supplier retains its actual hypotheses; a predicate definition alone supplies no theorem.

The general source surface also includes generic site/scheme tensor, coefficient and cartesian-open base change, finite-projective affine sections, actual projection formulas, bounded-below Godement/derived direct-image interfaces and the selected generic D+ triangle/truncation/contraction closure. Canonical finite-type pushforward belongs below the guarded locally Noetherian coherent category.

Four earlier general cuts from application owners supply qcqs affine induction, the actual polynomial zero section, good-truncation factorization in an arbitrary abelian category with original scheme specialization, and cartesian opens-range equality. Selected lower prerequisites also supply the generic identity-cone functor, exact-functor derived homology, locally split tensor exactness, ordinary module-complex restriction/tensor/acyclicity, actual Godement carrier/unit and open-span comparisons, and D+ open-cover reflection. Their original containing application modules are not imported wholesale. Remaining applications of perfect complexes to projective-line constructions, Waldhausen models and K-theory stay downstream. Godement categorical total exactness is valid on ordinary complexes; augmentation/QI/computational derived statements retain their own bounds and flasque/unit conditions.

The [finite-etale family](../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/README.md) includes empty covers and uses the actual `Over` objects, fibre maps and base-change comparisons. Finiteness of field-valued lifts through a finite morphism needs only an arbitrary field and permits an empty lift set. [Unramified algebra rigidity](../Aglib/RingTheory/Unramified/README.md) and [section rigidity](../Aglib/AlgebraicGeometry/Morphisms/FormallyUnramified/README.md) give equality of actual algebra and scheme maps under their distinct hypotheses, stated in the family guides. Their specialized pointed, inertia and cohomological application consumers remain downstream.
