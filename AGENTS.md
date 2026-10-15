# Aglib development

Maintain general commutative algebra, arbitrary-dimensional schemes and module-sheaf/cohomology theory. Keep curve, genus, degree, projective-line and K/G/Q/S applications in their original libraries. Inspect complete hypotheses, not source paths, when selecting general mathematics.

Use Lean's modern module system with explicit public imports and exposed public interfaces where reduction is intended. Preserve the pinned Lean and Mathlib revisions and Lean's default maxHeartbeats of 200000. Follow pinned Mathlib: options with a maxHeartbeats name component, including synthInstance.maxHeartbeats, may change only for an individual declaration with an explanatory comment after the scoped in. Documented local 0 is permitted; avoid global overrides. Comment quality and budget necessity belong to the mathematical owner.

Keep one implementation per declaration. Aglib is the module root; declaration namespaces use native mathematical owners and collision-safe subject namespaces below them. Follow the mathematical boundaries in doc/ARCHITECTURE.md. Original R5Lab/Quillen names are provenance; any compatibility adapters belong in original application packages. Production imports only Mathlib and precise lower Aglib leaves. Tests, scripts and downstream packages are consumers.

Follow Mathlib source style and preserve original contributor/license headers and exact source provenance. Keep all maintained text in English. Preserve actual objects, maps, universes, hypotheses and explicit general-theorem premises during extraction; compilation and axiom auditing do not discharge such premises.

Place mathematical/interface documentation in the owning subfamily README.md. Root doc/ owns the overview, dependency directions, cross-family routes and development/provenance. Add occupied structure for current consumers, not empty future families.

Build changed leaves and affected clients during iteration. At an integration milestone check complete source enrollment, import direction, private/generated defining-module axiom coverage, relevant rejection controls and kernel replay. Preserve foreign work and exact write ownership. Git operations are serial; do not push without an explicit current request.

Follow [doc/DEVELOPMENT.md](doc/DEVELOPMENT.md) for build, verification and publication commands.
