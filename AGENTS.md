# Agent instructions

- Keep Aglib focused on general commutative algebra, scheme geometry and module-sheaf/cohomology theory. Keep curve/P1/genus/degree/Riemann–Roch and K/G/Q/S applications downstream. Check complete hypotheses when selecting general results.
- Reuse Mathlib's actual objects and canonical maps. Maintain one implementation per declaration, precise lower-leaf imports, and native mathematical namespaces. Follow [architecture](doc/ARCHITECTURE.md) and [naming](doc/NAMING.md).
- Preserve universes, bounds, hypotheses and explicit theorem-family inputs. Distinguish arbitrary finite-type quasicoherent theory from guarded locally Noetherian coherence; use [interface boundaries](doc/INTERFACES.md).
- Use modern `module` headers, precise `public import` and exposed public interfaces where required. Keep the pinned dependencies and follow Mathlib style; see [development](doc/DEVELOPMENT.md).
- Write maintained text, identifiers and comments in English. Credit actual contributors and preserve licenses and source provenance; see [contribution conventions](doc/DEVELOPMENT.md#contribution-conventions).
- Update the owning family README when an interface or mathematical statement changes. Put cross-family rules in `doc/`; create structure only for current consumers.
- Build changed leaves and affected consumers; use the [integration checks](doc/DEVELOPMENT.md#local-verification-and-ci) before integration. Verification does not supply an explicit mathematical premise.
- Preserve other contributors' work and assigned write ownership. Coordinate shared builds and serial Git operations; do not push without an explicit current request.
