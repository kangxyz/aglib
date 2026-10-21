# Aglib

A Lean 4 library for general algebraic geometry and its algebraic, categorical
and homological foundations, built on Mathlib.

## Installation and use

Use the pinned [Lean toolchain](lean-toolchain). Add Aglib to your project's
`lakefile.toml`:

```toml
[[require]]
name = "Aglib"
git = "https://github.com/kangxyz/aglib.git"
rev = "main"
```

Run `lake update` to resolve the dependency, then build the client modules that
import it, for example `lake build MyProject.Main` for your own `MyProject.Main`
module. Use a specific
commit instead of `main` and retain `lake-manifest.json` for reproducible builds.
Obtain matching dependency caches before compiling missing prerequisites; see
[native caching](docs/CACHING.md) for artifact reuse.

Import a focused module, such as `Aglib.RingTheory.TensorProduct.Domain`, or use
`import Aglib` for the complete public library.

## Documentation and checks

The [documentation index](docs/README.md) links the mathematical guides.
[Scope](docs/SCOPE.md) and [interface boundaries](docs/INTERFACES.md) record coverage,
hypotheses and conditional inputs, including those of the reusable curve, degree,
Riemann--Roch, Picard and surface interfaces. Arithmetic markings, selected
arithmetic models, literal Tate analytic endpoints and K/G/Q/S applications remain
downstream.

Use the [development guide](docs/DEVELOPMENT.md) to select focused builds and
applicable final checks for the changed modules and their affected consumers.
It also covers cache setup and contribution conventions. Final checks use
`python3 -m lean_ci check --config .github/lean-ci.toml --root .` through the shared
tooling distribution; CI delegates to the same pinned reusable workflow.

## License

[Apache-2.0](LICENSE).
