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
[native caching](doc/CACHING.md) for artifact reuse.

Import a focused module, such as `Aglib.RingTheory.TensorProduct.Domain`, or use
`import Aglib` for the complete public library.

## Documentation and checks

The [documentation index](doc/README.md) links the mathematical guides.
[Scope](doc/SCOPE.md) and [interface boundaries](doc/INTERFACES.md) record coverage,
hypotheses and conditional inputs; specialized curve and K-theory applications
remain downstream.

Use the [development guide](doc/DEVELOPMENT.md) to select focused builds and
applicable final checks for the changed modules and their affected consumers.
It also covers cache setup and contribution conventions. The comprehensive
`scripts/check.sh` route serves separately requested diagnostics and declared CI.

## License

[Apache-2.0](LICENSE), with the retained source exceptions in
[third-party notices](THIRD_PARTY_NOTICES.md).
