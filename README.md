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

Run `lake update`, then `lake build`. Use a specific commit instead of `main`
and retain `lake-manifest.json` for reproducible builds.

Import a focused module, such as `Aglib.RingTheory.TensorProduct.Domain`, or use
`import Aglib` for the complete public library.

## Documentation and checks

The [documentation index](doc/README.md) links the mathematical guides.
[Scope](doc/SCOPE.md) and [interface boundaries](doc/INTERFACES.md) record coverage,
hypotheses and conditional inputs; specialized curve and K-theory applications
remain downstream.

From the library checkout, run `bash scripts/check.sh --rehash`.
The [development guide](doc/DEVELOPMENT.md) covers cache setup, focused builds,
verification and contribution conventions.

## License

[Apache-2.0](LICENSE), with the retained source exceptions in
[third-party notices](THIRD_PARTY_NOTICES.md).
