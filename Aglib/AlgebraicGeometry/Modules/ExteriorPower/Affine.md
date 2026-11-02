# Actual affine exterior powers

For an actual `R`-module `M`, the exterior presheaf of `tilde M` receives
the original exterior map of `tilde.toOpen` on every open. These maps
commute with the original restrictions. On principal opens they are
module localizations by the native exterior base-change theorem.

The original affine sheafification comparison therefore constructs

```text
moduleExteriorPower (Spec R) (tilde M) n ≅ tilde (exteriorPower R n M).
```

Its pure-wedge equation sends a wedge of the original localized entries
to the original localization of their wedge. No basis or scalar is
chosen. The statement includes degree zero and characteristic two and
does not require finite generation or freeness.

For an arbitrary quasicoherent sheaf on `Spec R`, the original
tilde/global-sections counit gives the comparison with the exterior
power of its actual section module. A finite source module has a finite
exterior power. Together with the original open-restriction comparison,
this proves preservation of the affine-local finite quasicoherent
property on arbitrary schemes.

That property is coherence on a locally Noetherian scheme. No
unrestricted coherence statement over non-Noetherian schemes is made.
The current consumer is the raw exterior sheaf of relative
differentials in the one-pole comparison for a surface-point blowup.
Its bidual line, height-one map extension, and proper-trace comparison
are separate geometric constructions.

## Native verification

The current source, including the original section-module instance docstring,
has SHA-256
`2256744a325654856444a4aea5380910d7e4fcc65776d8a35764df68405a0828`.
It passed the native rebuild, upstream declaration lint and pinned production
axiom audit. The final correction changed only the instance documentation,
not its module dictionary or any mathematical statement or proof.
