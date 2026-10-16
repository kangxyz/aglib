# Affine scalar adjunction and the original tilde counit

[Counit](Counit.lean) identifies the original scalar adjunction with the
geometric pullback adjunction through `tildePullbackIso`. The theorem
`tildePullbackIso_counit` says that tilde of the scalar adjoint followed by
the target counit equals the original pullback comparison, the source
counit, and the supplied sheaf map.

Both source and target module sheaves are arbitrary, and the ring map need
not be flat. In particular the identity applies to injective resolution
terms without assuming that they are quasicoherent. It is used to identify
the actual chain map in derived flat base change; it introduces no alternate
base-change map or tilde comparison.
