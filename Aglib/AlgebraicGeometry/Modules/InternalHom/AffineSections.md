# Affine internal-Hom evaluation and section maps

This leaf uses the original structure-linear internal-Hom sheaf, native
affine module category and global-sections functor. It supplies evaluation
and restriction laws, the counit-based Hom equivalence, and the affine
comparison `affineGlobalHomEquiv`.

For `R : CommRingCat.{u}` and actual modules `M N : (Spec R).Modules`,
only `M.IsQuasicoherent` is required. The target need not be quasicoherent,
and no Noetherian or finite-presentation hypothesis is added.
`affineGlobalHomEquiv_apply` identifies the forward equivalence with the
original global-sections map. `affineGlobalHomEquiv_symm_apply` states that
the native sections of its inverse at any original R-linear map q are
exactly q. The inverse law composes the existing forward comparison with
the native equivalence inverse law before any concrete chart map is
substituted; it creates no second equivalence or sheaf model.

The finite-cover affine-trace consumer uses this complete inverse law with
its same actual source restriction, bidual target and chart section map.
The complete native owner at source `42af7e5e` passed own129 in 6.3 seconds
(full receipt 9.65 seconds, exit 0, no aggregate guard, owned process group
gone) under the normal 7000-MiB frontend / 7168-MiB aggregate / one-thread
limits. This accepts the variable-module inverse law and the whole owner,
not the concrete finite-cover trace consumer. That consumer at `ca2a3f55`
remains unaccepted: its current normal check reached an aggregate guard
without a declaration phase. No kernel-cause or matched performance claim
follows from the owner pass.
