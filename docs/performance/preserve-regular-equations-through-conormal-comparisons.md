> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#preserve-regular-equations-through-conormal-comparisons) · [Context](original-context.md) · [Case index](README.md) · [Previous record](keep-one-representation-of-module-sections.md) · [Next record](preserve-module-types-in-finite-normalization.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Preserve regular equations through conormal comparisons

On Lean 4.34.1, the unipotent-overlap comparison in
[RankTwoExtension/Conormal](../../Aglib/AlgebraicGeometry/ProjectiveBundle/RankTwoExtension/Conormal.lean)
exceeded the default 200000-heartbeat limit during ordinary kernel checking
of `overlapConormalMaps_coordinate`. Abstract helpers, aligned section
carriers and a shared canonical map alone had not closed the specialization.

The passing implementation states both the abstract producer and concrete
comparison through the same regular definition `GlobalSectionImagesEq`.
Its arguments are the actual module objects, morphisms and original section.
The abstract frame-extensionality consumer accepts that same proposition;
its final application therefore retains the equation boundary at the
concrete spectral modules. Applying a wrapper to only one side would not
provide the same boundary. This follows the existing `CompEq` pattern below
and the pinned [kernel reduction hints](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L17-L47).
No new trace was collected, and no upstream compiler defect is established.

The localization calculations also use `Sections.translationOverlapPolynomial`
as the denominator of every inverse and lift. A separate
`overlapDenominator_algebraMap` states its coefficient equation using an
explicit `change` and ring-homomorphism laws. This avoids requesting an
instance for a differently expanded denominator inside an inverse argument.
The original maps and mathematical hypotheses are unchanged.

The failed source
`7b76a0eca7ab9cc764e6f32ac9c4dc686f6594c207897b02c1be38acf1d72f9e`
in native run `remote-f907e22742434203a1e1b46e479c1083` recorded the kernel
timeout at line 543, alongside denominator and rewrite errors. Source
`66f4b3a59348f687359b722c43295c569f9cd44843485c61d004d6037c80781e`
passed the complete Conormal module in 65 seconds in native run
`remote-ba6b25fe06e741aba407d12e644df10d`, with standard budgets and a
successful compiler exit. Other proof repairs and cache conditions differ,
so this establishes removal of the timeout on that module, not a controlled
speedup ratio or attribution to a single edit. The outer run failed on other
modules, including the separate global `Conormal.Compatibility` candidate;
that upper obligation was not covered by this pass.

The subsequent global frame transport retained the same regular
`FrameMapCompatible`, `FrameTransportSquare` and `PullbackFrameTransport`
equations in its generic proofs and actual consumers. Its final bare
`pullbackUnitIso_comp` rewrite still exhausted 200000 heartbeats at `whnf`.
Source `40fd6ed9804fc95d8fb6456c4aa92821f01c9caaad2076a5196de222c04a98db`
failed at line 593 in native run
`remote-4235fb93c0fe44f1ab828326a8daff66`.

Keep the typed naturality calculation and supply the exact composition fact
`pullbackUnitIso_comp a j₀` through `congrArg`, rather than asking rewriting
to infer the two scheme maps through the unit objects. After that repair and
removal of one unused simp argument, source
`edf1223ad5f5c00cc93161fbcb59fd92ecf9c4eee6c6e96e7cdd72567f98fc42`
passed the complete
[Compatibility module](../../Aglib/AlgebraicGeometry/ProjectiveBundle/RankTwoExtension/Conormal/Compatibility.lean)
in native run `remote-123316c95d424e5d98b249b27da5de4a`, reported duration
278.45 seconds, at unchanged default budgets and without diagnostics.
The original morphisms and short exact extension hypotheses are unchanged.
This verifies the global conormal isomorphism and its original frame formulas;
it does not prove the later H¹-injection, GR vanishing or surface capstones.
No controlled timing improvement or profiled compiler-cause claim follows.

