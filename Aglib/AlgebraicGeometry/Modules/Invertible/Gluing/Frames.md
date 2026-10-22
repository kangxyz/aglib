# The intrinsic cocycle of actual frames

For a module sheaf M on an arbitrary scheme, an original family of local unit frames
constructs actual transition units: the coefficient in frame i of the original generator
of frame j. The inverse coefficient and all restriction/cocycle equations are proved.
`LocalFrames.cocycle` is therefore a construction, rather than a cocycle-law input.

When the displayed opens cover the scheme, the existing native `homOfLocalSections`
glues the original generators. Its map on each original chart is proved to be the original
frame comparison. Local invertibility gives `LocalFrames.sheafIso`, an actual reconstruction
isomorphism. `sheafIso_hom_over` retains its exact local arrows. The helper
`overFrameOfChart` transports an actual frame on an open immersion to the original open range.
No Noetherian, finite-cover, field, flatness, or quasicoherence hypothesis is used.

The current consumer is `Blowup/RegularPoint/Normal.lean`. That consumer must construct
its actual kernel and dual frames and prove their actual Laurent transition comparison
with the native projective twist. This generic reconstruction does not supply a desired
normal-frame family, a normal-line comparison, or a contraction theorem.

The fixed Lean source `780be6b934226ffe4ff1df3099b3a182f0a82c1349044c86fee4f520444c8480`
passed its actual native frontend in surface run
`remote-08de3bc951bd4f2abd0c59fbc0775683`, on Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The mixed graph exited 1 because the
separate `IdealFrames` provider timed out; `RegularPoint/Normal` was not invoked.
This records generic frame reconstruction only, with no normal-line or whole-graph success.
