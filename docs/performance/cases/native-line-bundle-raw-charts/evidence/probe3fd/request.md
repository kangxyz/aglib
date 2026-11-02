# One section-family boundary diagnostic

Run only `SectionFamilyBoundaryProbe.lean` using the ordinary prepared native frontend and cached parent artifacts. It reproduces current AssociatedBundle2083 lines1–198 and the exact failing native sectionFamily_natural header/body at199–215. It imports no failed AssociatedBundle module. The only extra import is core `Lean.Elab.Tactic` for logging.

The first theorem puts the original target proposition in an explicit theorem binder and proves True. This is the prescribed formation-only probe, not a proof of naturality. The second theorem has the exact original header/body, with compact markers before intro, after intro, after the native pullHom view, and after relation specialization. Both declarations have scoped diagnostics/profiler output; no heartbeat/recursion/memory policy is changed.

Preserve the full log. Named profiler/kernel entries and the markers separate header formation, intro, change, relation specialization, and final simp/kernel conversion. If all four actual-body markers appear, markers alone cannot distinguish final simp from asynchronous kernel checking; the named profile/counters must do that. Reduction counts do not establish per-constant timings or a speedup.

No production source changed, no v4 rewrite is proposed before this evidence, and the live08756 fragment remains partial failure evidence. Full hashes and marker interpretation are in request.json.
