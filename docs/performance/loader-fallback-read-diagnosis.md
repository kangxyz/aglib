# Diagnose native loader fallback read failures

A bare loader read error can occur after allocation failure even when the
artifact is present. The [complete diagnosis](cases/loader-fallback-read-diagnosis/README.md)
retains the pinned loader branch, sampled resource counts, the failed allocator
trial and the observed NULL-buffer read, with [hash-bound supporting evidence](cases/loader-fallback-read-diagnosis/evidence/SHA256SUMS).
The instrumented failure supports a resource-pressure route; it does not
establish a successful repair, a unique map-limit cause or a lint/audit pass.
