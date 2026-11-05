# Fibre-product coefficient maps and comparison values

The original abelian coefficient functor imported the entire scalar
presheaf file to obtain the restriction naturality theorem. The theorem
now lives in its own lower module. Both the abelian map proofs and the
scalar functor import it. The value comparisons need neither of those
functors, so they can build on a separate branch of the import graph.

The original functor module continues to export the same declarations.
It imports the map and value modules and assembles the original
resolution and sheafification comparisons. The direct scalar consumer
builds against those same declarations.

The earlier native frontend for the monolithic functor took 519 seconds.
In the scoped native split, restriction naturality took 115 seconds,
values 202 seconds, maps 248 seconds and the final assembly 306 seconds.
The original scalar presheaf and direct scalar consumer took 342 and 203
seconds in the same build. The pinned compiler and frontend caps were
unchanged. Supporting coefficient sources changed during the integration,
so these numbers describe the observed modules and import boundaries.

The instrumented original module reported repeated kernel type checking
around the resolution naturality assembly and inverse comparison. The
profile's asynchronous intervals cannot be added to the measured native
wall time. The split build, generated-entry check, text style, declaration
lint and scoped approved-axiom audit passed.

[Source and evidence hashes](evidence/SHA256.json) index the corresponding
source snapshots, timings, compiler events and build logs.
