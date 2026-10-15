# Actual truncation embeddings and layers

[StupidTrunc](StupidTrunc/README.md) implements the native integer-cochain truncation maps, transition and layer sequence. Its inclusions split term by term and its layer sequence is actually short exact, without boundedness or projectivity assumptions.

The generic embedding comparison retains relation reflection. These lower statements support bounded homotopy/derived comparison and complex factorization; a termwise split inclusion is not a supplied chain retraction.

[CochainComplex/TruncGE](CochainComplex/README.md) separately factors an actual map into a strictly lower-bounded target through good lower truncation, with its original projection equation.
