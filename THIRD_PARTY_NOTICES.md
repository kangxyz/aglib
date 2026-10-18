# Retained source exceptions

Most source files are released under Apache-2.0 as stated in their headers.
The following seven Milnor K₂ implementations have no declared upstream
license and are excluded from that statement:

- `Aglib/KTheory/MilnorK/K2/Basic.lean`
- `Aglib/KTheory/MilnorK/K2/Map.lean`
- `Aglib/KTheory/MilnorK/K2/Symbols.lean`
- `Aglib/KTheory/MilnorK/K2/Residue.lean`
- `Aglib/KTheory/MilnorK/K2/Specialization.lean`
- `Aglib/KTheory/MilnorK/K2/DVR/Basic.lean`
- `Aglib/KTheory/MilnorK/K2/DVR/Uniformizer.lean`

These are local adaptations of the user-owned `kangxyz/r5-lab` source at
`1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`, subsequently maintained in
`kangxyz/motivic` at `b368f6965228e63643380033ec224335bcd24a2c`.
Each source header retains its original URL, blob and SHA-256 identity.
The repository owner explicitly authorized public publication of this code
on 17 October 2026. That authorization supersedes the earlier extraction-time
lack of redistribution authorization recorded in the headers; it does not
relicense those copied implementations under Apache-2.0.

The migration preserves the original statements and proofs while changing
module paths and native namespaces. Independently authored all-degree groups,
consumers and comparison adapters retain their own explicit license headers.
Exact source and destination correspondence is recorded in
[the migration map](doc/migration/motivic-milnor-k.json).
