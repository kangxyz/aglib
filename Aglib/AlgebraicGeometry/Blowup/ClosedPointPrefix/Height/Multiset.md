# Multiset of existing heights at finite actual roots

`heightMultiset` takes a finite set of actual eligible points and genuine empty
levels of their existing original prefixes. It attaches the actual membership
proofs, then uses native `Multiset.map` to collect the existing least-empty-level
heights. Equal heights retain their multiplicities; no `Finset.image` of heights
or deduplication is used.

`heightMultiset_eq_map` identifies this exact native multiset with any total
abbreviation that agrees with the same heights on the actual eligible roots.
It is only a map law, not a decreasing-weight premise or a new well-founded
relation. No prefix, path, tree or height definition is replaced.
