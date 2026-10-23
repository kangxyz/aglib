# Strictly local terminal covers and cohomology

This family concerns `Spec R` for a henselian local ring `R` with separably
closed residue field. Any actual jointly surjective family of étale schemes
has a member with an actual section; this is not restricted to finite étale
families or finite-type covers. The proof retains the original residue-point
triangle, and needs no Noetherianity, perfection, excellence or completeness.

| Source | Result |
| --- | --- |
| [Splitting](Splitting.lean) | Lifts an actual residue-valued point to a section and splits an arbitrary jointly surjective étale family. |
| [Site](Site.lean) | On the actual small-étale site, every covering sieve of the terminal identity contains a split arrow and is maximal. This only asserts splitting for covers of the terminal object. |
| [Cohomology](Cohomology.lean) | Actual terminal evaluation is exact; the native constant integer sheaf is projective; original `Sheaf.H F q` vanishes for every `q > 0`. The value universe `v` and Ext universe `w` remain arbitrary. |
| [Standard](Standard.lean) | Specializes the cohomology results to value universe `u + 1`. |

For arbitrary value and Ext universes, only the native `HasSheafify` and `HasExt`
existence assumptions remain. No `WEqualsLocallyBijective` instance is assumed.
The exactness supplier is owned below in
[site cohomology](../../../CategoryTheory/Sites/SheafCohomology/README.md):
[SplitTerminal](../../../CategoryTheory/Sites/SheafCohomology/SplitTerminal.lean)
constructs the local-image subsheaf used to prove surjectivity on sections.
These are inputs for future small-étale proper-base-change work, not a
proper-base-change theorem.
