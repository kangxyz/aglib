# Actual henselization maps

[GenericMap](GenericMap.lean) contains the original flatness and generic map
from a local domain to a separably closed field. Neither map is assumed local;
no residue embedding into the target is supplied. R and K remain independent.

[AtMaximal](AtMaximal.lean) retains the original maximal localization,
henselization, algebra/scalar towers, quotient-residue algebra equivalence and
finite/purely-inseparable/separably-closed residue conclusions. No residue field
is identified with the ground field. The old FiniteConstantsOne imports are
compatibility facades; their field-comparison/injectivity consumers are unchanged.
