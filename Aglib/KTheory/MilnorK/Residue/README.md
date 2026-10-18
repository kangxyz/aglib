# Milnor specialization and tame residue

`Specialization` constructs all-degree specialization from actual discrete
valuation and reduction data. It depends on the selected uniformizer. `Basic`
constructs the signed tame residue with the uniformizer in the last slot;
in degree one it is the integer valuation. `Compatibility` identifies the
same original degree-two and degree-three residue maps.

`DVR` realizes the data from actual DVR/fraction-field instances. `Change`
proves uniformizer independence under its normalization and compatibility
conditions. `Restriction`, `RamifiedRestriction`, `Product` and completion
leaves preserve the stated scalar, valuation and reduction maps.

[Polynomial residues](Polynomial/README.md) specialize these maps at actual
irreducible polynomial places. Characteristic-zero norm compatibility belongs
to the optional norm family rather than the basic residue construction.
