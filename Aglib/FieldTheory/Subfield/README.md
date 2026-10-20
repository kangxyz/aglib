# Finite subfield data

`FiniteData.lean` restricts actual units to a subfield containing their values,
with exact inclusion and multiplication formulas. `generatedSubfield` is the
join of a specified base subfield and the closure of a finite set. The finite
closure is finitely generated over its prime field in Mathlib's `Field.FG`
sense. These are the field-data suppliers for finite witness/model arguments.
