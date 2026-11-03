# The existing original coefficient-section comparisons

Source: [Sections.lean](Sections.lean).

This focused import path reexports the unchanged original
[coefficient provider](../Coefficients.lean). Its existing constructors,
instances, coefficient actions, native maps and theorems have one original
implementation. No second model or comparison is introduced. Migrated
consumers retain their explicit import path without modifying the original
provider or its established consumers.
