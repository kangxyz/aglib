# Natural unit composition

[Unit](Unit.lean), imported as `Aglib.CategoryTheory.NatTrans.Unit`, owns `CategoryTheory.NatTrans.unitPostcompose`, `unitTotalPostcompose` and `unitPrecompose`. These are actual pre/postcomposition of a supplied natural unit; the component formula retains the original arrow and functor maps.

This is the single category-only implementation used by original scheme unit/Godement tensor wrappers. It does not assert that the supplied unit is invertible. Godement augmentation, total-image comparison and derived-unit equations are later consumers with their own boundedness or acyclicity premises.
