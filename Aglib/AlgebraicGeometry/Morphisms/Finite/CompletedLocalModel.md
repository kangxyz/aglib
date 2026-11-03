# Actual completed branches of a finite local model

Source: [CompletedLocalModel.lean](CompletedLocalModel.lean).

Import `Aglib.AlgebraicGeometry.Morphisms.Finite.CompletedLocalModel`.
The namespace is `AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra`.

Let `f : X -> Y` be finite and dominant between integral schemes, `U` an
original nonempty affine open of `Y`, and `y : U`. Reuse the existing
`R = Y.presheaf.stalk y.val` and `S = Ring f U hU y`: `S` is the **whole**
finite inverse-image chart localized at the target point, not a selected
source stalk. The algebra structures remain the existing `stalkAlgebra`,
`chartAlgebra` and `functionFieldAlgebra`.

For `q : MaximalSpectrum S`, `completionBranch_contraction` proves that its
original ideal contracts to the maximal ideal of `R`. `completionBranch`
views the same point in `FiniteSemilocal.Branch R S`, the maximal spectrum
of the closed-fibre quotient. `branchIdeal_completionBranch` states that
its inverse-image ideal is exactly `q.asIdeal`.

`completionBranchLocalizationEquiv` compares the two presentations of the
same prime localization as `S`-algebras. `completionBranchLocalEquiv` then
uses the existing `branchStalkEquiv` to identify it with the actual stalk
at `branchPoint f U hU y q`. Its `stalkMap` equation preserves the original
map from `R`; its `fraction` equation preserves the original generic
restriction into `X.functionField`, through the existing branch fraction
algebra. No field model or embedding is replaced.

`completedBranchStalkEquiv` completes that same local-ring equivalence,
using `Scheme.LocalRing.completionCongr`. Its `algebraMap` equation retains
every original local element. Its `base` equation identifies the canonical
completed-base action on original elements with the completion of the
original structural stalk map.

`completionBranch_isLocalHom` proves locality of the original map to the
branch localization. `completionBranchResidueEquiv` is induced by the same
stalk equivalence, and `completionBranchResidueEquiv_stalkMap` identifies
the original structural residue maps, not just their fields or dimensions.

Finally, `exists_completedBranchStalkEquiv` shows that every actual closed
source point over `y` is such a completed factor, with the comparison and
coefficient equation on that original source stalk. It applies the proved
`exists_branch` for the entire finite local algebra.

There is no Noetherian, normal, regular, completion-domain or finite-stalk
hypothesis in this leaf. It makes no degree, normal-completion or resolution
existence claim. The completed-branch degree consumer must separately
derive those mathematical hypotheses and apply the existing
`AdicCompletion.FiniteSemilocalDegree` algebra. The comparison never asserts
that an uncompleted source stalk is finite over the target stalk or an
earlier base.

Direct consumers: [AlgebraicGeometry/Morphisms/Finite/CompletedLocalDegree](CompletedLocalDegree.md).
