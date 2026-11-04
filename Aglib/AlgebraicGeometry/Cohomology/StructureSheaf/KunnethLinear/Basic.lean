/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Factorization
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.DegreeForward
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.TotalInverse

/-!
# The one total comparison on the original Kunneth carriers

The native source, total operator and degreewise inverse are typed at the
original cohomology algebra and original finite antidiagonal sums. Their
complete composition reuses the chosen source and original degree maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

variable [QuasiCompact X.hom] [QuasiSeparated X.hom]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom]

/-- The whole forward operator is the original total Kunneth map. -/
theorem structureExternalLinearEquiv_toLinearMap :
    (structureExternalLinearEquiv X Y).toLinearMap = structureExternalLinearMap X Y :=
  rfl

end AlgebraicGeometry.Scheme.Cohomology
