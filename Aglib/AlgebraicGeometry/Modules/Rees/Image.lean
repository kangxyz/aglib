/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# The image of the affine pullback unit

For an affine morphism, the image of the actual pullback adjunction unit is
quasicoherent. Over a locally Noetherian target it is coherent whenever the
source coefficient is coherent. The direct-image codomain need not be coherent,
and the unit need not be monic.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual image of the pullback unit, not the pullback source itself. -/
def affineUnitImage {X Y : Scheme.{u}} (g : X ⟶ Y) (N : Y.Modules) : Y.Modules :=
  Abelian.image ((pullbackPushforwardAdjunction g).unit.app N)

/-- The original quotient map onto the unit image. -/
def toAffineUnitImage {X Y : Scheme.{u}} (g : X ⟶ Y) (N : Y.Modules) :
    N ⟶ affineUnitImage g N :=
  Abelian.factorThruImage ((pullbackPushforwardAdjunction g).unit.app N)

/-- The original inclusion of the unit image. -/
def affineUnitImageι {X Y : Scheme.{u}} (g : X ⟶ Y) (N : Y.Modules) :
    affineUnitImage g N ⟶ (pushforward g).obj ((pullback g).obj N) :=
  Abelian.image.ι ((pullbackPushforwardAdjunction g).unit.app N)

@[reassoc (attr := simp)]
theorem toAffineUnitImage_ι {X Y : Scheme.{u}} (g : X ⟶ Y) (N : Y.Modules) :
    toAffineUnitImage g N ≫ affineUnitImageι g N =
      (pullbackPushforwardAdjunction g).unit.app N :=
  Abelian.image.fac _

/-- The unit image is quasicoherent without a flatness assumption. -/
theorem isQuasicoherent_affineUnitImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsAffineHom g] (N : Y.Modules) [N.IsQuasicoherent] :
    (affineUnitImage g N).IsQuasicoherent := by
  let := isQuasicoherent_pushforward_of_isAffineHom g ((pullback g).obj N)
  let η : N ⟶ (pushforward g).obj ((pullback g).obj N) :=
    (pullbackPushforwardAdjunction g).unit.app N
  let := QuasiCoherent.quasicoherent_cokernel η
  exact QuasiCoherent.quasicoherent_kernel (cokernel.π η)

/-- The unit image is coherent as a quotient of the coherent source, not
because its direct-image codomain is coherent. -/
theorem affineLocallyFiniteType_affineUnitImage {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsAffineHom g] (N : Y.Modules)
    (hN : QuasiCoherent.affineLocallyFiniteType Y N) :
    QuasiCoherent.affineLocallyFiniteType Y (affineUnitImage g N) := by
  let : N.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts N (fun R j _ => (hN R j).1)
  let := isQuasicoherent_pushforward_of_isAffineHom g ((pullback g).obj N)
  let η : N ⟶ (pushforward g).obj ((pullback g).obj N) :=
    (pullbackPushforwardAdjunction g).unit.app N
  let := QuasiCoherent.quasicoherent_kernel η
  have hK := Coherent.affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι η) hN
  exact (QuasiCoherent.affineLocallyFiniteType Y).prop_of_iso
    (Abelian.coimageIsoImage η)
    ((QuasiCoherent.affineLocallyFiniteType Y).prop_cokernel (kernel.ι η) hK hN)

end AlgebraicGeometry.Scheme.Modules
