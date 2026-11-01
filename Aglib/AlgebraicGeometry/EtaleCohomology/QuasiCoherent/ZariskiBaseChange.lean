/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.ZariskiEtaleBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.Topology.Sheaves.Functors

/-! # The original Zariski--étale image square

The right-adjoint comparison is induced by actual base change of open charts.
The inverse-image comparison is its native adjunction transport, with the whole
original unit equation. This construction concerns arbitrary additive sheaves;
quasicoherence enters only its later cohomological use.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original direct-image square at the actual étale value universe. -/
def zariskiRestrictionDirectImageIso :
    directImage f ⋙ zariskiRestriction Y ≅
      zariskiRestriction X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base := by
  letI := Functor.isContinuous_comp (Opens.map f.base) (opensToEtale X)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) (smallEtaleTopology X)
  let e := Functor.sheafPushforwardContinuousComp'
    (opensToEtaleBaseChangeIso f) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (smallEtaleTopology Y) (smallEtaleTopology X)
  let e' := Functor.sheafPushforwardContinuousComp
    (Opens.map f.base) (opensToEtale X) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (smallEtaleTopology X)
  exact e ≪≫ e'.symm

/-- Native inverse-image comparison, obtained from the unchanged composite
adjunctions and the original right-adjoint square. -/
def zariskiInverseImagePullbackIso :
    zariskiInverseImage Y ⋙ inverseImage f ≅
      (Opens.map f.base).sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ⋙ zariskiInverseImage X :=
  (((zariskiEtaleAdjunction Y).comp (inverseImageAdjunction f)).ofNatIsoRight
    (zariskiRestrictionDirectImageIso f)).leftAdjointUniq
      (((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).comp
        (zariskiEtaleAdjunction X))

/-- The comparison is normalized by the actual composite units, not merely by
an isomorphism between the same objects. -/
@[reassoc]
theorem zariskiInverseImagePullbackIso_unit
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u + 1}) :
    (((zariskiEtaleAdjunction Y).comp (inverseImageAdjunction f)).ofNatIsoRight
      (zariskiRestrictionDirectImageIso f)).unit.app A ≫
        (zariskiRestriction X ⋙
          TopCat.Sheaf.pushforward AddCommGrpCat.{u + 1} f.base).map
            ((zariskiInverseImagePullbackIso f).hom.app A) =
      (((Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).comp
        (zariskiEtaleAdjunction X)).unit.app A :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ A

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
