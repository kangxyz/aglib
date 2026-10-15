/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/PullbackStalkUnit.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 41]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original pullback/stalk comparison keeps the original geometric unit
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct ChangeOfRings

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual pullback/stalk isomorphism sends the original unit germ to the
ordinary scalar-extension unit, with the original structure-sheaf stalk map. -/
theorem pullbackModuleStalkIso_unit_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (E : Y.Modules) (U : Y.Opens) (hx : f x ∈ U) (e : Γ(E, U)) :
    (pullbackModuleStalkIso f x).hom.app E
        (((Scheme.Modules.pullback f).obj E).presheaf.germ (f ⁻¹ᵁ U) x hx
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U e)) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x),(f.stalkMap x).hom]
        E.presheaf.germ U (f x) hx e := by
  let A₁ := (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (moduleStalkSkyscraperAdjunction X x)
  let A₂ := ((moduleStalkSkyscraperAdjunction Y (f x)).comp
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)).ofNatIsoRight
      (moduleSkyscraperPushforwardIso f x).symm
  have h := Adjunction.unit_leftAdjointUniq_hom_app A₁ A₂ E
  have hv := congrFun (congrArg (fun p => p.app U e) h) ⟨hx⟩
  exact hv

end AlgebraicGeometry.Scheme.Modules
