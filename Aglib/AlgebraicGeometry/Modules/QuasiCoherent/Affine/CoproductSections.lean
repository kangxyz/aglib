/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Coproduct
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms

/-!
# Affine sections of quasicoherent colimits

Global sections on an affine scheme preserve a colimiting cocone of actual
quasicoherent module sheaves. This is a statement about the original cocone
maps, not just an isomorphism of its vertex with an abstract module.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Affine global sections preserve colimits of diagrams of quasicoherent sheaves. -/
def affineSectionsIsColimit (R : CommRingCat.{max u v}) {J : Type v} [Category.{v} J]
    {F : J ⥤ (Spec R).Modules} (hF : ∀ j, (F.obj j).IsQuasicoherent)
    {c : Cocone F} (hc : IsColimit c) :
    IsColimit (moduleSpecΓFunctor.mapCocone c) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F' := P.lift F hF
  let c' : Cocone F' :=
    { pt := ⟨c.pt, P.prop_of_isColimit hc hF⟩
      ι := { app := fun j => ObjectProperty.homMk (c.ι.app j)
             naturality := fun i j f => by
               apply ObjectProperty.hom_ext
               exact c.ι.naturality f } }
  have hc' : IsColimit c' := isColimitOfReflects P.ι hc
  exact isColimitOfPreserves (tildeEquiv (R := R)).inverse hc'

/-- The affine-chart identification is natural in the original module coefficient. -/
def affineChartSectionsFunctorIso {X : Scheme.{u}} (U : X.affineOpens) :
    Scheme.Modules.restrictFunctor U.property.fromSpec ⋙ moduleSpecΓFunctor ≅
      Scheme.Modules.toPresheafOfModules X ⋙
        PresheafOfModules.evaluation X.ringCatSheaf.obj (op U.val) :=
  NatIso.ofComponents (affineChartΓIso U)
    (fun f => affineChartΓIso_naturality U f)

/-- Sections on an affine open preserve colimits of quasicoherent coefficients,
with the actual restriction maps and original module scalar action. -/
def affineOpenSectionsIsColimit {X : Scheme.{max u v}} (U : X.affineOpens)
    {J : Type v} [Category.{v} J] {F : J ⥤ X.Modules}
    (hF : ∀ j, (F.obj j).IsQuasicoherent) {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((Scheme.Modules.toPresheafOfModules X ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op U.val)).mapCocone c) := by
  let j := U.property.fromSpec
  let : PreservesColimitsOfSize.{v, v} (Scheme.Modules.restrictFunctor j) :=
    preservesColimitsOfSize_shrink.{v, u, v, u} _
  have hF' (i : J) : ((F ⋙ Scheme.Modules.restrictFunctor j).obj i).IsQuasicoherent := by
    have := hF i
    exact Scheme.Modules.isQuasicoherent_restrictFunctor j (F.obj i)
  exact IsColimit.mapCoconeEquiv (affineChartSectionsFunctorIso U)
    (affineSectionsIsColimit.{u, v} Γ(X, U) hF'
      (isColimitOfPreserves (Scheme.Modules.restrictFunctor j) hc))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
