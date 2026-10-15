/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.AffineTransport
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
/-!
# Quasicoherent kernel closure for coherent extension constructions

Quasicoherence is recognized on all actual affine open charts. Using the
proved exactness of the affine quasicoherent inclusion and actual open
restriction, quasicoherent sheaves are closed under ambient finite limits
and finite colimits. In particular, the kernel used to take the preimage of
an open subsheaf remains quasicoherent.

No extension theorem or noetherian hypothesis is used here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- Every quasicoherent affine sheaf has an actual global presentation,
with no finiteness restriction on the generators or relations. -/
theorem affineQuasicoherent_exists_presentation (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] : Nonempty M.Presentation := by
  let N := moduleSpecΓFunctor.obj M
  let s : Set N := Set.univ
  let f : (s →₀ R) →ₗ[R] N := Finsupp.linearCombination R (fun x : s => x.1)
  let P := presentationTilde N s (by simp [s]) (LinearMap.ker f) (Submodule.span_eq _)
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨P.ofIsIso M.fromTildeΓ⟩

/-- Affine-chart recognition of actual sheaf-theoretic quasicoherence. -/
theorem quasicoherent_of_affineCharts {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
      ((Scheme.Modules.restrictFunctor j).obj M).IsQuasicoherent) :
    M.IsQuasicoherent := by
  classical
  have h (V : X.affineOpens) : Nonempty (M.restrict V.2.fromSpec).Presentation := by
    have : (M.restrict V.2.fromSpec).IsQuasicoherent := hM _ V.2.fromSpec
    exact affineQuasicoherent_exists_presentation _ _
  let q : M.QuasicoherentData :=
    { I := X.affineOpens
      X := fun V => V.1
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover]
        exact iSup_affineOpens_eq_top X
      presentation V := affinePresentationToOver M V (h V).some }
  exact q.isQuasicoherent

/-- Quasicoherence is equivalent to quasicoherence on all affine charts. -/
theorem quasicoherent_iff_affineCharts {X : Scheme.{u}} (M : X.Modules) :
    M.IsQuasicoherent ↔
      ∀ (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j],
        ((Scheme.Modules.restrictFunctor j).obj M).IsQuasicoherent := by
  constructor
  · intro h R j _
    exact Scheme.Modules.isQuasicoherent_restrictFunctor j M
  · exact quasicoherent_of_affineCharts M

instance affineQuasicoherent_finiteLimits (R : CommRingCat.{u}) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    (SheafOfModules.isQuasicoherent (Spec
      R).ringCatSheaf).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι J

instance affineQuasicoherent_finiteColimits (R : CommRingCat.{u}) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ :=
    (SheafOfModules.isQuasicoherent (Spec
      R).ringCatSheaf).isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι J

instance quasicoherent_finiteLimits (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    { limitsOfShape_le := by
        rintro M ⟨p⟩
        apply quasicoherent_of_affineCharts M
        intro R j _
        exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_isLimit
          (isLimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isLimit)
          (fun i => by
            have : (p.diag.obj i).IsQuasicoherent := p.prop_diag_obj i
            change ((Scheme.Modules.restrictFunctor j).obj (p.diag.obj i)).IsQuasicoherent
            infer_instance) }

instance quasicoherent_finiteColimits (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ :=
    { colimitsOfShape_le := by
        rintro M ⟨p⟩
        apply quasicoherent_of_affineCharts M
        intro R j _
        exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_isColimit
          (isColimitOfPreserves (Scheme.Modules.restrictFunctor j) p.isColimit)
          (fun i => by
            have : (p.diag.obj i).IsQuasicoherent := p.prop_diag_obj i
            change ((Scheme.Modules.restrictFunctor j).obj (p.diag.obj i)).IsQuasicoherent
            infer_instance) }

/-- Actual sheaf kernels between quasicoherent objects are quasicoherent. -/
theorem quasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit (kernelIsKernel f)
  rintro (_ | _)
  · exact inferInstanceAs M.IsQuasicoherent
  · exact inferInstanceAs N.IsQuasicoherent

/-- Actual sheaf cokernels between quasicoherent objects are quasicoherent. -/
theorem quasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit (cokernelIsCokernel f)
  rintro (_ | _)
  · exact inferInstanceAs M.IsQuasicoherent
  · exact inferInstanceAs N.IsQuasicoherent

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
