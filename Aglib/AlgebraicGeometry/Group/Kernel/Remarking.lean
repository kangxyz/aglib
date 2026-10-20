/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Monodromy
public import Aglib.CategoryTheory.TorsorAction.CoefficientTransport

/-!
# Actual kernel-fibre and monodromy compatibility under coefficient transport

The group arrow stays fixed. The actual coefficient isomorphism and
Mathlib point-group equivalence identify the same kernel-fibre points and
the same marked monodromy. The finite-etale premises of the original map
remain explicit; no arithmetic character or marked application object is introduced.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.Kernel.Remarking`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`665948b0e062bd71557b3c956f09a9cb918e4110cf16d14588d7d28d65463f04`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group.Monodromy

namespace AlgebraicGeometry.Scheme.Group.Kernel.Remarking

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {T : Scheme.{u}} {A A' G H : Grp (Over T)} {p : G ⟶ H}
  (m : KernelMarking A G H p) (e : A ≅ A')

variable {L : Type u} [Field L] (t : Spec (.of L) ⟶ T)
variable [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]

theorem kernelFibreRemarking (a : Over.mk t ⟶ A.X) :
    kernelFibreEquiv p t (m.transportCoefficient e)
        (((yonedaGrp.mapIso e).app (Opposite.op (Over.mk t))).groupIsoToMulEquiv a) =
      kernelFibreEquiv p t m a := by
  apply Over.OverMorphism.ext
  rw [kernelFibreEquiv_left, kernelFibreEquiv_left]
  change ((a ≫ e.hom.hom.hom) ≫ (e.inv.hom.hom ≫ m.inclusion.hom.hom)).left = _
  have hei : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 A.X :=
    congrArg (fun z : A ⟶ A => z.hom.hom) e.hom_inv_id
  rw [Category.assoc, ← Category.assoc e.hom.hom.hom, hei, Category.id_comp]
  rfl

/-- Monodromy commutes with coefficient transport while the actual arrow is fixed. -/
theorem markedMonodromy_remarking (g : FiberAutGroup (originPoint t H))
    (a : Over.mk t ⟶ A.X) :
    ((yonedaGrp.mapIso e).app (Opposite.op (Over.mk t))).groupIsoToMulEquiv
        (markedMonodromy p t m g a) =
      markedMonodromy p t (m.transportCoefficient e) g
        (((yonedaGrp.mapIso e).app (Opposite.op (Over.mk t))).groupIsoToMulEquiv a) := by
  apply (kernelFibreEquiv p t (m.transportCoefficient e)).injective
  rw [kernelFibreRemarking]
  simp only [markedMonodromy_apply, Equiv.apply_symm_apply]
  rw [kernelFibreRemarking]

end AlgebraicGeometry.Scheme.Group.Kernel.Remarking
