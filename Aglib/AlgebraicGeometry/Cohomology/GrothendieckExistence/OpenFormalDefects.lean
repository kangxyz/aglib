/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenBoundedCandidate
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects

/-! # Original bounded formal defects under actual open pullback

The bounding ideal may be independent of the formal ideal. The same exponent
kills the two ordinary stage defects of the actual pulled comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (p : Y ⟶ X) [IsOpenImmersion p] {K : X.IdealSheafData}
  {F : AdicSystem X K} {H : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)

/-- Actual open pullback and its original target completion comparison retain
all ordinary finite-stage bounds, with the same independent ideal exponent. -/
theorem openReconstructionComparison_defectsKilled (J : X.IdealSheafData) (t : ℕ)
    (h : AdicSystem.DefectsKilled J t α) :
    AdicSystem.DefectsKilled (J.comap p) t (openReconstructionComparison p α) := by
  intro n
  let M : X.CoherentSheaf := ⟨F.obj.obj (op n), F.property.coherent n⟩
  let N : X.CoherentSheaf := ⟨((completionFunctor X K).obj H).obj.obj (op n),
    ((completionFunctor X K).obj H).property.coherent n⟩
  let a : M ⟶ N := ObjectProperty.homMk (α.hom.app (op n))
  have hp := openReconstructionCandidate_bounds (K := J) p a t (h n).1 (h n).2
  let e := (openIdealPullbackCompletionIso p K H).hom.hom.app (op n)
  let eIso := ((ObjectProperty.ι _).mapIso (openIdealPullbackCompletionIso p K H)).app (op n)
  have : IsIso e := show IsIso eIso.hom from inferInstance
  change killedByIdealSheaf (J.comap p ^ t)
      (kernel ((pullback p).map a.hom ≫ e)) ∧
    killedByIdealSheaf (J.comap p ^ t)
      (cokernel ((pullback p).map a.hom ≫ e))
  exact ⟨killedByIdealSheaf_of_iso _ (kernelCompMono ((pullback p).map a.hom) e).symm hp.1,
    killedByIdealSheaf_of_iso _ (cokernelCompIsIso ((pullback p).map a.hom) e).symm hp.2⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
