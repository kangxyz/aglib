/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotientSheafDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefectRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenAnnihilationDetection
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RestrictQuotientComparison

/-! # Global defects after an independent ideal quotient

Only the quotient step squares the annihilating ideal. Neither completeness,
flatness of completion, nor adicity of ordinary kernels is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} {M N : X.Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- One bound on the original ordinary defects yields a uniform doubled bound
on every independent quotient, with the original coefficient map. -/
theorem independentQuotient_defectsKilled (J K : X.IdealSheafData) (t : ℕ)
    (hk : killedByIdealSheaf (J ^ t) (kernel f))
    (hc : killedByIdealSheaf (J ^ t) (cokernel f)) :
    killedByIdealSheaf (J ^ (t * 2))
        (kernel ((idealSheafQuotientFunctor X K).map f)) ∧
      killedByIdealSheaf (J ^ (t * 2))
        (cokernel ((idealSheafQuotientFunctor X K).map f)) := by
  let : ((idealSheafQuotientFunctor X K).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom K.subschemeι
      ((pullback K.subschemeι).obj M)
  let : ((idealSheafQuotientFunctor X K).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom K.subschemeι
      ((pullback K.subschemeι).obj N)
  let q := (idealSheafQuotientFunctor X K).map f
  have hlocal (i : X.affineBasisCover.I₀) :
      killedByIdealSheaf (J.comap (X.affineBasisCover.f i) ^ (t * 2))
          ((kernel q).restrict (X.affineBasisCover.f i)) ∧
        killedByIdealSheaf (J.comap (X.affineBasisCover.f i) ^ (t * 2))
          ((cokernel q).restrict (X.affineBasisCover.f i)) := by
    let j := X.affineBasisCover.f i
    let g := (restrictFunctor j).map f
    have h := @affineQuotient_defectsKilled _ _ _
      (isQuasicoherent_restrictFunctor j M) (isQuasicoherent_restrictFunctor j N)
      g (J.comap j) (K.comap j) t 1
      (killed_kernel_restrict_pow j J f t hk) (killed_cokernel_restrict_pow j J f t hc)
    rw [pow_one] at h
    let ek := PreservesKernel.iso (restrictFunctor j) q ≪≫
      kernel.mapIso _ _ (restrictQuotientIso j K M) (restrictQuotientIso j K N)
        (restrictQuotientIso_naturality j K f)
    let ec := PreservesCokernel.iso (restrictFunctor j) q ≪≫
      cokernel.mapIso _ _ (restrictQuotientIso j K M) (restrictQuotientIso j K N)
        (restrictQuotientIso_naturality j K f)
    exact ⟨killedByIdealSheaf_of_iso _ ek.symm h.1,
      killedByIdealSheaf_of_iso _ ec.symm h.2⟩
  let : (kernel q).IsQuasicoherent := QuasiCoherent.quasicoherent_kernel q
  let : (cokernel q).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel q
  constructor
  · apply killedByIdealSheaf_of_pullback_openCover X.affineBasisCover.X
      X.affineBasisCover.f
      (fun x => ⟨X.affineBasisCover.idx x, X.affineBasisCover.covers x⟩)
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact killedByIdealSheaf_of_iso _
      ((restrictFunctorIsoPullback (X.affineBasisCover.f i)).app (kernel q)) (hlocal i).1
  · apply killedByIdealSheaf_of_pullback_openCover X.affineBasisCover.X
      X.affineBasisCover.f
      (fun x => ⟨X.affineBasisCover.idx x, X.affineBasisCover.covers x⟩)
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact killedByIdealSheaf_of_iso _
      ((restrictFunctorIsoPullback (X.affineBasisCover.f i)).app (cokernel q)) (hlocal i).2

end AlgebraicGeometry.Scheme.Modules.Coherent
