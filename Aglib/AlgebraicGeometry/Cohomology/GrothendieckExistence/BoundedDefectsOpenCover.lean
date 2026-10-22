/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenAnnihilationDetection

/-! # One global defect bound from an actual finite open cover

Each local exponent bounds every original formal stage. A finite maximum gives
one global positive exponent. Only ordinary kernels and cokernels and the
original open pullbacks occur; no formal abelian category or localization of
completed modules is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u v
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {ι : Type v} [Finite ι] (Y : ι → Scheme.{u})
  (p : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (p i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), p i y = x)
  {K : X.IdealSheafData} {F G : AdicSystem X K}

include hcover in
/-- Bounds on the ordinary defects of the original pulled maps on a finite
open cover give one positive bound for every stage of the original map. -/
theorem hasBoundedDefects_of_pullback_openCover
    (J : X.IdealSheafData) (φ : F ⟶ G)
    (hlocal : ∀ i, ∃ t : ℕ, ∀ n : ℕ,
      killedByIdealSheaf (J.comap (p i) ^ t)
        (kernel ((pullback (p i)).map (φ.hom.app (op n)))) ∧
      killedByIdealSheaf (J.comap (p i) ^ t)
        (cokernel ((pullback (p i)).map (φ.hom.app (op n))))) :
    HasBoundedDefects J φ := by
  classical
  let := Fintype.ofFinite ι
  choose t ht using hlocal
  let N := Finset.univ.sup t + 1
  have hn (i : ι) : t i ≤ N :=
    (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  let (i : ι) : PreservesLimits (pullback (p i)) :=
    preservesLimits_of_natIso (restrictFunctorIsoPullback (p i))
  refine ⟨N, Nat.succ_pos _, ?_⟩
  intro n
  let a := φ.hom.app (op n)
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _
      (fun R j _ => (F.property.coherent n R j).1)
  let : (G.obj.obj (op n)).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _
      (fun R j _ => (G.property.coherent n R j).1)
  let : (kernel a).IsQuasicoherent := QuasiCoherent.quasicoherent_kernel a
  let : (cokernel a).IsQuasicoherent := QuasiCoherent.quasicoherent_cokernel a
  constructor
  · apply killedByIdealSheaf_of_pullback_openCover Y p hcover (J ^ N) (kernel a)
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact killedByIdealSheaf_of_iso _ (PreservesKernel.iso (pullback (p i)) a).symm
      (killedByIdealSheaf_of_le (idealSheaf_pow_le (Y i) (J.comap (p i)) (hn i))
        (ht i n).1)
  · apply killedByIdealSheaf_of_pullback_openCover Y p hcover (J ^ N) (cokernel a)
    intro i
    rw [IdealSheafData.comap_pow_of_isOpenImmersion]
    exact killedByIdealSheaf_of_iso _ (PreservesCokernel.iso (pullback (p i)) a).symm
      (killedByIdealSheaf_of_le (idealSheaf_pow_le (Y i) (J.comap (p i)) (hn i))
        (ht i n).2)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
