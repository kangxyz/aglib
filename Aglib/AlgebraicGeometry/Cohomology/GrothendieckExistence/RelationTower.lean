/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.AmbientExact
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Naturality
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.AssociatedGraded
public import Aglib.CategoryTheory.Abelian.ReductionKernel

/-!
# The ordinary relation tower of a formal epimorphism

The kernels here are ordinary coherent sheaf kernels. Their transition maps
are epimorphisms; they are not asserted to be a cartesian adic system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The ordinary relation sheaf at a formal level. -/
abbrev relation (n : ℕ) : X.Modules := kernel (φ.hom.app (op n))

/-- Ordinary relation sheaves are coherent; this does not assert formal
cartesianness of the relation tower. -/
theorem relation_coherent (n : ℕ) : affineLocallyFiniteType X (relation φ n) := by
  let : (P.obj.obj (op n)).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (P.property.coherent n R j).1)
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (F.property.coherent n R j).1)
  let : (relation φ n).IsQuasicoherent := quasicoherent_kernel (φ.hom.app (op n))
  exact affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι (φ.hom.app (op n)))
    (P.property.coherent n)

/-- The original naturality square induces reduction on ordinary relations. -/
def relationMap {n m : ℕ} (h : n ≤ m) : relation φ m ⟶ relation φ n :=
  kernel.map _ _ (P.obj.map (homOfLE h).op) (F.obj.map (homOfLE h).op)
    (φ.hom.naturality (homOfLE h).op).symm

@[reassoc (attr := simp)]
theorem relationMap_ι {n m : ℕ} (h : n ≤ m) :
    relationMap φ h ≫ kernel.ι (φ.hom.app (op n)) =
      kernel.ι (φ.hom.app (op m)) ≫ P.obj.map (homOfLE h).op := by
  simp [relationMap]

/-- Every reduction on ordinary relations is onto whenever the original
upper coefficient map is onto. -/
theorem relationMap_epi {n m : ℕ} (h : n ≤ m) [Epi (φ.hom.app (op m))] :
    Epi (relationMap φ h) := by
  have he := CategoryTheory.Abelian.epi_kernel_map_of_reduction
    (idealSheafQuotientFunctor X (K ^ n)) (idealSheafQuotientUnit X (K ^ n))
    (φ.hom.app (op m)) (φ.hom.app (op n))
    (P.reductionIsoOfLE h) (F.reductionIsoOfLE h)
    (reductionIsoOfLE_naturality φ h)
  simpa only [unit_reductionIsoOfLE_hom, relationMap] using he

/-- The original adjacent reduction on ordinary relations. -/
abbrev relationTransition (n : ℕ) : relation φ (n + 1) ⟶ relation φ n :=
  relationMap φ (Nat.le_succ n)

instance relationTransition_epi (n : ℕ) [Epi (φ.hom.app (op (n + 1)))] :
    Epi (relationTransition φ n) := relationMap_epi φ (Nat.le_succ n)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
