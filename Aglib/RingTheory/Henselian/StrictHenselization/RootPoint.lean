/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.LocalRing
public import Aglib.RingTheory.Kummer.Point

/-! # The original root point over the geometric neighborhood colimit

Use the original colimit residue and the same given field to evaluate the
original root at zero. The whole original root-change and residue triangles
are retained. Only localness of the actual colimit is used, not Noetherianity,
domain properties or faithful flatness.
-/

@[expose] public noncomputable section

open IsLocalRing Algebra.Kummer

namespace GeometricEtaleColimit

universe u

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
  [IsLocalHom (algebraMap R Ω)]

local notation "C" => GeometricEtaleColimit R Ω

local instance residueAlgebra : Algebra C Ω := (residue R Ω).toRingHom.toAlgebra

local instance residueTower : IsScalarTower R C Ω :=
  IsScalarTower.of_algebraMap_eq fun r => ((residue R Ω).commutes r).symm

local instance residueAlgebra_local : IsLocalHom (algebraMap C Ω) :=
  inferInstanceAs (IsLocalHom (residue R Ω).toRingHom)

variable (N : ℕ) (hN : 0 < N) (f : R) (hf : f ∈ maximalIdeal R)

/-- The root-zero point over the original colimit residue, in the same original field. -/
def rootPoint : RootAlgebra N (algebraMap R C f) →ₐ[R] Ω :=
  (Algebra.Kummer.rootPoint C Ω N hN (algebraMap R C f)
    (rootPoint_parameter_mem R Ω f hf C)).restrictScalars R

include hN hf in
/-- The original coefficient-changed root algebra is local; no regularity premise is used. -/
theorem rootPoint_source_isLocalRing : IsLocalRing (RootAlgebra N (algebraMap R C f)) :=
  parameterRoot_isLocalRing C (algebraMap R C f)
    (rootPoint_parameter_mem R Ω f hf C) N hN

/-- The original root point is local, so its spectrum point is the actual closed point. -/
theorem rootPoint_isLocalHom : IsLocalHom (rootPoint R Ω N hN f hf).toRingHom :=
  Algebra.Kummer.rootPoint_isLocalHom C Ω N hN (algebraMap R C f)
    (rootPoint_parameter_mem R Ω f hf C)

/-- The entire original root-change triangle preserves the original field point. -/
theorem rootPoint_comp :
    (rootPoint R Ω N hN f hf).comp (rootBaseChangeHom C N f) =
      Algebra.Kummer.rootPoint R Ω N hN f hf :=
  rootPoint_baseChange R Ω N hN f hf C

/-- The entire coefficient triangle is the original colimit residue map. -/
theorem rootPoint_comp_algebraMap :
    (rootPoint R Ω N hN f hf).toRingHom.comp
      (algebraMap C (RootAlgebra N (algebraMap R C f))) = (residue R Ω).toRingHom := by
  ext c
  exact (Algebra.Kummer.rootPoint C Ω N hN (algebraMap R C f)
    (rootPoint_parameter_mem R Ω f hf C)).commutes c

@[simp] theorem rootPoint_root :
    rootPoint R Ω N hN f hf (AdjoinRoot.root (rootPolynomial N (algebraMap R C f))) = 0 :=
  Algebra.Kummer.rootPoint_root C Ω N hN (algebraMap R C f)
    (rootPoint_parameter_mem R Ω f hf C)

end GeometricEtaleColimit
