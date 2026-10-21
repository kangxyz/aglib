/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.NilpotentGeneration
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-! # Generation of an annihilated tower from one finite stage -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (K : X.IdealSheafData)
  {P : X.Modules} [hP : P.IsQuasicoherent]
  (F : ℕᵒᵖ ⥤ X.Modules)
  (hF : ∀ n : ℕ, (F.obj (op n)).IsQuasicoherent)
  (p : (Functor.const ℕᵒᵖ).obj P ⟶ F)

include hF hP in
/-- A compatible family generating one stage generates the entire tower
when the kernels of reduction to that stage lie in the first ideal multiple.
Low stages use only epimorphic transitions; high stages use nilpotence.
No cartesian relation-system condition is imposed. -/
theorem compatible_epi_of_nilpotent_kernel_bound (k : ℕ) [Epi (p.app (op k))]
    (hepi : ∀ n m (h : n ≤ m), Epi (F.map (homOfLE h).op))
    (hkilled : ∀ n : ℕ, killedByIdealSheaf (K ^ n) (F.obj (op n)))
    (hker : ∀ n (h : k ≤ n) (U : X.affineOpens),
      LinearMap.ker ((F.map (homOfLE h).op).val.app (op U.val)).hom ≤
        K.ideal U • (⊤ : Submodule Γ(X, U.val) Γ(F.obj (op n), U.val)))
    (n : ℕ) : Epi (p.app (op n)) := by
  rcases le_total k n with h | h
  · let : (((Functor.const ℕᵒᵖ).obj P).obj (op n)).IsQuasicoherent := hP
    let := hF k
    let := hF n
    have hc : p.app (op n) ≫ F.map (homOfLE h).op = p.app (op k) := by
      have hn := p.naturality (homOfLE h).op
      change 𝟙 P ≫ p.app (op k) = p.app (op n) ≫ F.map (homOfLE h).op at hn
      exact (Category.id_comp _).symm.trans hn |>.symm
    let : Epi (p.app (op n) ≫ F.map (homOfLE h).op) := by
      rw [hc]
      infer_instance
    let : (kernel (p.app (op n) ≫ F.map (homOfLE h).op)).IsQuasicoherent :=
      QuasiCoherent.quasicoherent_kernel _
    exact epi_of_epi_comp_of_nilpotent_reduction K (p.app (op n))
      (F.map (homOfLE h).op) (hker n h) n (hkilled n)
  · let := hepi n k h
    have hc : p.app (op n) = p.app (op k) ≫ F.map (homOfLE h).op := by
      have hn := p.naturality (homOfLE h).op
      change 𝟙 P ≫ p.app (op n) = p.app (op k) ≫ F.map (homOfLE h).op at hn
      exact (Category.id_comp _).symm.trans hn
    rw [hc]
    infer_instance

end AlgebraicGeometry.Scheme.Modules
