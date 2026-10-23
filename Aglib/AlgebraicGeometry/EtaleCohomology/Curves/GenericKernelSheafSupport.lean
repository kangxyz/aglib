/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericKernelSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.UnitZeroLocus

/-! # Actual etale-local finite support of original generic-unit kernel sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace Set
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- An original kernel section has finite support measured by actual etale-local zero charts. -/
theorem genericKernel_finite_support (hdim : topologicalKrullDim U.left ≤ 1)
    (a : (kernel (genericArtinUnit X)).obj.obj (op U)) :
    ((Etale.sectionZeroLocus (kernel (genericArtinUnit X)).obj a)ᶜ).Finite := by
  let ι := kernel.ι (genericArtinUnit X)
  let b := ι.hom.app (op U) a
  have hb : (genericArtinUnit X).hom.app (op U) b = 0 := by
    have h := congrArg (fun k : kernel (genericArtinUnit X) ⟶
      (directImage (genericArtinMap X)).obj (gm (genericArtinLocus X)) =>
        k.hom.app (op U)) (kernel.condition (genericArtinUnit X))
    exact ConcreteCategory.congr_hom h a
  apply (finite_genericUnit_kernel_support U hdim b hb).subset
  intro x hx
  by_contra h
  have hg : U.left.presheaf.germ ⊤ x trivial
      ((unitsSections X (op U) b).toMul : Γ(U.left, ⊤)) = 1 := by
    simpa only [Set.mem_ofPred_eq, not_not] using h
  obtain ⟨V, f, y, hy, hz⟩ := Kummer.mem_gm_sectionZeroLocus_of_germ_eq_one U b x hg
  apply hx
  refine ⟨V, f, y, hy, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (ι.hom.app (op V))).mp inferInstance
  rw [map_zero]
  have hn := ConcreteCategory.congr_hom (ι.hom.naturality f.op) a
  exact hn.trans hz

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
