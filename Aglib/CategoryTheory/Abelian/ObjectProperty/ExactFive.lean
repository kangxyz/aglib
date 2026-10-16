/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Object properties and exact sequences of five objects

Closure under kernels and cokernels of maps between known objects, together
with extension and isomorphism closure, detects the middle property in an
exact row of five objects. The proof uses the original middle short
complex's native cycles and opcycles. No closure under arbitrary subobjects
or quotients is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions]

/-- In an exact row of five objects, the four outside properties imply the
middle one using only kernels and cokernels between known objects and
extensions. This does not require arbitrary subobject or quotient closure. -/
theorem prop_middle_of_exact_five {X₁ X₂ X₃ X₄ X₅ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₄) (k : X₄ ⟶ X₅)
    {w₁ : f ≫ g = 0} {w₂ : g ≫ h = 0} {w₃ : h ≫ k = 0}
    (e₁ : (ShortComplex.mk f g w₁).Exact)
    (e₂ : (ShortComplex.mk g h w₂).Exact)
    (e₃ : (ShortComplex.mk h k w₃).Exact)
    (h₁ : P X₁) (h₂ : P X₂) (h₄ : P X₄) (h₅ : P X₅) : P X₃ := by
  let S := ShortComplex.mk g h w₂
  let L := ShortComplex.mk f S.toCycles (by
    rw [← cancel_mono S.iCycles, Category.assoc, S.toCycles_i, zero_comp]
    exact w₁)
  let i : L ⟶ ShortComplex.mk f g w₁ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := S.iCycles
      comm₁₂ := by simp [L]
      comm₂₃ := by simp [L, S] }
  have hL : L.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono i).mpr e₁
  let : Epi L.g := e₂.epi_toCycles
  have hK : P S.cycles := P.prop_of_isColimit_cokernelCofork hL.gIsCokernel h₁ h₂
  let T := ShortComplex.mk S.fromOpcycles k (by
    rw [← cancel_epi S.pOpcycles, ← Category.assoc, S.p_fromOpcycles, comp_zero]
    exact w₃)
  let p : ShortComplex.mk h k w₃ ⟶ T :=
    { τ₁ := S.pOpcycles
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, S]
      comm₂₃ := by simp [T] }
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono p).mp e₃
  let : Mono T.f := e₂.mono_fromOpcycles
  have hQ : P S.opcycles := P.prop_of_isLimit_kernelFork hT.fIsKernel h₄ h₅
  let d := S.homologyData
  exact P.prop_X₂_of_shortExact (e₂.shortExact d)
    (P.prop_of_iso d.left.cyclesIso hK) (P.prop_of_iso d.right.opcyclesIso hQ)

end CategoryTheory.ObjectProperty
