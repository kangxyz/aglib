/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Weak preservation by the actual mapping-cone square

The original rotated cone triangles form short exact sequences. Their original triangle map
has the supplied target map and the shifted source map as its two outer components. Genuine
short-exact extension of quasi-isomorphisms therefore applies to the literal middle cone map.

Source: `Quillen/Algebra/Homology/MappingConeWeakMap.lean` from the delivered archive.
Source SHA-256: `a490ef603748e13d17d4471fd64cc1c3ef02f30354b9bfe9dd15f97361d40bce`.
Selection: the complete general cone-square map and quasi-isomorphism result.
The private short-exact extension argument comes from
`Quillen/Algebra/Homology/QuasiIsoExtension.lean` in the same archive,
SHA-256: `e84480cac547c346b826a5e5238c79748fad2864518bf169e92c72ba54885681`.
The actual cone signs, components, universes and endpoint hypotheses are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows HomologicalComplex
open HomologicalComplex.HomologySequence
open _root_.CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original signed rotated cone triangle is a genuine short exact sequence. -/
theorem mappingCone_triangle_shortExact {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (mappingCone.triangleRotateShortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (mappingCone.triangleRotateShortComplexSplitting f n).shortExact)

/-- The actual cone-square map on the original rotated short exact sequences. -/
def mappingConeTriangleShortComplexMap {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    mappingCone.triangleRotateShortComplex f ⟶ mappingCone.triangleRotateShortComplex g where
  τ₁ := b
  τ₂ := mappingCone.map f g a b h
  τ₃ := a⟦(1 : ℤ)⟧'
  comm₁₂ := (mappingCone.triangleMap f g a b h).comm₂.symm
  comm₂₃ := (mappingCone.triangleMap f g a b h).comm₃.symm

private theorem quasiIso_middle_of_shortExact
    {S T : ShortComplex (CochainComplex A ℤ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap φ.τ₂ n) := by
    apply Abelian.mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS hT (n - 1) n (by simp)))
    · exact (composableArrows₅_exact hS (n - 1) n (by simp)).δ₀.δ₀
    · exact (composableArrows₅_exact hT (n - 1) n (by simp)).δ₀.δ₀
    all_goals dsimp; infer_instance
  have he : Epi (homologyMap φ.τ₂ n) := by
    apply Abelian.epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS hT n (n + 1) (by simp)))
    · exact (composableArrows₅_exact hS n (n + 1) (by simp)).δlast.δlast
    · exact (composableArrows₅_exact hT n (n + 1) (by simp)).δlast.δlast
    all_goals dsimp; infer_instance
  exact isIso_of_mono_of_epi _


/-- Actual quasi-isomorphisms of both endpoints induce a quasi-isomorphism of literal cones. -/
theorem mappingCone_map_quasiIso {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map f g a b h) :=
  quasiIso_middle_of_shortExact (mappingConeTriangleShortComplexMap f g a b h)
    (mappingCone_triangle_shortExact f) (mappingCone_triangle_shortExact g)
    (by change QuasiIso b; infer_instance)
    (by change QuasiIso (a⟦(1 : ℤ)⟧'); infer_instance)

end CochainComplex
