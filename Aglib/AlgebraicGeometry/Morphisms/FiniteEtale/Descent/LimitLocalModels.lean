/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitAffine
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverCharts

/-!
# Simultaneous local models over affine-transition limits

Actual finite-etale models over finitely many affine charts can be placed at
one common original stage. Their comparisons retain the native cone maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u v

/-- Finitely many prescribed covers over the chart limits have finite-etale
models at one common stage, with comparisons along the original chart cones. -/
theorem exists_common_affine_chart_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type v} [Finite J] (U : J → Scheme.{u}) [∀ j, IsAffine (U j)]
    (f : ∀ j, U j ⟶ D.obj i)
    (Y : ∀ j, FiniteEtale (baseChangeCone D c i (f j)).pt) :
    ∃ k : Over i, ∃ M : ∀ j, FiniteEtale ((baseChangeDiagram D i (f j)).obj k),
      ∀ j, Nonempty ((baseChange ((baseChangeCone D c i (f j)).π.app k)).obj (M j) ≅ Y j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  have (j : J) (k : Over i) : IsAffine ((baseChangeDiagram D i (f j)).obj k) := by
    change IsAffine (pullback (D.map k.hom) (f j))
    infer_instance
  have H (j : J) := exists_affine_cover_of_isLimit
    (baseChangeDiagram D i (f j)) (baseChangeCone D c i (f j))
    (isLimitBaseChangeCone D c hc i (f j)) (Y j)
  choose k M e using H
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  let N (j : J) := (baseChange ((baseChangeDiagram D i (f j)).map (q j))).obj (M j)
  refine ⟨l, N, fun j ↦ ⟨?_⟩⟩
  exact (baseChangeComp ((baseChangeDiagram D i (f j)).map (q j))
      ((baseChangeCone D c i (f j)).π.app l)).symm.app (M j) ≪≫
    (eqToIso (congrArg baseChange ((baseChangeCone D c i (f j)).w (q j)))).app (M j) ≪≫
    Classical.choice (e j)

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
