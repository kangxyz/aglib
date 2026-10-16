/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedRepresentativeNaturality
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalModels
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Restriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure

/-!
# Strict local models for distinguished native triangles

A distinguished native derived triangle whose first two objects have
supplied strict chain models has a strict model for its third object near
each point. The original third-object comparison, chain map and cone
triangle are retained.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalTriangles.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `fb369cad1a8b66a6e4b051d3108e0a301aba4de36a1efdeaeed3040f23b5f1b5`.
Selected declaration ranges: 47–81.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

theorem exists_local_strictModel_of_triangle {X : Scheme.{u}}
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang (DerivedCategory X.Modules))
    {P Q K : CochainComplex X.Modules ℤ} (hP : strictPerfect X P) (hQ : strictPerfect X Q)
    (eP : T.obj₁ ≅ (DerivedCategory.Q (C := X.Modules)).obj P)
      (eQ : T.obj₂ ≅ (DerivedCategory.Q (C := X.Modules)).obj Q)
    (eK : T.obj₃ ≅ (DerivedCategory.Q (C := X.Modules)).obj K) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      HasStrictModel ((@restrict Y X j hj).obj K) := by
  let φ := eP.inv ≫ T.mor₁ ≫ eQ.hom
  obtain ⟨Y, j, hj, y, hy, g, hg⟩ := exists_local_chain_representative_any_lift hP φ x
  let := hj
  let F := AlgebraicGeometry.Scheme.Modules.derivedRestrict j
  let η := AlgebraicGeometry.Scheme.Modules.derivedRestrictFactors j
  let a : F.obj T.obj₁ ≅ (DerivedCategory.Q (C := Y.Modules)).obj ((restrict j).obj P)
    := F.mapIso eP ≪≫ η.app P
  let b : F.obj T.obj₂ ≅ (DerivedCategory.Q (C := Y.Modules)).obj ((restrict j).obj Q)
    := F.mapIso eQ ≪≫ η.app Q
  have hcomm : F.map T.mor₁ ≫ b.hom = a.hom ≫ (DerivedCategory.Q (C := Y.Modules)).map g := by
    rw [← hg F η]
    dsimp only [a, b, liftedDerivedHom, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    dsimp only [φ]
    rw [F.map_comp, F.map_comp]
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id_assoc]
  let T' := F.mapTriangle.obj T
  let C' := (DerivedCategory.Q (C := Y.Modules)).mapTriangle.obj (mappingCone.triangle g)
  have hT' : T' ∈ distTriang (DerivedCategory Y.Modules) := F.map_distinguished T hT
  have hC' : C' ∈ distTriang (DerivedCategory Y.Modules)
    := DerivedCategory.mappingCone_triangle_distinguished g
  let et : T' ≅ C' := isoTriangleOfIso₁₂ T' C' hT' hC' a b hcomm
  let c : F.obj T.obj₃ ≅ (DerivedCategory.Q (C := Y.Modules)).obj ((restrict j).obj K)
    := F.mapIso eK ≪≫ η.app K
  refine ⟨Y, j, hj, y, hy, ⟨mappingCone g,
    strictPerfect_mappingCone (strictPerfect_restrict j hP) (strictPerfect_restrict j hQ) g⟩,
    ⟨c.symm ≪≫ Triangle.π₃.mapIso et⟩⟩

end AlgebraicGeometry.Scheme.Modules.Complex
