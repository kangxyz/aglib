/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitChartModels
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitGlobalModels
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitStructuredDiagram

/-!
# Finite-etale objects over affine-transition limits

Finite affine charts and their finite nonempty-intersection refinement provide
actual local models. Their comparison maps use the native closed squares.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
open AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

/-- Models on subcharts give literal cover comparisons on a pulled-back open
cover. Only the containing charts, not their intersections, must be affine. -/
theorem exists_common_open_cover_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (𝒰 : (D.obj i).OpenCover.{u}) [Finite 𝒰.I₀]
    (U : 𝒰.I₀ → Scheme.{u}) [∀ j, IsAffine (U j)]
    (f : ∀ j, U j ⟶ D.obj i) (l : ∀ j, 𝒰.X j ⟶ U j)
    (hl : ∀ j, l j ≫ f j = 𝒰.f j) (Y : FiniteEtale c.pt) :
    ∃ k : Over i,
      ∃ M : ∀ j, FiniteEtale ((𝒰.pullback₁ (D.map k.hom)).X j),
        ∀ j, Nonempty
          ((baseChange (pullback.fst ((𝒰.pullback₁ (D.map k.hom)).f j)
            (c.π.app k.left))).obj (M j) ≅
          (baseChange (pullback.snd ((𝒰.pullback₁ (D.map k.hom)).f j)
            (c.π.app k.left))).obj Y) := by
  obtain ⟨k, M, e⟩ := exists_common_subchart_models D c hc i U 𝒰.X f 𝒰.f l hl Y
  exact ⟨k, M, fun j ↦ ⟨chartComparison (isPullback_baseChangeCone D c i (𝒰.f j) k)
    (M j) Y (Classical.choice (e j))⟩⟩

/-- Actual local models with their literal comparisons produce a global model
at some later original stage. All overlap arrows and laws are constructed. -/
theorem exists_cover_of_local_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (𝒰 : (D.obj i).OpenCover.{u})
    [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀] [Finite 𝒰.I₀]
    [∀ j, CompactSpace (𝒰.X j)] [∀ j, QuasiSeparatedSpace (𝒰.X j)]
    (Y : FiniteEtale c.pt) (M : ∀ j, FiniteEtale (𝒰.X j))
    (e : ∀ j, (baseChange (pullback.fst (𝒰.f j) (c.π.app i))).obj (M j) ≅
      (baseChange (pullback.snd (𝒰.f j) (c.π.app i))).obj Y) :
    ∃ j, ∃ Z : FiniteEtale (D.obj j),
      Nonempty ((baseChange (c.π.app j)).obj Z ≅ Y) := by
  let A (j : 𝒰.I₀) : Over (D.obj i) := (Over.map (𝒰.f j)).obj (M j).obj
  let m (j : 𝒰.I₀) : A j ⟶ (chartDiagram 𝒰).obj j :=
    Over.homMk (M j).obj.hom rfl
  let α (j : 𝒰.I₀) : (Over.pullback (c.π.app i)).obj (A j) ≅
      (geometricLocalDiagram (c.π.app i) 𝒰 Y).obj j :=
    localObjectIso (c.π.app i) (𝒰.f j) (M j).obj Y.obj ((forget _).mapIso (e j))
  have hm (j : 𝒰.I₀) : (Over.pullback (c.π.app i)).map (m j) =
      (α j).hom ≫ (geometricLocalStructure (c.π.app i) 𝒰 Y).app j :=
    localObjectIso_structure (c.π.app i) (𝒰.f j) (M j).obj Y.obj ((forget _).mapIso (e j))
  have (j : 𝒰.I₀) : IsFinite (m j).left := inferInstanceAs (IsFinite (M j).obj.hom)
  have (j : 𝒰.I₀) : Etale (m j).left := inferInstanceAs (Etale (M j).obj.hom)
  obtain ⟨j, k, F, n, hfin, het, e', he'⟩ :=
    exists_diagram_with_structure D c hc i 𝒰 Y A m α hm
  let 𝒱₁ := 𝒰.pullback₁ (D.map j.hom)
  let 𝒱 := 𝒱₁.pullback₁ (D.map k.hom)
  have : Finite 𝒱.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  have (l : 𝒱₁.I₀) : CompactSpace (𝒱₁.X l) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map j.hom) (𝒰.f l))
  have (l : 𝒱₁.I₀) : QuasiSeparatedSpace (𝒱₁.X l) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map j.hom) (𝒰.f l))
  have (l : 𝒱.I₀) : CompactSpace (𝒱.X l) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map k.hom) (𝒱₁.f l))
  have (l : 𝒱.I₀) : QuasiSeparatedSpace (𝒱.X l) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map k.hom) (𝒱₁.f l))
  let : ∀ l, IsFinite (n.app l).left := hfin
  let : ∀ l, Etale (n.app l).left := het
  obtain ⟨l, Z, hZ⟩ := exists_cover_of_structured_diagram D c hc k.left 𝒱 Y F n e' he'
  exact ⟨l.left, Z, hZ⟩

/-- Every finite-etale cover of a qcqs inverse limit with affine transition maps
descends to an actual finite-etale cover at an original stage. Its comparison
uses the specified native cone projection and original base-change functor. -/
theorem exists_cover_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Y : FiniteEtale c.pt) :
    ∃ i, ∃ Yi : FiniteEtale (D.obj i),
      Nonempty ((baseChange (c.π.app i)).obj Yi ≅ Y) := by
  classical
  let : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  let X := D.obj i
  let 𝒜 := X.affineCover.finiteSubcover
  let U : 𝒜.I₀ → X.Opens := fun j ↦ (𝒜.f j).opensRange
  have hU : IsOpenCover U := 𝒜.isOpenCover_opensRange
  have hAffine (j : 𝒜.I₀) : IsAffineOpen (U j) := isAffineOpen_opensRange (𝒜.f j)
  let 𝒰 := intersectionCover U hU
  have (j : 𝒰.I₀) : CompactSpace (𝒰.X j) :=
    intersectionCover_compact U hU (fun j ↦ (hAffine j).isCompact) j
  have (j : 𝒰.I₀) : QuasiSeparatedSpace (𝒰.X j) :=
    intersectionCover_quasiSeparated U hU j
  let v (j : 𝒰.I₀) : 𝒜.I₀ := (intersectionOpen_le_chart U j).choose
  let V (j : 𝒰.I₀) : Scheme.{u} := (U (v j)).toScheme
  have (j : 𝒰.I₀) : IsAffine (V j) := hAffine (v j)
  let f (j : 𝒰.I₀) : V j ⟶ D.obj i := (U (v j)).ι
  let l (j : 𝒰.I₀) : 𝒰.X j ⟶ V j :=
    X.homOfLE (intersectionOpen_le_chart U j).choose_spec
  have hl (j : 𝒰.I₀) : l j ≫ f j = 𝒰.f j := X.homOfLE_ι _
  obtain ⟨k, M, e⟩ := exists_common_open_cover_models D c hc i 𝒰 V f l hl Y
  let 𝒱 := 𝒰.pullback₁ (D.map k.hom)
  have : Finite 𝒱.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  have (j : 𝒱.I₀) : CompactSpace (𝒱.X j) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (D.map k.hom) (𝒰.f j))
  have (j : 𝒱.I₀) : QuasiSeparatedSpace (𝒱.X j) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (D.map k.hom) (𝒰.f j))
  exact exists_cover_of_local_models D c hc k.left 𝒱 Y M (fun j ↦ Classical.choice (e j))

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
