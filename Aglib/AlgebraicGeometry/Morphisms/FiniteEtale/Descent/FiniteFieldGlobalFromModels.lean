/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldModelTransfer

/-! Descent of a finite collection of actual local models to a global cover at one later stage. -/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, Surjective (c.π.app i)] [∀ i, Flat (c.π.app i)] [∀ i, QuasiCompact (c.π.app i)]
  (i : I) (𝒰 : (D.obj i).OpenCover.{u})
  [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀] [Finite 𝒰.I₀]
  [∀ j, CompactSpace (𝒰.X j)] [∀ j, QuasiSeparatedSpace (𝒰.X j)]
  (Y : Scheme.FiniteEtale c.pt) (A : 𝒰.I₀ → Over (D.obj i))
  (m : ∀ j, A j ⟶ (chartDiagram 𝒰).obj j)
  [∀ j, IsFinite (m j).left] [∀ j, Etale (m j).left]
  (α : ∀ j, (Over.pullback (c.π.app i)).obj (A j) ≅
    (geometricLocalDiagram (c.π.app i) 𝒰 Y).obj j)
  (hm : ∀ j, (Over.pullback (c.π.app i)).map (m j) =
    (α j).hom ≫ (geometricLocalStructure (c.π.app i) 𝒰 Y).app j)

include hc hm in
/-- The overlap arrows, their laws and effectiveness are all produced. The inputs here are only
actual local models and their structural reconstruction isomorphisms. -/
theorem exists_globalCover_from_localModels :
    ∃ (j : Over i) (Z : Scheme.FiniteEtale (D.obj j.left)), Nonempty
      ((baseChange (c.π.app j.left)).obj Z ≅ Y) := by
  classical
  have (j : 𝒰.I₀) : CompactSpace ((chartDiagram 𝒰).obj j).left :=
    inferInstanceAs (CompactSpace (𝒰.X j))
  have (j : 𝒰.I₀) : QuasiSeparatedSpace ((chartDiagram 𝒰).obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace (𝒰.X j))
  have (j : 𝒰.I₀) : LocallyOfFinitePresentation ((chartDiagram 𝒰).obj j).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝒰.f j))
  have (j : 𝒰.I₀) : CompactSpace (A j).left :=
    QuasiCompact.compactSpace_of_compactSpace (m j).left
  have (j : 𝒰.I₀) : QuasiSeparatedSpace (A j).left :=
    quasiSeparatedSpace_of_quasiSeparated (m j).left
  have (j : 𝒰.I₀) : LocallyOfFinitePresentation (A j).hom := by
    rw [← Over.w (m j)]
    infer_instance
  let J := Σ (j k : 𝒰.I₀), j ⟶ k
  let U : J → Over (D.obj i) := fun d ↦ A d.1
  let V : J → Over (D.obj i) := fun d ↦ A d.2.1
  let q (d : J) : (Over.pullback (c.π.app i)).obj (U d) ⟶
      (Over.pullback (c.π.app i)).obj (V d) :=
    (α d.1).hom ≫ (geometricLocalDiagram (c.π.app i) 𝒰 Y).map d.2.2 ≫ (α d.2.1).inv
  obtain ⟨j, hj⟩ := exists_common_tail_overHom D c hc i U V q
  let a := D.map j.hom
  let b := c.π.app j.left
  let f := c.π.app i
  let h : b ≫ a = f := c.w j.hom
  let 𝒱 := 𝒰.pullback₁ a
  let B := transferredObject 𝒰 a A
  let n := transferredStructure 𝒰 a A m
  let β := transferredIso 𝒰 a b f h Y A α
  have hn : ∀ k, (Over.pullback b).map (n k) =
      (β k).hom ≫ (geometricLocalStructure b 𝒱 Y).app k :=
    transferredStructure_commutes 𝒰 a b f h Y A m α hm
  have hl : ∀ {k l : 𝒱.I₀} (d : k ⟶ l), ∃ g : B k ⟶ B l,
      (Over.pullback b).map g = (β k).hom ≫ (geometricLocalDiagram b 𝒱 Y).map d ≫ (β l).inv := by
    intro k l d
    obtain ⟨g, hg⟩ := hj ⟨k, l, d⟩
    exact ⟨g, transferred_arrow 𝒰 a b f h Y A α d g hg⟩
  let : Quiver.IsThin 𝒱.I₀ := inferInstanceAs (Quiver.IsThin 𝒰.I₀)
  exact ⟨j, OverModels.gluedCover b 𝒱 Y B n β hn hl,
    ⟨OverModels.baseChangeIso b 𝒱 Y B n β hn hl⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 b706f3b17211fcd74788b6358abfada6fde2cdcc7df8f6b19601b63135d5c061.
Definitions, hypotheses and universes are retained modulo native names. -/
