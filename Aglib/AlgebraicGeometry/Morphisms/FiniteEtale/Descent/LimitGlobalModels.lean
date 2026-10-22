/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitEquifibered
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitGluing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldModelTransfer

/-!
# Global reconstruction from a finite structured model diagram

Eventual invertibility of cartesian comparisons, followed by native relative
gluing, reconstructs the prescribed cover. No faithful-flatness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
open AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

/-- A finite structured diagram of local finite-etale models becomes effective
at a later original stage, with its prescribed literal reconstruction. -/
theorem exists_cover_of_structured_diagram
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (𝒰 : (D.obj i).OpenCover.{u})
    [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀] [Finite 𝒰.I₀]
    [∀ j, CompactSpace (𝒰.X j)]
    (Y : FiniteEtale c.pt) (F : 𝒰.I₀ ⥤ Over (D.obj i))
    (n : F ⟶ chartDiagram 𝒰)
    [∀ j, IsFinite (n.app j).left] [∀ j, Etale (n.app j).left]
    (e : F ⋙ Over.pullback (c.π.app i) ≅ geometricLocalDiagram (c.π.app i) 𝒰 Y)
    (he : ∀ j, (Over.pullback (c.π.app i)).map (n.app j) =
      e.hom.app j ≫ (geometricLocalStructure (c.π.app i) 𝒰 Y).app j) :
    ∃ k : Over i, ∃ Z : FiniteEtale (D.obj k.left),
      Nonempty ((baseChange (c.π.app k.left)).obj Z ≅ Y) := by
  have (j : 𝒰.I₀) : LocallyOfFinitePresentation ((chartDiagram 𝒰).obj j).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝒰.f j))
  have (j : 𝒰.I₀) : QuasiCompact ((chartDiagram 𝒰).obj j).hom :=
    inferInstanceAs (QuasiCompact (𝒰.f j))
  have (j : 𝒰.I₀) : QuasiSeparated ((chartDiagram 𝒰).obj j).hom :=
    inferInstanceAs (QuasiSeparated (𝒰.f j))
  have Hgeom : (geometricLocalStructure (c.π.app i) 𝒰 Y).Equifibered := by
    intro j k d
    apply IsPullback.of_map (Over.forget c.pt)
      ((geometricLocalStructure (c.π.app i) 𝒰 Y).naturality d)
    exact overPullback_map_isPullback Y.obj.hom
      ((Over.pullback (c.π.app i)).map ((chartDiagram 𝒰).map d))
  have H : (Functor.whiskerRight n (Over.pullback (c.π.app i))).Equifibered := by
    have h : Functor.whiskerRight n (Over.pullback (c.π.app i)) =
        e.hom ≫ geometricLocalStructure (c.π.app i) 𝒰 Y := NatTrans.ext (funext he)
    rw [h]
    exact (NatTrans.Equifibered.of_isIso e.hom).comp Hgeom
  obtain ⟨k, hk⟩ := exists_equifibered_stage D c hc i F (chartDiagram 𝒰) n H
  let a := D.map k.hom
  let b := c.π.app k.left
  let 𝒱 := 𝒰.pullback₁ a
  let F' := F ⋙ Over.pullback a
  let n' : F' ⟶ chartDiagram 𝒱 :=
    Functor.whiskerRight n (Over.pullback a) ≫ (chartPullbackIso 𝒰 a).inv
  have hn' : n'.Equifibered := hk.comp (NatTrans.Equifibered.of_isIso _)
  have (j : 𝒱.I₀) : IsFinite (n'.app j).left :=
    inferInstanceAs (IsFinite (transferredStructure 𝒰 a F.obj n.app j).left)
  have (j : 𝒱.I₀) : Etale (n'.app j).left :=
    inferInstanceAs (Etale (transferredStructure 𝒰 a F.obj n.app j).left)
  let e' : F' ⋙ Over.pullback b ≅ geometricLocalDiagram b 𝒱 Y :=
    Functor.associator F (Over.pullback a) (Over.pullback b) ≪≫
      Functor.isoWhiskerLeft F (overCompNatIso a b (c.π.app i) (c.w k.hom)) ≪≫
      e ≪≫ (geometricModelTransferIso 𝒰 a b (c.π.app i) (c.w k.hom) Y).symm
  refine ⟨k, gluedCover 𝒱 F' n' hn', ⟨?_⟩⟩
  exact baseChangeIsoOfCocone 𝒱 F' n' hn' b Y (geometricLocalDiagram b 𝒱 Y)
    (geometricLocalCocone b 𝒱 Y) (geometricLocalCoconeIsColimit b 𝒱 Y) e' (Iso.refl _)

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
