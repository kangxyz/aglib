/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! Canonical identity and composition transports for actual inverse image.

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, on frozen
interface basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u

/-- Canonical identity transport on the actual small étale site. -/
def siteBaseChangeId (X : Scheme.{u}) : siteBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk
      (asIso (pullback.fst U.hom (𝟙 X))) (by simpa using pullback.condition (f := U.hom) (g := 𝟙
        X)))
    (fun q => by
      apply MorphismProperty.Over.Hom.ext
      change pullback.lift _ _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q.left
      simp only [pullback.lift_fst])

/-- Canonical composition transport on small étale categories. -/
def siteBaseChangeComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    siteBaseChange (g ≫ f) ≅ siteBaseChange f ⋙ siteBaseChange g :=
  MorphismProperty.Over.pullbackComp g f

/-- The chosen inverse image of the identity is canonically the identity. -/
def inverseImageId (X : Scheme.{u}) : inverseImage (𝟙 X) ≅ 𝟭 (AbelianSheaf.{u, u + 1} X) := by
  let := hasSheafifyLarge X
  let adj := (siteBaseChange (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X)
  let e := Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
  exact (adj.ofNatIsoRight e).leftAdjointUniq Adjunction.id

/-- The chosen inverse images compose in the contravariant scheme direction. -/
def inverseImageComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    inverseImage (g ≫ f) ≅ inverseImage f ⋙ inverseImage g := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  let := hasSheafifyLarge T
  let adj := (siteBaseChange (g ≫ f)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology T)
  let adjf := (siteBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
  let adjg := (siteBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
  let e := Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)
  exact (Adjunction.leftAdjointCompIso adjf adjg adj e).symm

section ConstantTransport
variable (X : Scheme.{u})
local instance : HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  hasSheafifyLarge X

/-- Identity transport and constant-sheaf transport agree. -/
theorem inverseImageId_constant (A : AddCommGrpCat.{u + 1}) :
    (inverseImageId X).hom.app
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) =
    (inverseImageConstantIso (𝟙 X)).hom.app A := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal (@Etale :
    MorphismProperty Scheme.{u}) X
  let cAdj := constantSheafAdj (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} hT
  let adj := (siteBaseChange (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology X)
  let e := Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
  apply ((cAdj.comp adj).homEquiv _ _).injective
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp adj)
    (constantSheafAdj (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
      (hT.isTerminalObj (siteBaseChange (𝟙 X)))) A).symm
  change cAdj.homEquiv _ _ (adj.homEquiv _ _
    ((inverseImageId X).hom.app
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A))) = _
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj.ofNatIsoRight e) (Adjunction.id (C := AbelianSheaf.{u, u + 1} X))
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A)
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have h' : adj.homEquiv _ _ ((inverseImageId X).hom.app
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A)) =
      e.inv.app _ := by
    apply (cancel_mono (e.hom.app _)).mp
    exact h.trans (e.inv_hom_id_app _).symm
  rw [h']
  change (toSheafify (Scheme.smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj A)).app
      (Opposite.op (Scheme.Etale.mk (𝟙 X))) ≫
    (sheafify (Scheme.smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj A)).map
      ((siteBaseChangeId X).hom.app (Scheme.Etale.mk (𝟙 X))).op =
    (toSheafify (Scheme.smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj A)).app
      (Opposite.op ((siteBaseChange (𝟙 X)).obj (Scheme.Etale.mk (𝟙 X))))
  exact ((toSheafify (Scheme.smallEtaleTopology X) ((Functor.const X.Etaleᵒᵖ).obj A)).naturality
      ((siteBaseChangeId X).hom.app (Scheme.Etale.mk (𝟙 X))).op).symm.trans (Category.id_comp _)

universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Pullback along the identity is the identity on actual H¹ after the
canonical coefficient identification. -/
theorem h1Pullback_id (L : AbelianSheaf.{u, u + 1} X) (a : H1Etale X L) :
    coefficientMap ((inverseImageId X).hom.app L) (h1Pullback (𝟙 X) L a) = a := by
  change ((Abelian.Ext.mk₀ _).comp
      (a.mapExactFunctor (inverseImage (𝟙 X))) (zero_add 1)).comp
        (Abelian.Ext.mk₀ ((inverseImageId X).hom.app L)) (add_zero 1) = a
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Abelian.Ext.id_mapExactFunctor]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, inverseImageId_constant]
  simp

end ConstantTransport
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 b8e6328d6c9cb65e6417c00fe39bcae088c140491f5370d6303ec6a7bfa816bf.
Definitions, hypotheses and universes are retained modulo native names. -/
