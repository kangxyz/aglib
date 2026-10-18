/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenTensor
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# The original conormal wedge square on displayed sheaf objects

The comparison proposition contains exactly the original arrow equality.
Its computational equation is explicit, so native consumers can retain
shared sheaf-object heads while instantiating the original wedge proof.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem normalColumn_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {N X Y : C} {N' X' Y' : D} (e : N ⟶ X) (f : X ⟶ Y)
    (e' : N' ⟶ X') (f' : X' ⟶ Y')
    (aN : F.obj N ⟶ N') (aX : F.obj X ⟶ X') (aY : F.obj Y ⟶ Y')
    (hN : F.map e ≫ aX = aN ≫ e') (hF : F.map f ≫ aY = aX ≫ f') :
    F.map (e ≫ f) ≫ aY = aN ≫ e' ≫ f' := by
  rw [F.map_comp, Category.assoc, hF, ← Category.assoc, hN, Category.assoc]

/-- The literal normal/tangent tensor and middle arrow square on displayed sheaf heads. -/
@[no_expose] def CanonicalDeterminantOpenSquare
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (C Q P : X.Modules) (C' Q' P' : X'.Modules)
    (Δ : tensorSheaf X C Q ≅ P) (Δ' : tensorSheaf X' C' Q' ≅ P')
    (aC : (restrictFunctor j).obj C ⟶ C') (aQ : (restrictFunctor j).obj Q ⟶ Q')
    (aP : (restrictFunctor j).obj P ⟶ P') : Prop :=
  (restrictFunctor j).map Δ.hom ≫ aP = canonicalTensorOpenMap j C Q C' Q' aC aQ ≫ Δ'.hom

/-- The comparison is exactly equality of the same original tensor and middle arrows. -/
theorem canonicalDeterminantOpenSquare_iff
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (C Q P : X.Modules) (C' Q' P' : X'.Modules)
    (Δ : tensorSheaf X C Q ≅ P) (Δ' : tensorSheaf X' C' Q' ≅ P')
    (aC : (restrictFunctor j).obj C ⟶ C') (aQ : (restrictFunctor j).obj Q ⟶ Q')
    (aP : (restrictFunctor j).obj P ⟶ P') :
    CanonicalDeterminantOpenSquare j C Q P C' Q' P' Δ Δ' aC aQ aP ↔
      (restrictFunctor j).map Δ.hom ≫ aP =
        canonicalTensorOpenMap j C Q C' Q' aC aQ ≫ Δ'.hom := Iff.rfl

/-- The native exterior arrow retains the original prescribed images of its wedge vectors. -/
theorem canonicalExteriorOpenMap_wedge_congr
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) (N' : X'.Modules) (c : ℕ) (f : (restrictFunctor j).obj N ⟶ N')
    (U : X'.Opens) (v : Fin c → N.val.obj (op (j ''ᵁ U)))
    (v' : Fin c → N'.val.obj (op U)) (hv : ∀ i, f.val.app (op U) (v i) = v' i) :
    (canonicalExteriorOpenMap j N N' c f).val.app (op U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf N c).app (op (j ''ᵁ U)) v) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf N' c).app (op U) v' :=
  (canonicalExteriorOpenMap_wedge j N N' c f U v).trans
    (congrArg ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf N' c).app (op U))
      (funext hv))

/-- The original normal-first determinant square, with its actual sheaf objects retained. -/
@[no_expose] def canonicalConormalDeterminantSquare
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (NC : X.Modules) (NC' : X'.Modules)
    (K : ShortComplex X.Modules) (K' : ShortComplex X'.Modules) (c d : ℕ)
    (Δ : tensorSheaf X (moduleExteriorPower X NC c)
      (moduleExteriorPower X K.X₃ d) ≅ moduleExteriorPower X K.X₂ (c + d))
    (Δ' : tensorSheaf X' (moduleExteriorPower X' NC' c)
      (moduleExteriorPower X' K'.X₃ d) ≅ moduleExteriorPower X' K'.X₂ (c + d))
    (aC : (restrictFunctor j).obj NC ⟶ NC') (φK : K.map (restrictFunctor j) ⟶ K') : Prop :=
  (restrictFunctor j).map Δ.hom ≫ canonicalExteriorOpenMap j K.X₂ K'.X₂ (c + d) φK.τ₂ =
    canonicalTensorOpenMap j (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d)
      (moduleExteriorPower X' NC' c) (moduleExteriorPower X' K'.X₃ d)
      (canonicalExteriorOpenMap j NC NC' c aC)
      (canonicalExteriorOpenMap j K.X₃ K'.X₃ d φK.τ₃) ≫ Δ'.hom

/-- The comparison proposition states literally equality of the original exterior/tensor arrows. -/
theorem canonicalConormalDeterminantSquare_iff
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    (NC : X.Modules) (NC' : X'.Modules)
    (K : ShortComplex X.Modules) (K' : ShortComplex X'.Modules) (c d : ℕ)
    (Δ : tensorSheaf X (moduleExteriorPower X NC c)
      (moduleExteriorPower X K.X₃ d) ≅ moduleExteriorPower X K.X₂ (c + d))
    (Δ' : tensorSheaf X' (moduleExteriorPower X' NC' c)
      (moduleExteriorPower X' K'.X₃ d) ≅ moduleExteriorPower X' K'.X₂ (c + d))
    (aC : (restrictFunctor j).obj NC ⟶ NC') (φK : K.map (restrictFunctor j) ⟶ K') :
    canonicalConormalDeterminantSquare j NC NC' K K' c d Δ Δ' aC φK ↔
      (restrictFunctor j).map Δ.hom ≫ canonicalExteriorOpenMap j K.X₂ K'.X₂ (c + d) φK.τ₂ =
        canonicalTensorOpenMap j (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d)
          (moduleExteriorPower X' NC' c) (moduleExteriorPower X' K'.X₃ d)
          (canonicalExteriorOpenMap j NC NC' c aC)
          (canonicalExteriorOpenMap j K.X₃ K'.X₃ d φK.τ₃) ≫ Δ'.hom := Iff.rfl

section AbstractSquare
variable {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
  (NC : X.Modules) (NC' : X'.Modules)
  (K : ShortComplex X.Modules) (K' : ShortComplex X'.Modules)
  (eN : NC ≅ K.X₁) (eN' : NC' ≅ K'.X₁) (c d : ℕ)
  (Δ : tensorSheaf X (moduleExteriorPower X NC c)
    (moduleExteriorPower X K.X₃ d) ≅ moduleExteriorPower X K.X₂ (c + d))
  (Δ' : tensorSheaf X' (moduleExteriorPower X' NC' c)
    (moduleExteriorPower X' K'.X₃ d) ≅ moduleExteriorPower X' K'.X₂ (c + d))
  (aC : (restrictFunctor j).obj NC ⟶ NC') (φK : K.map (restrictFunctor j) ⟶ K')
  (hN : (restrictFunctor j).map eN.hom ≫ φK.τ₁ = aC ≫ eN'.hom)
  (hSource : ∀ (U : X.Opens) (v : Fin c → NC.val.obj (op U))
    (w : Fin d → K.X₂.val.obj (op U)),
    Δ.hom.val.app (op U) (moduleTensorSection X (moduleExteriorPower X NC c)
      (moduleExteriorPower X K.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app (op U)
        (fun i => K.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K.f.val.app (op U) (eN.hom.val.app (op U) (v i))) w))
  (hTarget : ∀ (U : X'.Opens) (v : Fin c → NC'.val.obj (op U))
    (w : Fin d → K'.X₂.val.obj (op U)),
    Δ'.hom.val.app (op U) (moduleTensorSection X' (moduleExteriorPower X' NC' c)
      (moduleExteriorPower X' K'.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf NC' c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₃ d).app (op U)
        (fun i => K'.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K'.f.val.app (op U) (eN'.hom.val.app (op U) (v i))) w))

local notation "NM" => ShortComplex.X₂ K
local notation "NM'" => ShortComplex.X₂ K'
local notation "NQ" => ShortComplex.X₃ K
local notation "NQ'" => ShortComplex.X₃ K'

include hN hSource hTarget in
/-- Actual commuting conormal arrows preserve the same original normal-first wedge value. -/
private theorem determinantSquare_section
    (U : X'.Opens) (v : Fin c → (NC).val.obj (op (j ''ᵁ U)))
    (w : Fin d → (NM).val.obj (op (j ''ᵁ U))) :
    let Ctop := moduleExteriorPower X NC c
    let Qtop := moduleExteriorPower X NQ d
    let Ctop' := moduleExteriorPower X' NC' c
    let Qtop' := moduleExteriorPower X' NQ' d
    let kC := canonicalExteriorOpenMap j NC NC' c aC
    let kQ := canonicalExteriorOpenMap j NQ NQ' d φK.τ₃
    let kM := canonicalExteriorOpenMap j NM NM' (c + d) φK.τ₂
    let kS := canonicalTensorOpenMap j Ctop Qtop Ctop' Qtop' kC kQ
    let z := moduleTensorSection X Ctop Qtop (j ''ᵁ U)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app
        (op (j ''ᵁ U)) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NQ d).app
        (op (j ''ᵁ U)) (fun k => (K).g.val.app (op (j ''ᵁ U)) (w k)))
    (((restrictFunctor j).map Δ.hom) ≫ kM).val.app (op U) z =
      (kS ≫ Δ'.hom).val.app (op U) z := by
  intro Ctop Qtop Ctop' Qtop' kC kQ kM kS z
  have hG : (restrictFunctor j).map (K).g ≫ φK.τ₃ = φK.τ₂ ≫ (K').g := φK.comm₂₃.symm
  have hF : (restrictFunctor j).map ((eN).hom ≫ (K).f) ≫ φK.τ₂ =
      aC ≫ (eN').hom ≫ (K').f :=
    normalColumn_square (C := X.Modules) (D := X'.Modules) (restrictFunctor j)
      (eN).hom (K).f (eN').hom (K').f aC φK.τ₁ φK.τ₂ hN φK.comm₁₂.symm
  let W := j ''ᵁ U
  let fv := fun k => (K).f.val.app (op W) ((eN).hom.val.app (op W) (v k))
  let v' := fun k => aC.val.app (op U) (v k)
  let w' := fun k => φK.τ₂.val.app (op U) (w k)
  have hGv (k : Fin d) : φK.τ₃.val.app (op U) ((K).g.val.app (op W) (w k)) =
      (K').g.val.app (op U) (w' k) :=
    congrArg (fun f => f.val.app (op U) (w k)) hG
  have hFv (k : Fin c) : φK.τ₂.val.app (op U) (fv k) =
      (K').f.val.app (op U) ((eN').hom.val.app (op U) (v' k)) :=
    congrArg (fun f => f.val.app (op U) (v k)) hF
  have hΔ := hSource W v w
  have hL := (congrArg (kM.val.app (op U)) hΔ).trans
    (canonicalExteriorOpenMap_wedge j NM NM' (c + d) φK.τ₂ U (Fin.append fv w))
  have hS := canonicalTensorOpenMap_section j Ctop Qtop Ctop' Qtop' kC kQ U
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app (op W) v)
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NQ d).app (op W)
      (fun k => (K).g.val.app (op W) (w k)))
  have hC := canonicalExteriorOpenMap_wedge j NC NC' c aC U v
  have hQ := (canonicalExteriorOpenMap_wedge j NQ NQ' d φK.τ₃ U
    (fun k => (K).g.val.app (op W) (w k))).trans
      (congrArg ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf NQ' d).app (op U))
        (funext hGv))
  have hS' := hS.trans (congrArg₂ (moduleTensorSection X' Ctop' Qtop' U) hC hQ)
  have hR := (congrArg (Δ'.hom.val.app (op U)) hS').trans
    (hTarget U v' w')
  have hfam : (fun k => φK.τ₂.val.app (op U) (Fin.append fv w k)) =
      Fin.append (fun k => (K').f.val.app (op U) ((eN').hom.val.app (op U) (v' k))) w' := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa only [Fin.append_left] using hFv k
    · simp only [Fin.append_right, w']
  exact hL.trans ((congrArg
    ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf NM' (c + d)).app (op U))
      hfam).trans hR.symm)

end AbstractSquare

private theorem determinantSquare_hom_ext {Z : Scheme.{u}} {L N : Z.Modules}
    (e : L ≅ SheafOfModules.unit Z.ringCatSheaf) (z : L.val.obj (op ⊤))
    (hz : e.hom.val.app (op ⊤) z = (1 : Γ(Z, ⊤))) {f g : L ⟶ N}
    (hfg : f.val.app (op ⊤) z = g.val.app (op ⊤) z) : f = g := by
  have hi : e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)) = z :=
    (congrArg (e.inv.val.app (op ⊤)) hz.symm).trans
      (congrArg (fun k => k.val.app (op ⊤) z) e.hom_inv_id)
  apply (cancel_epi e.inv).mp
  apply (unitHomGlobalSectionsEquiv Z N).injective
  change f.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤))) =
    g.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(Z, ⊤)))
  exact (congrArg (f.val.app (op ⊤)) hi).trans
    (hfg.trans (congrArg (g.val.app (op ⊤)) hi).symm)

section AbstractSquare
variable {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
  (NC : X.Modules) (NC' : X'.Modules)
  (K : ShortComplex X.Modules) (K' : ShortComplex X'.Modules)
  (eN : NC ≅ K.X₁) (eN' : NC' ≅ K'.X₁) (c d : ℕ)
  (Δ : tensorSheaf X (moduleExteriorPower X NC c)
    (moduleExteriorPower X K.X₃ d) ≅ moduleExteriorPower X K.X₂ (c + d))
  (Δ' : tensorSheaf X' (moduleExteriorPower X' NC' c)
    (moduleExteriorPower X' K'.X₃ d) ≅ moduleExteriorPower X' K'.X₂ (c + d))
  (aC : (restrictFunctor j).obj NC ⟶ NC') (φK : K.map (restrictFunctor j) ⟶ K')
  (hN : (restrictFunctor j).map eN.hom ≫ φK.τ₁ = aC ≫ eN'.hom)
  (hSource : ∀ (U : X.Opens) (v : Fin c → NC.val.obj (op U))
    (w : Fin d → K.X₂.val.obj (op U)),
    Δ.hom.val.app (op U) (moduleTensorSection X (moduleExteriorPower X NC c)
      (moduleExteriorPower X K.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app (op U)
        (fun i => K.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K.f.val.app (op U) (eN.hom.val.app (op U) (v i))) w))
  (hTarget : ∀ (U : X'.Opens) (v : Fin c → NC'.val.obj (op U))
    (w : Fin d → K'.X₂.val.obj (op U)),
    Δ'.hom.val.app (op U) (moduleTensorSection X' (moduleExteriorPower X' NC' c)
      (moduleExteriorPower X' K'.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf NC' c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₃ d).app (op U)
        (fun i => K'.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K'.f.val.app (op U) (eN'.hom.val.app (op U) (v i))) w))

include hN hSource hTarget in
/-- The original wedge laws and one genuine source unit frame prove the whole arrow square. -/
theorem canonicalConormalDeterminantSquare_of_wedgeFrame
    (eS : tensorSheaf X (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d) ≅
      SheafOfModules.unit X.ringCatSheaf)
    (v : Fin c → NC.val.obj (op (j ''ᵁ (⊤ : X'.Opens))))
    (w : Fin d → K.X₂.val.obj (op (j ''ᵁ (⊤ : X'.Opens))))
    (hz : eS.hom.val.app (op (j ''ᵁ (⊤ : X'.Opens)))
      (moduleTensorSection X (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d)
        (j ''ᵁ (⊤ : X'.Opens))
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app
          (op (j ''ᵁ (⊤ : X'.Opens))) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app
          (op (j ''ᵁ (⊤ : X'.Opens)))
          (fun i => K.g.val.app (op (j ''ᵁ (⊤ : X'.Opens))) (w i)))) =
      (1 : Γ(X, j ''ᵁ (⊤ : X'.Opens)))) :
    canonicalConormalDeterminantSquare j NC NC' K K' c d Δ Δ' aC φK := by
  let U : X'.Opens := ⊤
  let W := j ''ᵁ U
  let z := moduleTensorSection X (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d) W
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app (op W) v)
    ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app (op W)
      (fun i => K.g.val.app (op W) (w i)))
  let eR := (restrictFunctor j).mapIso eS ≪≫ restrictUnitIso j
  have hzR : eR.hom.val.app (op U) z = (1 : Γ(X', U)) :=
    (congrArg (j.appIso U).hom.hom hz).trans (map_one (j.appIso U).hom.hom)
  apply determinantSquare_hom_ext eR z hzR
  exact determinantSquare_section j NC NC' K K' eN eN' c d Δ Δ' aC φK hN
    hSource hTarget U v w

end AbstractSquare

section AbstractSquare
variable {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
  (NC : X.Modules) (NC' : X'.Modules)
  (K : ShortComplex X.Modules) (K' : ShortComplex X'.Modules)
  (eN : NC ≅ K.X₁) (eN' : NC' ≅ K'.X₁) (c d : ℕ)
  (Δ : tensorSheaf X (moduleExteriorPower X NC c)
    (moduleExteriorPower X K.X₃ d) ≅ moduleExteriorPower X K.X₂ (c + d))
  (Δ' : tensorSheaf X' (moduleExteriorPower X' NC' c)
    (moduleExteriorPower X' K'.X₃ d) ≅ moduleExteriorPower X' K'.X₂ (c + d))
  (aC : (restrictFunctor j).obj NC ⟶ NC') (φK : K.map (restrictFunctor j) ⟶ K')
  (hN : (restrictFunctor j).map eN.hom ≫ φK.τ₁ = aC ≫ eN'.hom)
  (hSource : ∀ (U : X.Opens) (v : Fin c → NC.val.obj (op U))
    (w : Fin d → K.X₂.val.obj (op U)),
    Δ.hom.val.app (op U) (moduleTensorSection X (moduleExteriorPower X NC c)
      (moduleExteriorPower X K.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app (op U)
        (fun i => K.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K.f.val.app (op U) (eN.hom.val.app (op U) (v i))) w))
  (hTarget : ∀ (U : X'.Opens) (v : Fin c → NC'.val.obj (op U))
    (w : Fin d → K'.X₂.val.obj (op U)),
    Δ'.hom.val.app (op U) (moduleTensorSection X' (moduleExteriorPower X' NC' c)
      (moduleExteriorPower X' K'.X₃ d) U
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf NC' c).app (op U) v)
      ((SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₃ d).app (op U)
        (fun i => K'.g.val.app (op U) (w i)))) =
    (SheafOfModulesOfCommRing.exteriorPowerMk X'.sheaf K'.X₂ (c + d)).app (op U)
      (Fin.append (fun i => K'.f.val.app (op U) (eN'.hom.val.app (op U) (v i))) w))

include hN hSource hTarget in
/-- The original wedge proof yields the same whole square with only its raw top sheaf heads. -/
theorem canonicalDeterminantOpenSquare_of_wedgeFrame
    (eS : tensorSheaf X (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d) ≅
      SheafOfModules.unit X.ringCatSheaf)
    (v : Fin c → NC.val.obj (op (j ''ᵁ (⊤ : X'.Opens))))
    (w : Fin d → K.X₂.val.obj (op (j ''ᵁ (⊤ : X'.Opens))))
    (hz : eS.hom.val.app (op (j ''ᵁ (⊤ : X'.Opens)))
      (moduleTensorSection X (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d)
        (j ''ᵁ (⊤ : X'.Opens))
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf NC c).app
          (op (j ''ᵁ (⊤ : X'.Opens))) v)
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf K.X₃ d).app
          (op (j ''ᵁ (⊤ : X'.Opens)))
          (fun i => K.g.val.app (op (j ''ᵁ (⊤ : X'.Opens))) (w i)))) =
      (1 : Γ(X, j ''ᵁ (⊤ : X'.Opens)))) :
    CanonicalDeterminantOpenSquare j
      (moduleExteriorPower X NC c) (moduleExteriorPower X K.X₃ d)
      (moduleExteriorPower X K.X₂ (c + d))
      (moduleExteriorPower X' NC' c) (moduleExteriorPower X' K'.X₃ d)
      (moduleExteriorPower X' K'.X₂ (c + d)) Δ Δ'
      (canonicalExteriorOpenMap j NC NC' c aC)
      (canonicalExteriorOpenMap j K.X₃ K'.X₃ d φK.τ₃)
      (canonicalExteriorOpenMap j K.X₂ K'.X₂ (c + d) φK.τ₂) := by
  apply (canonicalDeterminantOpenSquare_iff j _ _ _ _ _ _ Δ Δ' _ _ _).mpr
  exact (canonicalConormalDeterminantSquare_iff j NC NC' K K' c d Δ Δ' aC φK).mp
    (canonicalConormalDeterminantSquare_of_wedgeFrame j NC NC' K K' eN eN' c d Δ Δ'
      aC φK hN hSource hTarget eS v w hz)

end AbstractSquare

end AlgebraicGeometry.Scheme.Modules
