/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward

/-!
# The coherent completion functor for an arbitrary ideal sheaf

The terms are the original pushforwards of ordinary pullbacks to the actual
closed thickenings. The reduction maps are uniquely characterized by the
original adjunction units. No effectivity or exactness is assumed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- Ideal-sheaf powers decrease, checked on their original affine ideals. -/
theorem idealSheaf_pow_le {n m : ℕ} (h : n ≤ m) : K ^ m ≤ K ^ n := by
  intro U
  exact Ideal.pow_le_pow_right h

/-- The native inverse diagram of closed-thickening quotients. -/
def idealSheafQuotientTower (F : X.Modules) : ℕᵒᵖ ⥤ X.Modules where
  obj n := (idealSheafQuotientFunctor X (K ^ n.unop)).obj F
  map f := idealSheafQuotientMap X (K ^ _) (idealSheaf_pow_le X K (leOfHom f.unop)) F
  map_id n := idealSheafQuotientMap_refl X (K ^ n.unop) F
  map_comp _ _ := (idealSheafQuotientMap_comp X _ _ _ F).symm

/-- Original coefficient maps induce maps of the original thickening diagrams. -/
def idealSheafQuotientTowerHom {F G : X.Modules} (f : F ⟶ G) :
    idealSheafQuotientTower X K F ⟶ idealSheafQuotientTower X K G where
  app n := (idealSheafQuotientFunctor X (K ^ n.unop)).map f
  naturality m _ g :=
    (idealSheafQuotientMap_naturality X (K ^ m.unop)
      (idealSheaf_pow_le X K (leOfHom g.unop)) f).symm

/-- The original units form the reduction map from constant coefficients. -/
def idealSheafQuotientTowerUnit (F : X.Modules) :
    (Functor.const ℕᵒᵖ).obj F ⟶ idealSheafQuotientTower X K F where
  app n := (idealSheafQuotientUnit X (K ^ n.unop)).app F
  naturality m n g := by
    change 𝟙 F ≫ (idealSheafQuotientUnit X (K ^ n.unop)).app F =
      (idealSheafQuotientUnit X (K ^ m.unop)).app F ≫
        idealSheafQuotientMap X (K ^ m.unop)
          (idealSheaf_pow_le X K (leOfHom g.unop)) F
    simp

variable [IsLocallyNoetherian X]

/-- Closed-thickening quotients of a coherent coefficient remain coherent. -/
theorem idealSheafQuotient_coherent {F : X.Modules}
    (hF : QuasiCoherent.affineLocallyFiniteType X F) :
    QuasiCoherent.affineLocallyFiniteType X ((idealSheafQuotientFunctor X K).obj F) :=
  QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward K.subschemeι
    (QuasiCoherent.affineLocallyFiniteType_pullback K.subschemeι hF)

/-- Completion of a coherent coefficient satisfies the actual formal-system
conditions, without a completeness assumption on the scheme or its rings. -/
theorem idealSheafQuotientTower_isAdicSystem (F : X.CoherentSheaf) :
    IsAdicSystem X K (idealSheafQuotientTower X K F.obj) where
  coherent n := idealSheafQuotient_coherent X (K ^ n) F.property
  annihilated n := idealSheafQuotient_killed X (K ^ n) F.obj
  reduction n := ⟨idealSheafQuotientReductionIso X (K ^ (n + 1))
    (idealSheaf_pow_le X K (Nat.le_succ n)) F.obj,
    idealSheafQuotientUnit_reductionIso_hom X (K ^ (n + 1))
      (idealSheaf_pow_le X K (Nat.le_succ n)) F.obj⟩

/-- The actual coherent completion functor along an arbitrary ideal sheaf. -/
def completionFunctor : X.CoherentSheaf ⥤ AdicSystem X K where
  obj F := ⟨idealSheafQuotientTower X K F.obj, idealSheafQuotientTower_isAdicSystem X K F⟩
  map f := ObjectProperty.homMk (idealSheafQuotientTowerHom X K f.hom)
  map_id F := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientFunctor X (K ^ n.unop)).map_id F.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientFunctor X (K ^ n.unop)).map_comp f.hom g.hom

@[simp]
theorem completionFunctor_obj_diagram (F : X.CoherentSheaf) :
    ((completionFunctor X K).obj F).obj = idealSheafQuotientTower X K F.obj := rfl

@[simp]
theorem completionFunctor_map_app {F G : X.CoherentSheaf} (f : F ⟶ G) (n : ℕ) :
    ((completionFunctor X K).map f).hom.app (op n) =
      (idealSheafQuotientFunctor X (K ^ n)).map f.hom := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
