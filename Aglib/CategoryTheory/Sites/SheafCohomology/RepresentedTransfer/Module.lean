/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantLinearNatTrans
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImages

/-! # The same represented trace with native scalar-linear coefficients

An existing underlying-source comparison identifies the native module functor
with the actual abelian product-test functor. Scalar naturality lifts that same
trace; faithfulness transports the original unit/rank equation.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace ModuleCat.Sheaf

universe c h r

variable {C : Type c} [Category.{h} C] (R : Type r) [CommRing R]
  (J : GrothendieckTopology C)


section ContinuousAdjunction

variable {D : Type c} [Category.{h} D] (K : GrothendieckTopology D)
  (L : D ⥤ C) (G : C ⥤ D) [L.IsContinuous K J] [G.IsContinuous J K]

/-- The original comparison for restriction followed by continuous direct image,
assembled from the two canonical underlying comparisons in their actual order. -/
def continuousCompositeUnderlyingIso :
    (L.sheafPushforwardContinuous (ModuleCat.{max c h} R) K J ⋙
        G.sheafPushforwardContinuous (ModuleCat.{max c h} R) J K) ⋙ underlying R J ≅
      underlying R J ⋙
        (L.sheafPushforwardContinuous AddCommGrpCat.{max c h} K J ⋙
          G.sheafPushforwardContinuous AddCommGrpCat.{max c h} J K) :=
  Functor.isoWhiskerLeft (L.sheafPushforwardContinuous (ModuleCat.{max c h} R) K J)
      (pushforwardUnderlyingIso R G J K) ≪≫
    Functor.isoWhiskerRight (pushforwardUnderlyingIso R L K J)
      (G.sheafPushforwardContinuous AddCommGrpCat.{max c h} J K)

/-- The canonical comparison retains the actual sheaf-adjunction unit, evaluated
at every original test. This uses only the original site adjunction. -/
theorem continuousCompositeUnderlyingIso_unit (adj : L ⊣ G)
    (F : Sheaf J (ModuleCat.{max c h} R)) :
    (underlying R J).map
        ((adj.sheafPushforwardContinuous (E := ModuleCat.{max c h} R) K J).unit.app F) ≫
      (continuousCompositeUnderlyingIso R J K L G).hom.app F =
    (adj.sheafPushforwardContinuous (E := AddCommGrpCat.{max c h}) K J).unit.app
      ((underlying R J).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rfl

end ContinuousAdjunction

variable
  (P : Sheaf J (ModuleCat.{max c h} R) ⥤ Sheaf J (ModuleCat.{max c h} R))
  [P.Linear R]
  (Q : Sheaf J AddCommGrpCat.{max c h} ⥤ Sheaf J AddCommGrpCat.{max c h})
  (e : P ⋙ underlying R J ≅ underlying R J ⋙ Q)
  (τ : Q ⟶ 𝟭 (Sheaf J AddCommGrpCat.{max c h}))

/-- Lift the original underlying trace, after its existing source comparison. -/
def traceOfUnderlying : P ⟶ 𝟭 (Sheaf J (ModuleCat.{max c h} R)) :=
  natTransOfUnderlying R J P (𝟭 _)
    (e.hom ≫ Functor.whiskerLeft (underlying R J) τ)

/-- Forgetting the lift gives exactly the original compared abelian trace. -/
@[simp]
theorem traceOfUnderlying_underlying (F : Sheaf J (ModuleCat.{max c h} R)) :
    (underlying R J).map ((traceOfUnderlying R J P Q e τ).app F) =
      e.hom.app F ≫ τ.app ((underlying R J).obj F) := rfl

/-- The same unit compatibility transports the proved original abelian rank. -/
theorem traceOfUnderlying_rank
    (η : 𝟭 (Sheaf J (ModuleCat.{max c h} R)) ⟶ P)
    (ηA : 𝟭 (Sheaf J AddCommGrpCat.{max c h}) ⟶ Q)
    (n : ℕ) (F : Sheaf J (ModuleCat.{max c h} R))
    (hη : (underlying R J).map (η.app F) ≫ e.hom.app F =
      ηA.app ((underlying R J).obj F))
    (hτ : ηA.app ((underlying R J).obj F) ≫ τ.app ((underlying R J).obj F) =
      n • 𝟙 ((underlying R J).obj F)) :
    η.app F ≫ (traceOfUnderlying R J P Q e τ).app F = n • 𝟙 F := by
  have hs : (underlying R J).map (n • 𝟙 F) =
      n • 𝟙 ((underlying R J).obj F) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext x
    rfl
  apply (underlying R J).map_injective
  rw [(underlying R J).map_comp, hs, traceOfUnderlying_underlying, ← Category.assoc, hη]
  exact hτ

end ModuleCat.Sheaf
