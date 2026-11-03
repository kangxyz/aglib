/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedClassFiniteConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Finite-constant presentation of an original generic coefficient class

The coefficient is pulled back from the original coefficient base. Its generic
restriction is normalized by the original inverse-image square, and the actual
finite-Galois class theorem supplies the finite constant class. The resulting
coefficient arrow lands in the pullback along the original two-stage composite.
No generic vanishing, injectivity or normality is assumed or concluded.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX eG eL
attribute [local instance] hasSheafifyLarge

/-- Complete original coefficient presentation transport before inserting
field pullbacks and their native inverse-image square. -/
private theorem presentation_transport
    {Y V W : Scheme.{u}} (f₀ : V ⟶ Y) (f₁ : W ⟶ V)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eG} (AbelianSheaf.{u, u + 1} V)]
    [HasExt.{eL} (AbelianSheaf.{u, u + 1} W)]
    (M : AbelianSheaf.{u, u + 1} Y) (N : AbelianSheaf.{u, u + 1} V)
    (C : AbelianSheaf.{u, u + 1} W) (ε : N ≅ (inverseImage f₀).obj M)
    (q : ℕ) (c : Sheaf.H.{eX} M q) (β₀ : C ⟶ (inverseImage f₁).obj N)
    (d : Sheaf.H.{eL} C q)
    (hd : Sheaf.H.map β₀ q d = cohomologyPullback.{u, eG, eL} f₁ N q
      (Sheaf.H.map ε.inv q (cohomologyPullback.{u, eX, eG} f₀ M q c))) :
    Sheaf.H.map (β₀ ≫ (inverseImage f₁).map ε.hom ≫
      (inverseImageComp f₀ f₁).inv.app M) q d =
      cohomologyPullback.{u, eX, eL} (f₁ ≫ f₀) M q c := by
  let cη := Sheaf.H.map ε.inv q (cohomologyPullback.{u, eX, eG} f₀ M q c)
  have hε : Sheaf.H.map ε.hom q cη =
      cohomologyPullback.{u, eX, eG} f₀ M q c := by
    dsimp only [cη]
    rw [← Sheaf.H.map_comp_apply, ε.inv_hom_id]
    simp only [Sheaf.H.map_id_apply]
  have hd₁ : Sheaf.H.map (β₀ ≫ (inverseImage f₁).map ε.hom) q d =
      cohomologyPullback.{u, eG, eL} f₁ ((inverseImage f₀).obj M) q
        (cohomologyPullback.{u, eX, eG} f₀ M q c) := by
    rw [Sheaf.H.map_comp_apply, hd, ← cohomologyPullback_coefficientMap]
    exact congrArg (cohomologyPullback.{u, eG, eL} f₁ ((inverseImage f₀).obj M) q) hε
  let εc := (inverseImageComp f₀ f₁).app M
  rw [← Category.assoc, Sheaf.H.map_comp_apply, hd₁,
    ← cohomologyPullback_comp.{u, eX, eG, eL} f₀ f₁ M q c,
    ← Sheaf.H.map_comp_apply]
  change Sheaf.H.map (εc.hom ≫ εc.inv) q _ = _
  rw [εc.hom_inv_id]
  simp only [Sheaf.H.map_id_apply]

variable (B L : Type u) [CommRing B] [IsDomain B] [Field L]
  [Algebra B L] [IsFractionRing B L]
  {Y : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]

local notation "γ" => Spec.algebraMap B L
local notation "f₀" => pullback.fst e γ
local notation "e₀" => pullback.snd e γ

omit [IsDomain B] [IsFractionRing B L] in
/-- The original generic class has an actual finite-constant presentation after
one produced finite Galois extension. The original and both field-stage Ext
worlds remain independent. The coefficient is required to come from `Spec B`.
-/
theorem exists_generic_finiteGalois_coefficient_presentation
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eG} (AbelianSheaf.{u, u + 1} (pullback e γ))]
    [∀ K : FiniteGaloisIntermediateField L (SeparableClosure L),
      HasExt.{eL} (AbelianSheaf.{u, u + 1} (pullback e₀ (Spec.algebraMap L K)))]
    [UnivLE.{u + 1, eG}]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of B)))
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    (q : ℕ) (c : Sheaf.H.{eX} ((inverseImage e).obj F) q) :
    ∃ (K : FiniteGaloisIntermediateField L (SeparableClosure L))
      (C : Type u) (_ : AddCommGroup C) (_ : Finite C),
      (∀ z : C, n • z = 0) ∧
      ∃ (d : Sheaf.H.{eL} (ConstantFinite.coefficient C
          (pullback e₀ (Spec.algebraMap L K))) q)
        (β : ConstantFinite.coefficient C (pullback e₀ (Spec.algebraMap L K)) ⟶
          (inverseImage (pullback.fst e₀ (Spec.algebraMap L K) ≫ f₀)).obj
            ((inverseImage e).obj F)),
        Sheaf.H.map β q d = cohomologyPullback.{u, eX, eL}
          (pullback.fst e₀ (Spec.algebraMap L K) ≫ f₀) ((inverseImage e).obj F) q c := by
  let : QuasiSeparatedSpace (pullback e γ : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated e₀
  let Fη := (inverseImage γ).obj F
  have hFη : n • 𝟙 Fη = 0 := by
    have h := congrArg (inverseImage γ).map hF
    rw [Functor.map_nsmul, (inverseImage γ).map_id F, Functor.map_zero] at h
    exact h
  let ε := (inverseImageSquareIso e e₀ γ f₀ pullback.condition.symm).app F
  let cη : Sheaf.H.{eG} ((inverseImage e₀).obj Fη) q :=
    Sheaf.H.map ε.inv q (cohomologyPullback.{u, eX, eG} f₀ ((inverseImage e).obj F) q c)
  obtain ⟨F', a, _, _, K, C, hC, hfin, hCn, t, d, hd⟩ :=
    Fields.exists_finiteGalois_constant_class.{u, eG, eL} L Fη n hn hFη e₀ q cη
  let := hC
  let := hfin
  let f₁ := pullback.fst e₀ (Spec.algebraMap L K)
  let e₁ := pullback.snd e₀ (Spec.algebraMap L K)
  let tC := Fields.constantTrivializationAlongSquare e₀ f₁ e₁
    (Spec.algebraMap L K) pullback.condition F' (ConstantFinite.value C) t
  let β₀ := tC.inv ≫ (inverseImage f₁).map ((inverseImage e₀).map a)
  have hd₀ : Sheaf.H.map β₀ q d =
      cohomologyPullback.{u, eG, eL} f₁ ((inverseImage e₀).obj Fη) q cη := hd
  have htransport := presentation_transport f₀ f₁ ((inverseImage e).obj F)
    ((inverseImage e₀).obj Fη) (ConstantFinite.coefficient C _) ε q c β₀ d hd₀
  exact ⟨K, C, hC, hfin, hCn, d,
    β₀ ≫ (inverseImage f₁).map ε.hom ≫ (inverseImageComp f₀ f₁).inv.app _, htransport⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
