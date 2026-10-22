/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Epimorphism

/-!
# Detection of the original pulled-back closed ideal

Epimorphy of the original canonical ideal map of a commutative square of
closed immersions forces equality of the original pulled-back ideal and
the original target ideal. The proof compares their actual inclusions into
the structure module. No flatness, finiteness or Cartier hypothesis is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Hom

private theorem ker_eq_of_idealModule_iso
    {D E X : Scheme.{u}} (j : D ⟶ X) (i : E ⟶ X)
    [QuasiCompact j] [QuasiCompact i]
    (e : idealModule j ≅ idealModule i)
    (he : e.hom ≫ idealInclusion i = idealInclusion j) : j.ker = i.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [j.ker_apply U, i.ker_apply U]
  let ev : X.Modules ⥤ ModuleCat Γ(X, U.1) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let eU := (ev.mapIso e).toLinearEquiv
  let eK := (idealSectionsEquiv j U.1).symm.trans
    (eU.trans (idealSectionsEquiv i U.1))
  have hval (r : RingHom.ker (j.app U.1).hom) :
      (eK r : Γ(X, U.1)) = r := by
    change (idealSectionsEquiv i U.1
      (e.hom.val.app (op U.1) ((idealSectionsEquiv j U.1).symm r)) : Γ(X, U.1)) = r
    rw [idealSectionsEquiv_val]
    let s := (idealSectionsEquiv j U.1).symm r
    have hi : (idealInclusion i).val.app (op U.1) (e.hom.val.app (op U.1) s) =
        (idealInclusion j).val.app (op U.1) s :=
      congrArg (fun t => t.val.app (op U.1) s) he
    exact hi.trans ((idealSectionsEquiv_val j U.1 s).symm.trans
      (congrArg Subtype.val ((idealSectionsEquiv j U.1).apply_symm_apply r)))
  ext r
  constructor
  · intro hr
    simpa only [hval] using (eK ⟨r, hr⟩).property
  · intro hr
    obtain ⟨s, hs⟩ := eK.surjective ⟨r, hr⟩
    have hv : (s : Γ(X, U.1)) = r :=
      (hval s).symm.trans (congrArg Subtype.val hs)
    exact hv ▸ s.property

/-- Epimorphy of the original canonical ideal pullback map detects equality
of the actual pulled-back ideal and the original closed-immersion ideal. -/
theorem ker_comap_eq_of_idealPullbackMap_epi
    {D Z E X : Scheme.{u}} (c : D ⟶ Z) (i : E ⟶ X) (f : X ⟶ Z) (a : E ⟶ D)
    (h : a ≫ c = i ≫ f) [IsClosedImmersion c] [IsClosedImmersion i]
    [Epi (idealPullbackMap c i f a h)] : c.ker.comap f = i.ker := by
  let j := pullback.snd c f
  let ψ := idealPullbackMap c j f (pullback.fst c f)
    (pullback.condition (f := c) (g := f))
  let φ := idealPullbackMap c i f a h
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  have : Epi ψ := idealPullbackMap_epi_of_isPullback c j f (pullback.fst c f)
    (pullback.condition (f := c) (g := f)) (IsPullback.of_hasPullback c f)
  have ht : ψ ≫ idealInclusion j = φ ≫ idealInclusion i := by
    dsimp only [ψ, φ]
    rw [idealPullbackMap_inclusion, idealPullbackMap_inclusion]
  have hz : idealInclusion j ≫ structureModuleMap i = 0 := by
    apply (cancel_epi ψ).mp
    calc
      ψ ≫ (idealInclusion j ≫ structureModuleMap i) =
          (ψ ≫ idealInclusion j) ≫ structureModuleMap i := (Category.assoc _ _ _).symm
      _ = (φ ≫ idealInclusion i) ≫ structureModuleMap i :=
        congrArg (fun t => t ≫ structureModuleMap i) ht
      _ = ψ ≫ 0 := by simp only [Category.assoc, idealInclusion_structureMap, comp_zero]
  let τ : idealModule j ⟶ idealModule i :=
    kernel.lift (structureModuleMap i) (idealInclusion j) hz
  have hτ : τ ≫ idealInclusion i = idealInclusion j := kernel.lift_ι _ _ _
  have hfactor : ψ ≫ τ = φ := by
    apply (cancel_mono (idealInclusion i)).mp
    rw [Category.assoc, hτ]
    exact ht
  have : Epi (ψ ≫ τ) := by rw [hfactor]; infer_instance
  let : Epi τ := epi_of_epi ψ τ
  have : Mono (τ ≫ idealInclusion i) := by rw [hτ]; infer_instance
  let : Mono τ := mono_of_mono τ (idealInclusion i)
  let : IsIso τ := isIso_of_mono_of_epi τ
  have hji : j.ker = i.ker := ker_eq_of_idealModule_iso j i (asIso τ) hτ
  have hj : j.ker = c.ker.comap f := by
    change (pullback.snd c f).ker = c.ker.comap f
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion c f,
      ← Hom.ker_comp_of_isIso (pullbackSymmetry c f).hom (pullback.fst f c)]
    simp
  exact hj.symm.trans hji

end AlgebraicGeometry.Scheme.Hom
