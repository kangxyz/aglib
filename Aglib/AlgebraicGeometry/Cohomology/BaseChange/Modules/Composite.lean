/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.UnitTensor
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.PullbackComposition
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.RingTheory.LocalRing.ResidueFieldComap

/-!
# Iterated cohomology base change through a commutative square of rings

Let `f : X ⟶ Spec A`, and let `σ : A →+* B`, `τ : B →+* C`, `π : A →+* K`, `ψ : K →+* C` be ring
maps with `τ ∘ σ = ψ ∘ π`. Write `X_B = X ×_{Spec A} Spec B` with projections `p`, `f_B`,
`(X_B)_C = X_B ×_{Spec B} Spec C` with first projection `p'`, and `X_K = X ×_{Spec A} Spec K`
with first projection `p_K`. The lift `g : (X_B)_C ⟶ X_K` of `p' ≫ p` and `Spec ψ`
(`baseChangeCompLift`) makes a cartesian square over `Spec ψ`
(`isPullback_baseChangeCompLift`). Along it the comparison `g^* p_K^* M ≅ p'^* p^* M`
(`pullbackSquareCoefficientIso`, in `Functoriality/Modules/PullbackComposition`) is compatible
with the pullback maps on cohomology.

The core statement is made at variable schemes, morphisms, rings and structure maps
(`isIso_moduleCohomologyTensorMap_comp_of_square`): for a commutative square `g ≫ pK = p' ≫ p`
over `τ ∘ σ = ψ ∘ π`, the composite of the tensor map along `p` (extended along `τ`) with the
tensor map along `p'` is, up to `ModuleCat.extendScalarsComp` and
`ModuleCat.extendScalarsCongrIso`, the composite of the tensor map along `pK` (extended along
`ψ`), the tensor map along `g` and the coefficient comparison; both are checked on `1 ⊗ x`
(`moduleCohomologyPullback_pullbackSquare_apply`). Stating it at variable data keeps the kernel
from comparing concrete fibre products.

When `ψ` is flat and `f` is quasi-compact and separated, flat base change along `ψ` on `X_K`
(`isIso_moduleCohomologyTensorMap_baseChangeCompLift`) gives:
* if the base-change map of `M` along `π` is an isomorphism in degree `n`, then the composite
  `C ⊗_B (B ⊗_A H^n(X, M)) ⟶ C ⊗_B H^n(X_B, p^* M) ⟶ H^n((X_B)_C, p'^* p^* M)` of the two
  base-change maps is an isomorphism (`isIso_moduleCohomologyBaseChangeMap_comp_of_isIso`);
* if `H^n(X_K, p_K^* M) = 0`, then `H^n((X_B)_C, p'^* p^* M) = 0`
  (`subsingleton_moduleCohomology_baseChangeComp`).

For residue fields, `K = κ(s)`, `C = κ(t)` with `s` the image of `t ∈ Spec B`, these say that the
fibres of the base change `p^* M` are the field base changes of the fibres of `M`, with their
fibre maps. This is the fibre comparison in the proof of the universal property of the
flattening stratification, Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 4.3 (ii), pp. 22–23.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X : Scheme.{u}} {A B C K : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing K]
  (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (τ : B →+* C) (π : A →+* K) (ψ : K →+* C)

/-- The two composite spectrum maps of a commutative square of rings agree. -/
theorem specMap_comp_specMap_eq (h : τ.comp σ = ψ.comp π) :
    Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom σ) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

/-- The square defining `baseChangeCompLift` commutes. -/
theorem baseChangeCompLift_condition (h : τ.comp σ = ψ.comp π) :
    (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom σ))) ≫ f =
      (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)) ≫ Spec.map (CommRingCat.ofHom ψ)) ≫
          Spec.map (CommRingCat.ofHom π) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
    specMap_comp_specMap_eq σ τ π ψ h, Category.assoc]

/-- The comparison `g : (X_B)_C ⟶ X_K` over `Spec ψ`, the lift of `p' ≫ p`. -/
def baseChangeCompLift (h : τ.comp σ = ψ.comp π) :
    pullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) (Spec.map (CommRingCat.ofHom τ)) ⟶
      pullback f (Spec.map (CommRingCat.ofHom π)) :=
  pullback.lift _ _ (baseChangeCompLift_condition f σ τ π ψ h)

/-- The comparison `g` lies over the composite projection `p' ≫ p` to `X`. -/
theorem baseChangeCompLift_fst (h : τ.comp σ = ψ.comp π) :
    baseChangeCompLift f σ τ π ψ h ≫ pullback.fst f (Spec.map (CommRingCat.ofHom π)) =
      pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom σ)) :=
  pullback.lift_fst _ _ _

/-- The comparison `g` lies over `Spec ψ`. -/
theorem baseChangeCompLift_snd (h : τ.comp σ = ψ.comp π) :
    baseChangeCompLift f σ τ π ψ h ≫ pullback.snd f (Spec.map (CommRingCat.ofHom π)) =
      pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)) ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_snd _ _ _

/-- **The comparison square is cartesian**: `(X_B)_C = X_K ×_{Spec K} Spec C` through `g`. -/
theorem isPullback_baseChangeCompLift (h : τ.comp σ = ψ.comp π) :
    IsPullback (baseChangeCompLift f σ τ π ψ h)
      (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ)))
      (pullback.snd f (Spec.map (CommRingCat.ofHom π))) (Spec.map (CommRingCat.ofHom ψ)) := by
  have hout := (IsPullback.of_hasPullback (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
    (Spec.map (CommRingCat.ofHom τ))).paste_horiz
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom σ)))
  rw [← baseChangeCompLift_fst f σ τ π ψ h, specMap_comp_specMap_eq σ τ π ψ h] at hout
  exact hout.of_right (baseChangeCompLift_snd f σ τ π ψ h)
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom π)))

/-- **Flat base change through the comparison square**: if `ψ` is flat and `f` is quasi-compact
and separated, the base-change map along `ψ` of `p_K^* M` on `X_K`, with `(X_B)_C` as fibre
product, is an isomorphism in every degree. -/
theorem isIso_moduleCohomologyTensorMap_baseChangeCompLift [QuasiCompact f] [IsSeparated f]
    (h : τ.comp σ = ψ.comp π) (hψ : ψ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso (moduleCohomologyTensorMap (baseChangeCompLift f σ τ π ψ h) ψ
      ((pullback.snd f (Spec.map (CommRingCat.ofHom π))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      ((pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom τ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (moduleSectionsBaseChangeScalars (baseChangeCompLift f σ τ π ψ h) _ _ ψ
        (isPullback_baseChangeCompLift f σ τ π ψ h).w)
      ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeCompLift f σ τ π ψ h)).unit.app
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom π)))).obj M)) n) :=
  moduleCohomologyTensorMap_isIso_of_isPullback (baseChangeCompLift f σ τ π ψ h) _ _ ψ
    (isPullback_baseChangeCompLift f σ τ π ψ h) hψ _ n

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

section Square

variable {X Y Z W : Scheme.{u}} {A B C K : Type u} [CommRing A] [CommRing B] [CommRing C]
  [CommRing K] {p : Y ⟶ X} {p' : Z ⟶ Y} {pK : W ⟶ X} {g : Z ⟶ W}
  {σ : A →+* B} {τ : B →+* C} {π : A →+* K} {ψ : K →+* C}
  {αX : A →+* Γ(X, ⊤)} {αY : B →+* Γ(Y, ⊤)} {αZ : C →+* Γ(Z, ⊤)} {αW : K →+* Γ(W, ⊤)}

/-- **Iterated tensor maps through a commutative square**, at variable data. For
`g ≫ pK = p' ≫ p` over `τ ∘ σ = ψ ∘ π`, if the tensor maps of `M` along `pK` and of `pK^* M`
along `g` are isomorphisms, so is the composite of the tensor map of `M` along `p` (extended
along `τ`) with the tensor map of `p^* M` along `p'`. -/
theorem isIso_moduleCohomologyTensorMap_comp_of_square (hg : g ≫ pK = p' ≫ p)
    (hring : τ.comp σ = ψ.comp π) (hp : p.appTop.hom.comp αX = αY.comp σ)
    (hp' : p'.appTop.hom.comp αY = αZ.comp τ) (hpK : pK.appTop.hom.comp αX = αW.comp π)
    (hgW : g.appTop.hom.comp αW = αZ.comp ψ) (M : X.Modules) (n : ℕ)
    (hK : IsIso (moduleCohomologyTensorMap (M := M) (N := (Scheme.Modules.pullback pK).obj M)
      pK π αX αW hpK ((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M) n))
    (hG : IsIso (moduleCohomologyTensorMap (M := (Scheme.Modules.pullback pK).obj M)
      (N := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback pK).obj M)) g ψ αW αZ hgW
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pullback pK).obj M)) n)) :
    IsIso ((ModuleCat.extendScalars τ).map (moduleCohomologyTensorMap (M := M)
        (N := (Scheme.Modules.pullback p).obj M) p σ αX αY hp
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n) ≫
      moduleCohomologyTensorMap (M := (Scheme.Modules.pullback p).obj M)
        (N := (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback p).obj M)) p' τ αY αZ hp'
        ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app
          ((Scheme.Modules.pullback p).obj M)) n) := by
  let := moduleCohomologyModuleOfHom X αX M n
  let := moduleCohomologyModuleOfHom Y αY ((Scheme.Modules.pullback p).obj M) n
  let := moduleCohomologyModuleOfHom W αW ((Scheme.Modules.pullback pK).obj M) n
  let HA := ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf X M) n)
  let E₃ := ModuleCat.extendScalarsCongrIso hring.symm HA
  let E₁ := (ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app HA
  let E₂ := (ModuleCat.extendScalarsComp.{u, u + 1} π ψ).hom.app HA
  let E := moduleCohomologyIsoOfHom Z αZ (pullbackSquareCoefficientIso hg M) n
  let Tp := moduleCohomologyTensorMap (M := M) (N := (Scheme.Modules.pullback p).obj M) p σ αX αY
    hp ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
  let Tp' := moduleCohomologyTensorMap (M := (Scheme.Modules.pullback p).obj M)
    (N := (Scheme.Modules.pullback p').obj ((Scheme.Modules.pullback p).obj M)) p' τ αY αZ hp'
    ((Scheme.Modules.pullbackPushforwardAdjunction p').unit.app
      ((Scheme.Modules.pullback p).obj M)) n
  let TK := moduleCohomologyTensorMap (M := M) (N := (Scheme.Modules.pullback pK).obj M) pK π αX
    αW hpK ((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M) n
  let TG := moduleCohomologyTensorMap (M := (Scheme.Modules.pullback pK).obj M)
    (N := (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback pK).obj M)) g ψ αW αZ hgW
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback pK).obj M)) n
  have key : E₃.hom ≫ E₁ ≫ (ModuleCat.extendScalars τ).map Tp ≫ Tp' =
      E₂ ≫ (ModuleCat.extendScalars ψ).map TK ≫ TG ≫ E.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have e₃ : E₃.hom ((1 : C) ⊗ₜ[A,ψ.comp π] m) = (1 : C) ⊗ₜ[A,τ.comp σ] m :=
      ModuleCat.extendScalarsCongrIso_hom_one_tmul hring.symm HA m
    have e₁ := ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1} σ τ HA m
    have e₂ := ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1} π ψ HA m
    change Tp' ((ModuleCat.extendScalars τ).map Tp
        ((ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app HA
          (E₃.hom ((1 : C) ⊗ₜ[A,ψ.comp π] m)))) =
      E.hom (TG ((ModuleCat.extendScalars ψ).map TK
        ((ModuleCat.extendScalarsComp.{u, u + 1} π ψ).hom.app HA ((1 : C) ⊗ₜ[A,ψ.comp π] m))))
    rw [e₃]
    erw [e₁, e₂, ModuleCat.ExtendScalars.map_tmul, ModuleCat.ExtendScalars.map_tmul]
    calc
      _ = Tp' ((1 : C) ⊗ₜ[B,τ] moduleCohomologyPullback p M n m) :=
        congrArg (fun z => Tp' ((1 : C) ⊗ₜ[B,τ] z))
          (moduleCohomologyTensorMap_one_tmul p σ αX αY hp _ n m)
      _ = moduleCohomologyPullback p' ((Scheme.Modules.pullback p).obj M) n
            (moduleCohomologyPullback p M n m) :=
        moduleCohomologyTensorMap_one_tmul p' τ αY αZ hp' _ n _
      _ = Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
              (pullbackSquareCoefficientIso hg M).hom) n
            (moduleCohomologyPullback g ((Scheme.Modules.pullback pK).obj M) n
              (moduleCohomologyPullback pK M n m)) :=
        moduleCohomologyPullback_pullbackSquare_apply hg M n m
      _ = E.hom (moduleCohomologyPullback g ((Scheme.Modules.pullback pK).obj M) n
            (moduleCohomologyPullback pK M n m)) :=
        (moduleCohomologyIsoOfHom_hom_apply Z αZ (pullbackSquareCoefficientIso hg M) n _).symm
      _ = E.hom (TG ((1 : C) ⊗ₜ[K,ψ] moduleCohomologyPullback pK M n m)) :=
        congrArg E.hom (moduleCohomologyTensorMap_one_tmul g ψ αW αZ hgW _ n _).symm
      _ = _ :=
        congrArg (fun z => E.hom (TG ((1 : C) ⊗ₜ[K,ψ] z)))
          (moduleCohomologyTensorMap_one_tmul pK π αX αW hpK _ n m).symm
  have hcomp : IsIso ((E₃.hom ≫ E₁) ≫ ((ModuleCat.extendScalars τ).map Tp ≫ Tp')) := by
    rw [Category.assoc, key]
    infer_instance
  exact IsIso.of_isIso_comp_left (E₃.hom ≫ E₁) _

end Square

variable {X : Scheme.{u}} {A B C K : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing K]
  (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B) (τ : B →+* C) (π : A →+* K) (ψ : K →+* C)

/-- **Iterated base change through a flat square**: if `ψ` is flat, `f` is quasi-compact and
separated, `M` is quasicoherent and the base-change map of `M` along `π` is an isomorphism in
degree `n`, then the composite
`C ⊗_B (B ⊗_A H^n(X, M)) ⟶ C ⊗_B H^n(X_B, p^* M) ⟶ H^n((X_B)_C, p'^* p^* M)`
of the base-change map of `M` along `σ`, extended along `τ`, with the base-change map of `p^* M`
along `τ` is an isomorphism. -/
theorem isIso_moduleCohomologyBaseChangeMap_comp_of_isIso [QuasiCompact f] [IsSeparated f]
    (h : τ.comp σ = ψ.comp π) (hψ : ψ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (hπ : IsIso (moduleCohomologyBaseChangeMap f π M n)) :
    IsIso ((ModuleCat.extendScalars τ).map (moduleCohomologyBaseChangeMap f σ M n) ≫
      moduleCohomologyBaseChangeMap (pullback.snd f (Spec.map (CommRingCat.ofHom σ))) τ
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n) :=
  isIso_moduleCohomologyTensorMap_comp_of_square (baseChangeCompLift_fst f σ τ π ψ h) h
    (moduleSectionsBaseChangeScalars _ _ f σ pullback.condition)
    (moduleSectionsBaseChangeScalars _ _ _ τ pullback.condition)
    (moduleSectionsBaseChangeScalars _ _ f π pullback.condition)
    (moduleSectionsBaseChangeScalars (baseChangeCompLift f σ τ π ψ h) _ _ ψ
      (isPullback_baseChangeCompLift f σ τ π ψ h).w) M n hπ
    (isIso_moduleCohomologyTensorMap_baseChangeCompLift f σ τ π ψ h hψ M n)

/-- **Vanishing passes to the iterated base change through a flat square**: if `ψ` is flat,
`f` is quasi-compact and separated, `M` is quasicoherent and `H^n(X_K, p_K^* M) = 0`, then
`H^n((X_B)_C, p'^* p^* M) = 0`. -/
theorem subsingleton_moduleCohomology_baseChangeComp [QuasiCompact f] [IsSeparated f]
    (h : τ.comp σ = ψ.comp π) (hψ : ψ.Flat) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (hK : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom π)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom π)))).obj M)) n)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback (pullback.snd f
        (Spec.map (CommRingCat.ofHom σ))) (Spec.map (CommRingCat.ofHom τ)))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom τ)))).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)))
          n) := by
  have hT := isIso_moduleCohomologyTensorMap_baseChangeCompLift f σ τ π ψ h hψ M n
  let α := (pullback.snd f (Spec.map (CommRingCat.ofHom π))).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let := moduleCohomologyModuleOfHom _ α
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom π)))).obj M) n
  have hz : IsZero ((ModuleCat.extendScalars ψ).obj (ModuleCat.of K (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom π)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom π)))).obj M)) n))) :=
    (ModuleCat.extendScalars ψ).map_isZero (ModuleCat.isZero_of_subsingleton _)
  have hG : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _
      ((Scheme.Modules.pullback (baseChangeCompLift f σ τ π ψ h)).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom π)))).obj M))) n) :=
    ModuleCat.subsingleton_of_isZero (hz.of_iso (@asIso _ _ _ _ _ hT).symm)
  exact (bijective_sheafH_map_of_iso
    (pullbackSquareCoefficientIso (baseChangeCompLift_fst f σ τ π ψ h) M) n).2.subsingleton

/-! ### Residue fields

For `t ∈ Spec B` over `s = σ⁻¹ t`, the square `A → κ(s) → κ(t)`, `A → B → κ(t)` commutes and
`κ(s) → κ(t)` is flat (`Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp`,
`Ideal.ResidueField.flat_mapComap`, in `RingTheory/LocalRing/ResidueFieldComap`). -/

section ResidueField

variable {A B : Type u} [CommRing A] [CommRing B]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact f] [IsSeparated f]
  (σ : A →+* B) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)

/-- **Fibres of a base change are field base changes of fibres, with their fibre maps**: for
`t ∈ Spec B` over `s = σ⁻¹ t`, if the fibre map `κ(s) ⊗_A H^n(X, M) ⟶ H^n(X_s, M_s)` is an
isomorphism, then so is the composite
`κ(t) ⊗_B (B ⊗_A H^n(X, M)) ⟶ κ(t) ⊗_B H^n(X_B, M_B) ⟶ H^n((X_B)_t, (M_B)_t)`. -/
theorem isIso_moduleCohomologyBaseChangeMap_comp_residueField (t : PrimeSpectrum B)
    (hs : IsIso (moduleCohomologyBaseChangeMap f
      (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField) M n)) :
    IsIso ((ModuleCat.extendScalars (algebraMap B t.asIdeal.ResidueField)).map
        (moduleCohomologyBaseChangeMap f σ M n) ≫
      moduleCohomologyBaseChangeMap (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        (algebraMap B t.asIdeal.ResidueField)
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) n) :=
  isIso_moduleCohomologyBaseChangeMap_comp_of_isIso f σ _ _ (Ideal.ResidueField.mapComap σ t)
    (Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp σ t) (Ideal.ResidueField.flat_mapComap σ t)
    M n hs

/-- **Vanishing on the fibres of a base change**: for `t ∈ Spec B` over `s = σ⁻¹ t`, if
`H^n(X_s, M_s) = 0`, then `H^n((X_B)_t, (M_B)_t) = 0`. -/
theorem subsingleton_moduleCohomology_residueField_pullback (t : PrimeSpectrum B)
    (hs : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))).obj M)) n)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback (pullback.snd f
        (Spec.map (CommRingCat.ofHom σ)))
        (Spec.map (CommRingCat.ofHom (algebraMap B t.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
          (Spec.map (CommRingCat.ofHom (algebraMap B t.asIdeal.ResidueField))))).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M))) n) :=
  subsingleton_moduleCohomology_baseChangeComp f σ _ _ (Ideal.ResidueField.mapComap σ t)
    (Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp σ t) (Ideal.ResidueField.flat_mapComap σ t)
    M n hs

end ResidueField

end AlgebraicGeometry.Scheme.Cohomology
