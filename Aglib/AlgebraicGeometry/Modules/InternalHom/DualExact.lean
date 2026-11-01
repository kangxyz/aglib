/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DualAffine
public import Aglib.AlgebraicGeometry.Modules.InternalHom.LocallyFree
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exactness
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Reversed exactness of original finite locally free duals

Original affine sections split by finite projectivity. The existing dual
section comparison transports that splitting, and the actual tilde counit
and open-cover locality recover the original sheaf sequence. No global
splitting hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u

/-- The existing dual section comparison, with the native categorical Hom carrier. -/
def affineDualSectionsIso {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    [(M.restrict j).IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X M).restrict j) ≅
      ((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj
        (op (moduleSpecΓFunctor.obj (M.restrict j))) :=
  ((affineDualSectionsEquiv j M).trans
    (ModuleCat.homLinearEquiv (R := R) (S := R)
      (M := moduleSpecΓFunctor.obj (M.restrict j)) (N := ModuleCat.of R R)).symm).toModuleIso

/-- Actual sections of the reversed dual sequence are the reversed original Hom sequence. -/
def dualShortComplexSectionsIso {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (S : ShortComplex X.Modules)
    [(S.X₁.restrict j).IsQuasicoherent] [(S.X₂.restrict j).IsQuasicoherent]
    [(S.X₃.restrict j).IsQuasicoherent] :
    (((S.op.map (dualFunctor X)).map (restrictFunctor j)).map moduleSpecΓFunctor) ≅
      (((S.map (restrictFunctor j)).map moduleSpecΓFunctor).op.map
        ((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R))) := by
  refine ShortComplex.isoMk (affineDualSectionsIso j S.X₃)
    (affineDualSectionsIso j S.X₂) (affineDualSectionsIso j S.X₁) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply ModuleCat.hom_ext
    exact (affineDualSectionsEquiv_map j S.g s).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply ModuleCat.hom_ext
    exact (affineDualSectionsEquiv_map j S.f s).symm

/-- Reversed dual exactness on every original affine chart. -/
theorem dual_shortExact_affineRestriction {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₂]
    [IsFiniteLocallyFree X S.X₃] {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] :
    ((S.op.map (dualFunctor X)).map (restrictFunctor j)).ShortExact := by
  let T := (S.op.map (dualFunctor X)).map (restrictFunctor j)
  let : IsFiniteLocallyFree X (dualSheaf X S.X₁) := finiteLocallyFree_dual S.X₁
  let : IsFiniteLocallyFree X (dualSheaf X S.X₂) := finiteLocallyFree_dual S.X₂
  let : IsFiniteLocallyFree X (dualSheaf X S.X₃) := finiteLocallyFree_dual S.X₃
  let : (S.map (restrictFunctor j)).X₁.IsQuasicoherent :=
    inferInstanceAs (S.X₁.restrict j).IsQuasicoherent
  let : T.X₁.IsQuasicoherent :=
    inferInstanceAs ((show X.Modules from dualSheaf X S.X₃).restrict j).IsQuasicoherent
  let : T.X₂.IsQuasicoherent :=
    inferInstanceAs ((show X.Modules from dualSheaf X S.X₂).restrict j).IsQuasicoherent
  let : T.X₃.IsQuasicoherent :=
    inferInstanceAs ((show X.Modules from dualSheaf X S.X₁).restrict j).IsQuasicoherent
  have hΓ := AffineCech.shortExact_globalSections_of_quasicoherent_kernel
    (hS.map_of_exact (restrictFunctor j))
  let P := ((S.map (restrictFunctor j)).map moduleSpecΓFunctor).X₃
  let : Module.Projective R P :=
    projective_globalSections_of_finiteLocallyFree R (S.X₃.restrict j)
  let : Projective P := ModuleCat.projective_of_categoryTheory_projective P
  let split := (hΓ.splittingOfProjective.op.map
    ((linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R))).ofIso
      (dualShortComplexSectionsIso j S).symm
  let : IsIso T.X₁.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent T.X₁
  let : IsIso T.X₂.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent T.X₂
  let : IsIso T.X₃.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent T.X₃
  let e : (T.map moduleSpecΓFunctor).map (tilde.functor R) ≅ T :=
    ShortComplex.isoMk (asIso T.X₁.fromTildeΓ) (asIso T.X₂.fromTildeΓ)
      (asIso T.X₃.fromTildeΓ)
      (fromTildeΓNatTrans.naturality T.f).symm
      (fromTildeΓNatTrans.naturality T.g).symm
  exact ((split.map (tilde.functor R)).ofIso e).shortExact

/-- The original dual reverses short exact sequences of finite locally free sheaves. -/
theorem dual_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₁] [IsFiniteLocallyFree X S.X₂]
    [IsFiniteLocallyFree X S.X₃] : (S.op.map (dualFunctor X)).ShortExact := by
  let 𝒰 := X.affineOpenCover
  apply shortExact_of_restrict_openCover (fun i => Spec (𝒰.X i)) 𝒰.f
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)
  intro i
  exact dual_shortExact_affineRestriction S hS (𝒰.f i)

end AlgebraicGeometry.Scheme.Modules.InternalHom
