/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Epimorphisms
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorAdjunction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Short exact rows with structure-module quotient remain short exact under the native tensor. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u v w

namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]

local notation "R₀" => (Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) R)
local notation "𝒪" => SheafOfModules.unit R₀

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem associatedSheaf_mono_of_locallyInjective
    {P Q : PresheafOfModulesOfCommRing.{u} R.obj} (f : P ⟶ Q)
    [PresheafOfModules.IsLocallyInjective J f] :
    Mono ((associatedSheaf R).map f) := by
  apply (SheafOfModules.toSheaf R₀).mono_of_mono_map
  change Mono ((presheafToSheaf J AddCommGrpCat.{u}).map
    ((PresheafOfModules.toPresheaf (R₀).obj).map f))
  have : Sheaf.IsLocallyInjective ((presheafToSheaf J AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf (R₀).obj).map f)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).2
      ‹PresheafOfModules.IsLocallyInjective J f›
  exact Sheaf.mono_of_isLocallyInjective _

omit [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})] in
private theorem sectionIsSplitMono_of_lift_one
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    (e : S.X₃ ≅ 𝒪) (V : Cᵒᵖ) (x : S.X₂.val.obj V)
    (hx : e.hom.val.app V (S.g.val.app V x) = (1 : (R₀).obj.obj V)) :
    IsSplitMono (S.f.val.app V) := by
  let F := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation (R₀).obj V
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let b : F.obj 𝒪 ⟶ F.obj S.X₂ := ModuleCat.ofHom
    (LinearMap.toSpanSingleton ((R₀).obj.obj V) (S.X₂.val.obj V) x)
  let s : F.obj S.X₃ ⟶ F.obj S.X₂ := F.map e.hom ≫ b
  have hb : b ≫ F.map (S.g ≫ e.hom) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ↥((R₀).obj.obj V) at a
    change e.hom.val.app V (S.g.val.app V (a • x)) = a
    rw [map_smul, map_smul, hx]
    exact mul_one a
  have hs : s ≫ F.map S.g = 𝟙 _ := by
    rw [← cancel_mono (F.map e.hom)]
    simp only [s, Category.assoc, Category.id_comp, ← Functor.map_comp, hb, Category.comp_id]
  have hi := KernelFork.mapIsLimit _ hS.fIsKernel F
  let d : F.obj S.X₂ ⟶ F.obj S.X₂ := 𝟙 _ - F.map S.g ≫ s
  have hd : d ≫ F.map S.g = 0 := by
    simp [d, Preadditive.sub_comp, Category.assoc, hs]
  let p := hi.lift (KernelFork.ofι d hd)
  have hp : p ≫ F.map S.f = d := Fork.IsLimit.lift_ι hi
  let : Mono (F.map S.f) := mono_of_isLimit_fork hi
  refine ⟨⟨⟨p, ?_⟩⟩⟩
  change F.map S.f ≫ p = 𝟙 _
  rw [← cancel_mono (F.map S.f), Category.assoc, hp]
  simp [d, Preadditive.comp_sub, ← Functor.map_comp_assoc, S.zero]

/-- Tensoring the first map of a short exact sequence with unit quotient gives a mono. -/
theorem tensorFunctor_mono_f_of_unit_quotient
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    (e : S.X₃ ≅ 𝒪) (M : SheafOfModulesOfCommRing R) :
    Mono (((tensorFunctor R).map S.f).app M) := by
  rw [tensorFunctor_map_app]
  let q := (toPresheaf R).map (S.g ≫ e.hom)
  let a := (toPresheaf R).map S.f ⊗ₘ 𝟙 ((toPresheaf R).obj M)
  let : Epi S.g := hS.epi_g
  have hq : PresheafOfModules.IsLocallySurjective J q :=
    SheafOfModules.isLocallySurjective_of_epi R₀ (S.g ≫ e.hom)
  let q' := (PresheafOfModules.toPresheaf (R₀).obj).map q
  let : Presheaf.IsLocallySurjective J q' := hq
  have : PresheafOfModules.IsLocallyInjective J a := by
    change Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf (R₀).obj).map a)
    constructor
    intro U x y hxy
    apply J.superset_covering _ (Presheaf.imageSieve_mem J q' (1 : (R₀).obj.obj U))
    intro V j hj
    obtain ⟨z, hz⟩ := hj
    have hz' : e.hom.val.app (op V) (S.g.val.app (op V) z) = (1 : (R₀).obj.obj (op V)) :=
      hz.trans (PresheafOfModules.unit_map_one (R₀).obj j.op)
    let : IsSplitMono (S.f.val.app (op V)) :=
      sectionIsSplitMono_of_lift_one R S hS e (op V) z hz'
    have ha : Mono (a.app (op V)) := by
      change Mono (((tensorRight (M.val.obj (op V))).map (S.f.val.app (op V))))
      infer_instance
    have hi := (ModuleCat.mono_iff_injective (a.app (op V))).1 ha
    change a.app U x = a.app U y at hxy
    apply hi
    let Q := (toPresheaf R).obj S.X₂ ⊗ (toPresheaf R).obj M
    exact (PresheafOfModules.naturality_apply a j.op x).trans
      ((congrArg (fun t : Q.obj U => Q.map j.op t) hxy).trans
        (PresheafOfModules.naturality_apply a j.op y).symm)
  exact associatedSheaf_mono_of_locallyInjective R a

end SheafOfModulesOfCommRing

namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max v w u} RingCat.{max v w u})]
    (R : Sheaf J CommRingCat.{max v w u}) [HasSheafify J AddCommGrpCat.{max v w u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v w u}]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max v w u})]
    [(presheafLocalIso R).IsMonoidal]

/-- An actual short exact sequence with tensor-unit quotient remains short exact
after tensoring on the right by any module sheaf. -/
theorem shortExact_tensorRight_of_unit_quotient
    (S : ShortComplex (SheafOfModulesOfCommRing R)) (hS : S.ShortExact)
    (e : S.X₃ ≅ 𝟙_ (SheafOfModulesOfCommRing R)) (M : SheafOfModulesOfCommRing R) :
    (S.map (tensorRight M)).ShortExact := by
  let F := tensorRight M
  let : F.IsLeftAdjoint :=
    (SheafOfModules.InternalHom.tensorHomAdjunction.{v, w, u} R M).isLeftAdjoint
  let : Epi S.g := hS.epi_g
  exact
    { exact := hS.exact.map_of_epi_of_preservesCokernel F inferInstance inferInstance
      mono_f := tensorFunctor_mono_f_of_unit_quotient R S hS e M
      epi_g := inferInstanceAs (Epi (F.map S.g)) }

end SheafOfModulesOfCommRing
