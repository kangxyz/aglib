/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CommonOpen
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CommonModelOverBase

/-!
# Constructing the actual finite normal common model

The common open, schematic graph component, normalization and both original
projections are all constructed. Nagata is required only on the original
base's actual affine charts. No common model, resolving chain, regularity
premise, graph finiteness or curve injection is supplied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- Two proper birational integral models of the current normal surface have
an actual normal common model finite over their literal fibre product.
The current surface retains its accumulated proper birational map to the
original Noetherian Nagata surface; it is not assumed regular. -/
theorem exists_normalCommonModel
    {X Y S P : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral S] [IsIntegral P]
    [IsNoetherian P]
    (b : S ⟶ P) [IsProper b] [IsDominant b]
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hS : NormalStalks S)
    (hNagata : ∀ V : P.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(P, V.1))
    (hdP : topologicalKrullDim P ≤ 2)
    (f : X ⟶ S) [IsProper f] [IsDominant f]
    (hf : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (g : Y ⟶ S) [IsProper g] [IsDominant g]
    (hg : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ X) (c : Z ⟶ Y) (hZ : IsIntegral Z),
      letI := hZ
      ∃ (ha : IsDominant a) (hc : IsDominant c),
        letI := ha
        letI := hc
        NormalStalks Z ∧ IsNoetherian Z ∧ topologicalKrullDim Z ≤ 2 ∧
          IsProper a ∧ IsProper c ∧
          IsIso (CommRingCat.ofHom (functionFieldMap a)) ∧
          IsIso (CommRingCat.ofHom (functionFieldMap c)) ∧
          ∃ w : a ≫ f = c ≫ g, IsFinite (pullback.lift a c w) := by
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian b
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
  let : IsNoetherian S := ⟨⟩
  obtain ⟨U, h, hU, hqc, hi, w⟩ := exists_commonOpen f hf g hg hS
  let : Nonempty U := hU
  let : QuasiCompact U.ι := hqc
  let : IsOpenImmersion h := hi
  let Z := CommonModel.model f g U h w
  let a := CommonModel.toSource f g U h w
  let c := CommonModel.toTarget f g U h w
  have hproper := CommonModel.projections_isProper_over_base f g hf U h w b hb hNagata hdP
  refine ⟨Z, a, c, inferInstance, inferInstance, inferInstance,
    CommonModel.normalStalks_model f g U h w,
    CommonModel.model_isNoetherian_over_base f g hf U h w b hb hNagata hdP,
    CommonModel.model_dimension_over_base f g hf U h w b hb hNagata hdP,
    hproper.1, hproper.2, CommonModel.toSource_fieldMap_isIso f g U h w,
    CommonModel.toTarget_fieldMap_isIso f g U h w, CommonModel.toSource_comp f g U h w,
    CommonModel.pair_isFinite_over_base f g hf U h w b hb hNagata hdP⟩

end AlgebraicGeometry.Scheme.NormalizedPointDomination
