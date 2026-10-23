/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinEtaleIndex
public import Aglib.AlgebraicGeometry.Limits.FiniteCoproductPullback

/-!
# Actual generic points of the whole etale base change

Finite coproduct/pullback distribution identifies the original whole base
change with its genuine Artin components. The resulting point indexing retains
the original projection, rather than an unrelated bijection of finite sets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {U X : Scheme.{u}} (f : U ⟶ X) [IsNoetherian X]

/-- Canonical distribution of the actual generic coproduct across base change. -/
def genericArtinBaseChangeIso :
    (∐ fun η : genericPoints X => genericEtaleComponent f η) ≅
      pullback f (genericArtinMap X) :=
  Sigma.mapIso (fun η : genericPoints X => pullbackSymmetry f (X.fromSpecStalk η.val)) ≪≫
    FiniteCoproductPullback.iso (genericArtinComponent X)
      (fun η => X.fromSpecStalk η.val) f ≪≫
    pullbackSymmetry (genericArtinMap X) f

private theorem coproductPullback_component_fst {I : Type u} [Finite I]
    (A : I → Scheme.{u}) {S T : Scheme.{u}} (h : ∀ i, A i ⟶ S) (g : T ⟶ S) (i : I) :
    Sigma.ι (fun j => pullback g (h j)) i ≫
      (Sigma.mapIso (fun j => pullbackSymmetry g (h j)) ≪≫
        FiniteCoproductPullback.iso A h g ≪≫ pullbackSymmetry (Sigma.desc h) g).hom ≫
      pullback.fst g (Sigma.desc h) = pullback.fst g (h i) := by
  simp only [Iso.trans_hom, Category.assoc, Sigma.ι_mapIso_hom_assoc,
    pullbackSymmetry_hom_comp_fst, FiniteCoproductPullback.iso_hom_snd,
    Sigma.ι_comp_desc, pullbackSymmetry_hom_comp_snd]

/-- The canonical component map followed by the whole projection is the component projection. -/
@[reassoc (attr := simp)]
theorem genericArtinBaseChangeIso_component_fst (η : genericPoints X) :
    Sigma.ι (fun η => genericEtaleComponent f η) η ≫
      (genericArtinBaseChangeIso f).hom ≫ pullback.fst f (genericArtinMap X) =
      pullback.fst f (X.fromSpecStalk η.val) := by
  exact coproductPullback_component_fst (genericArtinComponent X)
    (fun θ => X.fromSpecStalk θ.val) f η


/-- The point equivalence induced by the actual component inclusions. -/
def genericArtinBaseChangePointEquiv :
    (Σ η : genericPoints X, genericEtaleComponent f η) ≃
      (pullback f (genericArtinMap X) : Scheme.{u}) :=
  (AlgebraicGeometry.sigmaMk (fun η => genericEtaleComponent f η)).toEquiv.trans
    (Scheme.homeoOfIso (genericArtinBaseChangeIso f)).toEquiv

private theorem genericArtinBaseChangePointEquiv_fst
    (p : Σ η : genericPoints X, genericEtaleComponent f η) :
    (pullback.fst f (genericArtinMap X)) (genericArtinBaseChangePointEquiv f p) =
      (pullback.fst f (X.fromSpecStalk p.1.val)) p.2 := by
  rcases p with ⟨η, p⟩
  have h := congrArg (fun g : genericEtaleComponent f η ⟶ U => g p)
    (genericArtinBaseChangeIso_component_fst f η)
  change (pullback.fst f (genericArtinMap X))
    ((genericArtinBaseChangeIso f).hom
      (AlgebraicGeometry.sigmaMk (fun η => genericEtaleComponent f η) ⟨η, p⟩)) = _
  rw [AlgebraicGeometry.sigmaMk_mk]
  exact h

variable [Etale f] [QuasiCompact f]

/-- Original whole-base-change points indexed by the genuine generic points of the test. -/
def genericArtinBaseChangeIndexEquiv :
    (pullback f (genericArtinMap X) : Scheme.{u}) ≃ genericPoints U :=
  (genericArtinBaseChangePointEquiv f).symm.trans (genericEtaleIndexEquiv f)

/-- The index is literally the original base-change projection. -/
theorem genericArtinBaseChangeIndexEquiv_val
    (p : (pullback f (genericArtinMap X) : Scheme.{u})) :
    (genericArtinBaseChangeIndexEquiv f p).val =
      (pullback.fst f (genericArtinMap X)) p := by
  have h := genericArtinBaseChangePointEquiv_fst f
    ((genericArtinBaseChangePointEquiv f).symm p)
  exact h.symm.trans (congrArg (pullback.fst f (genericArtinMap X))
    ((genericArtinBaseChangePointEquiv f).apply_symm_apply p))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
