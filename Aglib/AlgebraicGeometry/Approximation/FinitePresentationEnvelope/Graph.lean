/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.AffineGraphFamily
public import Aglib.AlgebraicGeometry.Limits.GraphRestriction

/-!
# Closed finite-type graphs in actual inverse systems

Finite affine covers descend to an original stage. Applying finite-generator
capture on every descended chart and choosing a common stage makes the
original finite-type graph a closed immersion. The original source, base,
projection, and structural map are retained literally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite-type map to an affine base, together with a sufficiently late
projection of a qcqs affine-transition inverse system, is a closed immersion
into the literal relative product over an affine terminal scheme. -/
lemma exists_isClosedImmersion_graph_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (hT : IsTerminal T)
    (s : S ⟶ T) (t : ∀ i, D.obj i ⟶ T)
    (f : c.pt ⟶ S) [LocallyOfFiniteType f] :
    ∃ i, IsClosedImmersion (pullback.lift (f := t i) (g := s)
      (c.π.app i) f (hT.hom_ext _ _)) := by
  classical
  have : CompactSpace c.pt := compactSpace_of_isLimit D c hc
  let 𝒰 := c.pt.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨j, V, hV, hVa⟩ := exists_isOpenCover_and_isAffine_of_finite D c hc
    (fun a => (𝒰.f a).opensRange) 𝒰.isOpenCover_opensRange
    (fun a => isAffineOpen_opensRange (𝒰.f a))
  let E (a : 𝒰.I₀) := opensDiagram D j (V a)
  let cE (a : 𝒰.I₀) := opensCone D c j (V a)
  have (a : 𝒰.I₀) (k : Over j) : IsAffine ((E a).obj k) :=
    (hVa a).1.preimage (D.map k.hom)
  let fE (a : 𝒰.I₀) : (cE a).pt ⟶ S := (c.π.app j ⁻¹ᵁ V a).ι ≫ f
  have (a : 𝒰.I₀) : LocallyOfFiniteType (fE a) := by
    dsimp [fE]
    infer_instance
  let tE (a : 𝒰.I₀) (k : Over j) : (E a).obj k ⟶ T :=
    (D.map k.hom ⁻¹ᵁ V a).ι ≫ t k.left
  obtain ⟨k, hk⟩ := exists_common_isClosedImmersion_graph_of_isLimit_of_isAffine
    E cE (fun a => isLimitOpensCone D c hc j (V a)) hT s tE fE
  let W (a : 𝒰.I₀) : (D.obj k.left).Opens := D.map k.hom ⁻¹ᵁ V a
  have hW : IsOpenCover W := by
    change (⨆ a, D.map k.hom ⁻¹ᵁ V a) = ⊤
    rw [← Hom.preimage_iSup, hV]
    simp
  let 𝒱 := openCoverOfIsOpenCover (D.obj k.left) W hW
  have H (a : 𝒰.I₀) : IsPullback ((cE a).π.app k)
      (c.π.app j ⁻¹ᵁ V a).ι (𝒱.f a) (c.π.app k.left) := by
    apply IsOpenImmersion.isPullback
    · simp [cE, 𝒱, W]
    · simp [𝒱, W, ← Hom.comp_preimage]
  refine ⟨k.left, ?_⟩
  exact isClosedImmersion_graph_of_openCover
    (c.π.app k.left) f (t k.left) s (hT.hom_ext _ _) 𝒱
    (fun a => (cE a).pt) (fun a => (c.π.app j ⁻¹ᵁ V a).ι)
    (fun a => (cE a).π.app k) H hk

end AlgebraicGeometry.Scheme
