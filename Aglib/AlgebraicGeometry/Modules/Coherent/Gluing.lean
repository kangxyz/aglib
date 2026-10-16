/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction

/-!
# Finite-type gluing on Noetherian open charts

Finite type is local for the displayed binary open cover. Compatible finite-type subobjects glue
on a locally Noetherian scheme, and their restriction to the union retains finite type.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Gluing.lean`.
SHA-256: `6aaa5fe7afa5e725eb43e457c3c85cd644113f236df923a0ead266175ea61559`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/AffineEnlargement.lean`.
SHA-256: `1c66fc512c3d458b75d6297240bf629f19f1a3df85c2240579d5c7d8f4c97986`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Coherence is local for a binary covering family of arbitrary open
immersions, not only literal inclusions of opens. -/
theorem affineLocallyFiniteType_of_binary_openImmersionCover
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤) (M : X.Modules)
    (hU : affineLocallyFiniteType U (M.restrict j)) (hV : affineLocallyFiniteType V (M.restrict a))
      :
    affineLocallyFiniteType X M :=
  affineLocallyFiniteType_of_binary_openCover M j.opensRange a.opensRange hcover
    (affineLocallyFiniteType_restrict_opensRange j M hU)
      (affineLocallyFiniteType_restrict_opensRange a M hV)

/-- Coherent subsheaves glue along a binary covering family of arbitrary
open immersions. This version applies directly to the two maps into a union. -/
theorem exists_coherent_glued_subobject_of_openImmersionCover
    {U V X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) (a : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion a]
    (hcover : j.opensRange ⊔ a.opensRange = ⊤) (M : X.Modules)
    (A : FiniteTypeSheaves U) (B : FiniteTypeSheaves V)
    (i : A.obj ⟶ M.restrict j) (k : B.obj ⟶ M.restrict a)
    [Mono i] [Mono k]
    (e : A.obj.restrict (pullback.fst j a) ≅ B.obj.restrict (pullback.snd j a))
    (he : (Scheme.Modules.restrictFunctor (pullback.fst j a)).map i ≫
        (overlapRestrictIso j a).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd j a)).map k) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      ∃ (eU : N.obj.restrict j ≅ A.obj) (eV : N.obj.restrict a ≅ B.obj),
        (Scheme.Modules.restrictFunctor j).map s = eU.hom ≫ i ∧
        (Scheme.Modules.restrictFunctor a).map s = eV.hom ≫ k := by
  obtain ⟨N, s, hs, eU, eV, hU, hV⟩ := exists_glued_subobject j a i k e he
  have hN : affineLocallyFiniteType X N := affineLocallyFiniteType_of_binary_openImmersionCover j a
    hcover N
    ((affineLocallyFiniteType U).prop_of_iso eU.symm A.property)
    ((affineLocallyFiniteType V).prop_of_iso eV.symm B.property)
  exact ⟨⟨N, hN⟩, s, hs, eU, eV, hU, hV⟩

/-- Two coherent subobjects of the restrictions of an arbitrary ambient
module sheaf glue whenever their actual overlap subobjects agree. Both
comparison isomorphisms commute with the given inclusions. -/
theorem exists_coherent_glued_subobject
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (W V : X.Opens) (hWV : W ⊔ V = ⊤) (M : X.Modules)
    (A : FiniteTypeSheaves W.toScheme) (B : FiniteTypeSheaves V.toScheme)
    (i : A.obj ⟶ M.restrict W.ι) (k : B.obj ⟶ M.restrict V.ι)
    [Mono i] [Mono k]
    (e : A.obj.restrict (pullback.fst W.ι V.ι) ≅
      B.obj.restrict (pullback.snd W.ι V.ι))
    (he : (Scheme.Modules.restrictFunctor (pullback.fst W.ι V.ι)).map i ≫
        (overlapRestrictIso W.ι V.ι).hom.app M =
      e.hom ≫ (Scheme.Modules.restrictFunctor (pullback.snd W.ι V.ι)).map k) :
    ∃ (N : FiniteTypeSheaves X) (s : N.obj ⟶ M), Mono s ∧
      ∃ (eW : N.obj.restrict W.ι ≅ A.obj) (eV : N.obj.restrict V.ι ≅ B.obj),
        (Scheme.Modules.restrictFunctor W.ι).map s = eW.hom ≫ i ∧
        (Scheme.Modules.restrictFunctor V.ι).map s = eV.hom ≫ k := by
  obtain ⟨N, s, hs, eW, eV, hW, hV⟩ := exists_glued_subobject W.ι V.ι i k e he
  have hN : affineLocallyFiniteType X N := affineLocallyFiniteType_of_binary_openCover N W V hWV
    ((affineLocallyFiniteType W.toScheme).prop_of_iso eW.symm A.property)
    ((affineLocallyFiniteType V.toScheme).prop_of_iso eV.symm B.property)
  exact ⟨⟨N, hN⟩, s, hs, eW, eV, hW, hV⟩

/-- A sheaf coherent on two opens is coherent on their union, with the
actual restriction-composition identifications. -/
theorem affineLocallyFiniteType_restrict_sup
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : X.Modules) (W V : X.Opens)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (hV : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    affineLocallyFiniteType (W ⊔ V).toScheme (M.restrict (W ⊔ V).ι) := by
  let T : X.Opens := W ⊔ V
  let j : W.toScheme ⟶ T.toScheme := X.homOfLE (show W ≤ T from le_sup_left)
  let a : V.toScheme ⟶ T.toScheme := X.homOfLE (show V ≤ T from le_sup_right)
  have hc : j.opensRange ⊔ a.opensRange = ⊤ := by
    dsimp [j, a]
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE,
      ← Scheme.Hom.preimage_sup]
    exact T.ι_preimage_self
  let eW : (M.restrict T.ι).restrict j ≅ M.restrict W.ι :=
    ((Scheme.Modules.restrictFunctorComp j T.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι _)).app M
  let eV : (M.restrict T.ι).restrict a ≅ M.restrict V.ι :=
    ((Scheme.Modules.restrictFunctorComp a T.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι _)).app M
  exact affineLocallyFiniteType_of_binary_openImmersionCover j a hc (M.restrict T.ι)
    ((affineLocallyFiniteType W.toScheme).prop_of_iso eW.symm hW)
    ((affineLocallyFiniteType V.toScheme).prop_of_iso eV.symm hV)

end AlgebraicGeometry.Scheme.Modules.Coherent
