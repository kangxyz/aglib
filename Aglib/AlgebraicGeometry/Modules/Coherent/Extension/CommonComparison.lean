/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Subobjects
public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# A common coherent comparison for an isomorphism on an open

The graph of an actual restriction isomorphism `M|U ≅ N|U` extends inside
the single ambient biproduct `M ⊞ N` by the existing coherent-subobject
constructor. Its two projections are isomorphisms on that same open.
Their original kernels and cokernels are supported in the complement.

The extension and its coherence are proved, not supplied as a theorem
family. Intrinsic numerical consumers can choose this comparison once
inside their proof, without exposing its implementation data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

attribute [local instance] Abelian.hasFiniteBiproducts

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- An isomorphism between the actual open restrictions of two coherent
modules extends to a coherent comparison span on the original scheme.
Its combined map to the original biproduct is a monomorphism. -/
theorem exists_coherent_common_comparison
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (e : M.restrict j ≅ N.restrict j) :
    ∃ (H : X.Modules) (a : H ⟶ M) (b : H ⟶ N),
      affineLocallyFiniteType X H ∧ Mono (biprod.lift a b) ∧
        IsIso ((restrictFunctor j).map a) ∧ IsIso ((restrictFunctor j).map b) := by
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let R := restrictFunctor j
  let eR : R.obj M ≅ R.obj N := e
  have hMN : affineLocallyFiniteType X (M ⊞ N) :=
    (affineLocallyFiniteType X).prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit M N) hM hN
  let iU : R.obj M ⟶ R.obj (M ⊞ N) :=
    R.map biprod.inl + eR.hom ≫ R.map biprod.inr
  have hfst : iU ≫ R.map biprod.fst = 𝟙 (R.obj M) := by
    simp [iU, Preadditive.add_comp, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have hsnd : iU ≫ R.map biprod.snd = eR.hom := by
    simp [iU, Preadditive.add_comp, Category.assoc, ← CategoryTheory.Functor.map_comp]
  let : Mono iU := by
    have : Mono (iU ≫ R.map biprod.fst) := by rw [hfst]; infer_instance
    exact mono_of_mono iU (R.map biprod.fst)
  let H₀ : FiniteTypeSheaves X := ⟨M ⊞ N, hMN⟩
  let M₀ : FiniteTypeSheaves X := ⟨M, hM⟩
  let A := (finiteTypeSheavesRestriction j).obj M₀
  let i : A ⟶ (finiteTypeSheavesRestriction j).obj H₀ := ObjectProperty.homMk iU
  let : Mono i := by
    apply (finiteTypeSheavesToModules U).mono_of_mono_map
    exact inferInstanceAs (Mono iU)
  obtain ⟨H, s, hs, eH, heH⟩ := coherent_subobject_extension j H₀ A i
  let : Mono s := hs
  let : Mono s.hom := (finiteTypeSheavesToModules X).map_mono s
  let a : H.obj ⟶ M := s.hom ≫ biprod.fst
  let b : H.obj ⟶ N := s.hom ≫ biprod.snd
  let eM : R.obj H.obj ≅ R.obj M := (finiteTypeSheavesToModules U).mapIso eH
  have hsR : R.map s.hom = eM.hom ≫ iU :=
    congrArg (finiteTypeSheavesToModules U).map heH
  have ha : R.map a = eM.hom := by
    change R.map (s.hom ≫ biprod.fst) = _
    rw [CategoryTheory.Functor.map_comp, hsR, Category.assoc, hfst, Category.comp_id]
  have hb : R.map b = eM.hom ≫ eR.hom := by
    change R.map (s.hom ≫ biprod.snd) = _
    rw [CategoryTheory.Functor.map_comp, hsR, Category.assoc, hsnd]
  have hab : biprod.lift a b = s.hom := by
    apply biprod.hom_ext <;> simp [a, b]
  refine ⟨H.obj, a, b, H.property, ?_, ?_, ?_⟩
  · rw [hab]
    infer_instance
  · change IsIso (R.map a)
    rw [ha]
    infer_instance
  · change IsIso (R.map b)
    rw [hb]
    infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Modules

/-- The original kernel of a map that is an isomorphism on an open is
supported outside the actual image of that open immersion. -/
theorem support_kernel_subset_compl_of_restrict_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules}
    (f : M ⟶ N) [IsIso ((restrictFunctor j).map f)] :
    support (kernel f) ⊆ (Set.range j)ᶜ := by
  have hz : IsZero ((restrictFunctor j).obj (kernel f)) :=
    (isZero_kernel_of_mono ((restrictFunctor j).map f)).of_iso
      (PreservesKernel.iso (restrictFunctor j) f)
  have hd := (supportedAway_iff_support_disjoint j (kernel f)).mp
    ((supportedAway_iff j (kernel f)).mpr hz)
  exact fun _ hx hU => (Set.disjoint_left.mp hd) hx hU

/-- The original cokernel of a map that is an isomorphism on an open is
supported outside the actual image of that open immersion. -/
theorem support_cokernel_subset_compl_of_restrict_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {M N : X.Modules}
    (f : M ⟶ N) [IsIso ((restrictFunctor j).map f)] :
    support (cokernel f) ⊆ (Set.range j)ᶜ := by
  have hz : IsZero ((restrictFunctor j).obj (cokernel f)) :=
    (isZero_cokernel_of_epi ((restrictFunctor j).map f)).of_iso
      (PreservesCokernel.iso (restrictFunctor j) f)
  have hd := (supportedAway_iff_support_disjoint j (cokernel f)).mp
    ((supportedAway_iff j (cokernel f)).mpr hz)
  exact fun _ hx hU => (Set.disjoint_left.mp hd) hx hU

end AlgebraicGeometry.Scheme.Modules
