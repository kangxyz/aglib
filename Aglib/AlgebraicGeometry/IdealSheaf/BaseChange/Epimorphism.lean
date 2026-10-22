/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange.Epimorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-!
# The canonical epimorphism onto a pulled-back closed ideal

For an actual cartesian square of a closed immersion, the original canonical
`idealPullbackMap` is an epimorphism for every base morphism. Its affine
comparison is the scalar-extended kernel map onto the actual image ideal.
Restriction of that same map and local cokernel vanishing give the global
statement. No flatness, Noetherian, or Cartier hypothesis is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

private theorem idealPullbackMap_epi_of_eq_base
    {D D' X Y : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b b' : Y ⟶ X) (a a' : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (h' : a' ≫ i = i' ≫ b') (hb : b = b')
    [Epi (idealPullbackMap i i' b' a' h')] : Epi (idealPullbackMap i i' b a h) := by
  subst b'
  rw [idealPullbackMap_eq_of_same_base i i' b a a' h h']
  infer_instance

private theorem idealPullbackMap_epi_of_isoSquares
    {D X D' Y DS XS DS' YS : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b)
    (j : DS ⟶ XS) (j' : DS' ⟶ YS) (c : YS ⟶ XS) (d : DS' ⟶ DS)
    (hs : d ≫ j = j' ≫ c)
    (eX : X ≅ XS) (eD : D ≅ DS) (eY : Y ≅ YS) (eD' : D' ≅ DS')
    (hX : eD.hom ≫ j = i ≫ eX.hom) (hY : eD'.hom ≫ j' = i' ≫ eY.hom)
    (hb : eY.hom ≫ c = b ≫ eX.hom)
    [Epi (idealPullbackMap j j' c d hs)] : Epi (idealPullbackMap i i' b a h) := by
  have : IsIso (idealPullbackMap j' i' eY.hom eD'.hom hY) :=
    idealPullbackMap_isIso_of_iso_square j' i' eY.hom eD'.hom hY
  have hleft : (a ≫ eD.hom) ≫ j = i' ≫ (b ≫ eX.hom) := by
    rw [Category.assoc, hX, ← Category.assoc, h, Category.assoc]
  have hright : (eD'.hom ≫ d) ≫ j = i' ≫ (eY.hom ≫ c) := by
    rw [Category.assoc, hs, ← Category.assoc, hY, Category.assoc]
  have : Epi (idealPullbackMap j i' (eY.hom ≫ c) (eD'.hom ≫ d) hright) := by
    rw [← idealPullbackMap_comp j j' i' c eY.hom d eD'.hom hs hY]
    infer_instance
  have : Epi (idealPullbackMap j i' (b ≫ eX.hom) (a ≫ eD.hom) hleft) :=
    idealPullbackMap_epi_of_eq_base j i' (b ≫ eX.hom) (eY.hom ≫ c)
      (a ≫ eD.hom) (eD'.hom ≫ d) hleft hright hb.symm
  have : Epi ((Scheme.Modules.pullbackComp b eX.hom).inv.app (idealModule j) ≫
      (Scheme.Modules.pullback b).map (idealPullbackMap j i eX.hom eD.hom hX) ≫
        idealPullbackMap i i' b a h) := by
    rw [idealPullbackMap_comp]
    infer_instance
  have : Epi ((Scheme.Modules.pullback b).map
      (idealPullbackMap j i eX.hom eD.hom hX) ≫ idealPullbackMap i i' b a h) :=
    epi_of_epi ((Scheme.Modules.pullbackComp b eX.hom).inv.app (idealModule j)) _
  exact epi_of_epi
    ((Scheme.Modules.pullback b).map (idealPullbackMap j i eX.hom eD.hom hX)) _

private theorem affineIdealPullbackMap_epi_of_ker_eq_map
    {R S R' S' : CommRingCat.{u}} (φ : R ⟶ S) (φ' : R' ⟶ S')
    (b : R ⟶ R') (a : S ⟶ S') (h : φ ≫ a = b ≫ φ')
    (hs : Spec.map a ≫ Spec.map φ = Spec.map φ' ≫ Spec.map b)
    (hker : RingHom.ker φ'.hom = (RingHom.ker φ.hom).map b.hom) :
    Epi (idealPullbackMap (Spec.map φ) (Spec.map φ') (Spec.map b) (Spec.map a) hs) := by
  have : Epi (ModuleCat.extendedKernelMap φ φ' b a h) :=
    ModuleCat.extendedKernelMap_epi_of_ker_eq_map φ φ' b a h hker
  have : Epi (tilde.map (ModuleCat.extendedKernelMap φ φ' b a h)) :=
    inferInstanceAs (Epi ((tilde.functor R').map (ModuleCat.extendedKernelMap φ φ' b a h)))
  have : Epi ((Scheme.Modules.pullback (Spec.map b)).map (affineIdealIso φ).hom ≫
      idealPullbackMap (Spec.map φ) (Spec.map φ') (Spec.map b) (Spec.map a) hs) := by
    rw [affineIdealPullbackMap_eq φ φ' b a h hs]
    infer_instance
  exact epi_of_epi ((Scheme.Modules.pullback (Spec.map b)).map (affineIdealIso φ).hom) _

private theorem affine_idealPullbackMap_epi
    {D X D' Y : Scheme.{u}} [IsAffine D] [IsAffine X] [IsAffine D'] [IsAffine Y]
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (H : IsPullback a i' i b) [IsClosedImmersion i] :
    Epi (idealPullbackMap i i' b a h) := by
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H inferInstance
  have hker : i'.ker = i.ker.comap b := by
    have hsnd : (pullback.snd i b).ker = i.ker.comap b := by
      rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b,
        ← Hom.ker_comp_of_isIso (pullbackSymmetry i b).hom (pullback.fst b i)]
      simp
    rw [← hsnd, ← Hom.ker_comp_of_isIso H.isoPullback.hom (pullback.snd i b)]
    simp
  have htop : b.appLE ⊤ ⊤ le_top = b.appTop :=
    (show b.appLE ⊤ ⊤ le_top = b.appLE ⊤ (b ⁻¹ᵁ ⊤) le_rfl from rfl).trans
      b.appLE_eq_app
  have hring : RingHom.ker i'.appTop.hom =
      (RingHom.ker i.appTop.hom).map b.appTop.hom := by
    rw [← i'.ker_apply ⟨⊤, isAffineOpen_top Y⟩, hker,
      Scheme.IdealSheafData.ideal_comap_eq_map_appLE i.ker b
        ⟨⊤, isAffineOpen_top X⟩ ⟨⊤, isAffineOpen_top Y⟩ le_top,
      i.ker_apply ⟨⊤, isAffineOpen_top X⟩, htop]
  have hr : i.appTop ≫ a.appTop = b.appTop ≫ i'.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h]
  have hs : Spec.map a.appTop ≫ Spec.map i.appTop =
      Spec.map i'.appTop ≫ Spec.map b.appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp, hr]
  have : Epi (idealPullbackMap (Spec.map i.appTop) (Spec.map i'.appTop)
      (Spec.map b.appTop) (Spec.map a.appTop) hs) :=
    affineIdealPullbackMap_epi_of_ker_eq_map i.appTop i'.appTop b.appTop a.appTop hr hs hring
  exact idealPullbackMap_epi_of_isoSquares i i' b a h
    (Spec.map i.appTop) (Spec.map i'.appTop) (Spec.map b.appTop) (Spec.map a.appTop) hs
    X.isoSpec D.isoSpec Y.isoSpec D'.isoSpec
    (Scheme.isoSpec_hom_naturality i) (Scheme.isoSpec_hom_naturality i')
    (Scheme.isoSpec_hom_naturality b)

private theorem idealPullbackMap_restrict_epi_of_local
    {D X D' Y : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (V : X.Opens) (W : Y.Opens) (hWV : W ≤ b ⁻¹ᵁ V)
    [Epi (idealPullbackMap (i ∣_ V) (i' ∣_ W) (b.resLE V W hWV)
      (restrictedSquareSourceMap i i' b a h V W hWV)
      (restrictedSquareSourceMap_comm i i' b a h V W hWV))] :
    Epi ((Scheme.Modules.restrictFunctor W.ι).map (idealPullbackMap i i' b a h)) := by
  let b₀ := b.resLE V W hWV
  let a₀ := restrictedSquareSourceMap i i' b a h V W hWV
  have h₀ : a₀ ≫ (i ∣_ V) = (i' ∣_ W) ≫ b₀ :=
    restrictedSquareSourceMap_comm i i' b a h V W hWV
  have hV := (morphismRestrict_ι i V).symm
  have hW := (morphismRestrict_ι i' W).symm
  have hcompV : (a₀ ≫ (i ⁻¹ᵁ V).ι) ≫ i = (i' ∣_ W) ≫ (b₀ ≫ V.ι) := by
    rw [Category.assoc, hV, ← Category.assoc, h₀, Category.assoc]
  have hcompW : ((i' ⁻¹ᵁ W).ι ≫ a) ≫ i = (i' ∣_ W) ≫ (W.ι ≫ b) := by
    rw [Category.assoc, h, ← Category.assoc, hW, Category.assoc]
  have : Epi (idealPullbackMap i (i' ∣_ W) (b₀ ≫ V.ι)
      (a₀ ≫ (i ⁻¹ᵁ V).ι) hcompV) := by
    rw [← idealPullbackMap_comp i (i ∣_ V) (i' ∣_ W) V.ι b₀
      (i ⁻¹ᵁ V).ι a₀ hV h₀]
    infer_instance
  have : Epi (idealPullbackMap i (i' ∣_ W) (W.ι ≫ b)
      ((i' ⁻¹ᵁ W).ι ≫ a) hcompW) :=
    idealPullbackMap_epi_of_eq_base i (i' ∣_ W) (W.ι ≫ b) (b₀ ≫ V.ι)
      ((i' ⁻¹ᵁ W).ι ≫ a) (a₀ ≫ (i ⁻¹ᵁ V).ι) hcompW hcompV
      (b.resLE_comp_ι hWV).symm
  have : Epi ((Scheme.Modules.pullbackComp W.ι b).inv.app (idealModule i) ≫
      (Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h) ≫
        idealPullbackMap i' (i' ∣_ W) W.ι (i' ⁻¹ᵁ W).ι hW) := by
    rw [idealPullbackMap_comp]
    infer_instance
  have : Epi ((Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h) ≫
      idealPullbackMap i' (i' ∣_ W) W.ι (i' ⁻¹ᵁ W).ι hW) :=
    epi_of_epi ((Scheme.Modules.pullbackComp W.ι b).inv.app (idealModule i)) _
  have : Epi ((Scheme.Modules.pullback W.ι).map (idealPullbackMap i i' b a h)) :=
    (epi_comp_iff_of_isIso _ (idealPullbackMap i' (i' ∣_ W) W.ι
      (i' ⁻¹ᵁ W).ι hW)).mp inferInstance
  have hn := (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.naturality
    (idealPullbackMap i i' b a h)
  have : Epi ((Scheme.Modules.restrictFunctor W.ι).map (idealPullbackMap i i' b a h) ≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app (idealModule i')) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app (idealModule i'))).mp inferInstance

private theorem epi_of_local_restrict {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    (hloc : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      Epi ((Scheme.Modules.restrictFunctor W.ι).map φ)) : Epi φ := by
  classical
  choose W hy hE using hloc
  apply Preadditive.epi_of_isZero_cokernel
  apply Scheme.Modules.isZero_of_restrict_openCover
    (fun y => (W y).toScheme) (fun y => (W y).ι)
    (fun y => ⟨y, ⟨y, hy y⟩, rfl⟩)
  intro y
  have : Epi ((Scheme.Modules.restrictFunctor (W y).ι).map φ) := hE y
  exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor (W y).ι).map φ)).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor (W y).ι) φ)

/-- For an actual cartesian square of a closed immersion, the original
canonical ideal pullback map is an epimorphism along every base morphism.
No flatness, Noetherian, or Cartier hypothesis is required. -/
theorem idealPullbackMap_epi_of_isPullback
    {D X D' Y : Scheme.{u}} (i : D ⟶ X) (i' : D' ⟶ Y)
    (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (H : IsPullback a i' i b) [IsClosedImmersion i] :
    Epi (idealPullbackMap i i' b a h) := by
  have : IsClosedImmersion i' := MorphismProperty.of_isPullback H inferInstance
  apply epi_of_local_restrict
  intro y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show b y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ b ⁻¹ᵁ V from hyV)
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have : IsAffine (i ⁻¹ᵁ V).toScheme := hV.preimage i
  have : IsAffine (i' ⁻¹ᵁ W).toScheme := hW.preimage i'
  have : Epi (idealPullbackMap (i ∣_ V) (i' ∣_ W) (b.resLE V W hWV)
      (restrictedSquareSourceMap i i' b a h V W hWV)
      (restrictedSquareSourceMap_comm i i' b a h V W hWV)) :=
    affine_idealPullbackMap_epi (i ∣_ V) (i' ∣_ W) (b.resLE V W hWV)
      (restrictedSquareSourceMap i i' b a h V W hWV)
      (restrictedSquareSourceMap_comm i i' b a h V W hWV)
      (restrictedSquareSourceMap_isPullback i i' b a h H V W hWV)
  exact ⟨W, hyW, idealPullbackMap_restrict_epi_of_local i i' b a h V W hWV⟩

end AlgebraicGeometry.Scheme.Hom
