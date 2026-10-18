/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.TensorFunctors

/-!
# Twist multiplication with free target degrees

`twistingTensorMultiplyTo a d d' h s : T_d ⟶ T_{d'}`, for `h : a + d = d'`, is multiplication by
a global section `s` of `O(a)` on the twist factor of `T_d = moduleTensorLeftFunctor _ O(d)`,
followed by the transport of twists to the free target degree `d'`; with `d' = a + d` it is
`twistingTensorMultiply` (`twistingTensorMultiplyTo_rfl`). Multiplications by two global twist
sections commute through arbitrary intermediate degrees (`twistingTensorMultiplyTo_comm`).

`twistingTensorCompIsoTo a b c h : T_b ⋙ T_a ≅ T_c` is the composition isomorphism with a free
degree `c`, and the monoidal comparisons of `TensorFunctors` hold for free degrees
(`twistingTensor_map_multiplyTo_comp_compIsoTo`, `twistingTensorMultiplyTo_app_comp_compIsoTo`).
Multiplication by `s` is multiplication by the unit morphism `twistingSectionUnitHom s : 𝟙_ ⟶ O(a)`
followed by the inverse associator and twist multiplication
(`twistingTensorMultiply_app_eq_unitMultiply`).

The composition isomorphisms in the monoidal spelling `O(a) ⊗ T_b.obj G` are
`twistMerge`/`twistMergeInv`; every conversion between that spelling and the composite-functor
spelling `(T_b ⋙ T_a).obj G` is checked once, here, at variable degrees. Whiskering by a twisting
sheaf preserves monomorphisms (`twisting_whiskerLeft_mono`) and reflects epimorphisms
(`epi_of_twisting_whiskerLeft`), since the twist tensor functor is an equivalence.

These declarations serve the Koszul complex of the coordinates and Castelnuovo–Mumford regularity
(`Cohomology/Projective/Regularity`); this leaf imports neither the regularity nor the cohomology
layer.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

variable {ι} in
/-- Multiplication by a global section `s` of `O(a)` from the twist `d` to a twist `d'` with
`a + d = d'`. The free target degree avoids transports between Koszul terms. -/
def twistingTensorMultiplyTo (a d d' : ℤ) (h : a + d = d')
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤)) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d) ⟶
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d') :=
  moduleTensorCoefficientMap (ProjectiveSpace R ι)
    (twistingMultiplyGlobal R ι a d s ≫ eqToHom (congrArg (twistingSheaf R ι) h))

variable {ι} in
/-- With the canonical target degree it is `twistingTensorMultiply`. -/
theorem twistingTensorMultiplyTo_rfl (a d : ℤ)
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤)) :
    twistingTensorMultiplyTo R a d (a + d) rfl s = twistingTensorMultiply R ι a d s := by
  simp only [twistingTensorMultiplyTo, eqToHom_refl, Category.comp_id]
  rfl

variable {ι} in
-- Section types of twists agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplications by two global twist sections commute, for arbitrary intermediate twists. -/
theorem twistingTensorMultiplyTo_comm (a b d d₁ d₂ e₁ : ℤ) (h₁ : a + d = d₁)
    (h₂ : b + d₁ = d₂) (h₃ : b + d = e₁) (h₄ : a + e₁ = d₂)
    (s : (twistingSheaf R ι a).val.obj (Opposite.op ⊤))
    (t : (twistingSheaf R ι b).val.obj (Opposite.op ⊤)) :
    twistingTensorMultiplyTo R a d d₁ h₁ s ≫ twistingTensorMultiplyTo R b d₁ d₂ h₂ t =
      twistingTensorMultiplyTo R b d e₁ h₃ t ≫ twistingTensorMultiplyTo R a e₁ d₂ h₄ s := by
  subst h₁ h₂ h₃
  simp only [twistingTensorMultiplyTo, eqToHom_refl, Category.comp_id,
    ← moduleTensorCoefficientMap_comp]
  congr 1
  ext V x
  apply Subtype.ext
  funext i
  change ((twistingMultiplyGlobal R ι b (a + d) t).val.app (Opposite.op V)
      ((twistingMultiplyGlobal R ι a d s).val.app (Opposite.op V) x)).val i =
    ((eqToHom (congrArg (twistingSheaf R ι) h₄)).val.app (Opposite.op V)
      ((twistingMultiplyGlobal R ι a (b + d) s).val.app (Opposite.op V)
        ((twistingMultiplyGlobal R ι b d t).val.app (Opposite.op V) x))).val i
  rw [twistingSection_eqToHom_val R ι h₄]
  simp only [twistingMultiplyGlobal_app, twistingSectionMul_apply]
  ring

/-- The composition isomorphism `O(a) ⊗ (O(b) ⊗ -) ≅ O(c) ⊗ -` for `a + b = c`. -/
def twistingTensorCompIsoTo (a b c : ℤ) (h : a + b = c) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b) ⋙
        moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a) ≅
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c) :=
  twistingTensorCompIso R ι a b ≪≫
    eqToIso (congrArg (fun d => moduleTensorLeftFunctor (ProjectiveSpace R ι)
      (twistingSheaf R ι d)) h)

/-- The coefficient map of a transport of twists is the transport of twist functors. -/
theorem moduleTensorCoefficientMap_twistingEqToHom {c c' : ℤ} (h : c = c') :
    moduleTensorCoefficientMap (ProjectiveSpace R ι) (eqToHom (congrArg (twistingSheaf R ι) h)) =
      (eqToIso (congrArg (fun d => moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι d)) h)).hom := by
  subst h
  simp only [eqToHom_refl, moduleTensorCoefficientMap_id, eqToIso_refl, Iso.refl_hom]

/-- Multiplication with a free target degree is the canonical multiplication followed by the
transport of twist functors. -/
theorem twistingTensorMultiplyTo_eq (a d d' : ℤ) (h : a + d = d')
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) :
    twistingTensorMultiplyTo R a d d' h s = twistingTensorMultiply R ι a d s ≫
      (eqToIso (congrArg (fun k => moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι k)) h)).hom := by
  rw [twistingTensorMultiplyTo, moduleTensorCoefficientMap_comp,
    moduleTensorCoefficientMap_twistingEqToHom R ι h]
  rfl

/-- Multiplication on the inner factor commutes with the composition isomorphisms, for free
degrees. -/
theorem twistingTensor_map_multiplyTo_comp_compIsoTo (a b b' e c c' : ℤ) (h₁ : a + b = b')
    (h₂ : e + b = c) (h₃ : e + b' = c') (h₄ : a + c = c')
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) (G : (ProjectiveSpace R ι).Modules) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι e)).map
        ((twistingTensorMultiplyTo R a b b' h₁ s).app G) ≫
        (twistingTensorCompIsoTo R ι e b' c' h₃).hom.app G =
      (twistingTensorCompIsoTo R ι e b c h₂).hom.app G ≫
        (twistingTensorMultiplyTo R a c c' h₄ s).app G := by
  subst h₁ h₂ h₃
  simp only [twistingTensorCompIsoTo, eqToIso_refl, Iso.trans_refl, twistingTensorMultiplyTo_rfl]
  rw [twistingTensorMultiplyTo_eq, NatTrans.comp_app]
  exact twistingMultiplyGlobal_coefficientMap_map_tensor_comp R ι a e b s G h₄

/-- Multiplication on the outer factor, followed by the composition isomorphism, is the
composition isomorphism followed by multiplication, for free degrees. -/
theorem twistingTensorMultiplyTo_app_comp_compIsoTo (a e e' b c c' : ℤ) (h₁ : a + e = e')
    (h₂ : e + b = c) (h₃ : e' + b = c') (h₄ : a + c = c')
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) (G : (ProjectiveSpace R ι).Modules) :
    (twistingTensorMultiplyTo R a e e' h₁ s).app
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).obj G) ≫
        (twistingTensorCompIsoTo R ι e' b c' h₃).hom.app G =
      (twistingTensorCompIsoTo R ι e b c h₂).hom.app G ≫
        (twistingTensorMultiplyTo R a c c' h₄ s).app G := by
  subst h₁ h₂ h₃
  simp only [twistingTensorCompIsoTo, eqToIso_refl, Iso.trans_refl, twistingTensorMultiplyTo_rfl]
  rw [twistingTensorMultiplyTo_eq, NatTrans.comp_app]
  exact twistingMultiplyGlobal_coefficientMap_app_tensor_comp R ι a e b s G h₄

open MonoidalCategory

-- The component of `twistingTensorMultiply` is spelled with the coefficient map; it is the
-- whiskering `twistingMultiplyGlobal a d s ▷ G` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a global section `s` of `O(a)` on the twist factor of `O(d) ⊗ G` is
multiplication by the unit morphism of `s`, followed by the inverse associator and twist
multiplication. -/
theorem twistingTensorMultiply_app_eq_unitMultiply (a d : ℤ) (s : Γ(twistingSheaf R ι a, ⊤))
    (G : (ProjectiveSpace R ι).Modules) :
    (twistingTensorMultiply R ι a d s).app G =
      unitMultiply (twistingSectionUnitHom s) (twistingSheaf R ι d ⊗ G) ≫
        (α_ (twistingSheaf R ι a) (twistingSheaf R ι d) G).inv ≫
          twistingTensorMap R ι a d ▷ G := by
  change twistingMultiplyGlobal R ι a d s ▷ G = _
  rw [twistingMultiplyGlobal_eq_unitMultiply, comp_whiskerRight,
    ← unitMultiply_whiskerRight_associator, Category.assoc, Iso.hom_inv_id_assoc]

/-! ### The composition isomorphisms in the monoidal spelling -/

-- The component of the composition isomorphism has source `(T_b ⋙ T_a).obj G`; the declared
-- source `O(a) ⊗ T_b.obj G` agrees with it only after unfolding. The conversion is checked here,
-- once, at variable degrees.
set_option backward.isDefEq.respectTransparency false in
/-- The composition isomorphism `O(a) ⊗ (O(b) ⊗ G) ⟶ O(c) ⊗ G` for `a + b = c`, with the monoidal
tensor product on the outer factor. -/
def twistMerge (a b c : ℤ) (h : a + b = c) (G : (ProjectiveSpace R ι).Modules) :
    twistingSheaf R ι a ⊗ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι b)).obj G ⟶
      (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G :=
  (twistingTensorCompIsoTo R ι a b c h).hom.app G

-- The declared target `O(a) ⊗ T_b.obj G` agrees with `(T_b ⋙ T_a).obj G` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse composition isomorphism `O(c) ⊗ G ⟶ O(a) ⊗ (O(b) ⊗ G)` for `a + b = c`. -/
def twistMergeInv (a b c : ℤ) (h : a + b = c) (G : (ProjectiveSpace R ι).Modules) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι c)).obj G ⟶
      twistingSheaf R ι a ⊗ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι b)).obj G :=
  (twistingTensorCompIsoTo R ι a b c h).inv.app G

-- The declared objects agree with the composite-functor spelling only after unfolding.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem twistMergeInv_twistMerge (a b c : ℤ) (h : a + b = c) (G : (ProjectiveSpace R ι).Modules) :
    twistMergeInv R ι a b c h G ≫ twistMerge R ι a b c h G = 𝟙 _ :=
  (twistingTensorCompIsoTo R ι a b c h).inv_hom_id_app G

-- The declared objects agree with the composite-functor spelling only after unfolding.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem twistMerge_twistMergeInv (a b c : ℤ) (h : a + b = c) (G : (ProjectiveSpace R ι).Modules) :
    twistMerge R ι a b c h G ≫ twistMergeInv R ι a b c h G = 𝟙 _ :=
  (twistingTensorCompIsoTo R ι a b c h).hom_inv_id_app G

instance twistMerge_isIso (a b c : ℤ) (h : a + b = c) (G : (ProjectiveSpace R ι).Modules) :
    IsIso (twistMerge R ι a b c h G) :=
  ⟨⟨twistMergeInv R ι a b c h G, twistMerge_twistMergeInv R ι a b c h G,
    twistMergeInv_twistMerge R ι a b c h G⟩⟩

-- The declared source `O(a) ⊗ T_d.obj G` agrees with `(T_d ⋙ T_a).obj G` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- With the canonical degree, `twistMerge` is the inverse associator followed by twist
multiplication. -/
theorem twistMerge_eq (a d : ℤ) (G : (ProjectiveSpace R ι).Modules) :
    twistMerge R ι a d (a + d) rfl G =
      (α_ (twistingSheaf R ι a) (twistingSheaf R ι d) G).inv ≫ twistingTensorMap R ι a d ▷ G := by
  rw [twistMerge, twistingTensorCompIsoTo, Iso.trans_hom, NatTrans.comp_app,
    ← twistingTensorCompIso_hom_app]
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.comp_id _

-- The unit multiplication has source `O(d) ⊗ G` in the bridge and `T_d.obj G` here; they agree
-- only after unfolding, at variable degrees.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a global section `s` of `O(a)`, followed by `twistMerge`, is twist
multiplication with a free target degree. -/
theorem unitMultiply_twistMerge (a d d' : ℤ) (h : a + d = d') (s : Γ(twistingSheaf R ι a, ⊤))
    (G : (ProjectiveSpace R ι).Modules) :
    unitMultiply (twistingSectionUnitHom s)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj G) ≫
        twistMerge R ι a d d' h G =
      (twistingTensorMultiplyTo R a d d' h s).app G := by
  subst h
  rw [twistMerge_eq, twistingTensorMultiplyTo_rfl, twistingTensorMultiply_app_eq_unitMultiply]
  rfl

-- `T_a.map f` and `O(a) ◁ f`, and the composite-functor objects, agree only after unfolding,
-- at variable degrees.
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication on the inner factor commutes with the inverse composition isomorphisms. -/
theorem multiplyTo_comp_twistMergeInv (a₀ a b b' c c' : ℤ) (h₁ : a₀ + b = b') (h₂ : a + b = c)
    (h₃ : a + b' = c') (h₄ : a₀ + c = c') (s : (twistingSheaf R ι a₀).val.obj (op ⊤))
    (G : (ProjectiveSpace R ι).Modules) :
    (twistingTensorMultiplyTo R a₀ c c' h₄ s).app G ≫ twistMergeInv R ι a b' c' h₃ G =
      twistMergeInv R ι a b c h₂ G ≫
        twistingSheaf R ι a ◁ (twistingTensorMultiplyTo R a₀ b b' h₁ s).app G := by
  have hI := twistingTensor_map_multiplyTo_comp_compIsoTo R ι a₀ b b' a c c' h₁ h₂ h₃ h₄ s G
  rw [← cancel_epi (twistMerge R ι a b c h₂ G), twistMerge_twistMergeInv_assoc,
    ← cancel_mono (twistMerge R ι a b' c' h₃ G), Category.assoc, Category.assoc,
    twistMergeInv_twistMerge, Category.comp_id]
  exact hI.symm

/-- Whiskering by a twisting sheaf preserves monomorphisms. -/
instance twisting_whiskerLeft_mono (a : ℤ) {A B : (ProjectiveSpace R ι).Modules} (f : A ⟶ B)
    [Mono f] : Mono (twistingSheaf R ι a ◁ f) :=
  inferInstanceAs (Mono ((moduleTensorLeftFunctor (ProjectiveSpace R ι)
    (twistingSheaf R ι a)).map f))

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace MonoidalCategory

variable (R : Type u) [CommRing R] (ι : Type u)

-- The functor of the twist equivalence is the twist tensor functor, whose maps are the
-- whiskerings only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Whiskering by a twisting sheaf reflects epimorphisms. -/
theorem epi_of_twisting_whiskerLeft (a : ℤ) {A B : (ProjectiveSpace R ι).Modules} (f : A ⟶ B)
    (h : Epi (twistingSheaf R ι a ◁ f)) : Epi f := by
  let E := twistingTensorEquivalence R ι a
  have h' : Epi (E.functor.map f) := h
  constructor
  intro Z g k hgk
  apply E.functor.map_injective
  rw [← cancel_epi (E.functor.map f), ← E.functor.map_comp, ← E.functor.map_comp, hgk]

end AlgebraicGeometry.Scheme.Cohomology
