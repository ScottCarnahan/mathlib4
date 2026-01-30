/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Loop Lie algebras and their central extensions
Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Loop Lie algebras admit central extensions attached to invariant inner products on the base Lie
algebra. When the base Lie algebra is finite dimensional and simple, the corresponding central
extension (with an outer derivation attached) admits an infinite root system with affine Weyl group.
These extended Lie algebras are called untwisted affine Kac-Moody Lie algebras.

We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `loopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.loopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.loopAlgebra.toFinsupp`: A linear equivalence from the loop algebra to the space of
  finitely supported functions.
* `LieAlgebra.loopAlgebra.twoCochainOfBilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
* `LieAlgebra.loopAlgebra.twoCocycleOfBilinear`: The 2-cocycle for a loop algebra with trivial
  coefficients attached to a symmetric invariant bilinear form on the base Lie algebra.

## TODO
* Evaluation representations
* Construction of central extensions from invariant forms.
* Positive energy representations induced from a fixed central character

## Tags
lie ring, lie algebra, base change, Laurent polynomial
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R A L : Type*)

--delete this
lemma residuePairing_finite_support [CommRing R] [AddCommGroup A] [SMulZeroClass A R]
    [AddCommGroup L] [Module R L]
    (Φ : LinearMap.BilinForm R L) (f g : A →₀ L) :
    Finite (fun a ↦ a • (Φ (f (-a)) (g a))).support := by
  refine Finite.Set.subset ((fun a ↦ (-a)) '' f.support) ?_
  intro n hn
  simp only [Set.image_neg_eq_neg, Set.mem_neg, SetLike.mem_coe, Finsupp.mem_support_iff]
  contrapose! hn
  simp [hn]

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z⁻¹]`. We make a
slightly more general definition which coincides with the Laurent polynomial construction when
`A = ℤ` -/
abbrev loopAlgebra := AddMonoidAlgebra R A ⊗[R] L

open LaurentPolynomial in
/-- An Lie algebra isomorphism between the Loop algebra (with `A = ℤ`) and the tensor product with
Laurent polynomials. -/
def loopAlgebraEquivLaurent :
    loopAlgebra R ℤ L ≃ₗ⁅R⁆ R[T;T⁻¹] ⊗[R] L :=
  LieEquiv.refl

namespace LoopAlgebra

open Classical in
/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : loopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]
lemma toFinsupp_symm_single (c : A) (z : L) :
    (toFinsupp R A L).symm (Finsupp.single c z) = AddMonoidAlgebra.single c 1 ⊗ₜ[R] z := by
  simp [toFinsupp]

@[simp]
lemma toFinsupp_single_tmul (c : A) (z : L) :
    (toFinsupp R A L (AddMonoidAlgebra.single c 1 ⊗ₜ[R] z)) = Finsupp.single c z := by
  simp [← toFinsupp_symm_single]

/-- The residue pairing on the loop algebra.  When `A = ℤ` and the elements are viewed as Laurent
polynomials with coefficients in `L`, the pairing is interpreted as `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairing [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) where
  toFun f :=
    { toFun g := (toFinsupp R A L g).sum fun a v ↦ a • Φ (toFinsupp R A L f (-a)) v
      map_add' x y := by
        classical
        have : ((toFinsupp R A L (x + y))).support ⊆
            (toFinsupp R A L x).support ∪ (toFinsupp R A L y).support := by
          intro a ha
          contrapose! ha
          simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, Decidable.not_not] at ha
          simp [ha.1, ha.2]
        rw [Finsupp.sum_of_support_subset _ this _ (by simp), Finsupp.sum_of_support_subset _
          (Finset.union_subset_left (u := (toFinsupp R A L x).support ∪ (toFinsupp R A L y).support)
          fun _ z ↦ z) _ (by simp), Finsupp.sum_of_support_subset _ (Finset.union_subset_right
          (u := (toFinsupp R A L x).support ∪ (toFinsupp R A L y).support) fun _ y ↦ y) _ (by simp)]
        simp [Finset.sum_add_distrib]
      map_smul' r x := by
        rw [map_smul, Finsupp.sum_of_support_subset _ (Finsupp.support_smul) _ (by simp),
          Finsupp.sum, Finset.smul_sum]
        simp [-smul_eq_mul, smul_comm] }
  map_add' x y := by
    ext
    simp [Finsupp.sum_add]
  map_smul' r x := by
    ext
    simp [-smul_eq_mul, smul_comm]

/-- A 2-cochain on a loop algebra given by an invariant bilinear form. When `A = ℤ`, the alternating
condition amounts to the fact that Res f df = 0. -/
def twoCochainOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ) :
    LieModule.Cohomology.twoCochain R (loopAlgebra R A L)
      (TrivialLieModule R (loopAlgebra R A L) R) where
  val := ((residuePairing R A L Φ).compr₂
    ((TrivialLieModule.equiv R (loopAlgebra R A L) R).symm.toLinearMap))
  property := by
    refine LieModule.Cohomology.mem_twoCochain_iff.mpr ?_
    intro f
    simp only [LinearMap.compr₂_apply, residuePairing_apply_apply, LinearEquiv.coe_coe,
      EmbeddingLike.map_eq_zero_iff]
    classical
    set s := (toFinsupp R A L f).support ∪ (toFinsupp R A L f).support.image (Equiv.neg A) with hs
    rw [Finsupp.sum_of_support_subset _ (Finset.union_subset_left (u := s) fun _ x ↦ x) _ (by simp)]
    let g := fun n ↦ n • (Φ (toFinsupp R A L f (-n))) (toFinsupp R A L f n)
    refine Function.Odd.finset_sum_eq_zero (fun n ↦ by simp [hΦ.eq]) (Finset.map_eq_of_subset ?_)
    intro x hx
    rw [Finset.mem_union]
    simp only [Finset.mem_map_equiv, Equiv.neg_symm, Equiv.neg_apply, hs, Finset.mem_union] at hx
    obtain (h|h) := hx
    · exact Or.inr <| Finset.mem_image.mpr <| Exists.intro (-x) (by simp [h])
    · exact Or.inl (by simpa using h)

@[simp]
lemma twoCochainOfBilinear_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (x y : loopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm ((residuePairing R A L Φ) x y) :=
  rfl

/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
@[simps]
def twoCocycleOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) :
    LieModule.Cohomology.twoCocycle R (loopAlgebra R A L)
      (TrivialLieModule R (loopAlgebra R A L) R) where
  val := twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LieModule.Cohomology.d₂₃_apply, twoCochainOfBilinear_apply_apply,
      residuePairing_apply_apply, toFinsupp_single_tmul, map_zero, smul_zero,
      Finsupp.sum_single_index, trivial_lie_zero, sub_self, add_zero, ExtendScalars.bracket_tmul,
      AddMonoidAlgebra.single_mul_single, mul_one, zero_sub, LinearMap.zero_apply]
    rw [sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add, EquivLike.apply_eq_iff_eq]
    by_cases h0 : a + b + c = 0
    · rw [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind]
      simp only [Finsupp.single_eq_same]
      rw [hΦ, hΦs.eq z ⁅x, y⁆, hΦ y, ← lie_skew y x, hΦs.eq z, LinearMap.BilinForm.neg_left,
        neg_neg, show b = -(a + c) by grind, neg_smul, smul_neg, neg_neg, add_smul, add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

end LoopAlgebra

end LieAlgebra
