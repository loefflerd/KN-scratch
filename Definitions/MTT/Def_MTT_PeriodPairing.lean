module

public import Definitions.MTT.Def_MTT_Cohomology_Integration
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.NumberTheory.Modular

@[expose] public section publicSection

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace MTT.Cohomology

/-- The antiholomorphic involution of the upper half-plane. -/
def periodReflect (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-conj (z : ℂ), by simpa using z.im_pos⟩

/-- The pure power (zX+Y)^n. -/
def periodPower (n : ℕ) (z : ℂ) : Binary ℂ :=
  (MvPolynomial.C z * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n

/-- Determinant contraction, normalized to B((zX+Y)^n,(wX+Y)^n)=(z-w)^n. -/
def periodContraction (n : ℕ) (P Q : Binary ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (n - j) * AddMonoidAlgebra.coeff P (binaryExponent n j) *
      AddMonoidAlgebra.coeff Q (binaryExponent n (n - j)) / (n.choose j : ℂ)

/-- Complex-valued real-linear differential a dz + b d(conj z). -/
def periodDifferential (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • (ContinuousLinearMap.id ℝ ℂ) + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

/-- Coefficientwise C¹ primitive of g(z)(zX+Y)^n dz - conj(v(z))(conj(z)X+Y)^n d(conj z),
with equivariance and at most polynomial growth in every cusp chart.
The derivative is taken on the open upper half-plane, so values below it are immaterial. -/
def IsMixedPeriodPrimitive {N k : ℕ}
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ)) (U : ℂ → Binary ℂ) : Prop :=
  (∀ z : UpperHalfPlane, U z ∈ Sym ℂ (k - 2)) ∧
  (∀ (γ : CongruenceSubgroup.Gamma1 N) (z : UpperHalfPlane),
    U (γ.val • z : UpperHalfPlane) = act γ.val.val (U z)) ∧
  (∀ (z : UpperHalfPlane) (e : Fin 2 →₀ ℕ),
    HasFDerivAt (fun w : ℂ => AddMonoidAlgebra.coeff (U w) e)
      (periodDifferential
        (AddMonoidAlgebra.coeff (g z • periodPower (k - 2) z) e)
        (-AddMonoidAlgebra.coeff (conj (v z) • periodPower (k - 2) (conj (z : ℂ))) e))
      (z : ℂ)) ∧
  (∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (e : Fin 2 →₀ ℕ)
      (W : ℝ), 0 < W → ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧
    ∀ z : UpperHalfPlane, 1 ≤ z.im → |z.re| ≤ W →
      ‖AddMonoidAlgebra.coeff (act (δ⁻¹).val (U (δ • z : UpperHalfPlane))) e‖ ≤
        C * (1 + z.im) ^ A)

/-- Integrate an invariant scalar density by summing over right-coset representatives
(inverted to obtain left-coset representatives), using hyperbolic measure.
For N>0 the indexing quotient is finite. The possible central multiplicity is harmless. -/
def periodDomainIntegral (N : ℕ) (F : UpperHalfPlane → ℂ) : ℂ :=
  ∑' q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma1 N,
    ∫ z in ModularGroup.fd, F (q.out⁻¹ • z)

/-- Wedge contraction with the universal nonzero dz∧d(conj z) factor removed.
The factor y² converts the area density to hyperbolic measure. -/
def periodPairing (N n : ℕ) (f q : UpperHalfPlane → ℂ) : ℂ :=
  periodDomainIntegral N (fun z => (z.im : ℂ) ^ 2 *
    periodContraction n (f z • periodPower n z)
      (conj (q z) • periodPower n (conj (z : ℂ))))

/-- The Petersson product, linear in the first argument, with the same domain convention. -/
def periodPetersson (N k : ℕ) (f q : UpperHalfPlane → ℂ) : ℂ :=
  periodDomainIntegral N (fun z => f z * conj (q z) * (z.im : ℂ) ^ k)

end MTT.Cohomology

end

end publicSection
