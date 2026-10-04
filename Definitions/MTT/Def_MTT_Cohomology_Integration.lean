module

public import Definitions.MTT.Def_MTT_Cohomology

@[expose] public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
namespace MTT.Cohomology

/-- The exponent vector of the binary monomial X^j Y^(n-j). -/
def binaryExponent (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

/-- The homogeneous period polynomial based at the cusp at infinity. Its coefficient
of X^j Y^(k-2-j) is the normalized vertical modular integral. -/
def cuspPeriodPolynomial {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) : Binary ℂ :=
  ∑ j ∈ Finset.range (k - 1),
    MvPolynomial.monomial (binaryExponent (k - 2) j)
      (((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r)

/-- A primitive for cusp-to-cusp integration, normalized to vanish at infinity. -/
def cuspPrimitive {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp) : Binary ℂ :=
  match x with
  | none => 0
  | some r => cuspPeriodPolynomial f r

/-- The raw polynomial-valued modular-symbol cocycle attached to a cusp form.
It represents -2*pi*i times the integral from the second cusp to the first. -/
def integrationCochain {N k : ℕ}
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    (Cusp × Cusp) → Binary ℂ :=
  fun D => cuspPrimitive f D.2 - cuspPrimitive f D.1

end MTT.Cohomology

end

end publicSection
