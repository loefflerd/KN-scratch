/-
Based on Prove2Me node MTT.Cohomology.base_change
(55e287ab-365f-40fb-a1e3-d7a58f9f4d43) by davidloeffler (2026-09-06).

Proof based on Prove2Me submission 4c16e7fa-0b5a-4e2e-adf3-ffd753485b18
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

import Theorems.MTT.Thm_MTT_Cohomology_integral_classes_span
import Theorems.MTT.Thm_MTT_Cohomology_manin_generation

/-!
# Flat base change for compactly supported group cohomology

Theorem statement: `MTT.Cohomology.base_change` (`55e287ab-365f-40fb-a1e3-d7a58f9f4d43`), by
davidloeffler, 2026-09-06.

Proof: submission `4c16e7fa-0b5a-4e2e-adf3-ffd753485b18`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

For positive level, coefficientwise extension gives the canonical R-linear isomorphism R ⊗_Z
Hc¹(Γ₁(N), Symⁿ Z²) ≃ Hc¹(Γ₁(N), Symⁿ R²) for every commutative ring flat over Z. This includes
Qbar, C and Cp. Compatibility is specified on pure tensors, not merely existence of an unrelated
isomorphism.

## Explanation of the source proof

## Flat base change, reduced to Manin's presentation

Write $M_R := H^1_c(\Gamma_1(N),\operatorname{Sym}^n R^2)$ for the modular-symbol model used here:
$\Gamma_1(N)$-equivariant cocycles on pairs of cusps with values in the binary forms of degree $n$.
Coefficientwise extension along $\mathbf Z\to R$ gives a $\mathbf Z$-linear map
$\mathrm{ext}\colon M_{\mathbf Z}\to M_R$, and its $R$-linear extension
$$\beta\colon R\otimes_{\mathbf Z} M_{\mathbf Z}\longrightarrow M_R,\qquad
\beta(r\otimes\varphi)=r\cdot\mathrm{ext}(\varphi),$$
is the map whose bijectivity is asserted. This submission proves that $\beta$ is well defined,
proves that it is **injective**, and reduces **surjectivity** to the imported open lemma
`integral_classes_span`.

### 1. $\beta$ is well defined

The three defining conditions survive coefficient extension. Homogeneity does because
$\operatorname{coeff}_d(\mathrm{map}\,f\,P)=f(\operatorname{coeff}_d P)$, so a coefficient that is
nonzero after extension was already nonzero. The cocycle relation does because
$\mathrm{map}\,f$ is additive. Equivariance does because the coefficient action
$$(\mathrm{act}\,A\,P)(X,Y)=P\bigl((X,Y)A\bigr)$$
is substitution of $\mathbf Z$-linear forms: with $A$ an *integral* matrix,
$\mathrm{act}\,A\circ \mathrm{map}\,f=\mathrm{map}\,f\circ \mathrm{act}\,A$ for every ring
homomorphism $f$ (`act_map`, proved by $\mathrm{bind}_1$-naturality). This is the only place where
integrality of the group elements is used, and it is what makes the whole diagram defined over
$\mathbf Z$.

### 2. Manin coordinates

Let $\mathcal C = \Gamma_1(N)\backslash SL_2(\mathbf Z)$, a **finite** set for $N>0$, and fix a
representative $g_q$ of each coset. Define
$$\Theta_R\colon M_R\longrightarrow \bigoplus_{(q,j)\in \mathcal C\times\{0,\dots,n\}} R,
\qquad \Theta_R(\varphi)_{q,j}=\operatorname{coeff}_{X^jY^{n-j}}\varphi(g_q\cdot 0,\
g_q\cdot\infty).$$

$\Theta_R$ is **injective for every** $R$. Indeed, if $\Theta_R(\varphi)=0$ then, since a form
homogeneous of degree $n$ in two variables is determined by its $n+1$ coefficients on the line
$d_0+d_1=n$, we get $\varphi(g_q\cdot 0,g_q\cdot\infty)=0$ for each representative; equivariance
$\varphi(\gamma x,\gamma y)=\mathrm{act}\,\gamma\,\varphi(x,y)$ propagates this to *every*
$g\in SL_2(\mathbf Z)$, and the imported lemma `manin_generation` — the statement that unimodular
paths generate $\operatorname{Div}^0(\mathbf P^1(\mathbf Q))$, proved by the continued-fraction
algorithm — gives $\varphi=0$.

### 3. Injectivity of $\beta$

The point of $\Theta$ is that it is defined over $\mathbf Z$ and lands in a **finite free** module,
so it converts flatness into the statement we need. The square
$$\begin{array}{ccc}
R\otimes_{\mathbf Z} M_{\mathbf Z} & \xrightarrow{\ \beta\ } & M_R\\
\downarrow{\scriptstyle \mathrm{id}\otimes\Theta_{\mathbf Z}} & & \downarrow{\scriptstyle
\Theta_R}\\
R\otimes_{\mathbf Z}\bigl(\mathcal I\to \mathbf Z\bigr) & \xrightarrow{\ \sim\ } & \bigl(\mathcal
I\to R\bigr)
\end{array}$$
commutes, where $\mathcal I=\mathcal C\times\{0,\dots,n\}$ and the bottom isomorphism is the
canonical one for a *finite* index set. Commutativity is checked on pure tensors, where both routes
send $r\otimes\varphi$ to the family $r\cdot\overline{\Theta_{\mathbf Z}(\varphi)_{q,j}}$ — the
$\mathbf Z$-action $m\cdot r$ on the left, multiplication by the image of $m$ in $R$ on the right —
and then extended by additivity through `TensorProduct.induction_on`.

Now $\Theta_{\mathbf Z}$ is injective by §2 with $R=\mathbf Z$; flatness of $R$ over $\mathbf Z$
makes $\mathrm{id}_R\otimes\Theta_{\mathbf Z}$ injective; the bottom map is an isomorphism because
$\mathcal I$ is finite. Hence $\Theta_R\circ\beta$ is injective, and therefore so is $\beta$.
Note that this half needs only the *generation* half of Manin's theorem.

### 4. Surjectivity: the reduction

Surjectivity is the assertion that every $R$-valued class is an $R$-linear combination of
coefficientwise extensions of integral classes; that is exactly the imported open lemma
`integral_classes_span`. Given $\Phi\in M_R$ and a representation
$\Phi=\sum_{i} c_i\,\mathrm{ext}(\varphi_i)$, the element $\sum_i c_i\otimes\varphi_i$ maps to
$\Phi$ under $\beta$.

This is where the genuinely deeper input sits, and it is why the decomposition is drawn here.
Injectivity needs only that the unimodular paths *generate*; surjectivity needs Manin's full
**presentation** — that the two-term and three-term relations generate all relations among the
Manin symbols — so that $M_{(-)}$ is the kernel of a fixed integer matrix on a finite free
coefficient module and flatness lets the kernel commute with $-\otimes_{\mathbf Z}R$. Splitting the
theorem along this line isolates the presentation as a single reusable obligation instead of
burying it inside a base-change proof.

### 5. Conclusion

$\beta$ is bijective, so `LinearEquiv.ofBijective` produces the required $R$-linear isomorphism
$e$, and the compatibility demanded on pure tensors holds on the nose:
$e(1\otimes\varphi)=1\cdot \mathrm{ext}(\varphi)=\mathrm{ext}(\varphi)$, whose value at $(x,y)$ is
by construction $\mathrm{map}\,(\mathbf Z\to R)\,\varphi(x,y)$. $\square$

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MBC

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

/-! ### The defining properties, unpacked -/

theorem hc_hom (φ : Hc N n R) (x y : Cusp) : φ.val (x, y) ∈ MTT.Cohomology.Sym R n := φ.2.1 x y

theorem hc_add (φ : Hc N n R) (x y z : Cusp) :
    φ.val (x, y) + φ.val (y, z) = φ.val (x, z) := φ.2.2.1 x y z

theorem hc_equiv (φ : Hc N n R) (γ : CongruenceSubgroup.Gamma1 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ.val (x, y)) := φ.2.2.2 γ x y

theorem cuspAct_mul (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : Cusp) :
    cuspAct (g * h) x = cuspAct g (cuspAct h x) := by
  simp [cuspAct, map_mul, mul_smul]

/-! ### Coefficientwise extension along a ring homomorphism -/

/-- The coefficient action is defined by an integral matrix, hence commutes with any
change of coefficient ring. -/
theorem act_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A (MvPolynomial.map f P) = MvPolynomial.map f (act A P) := by
  unfold act
  simp only [AlgHom.toLinearMap_apply]
  show MvPolynomial.bind₁ (fun i : Fin 2 => ∑ a : Fin 2, (A a i : S) • MvPolynomial.X a)
      (MvPolynomial.map f P)
    = MvPolynomial.map f (MvPolynomial.bind₁
        (fun i : Fin 2 => ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P)
  have hfun : (fun i : Fin 2 =>
      MvPolynomial.map f (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a))
      = fun i : Fin 2 => (∑ a : Fin 2, (A a i : S) • MvPolynomial.X a) := by
    funext i; simp [MvPolynomial.smul_eq_C_mul]
  rw [MvPolynomial.map_bind₁, hfun]

theorem map_homogeneous {S : Type*} [CommRing S] (f : R →+* S) {P : Binary R}
    (hP : P ∈ MTT.Cohomology.Sym R n) : MvPolynomial.map f P ∈ MTT.Cohomology.Sym S n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  refine hP (d := d) ?_
  intro h0
  rw [MvPolynomial.coeff_map, h0, map_zero] at hd
  exact hd rfl

/-- Coefficientwise extension of an integral class, as a `ℤ`-linear map. -/
def extHom (N n : ℕ) (R : Type*) [CommRing R] : Hc N n ℤ →+ Hc N n R where
  toFun φ := ⟨fun D => MvPolynomial.map (Int.castRingHom R) (φ.val D),
    ⟨fun x y => map_homogeneous _ (hc_hom φ x y),
     fun x y z => by rw [← map_add]; exact congrArg _ (hc_add φ x y z),
     fun γ x y => by
       dsimp only
       rw [hc_equiv φ γ x y]
       exact (act_map (Int.castRingHom R) _ _).symm⟩⟩
  map_zero' := by
    refine Subtype.ext (funext fun D => ?_)
    show MvPolynomial.map (Int.castRingHom R) (0 : Binary ℤ) = 0
    simp
  map_add' φ ψ := by
    refine Subtype.ext (funext fun D => ?_)
    show MvPolynomial.map (Int.castRingHom R) (φ.val D + ψ.val D) = _
    simp [map_add]

/-- Coefficientwise extension, as a `ℤ`-linear map. -/
def ext (N n : ℕ) (R : Type*) [CommRing R] : Hc N n ℤ →ₗ[ℤ] Hc N n R :=
  (extHom N n R).toIntLinearMap

@[simp] theorem ext_val (φ : Hc N n ℤ) (D : Cusp × Cusp) :
    (ext N n R φ).val D = MvPolynomial.map (Int.castRingHom R) (φ.val D) := rfl

end P2MBC

namespace P2MBC

open MvPolynomial

/-- The right-coset space of `Γ₁(N)` in `SL(2,ℤ)`. -/
abbrev Cos (N : ℕ) := Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N))

instance cosFinite (N : ℕ) [NeZero N] : Finite (Cos N) :=
  Finite.of_equiv _
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (CongruenceSubgroup.Gamma1 N)).symm

/-- The finite index set of Manin coordinates. -/
abbrev Idx (N n : ℕ) := Cos N × Fin (n + 1)

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- Reduction to coset representatives: `Γ₁(N)`-equivariance moves any unimodular path to
the representative of its coset, so vanishing on representatives suffices. -/
theorem hc_eq_zero_of_reps (φ : Hc N n R)
    (hR : ∀ q : Cos N,
      φ.val (cuspAct q.out ((0 : ℚ) : Cusp), cuspAct q.out OnePoint.infty) = 0) :
    φ = 0 := by
  refine MTT.Cohomology.manin_generation φ fun g => ?_
  set q : Cos N := Quotient.mk _ g with hqdef
  have hmk : (Quotient.mk (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N)) q.out)
      = Quotient.mk _ g := by rw [Quotient.out_eq]
  have hrel : g * (Quotient.out q)⁻¹ ∈ CongruenceSubgroup.Gamma1 N :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hmk)
  obtain ⟨γ, hγ⟩ : ∃ γ : CongruenceSubgroup.Gamma1 N, g = γ.val * q.out :=
    ⟨⟨g * (q.out)⁻¹, hrel⟩, by simp⟩
  rw [hγ, cuspAct_mul, cuspAct_mul, hc_equiv φ γ, hR q, map_zero]

/-! ### Binary forms are determined by their `X^j Y^{n-j}` coefficients -/

/-- The exponent vector of `X^j Y^{n-j}`. -/
def mono (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem mono_apply (n j : ℕ) (i : Fin 2) : mono n j i = if i = 0 then j else n - j := rfl

theorem hom_eq_zero (P : Binary R) (hP : P ∈ MTT.Cohomology.Sym R n)
    (h : ∀ j : Fin (n + 1), AddMonoidAlgebra.coeff P (mono n j.val) = 0) : P = 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP
  ext d
  change AddMonoidAlgebra.coeff P d = 0
  by_cases hdeg : d.degree = n
  · have hsum : d 0 + d 1 = n := by
      have hds := Finsupp.degree_eq_sum d
      rw [Fin.sum_univ_two] at hds
      rw [hds] at hdeg
      exact hdeg
    have hd : d = mono n (d 0) := by
      refine Finsupp.ext fun i => ?_
      fin_cases i
      · simp [mono_apply]
      · simp only [mono_apply]
        norm_num
        omega
    have := h ⟨d 0, by omega⟩
    rwa [← hd] at this
  · exact hP.coeff_eq_zero hdeg

/-! ### The Manin coordinate map -/

variable [NeZero N]

/-- Coordinates of a class: the `X^j Y^{n-j}` coefficients on the unimodular paths attached
to a fixed set of coset representatives. -/
def ThetaF (N n : ℕ) [NeZero N] (R : Type*) [CommRing R] :
    Hc N n R →ₗ[R] (Idx N n →₀ R) where
  toFun φ := Finsupp.equivFunOnFinite.symm fun z : Idx N n =>
    AddMonoidAlgebra.coeff (φ.val (cuspAct z.1.out ((0 : ℚ) : Cusp), cuspAct z.1.out OnePoint.infty)) (mono n z.2.val)
  map_add' φ ψ := by ext z; simp
  map_smul' c φ := by
    ext z
    show AddMonoidAlgebra.coeff ((c • φ).val _) _ = c * AddMonoidAlgebra.coeff (φ.val _) _
    exact MvPolynomial.coeff_smul _ _ _

@[simp] theorem ThetaF_apply (φ : Hc N n R) (z : Idx N n) :
    ThetaF N n R φ z = AddMonoidAlgebra.coeff (φ.val (cuspAct z.1.out ((0 : ℚ) : Cusp), cuspAct z.1.out OnePoint.infty)) (mono n z.2.val) := rfl

theorem ThetaF_injective : Function.Injective (ThetaF N n R) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine hc_eq_zero_of_reps φ fun q => ?_
  refine hom_eq_zero _ (hc_hom φ _ _) fun j => ?_
  have := congrArg (fun f => f (q, j)) hφ
  simpa using this

end P2MBC

namespace P2MBC

open MvPolynomial

local instance idxDecEq (N n : ℕ) : DecidableEq (Idx N n) := Classical.decEq _

variable {N n : ℕ} {R : Type*} [CommRing R] [NeZero N]

/-- The canonical base-change map, the `R`-linear extension of coefficientwise extension. -/
abbrev beta (N n : ℕ) (R : Type*) [CommRing R] :
    R ⊗[ℤ] Hc N n ℤ →ₗ[R] Hc N n R :=
  (ext N n R).liftBaseChange R

theorem ThetaF_ext (φ : Hc N n ℤ) (z : Idx N n) :
    ThetaF N n R (ext N n R φ) z = ((ThetaF N n ℤ φ z : ℤ) : R) := by
  rw [ThetaF_apply, ThetaF_apply, ext_val, MvPolynomial.coeff_map]
  rfl

/-- The Manin coordinates intertwine the base-change map with the tensor product of the
integral coordinate map. -/
theorem square (x : R ⊗[ℤ] Hc N n ℤ) (z : Idx N n) :
    TensorProduct.finsuppScalarRight ℤ ℤ R (Idx N n)
        (LinearMap.lTensor R (ThetaF N n ℤ) x) z
      = ThetaF N n R (beta N n R x) z := by
  induction x using TensorProduct.inductionOn with
  | tmul r φ =>
      rw [LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply,
        beta, LinearMap.liftBaseChange_tmul, map_smul, Finsupp.smul_apply,
        ThetaF_ext φ z, smul_eq_mul, zsmul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem beta_injective [Module.Flat ℤ R] : Function.Injective (beta N n R) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : LinearMap.lTensor R (ThetaF N n ℤ) x = 0 := by
    apply (TensorProduct.finsuppScalarRight ℤ ℤ R (Idx N n)).injective
    rw [map_zero]
    refine Finsupp.ext fun z => ?_
    rw [square x z, hx, map_zero]
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap
    (M := R) (ThetaF N n ℤ) ThetaF_injective
  exact hinj (by rw [h1, map_zero])

omit [NeZero N] in
theorem beta_surjective (hN : 0 < N) [Module.Flat ℤ R] :
    Function.Surjective (beta N n R) := by
  intro Φ
  obtain ⟨m, c, φ, hφ⟩ := MTT.Cohomology.integral_classes_span hN R Φ
  refine ⟨∑ i, c i ⊗ₜ[ℤ] φ i, ?_⟩
  rw [map_sum]
  refine Subtype.ext (funext fun D => ?_)
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [hφ D]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta, LinearMap.liftBaseChange_tmul]
  rfl

end P2MBC

open P2MBC in
theorem solution {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [Module.Flat ℤ R] :
    BaseChange N n R := by
  have : NeZero N := ⟨hN.ne'⟩
  have hbij : Function.Bijective (beta N n R) :=
    ⟨beta_injective, beta_surjective hN⟩
  refine ⟨LinearEquiv.ofBijective (beta N n R) hbij, fun φ x y => ?_⟩
  show ((beta N n R) (1 ⊗ₜ[ℤ] φ)).val (x, y) = _
  rw [LinearMap.liftBaseChange_one_tmul]
  rfl
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.base_change
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [Module.Flat ℤ R] :
    BaseChange N n R := _root_.solution hN R
end

end publicSection
