import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The only matrix identities needed for the first negative answer.
The exact Pell filtration and cardinalities from issue #14 are not used.
Mathlib's matrix units, transvections, and ring/units APIs are used
throughout. -/
namespace QuandleResearch.Q525
namespace MatrixModel

abbrev Mat (R : Type*) := Matrix (Fin 3) (Fin 3) R

section RingIdentity
variable {A : Type*} [Ring A]

/-- Characteristic-two ring computation underlying the local
reductivity of the elementary conjugacy-class model. -/
theorem fourth_of_cross_sq_zero (hc : ∀ x : A, x+x=0)
    (N M : A) (hN : N*N=0) (hM : M*M=0)
    (hNM : (N*M)*(N*M)=0) (hMN : (M*N)*(M*N)=0) :
    ((1+N)*(1+M))^4=1 := by
  let U := 1+N
  let V := 1+M
  let P := U*V
  let Q := V*U
  have hU : U*U=1 := by
    calc
      U*U = 1+(N+N)+N*N := by dsimp [U]; noncomm_ring
      _ = 1 := by rw [hc N,hN]; simp
  have hV : V*V=1 := by
    calc
      V*V = 1+(M+M)+M*M := by dsimp [V]; noncomm_ring
      _ = 1 := by rw [hc M,hM]; simp
  have hPQ : P*Q=1 := by
    calc
      P*Q = U*(V*V)*U := by dsimp [P,Q]; noncomm_ring
      _ = 1 := by rw [hV,mul_one,hU]
  have hQP : Q*P=1 := by
    calc
      Q*P = V*(U*U)*V := by dsimp [P,Q]; noncomm_ring
      _ = 1 := by rw [hU,mul_one,hV]
  have hsum : P+Q=N*M+M*N := by
    calc
      P+Q = (1+1)+(N+N)+(M+M)+(N*M+M*N) := by
        dsimp [P,Q,U,V]
        noncomm_ring
      _ = _ := by rw [hc 1,hc N,hc M]; simp
  have hs : (P+Q)*(P+Q)=0 := by
    rw [hsum]
    calc
      _ = (N*M)*(N*M)+N*(M*M)*N+M*(N*N)*M+(M*N)*(M*N) := by
        noncomm_ring
      _ = 0 := by rw [hNM,hM,hN,hMN]; simp
  have h : P*P+Q*Q=0 := by
    calc
      P*P+Q*Q = (P*P+Q*Q)+(P*Q+Q*P) := by rw [hPQ,hQP,hc 1,add_zero]
      _ = (P+Q)*(P+Q) := by noncomm_ring
      _ = 0 := hs
  have hq : (Q*Q)*(P*P)=1 := by
    calc
      _ = Q*(Q*P)*P := by noncomm_ring
      _ = 1 := by rw [hQP,mul_one,hQP]
  have hfour : P^4+1=0 := by
    calc
      P^4+1 = (P*P+Q*Q)*(P*P) := by
        rw [add_mul,hq]
        congr 1
        noncomm_ring
      _ = 0 := by rw [h,zero_mul]
  change P^4=1
  calc
    P^4 = (P^4+1)+1 := by rw [add_assoc,hc 1,add_zero]
    _ = 1 := by rw [hfour,zero_add]
end RingIdentity

section Matrices
variable {R : Type*} [CommRing R]

def T (i j : Fin 3) (h : i≠j) (r : R) : (Mat R)ˣ :=
  let t : Matrix.TransvectionStruct (Fin 3) R := ⟨i,j,h,r⟩
  ⟨t.toMatrix,t.inv.toMatrix,t.mul_inv,t.inv_mul⟩

@[simp] theorem val_T (i j : Fin 3) (h : i≠j) (r : R) :
    (T i j h r).val = Matrix.transvection i j r := rfl
@[simp] theorem inv_val_T (i j : Fin 3) (h : i≠j) (r : R) :
    ((T i j h r)⁻¹).val = Matrix.transvection i j (-r) := rfl

abbrev T12 (r : R) := T 0 1 (by decide) r
abbrev T13 (r : R) := T 0 2 (by decide) r
abbrev T21 (r : R) := T 1 0 (by decide) r
abbrev T23 (r : R) := T 1 2 (by decide) r
abbrev T31 (r : R) := T 2 0 (by decide) r
abbrev T32 (r : R) := T 2 1 (by decide) r

theorem T_zero (i j : Fin 3) (h : i≠j) : T i j h (0:R)=1 := by
  apply Units.ext
  simp

theorem T_mul (i j : Fin 3) (h : i≠j) (r s : R) :
    T i j h r * T i j h s = T i j h (r+s) := by
  apply Units.ext
  exact Matrix.transvection_mul_transvection_same i j h r s

theorem T12_square (hc : ∀ x : R, x+x=0) :
    T12 (1:R)*T12 1=1 := by
  rw [T_mul,hc 1,T_zero]

theorem neg_eq_self (hc : ∀ x : R, x+x=0) (x : R) : -x=x := by
  calc
    -x = -x+(x+x) := by rw [hc x,add_zero]
    _ = x := by abel

theorem T_inv_self (hc : ∀ x : R, x+x=0) (i j : Fin 3) (h : i≠j) (r : R) :
    (T i j h r)⁻¹ = T i j h r := by
  apply inv_eq_of_mul_eq_one_right
  rw [T_mul,hc,T_zero]

set_option maxHeartbeats 2000000 in
/-- All five required elementary commutators, with signs absorbed by
characteristic two. No normal forms or upper filtration bounds. -/
theorem comm_23_12 (hc : ∀ x : R, x+x=0) (x : R) :
    T23 x*T12 1*(T23 x)⁻¹*(T12 1)⁻¹=T13 x := by
  simp only [T_inv_self hc]
  apply Units.ext
  simp only [Units.val_mul,val_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.single_apply,neg_eq_self hc,hc]

set_option maxHeartbeats 2000000 in
theorem comm_31_12 (hc : ∀ x : R, x+x=0) (x : R) :
    T31 x*T12 1*(T31 x)⁻¹*(T12 1)⁻¹=T32 x := by
  simp only [T_inv_self hc]
  apply Units.ext
  simp only [Units.val_mul,val_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.single_apply,neg_eq_self hc,hc]

set_option maxHeartbeats 2000000 in
theorem comm_21_13 (hc : ∀ x : R, x+x=0) (x y : R) :
    T21 x*T13 y*(T21 x)⁻¹*(T13 y)⁻¹=T23 (x*y) := by
  simp only [T_inv_self hc]
  apply Units.ext
  simp only [Units.val_mul,val_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.single_apply,neg_eq_self hc,hc]

set_option maxHeartbeats 2000000 in
theorem comm_21_32 (hc : ∀ x : R, x+x=0) (x y : R) :
    T21 x*T32 y*(T21 x)⁻¹*(T32 y)⁻¹=T31 (x*y) := by
  simp only [T_inv_self hc]
  apply Units.ext
  simp only [Units.val_mul,val_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.single_apply,neg_eq_self hc,hc,mul_comm]

set_option maxHeartbeats 2000000 in
theorem comm_31_23 (hc : ∀ x : R, x+x=0) (x y : R) :
    T31 x*T23 y*(T31 x)⁻¹*(T23 y)⁻¹=T21 (x*y) := by
  simp only [T_inv_self hc]
  apply Units.ext
  simp only [Units.val_mul,val_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,Matrix.single_apply,neg_eq_self hc,hc,mul_comm]

/-- Nonzero 23-transvections do not centralize T12(1), directly from
the first commutator identity. -/
theorem noncentral_23 (hc : ∀ x : R, x+x=0) {x : R} (hx : x≠0) :
    T23 x*T12 1*(T23 x)⁻¹ ≠ T12 1 := by
  intro h
  have he := comm_23_12 hc x
  rw [h,mul_inv_cancel] at he
  have hentry := congrArg (fun u : (Mat R)ˣ => u.val 0 2) he
  exact hx (by simpa [Matrix.transvection,Matrix.one_apply,Matrix.single_apply] using hentry.symm)

/-- Write a conjugate of I+E12 as I+H E12 K. The cross products
have square zero if the 21 entries of H and K square to zero.
Matrix.single_mul_mul_single makes the calculation shorter than
introducing a rank-one parametrization. -/
theorem cross_sq_zero (H K : Mat R)
    (hH : H 1 0 * H 1 0=0) (hK : K 1 0 * K 1 0=0) :
    let N : Mat R := Matrix.single 0 1 1
    let M := H*N*K
    (N*M)*(N*M)=0 ∧ (M*N)*(M*N)=0 := by
  let E (x : R) : Mat R := Matrix.single 0 1 x
  let N := E 1
  have hsingle (a b : R) (L : Mat R) :
      E a*L*E b=E (a*L 1 0*b) :=
    Matrix.single_mul_mul_single 0 1 0 1 a L b
  constructor
  · change (N*(H*N*K))*(N*(H*N*K))=0
    calc
      _ = (((N*H*N)*K*N)*H*N)*K := by noncomm_ring
      _ = 0 := by
        dsimp [N]
        rw [hsingle,hsingle,hsingle]
        simp only [one_mul,mul_one]
        have hz : H 1 0 * K 1 0 * H 1 0=0 := by
          calc
            _ = (H 1 0 * H 1 0) * K 1 0 := by ring
            _ = 0 := by rw [hH,zero_mul]
        rw [hz]
        simp [E]
  · change ((H*N*K)*N)*((H*N*K)*N)=0
    calc
      _ = H*((((N*K*N)*H*N)*K)*N) := by noncomm_ring
      _ = 0 := by
        dsimp [N]
        rw [hsingle,hsingle,hsingle]
        simp only [one_mul,mul_one]
        have hz : K 1 0 * H 1 0 * K 1 0=0 := by
          calc
            _ = (K 1 0 * K 1 0) * H 1 0 := by ring
            _ = 0 := by rw [hK,zero_mul]
        rw [hz]
        simp [E]

end Matrices
end MatrixModel
end QuandleResearch.Q525
