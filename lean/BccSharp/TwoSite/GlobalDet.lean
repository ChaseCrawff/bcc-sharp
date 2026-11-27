import BccSharp.TwoSite.GlobalAttain

set_option autoImplicit false

/-! Determinant and integer-lattice lemmas for the registration. Three
lattice vectors within root-sum-square distance `1/5` of a rotated primitive
BCC basis have determinant strictly between zero and one. In a unimodular
lattice this is impossible, and in a lattice of covolume one half it forces
a basis. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.KZ

/-- The primitive BCC basis `(p₁,p₂,p₃)` of the registration theorem, with `p₁ = ½(-1,1,1)`,
`p₂ = ½(1,-1,1)` and `p₃ = ½(1,1,-1)`. -/
def bccPrimitive : Mat := Constants.Reference.naturalBasis .bcc

theorem bccPrimitive_det : bccPrimitive.det = 1/2 := by
  rw [bccPrimitive, Matrix.det_fin_three]
  norm_num [Constants.Reference.naturalBasis]

theorem bccPrimitive_lattice : lattice bccPrimitive = bcc.points := Constants.bcc_primitive_points

theorem bccPrimitive_label (j : Fin 14) :
    bccPrimitive.mulVec (castVec (primitiveLabel j)) = star j := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [bccPrimitive,Constants.Reference.naturalBasis,primitiveLabel,starTwice,star,
      Matrix.mulVec,dotProduct,castVec,Fin.sum_univ_three]

theorem primitiveLabel_range :
    ∀ j : Fin 14, ∀ i : Fin 3, -1 ≤ primitiveLabel j i ∧ primitiveLabel j i ≤ 1 := by
  decide

theorem bccPrimitive_columns : bccPrimitive = columns (star 6) (star 5) (star 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [bccPrimitive,Constants.Reference.naturalBasis,columns,star]

theorem frobSq_eq_columns (M : Mat) : frobSq M = ∑ j, sq (fun i => M i j) := by
  unfold frobSq sq
  rw [Finset.sum_comm]

theorem frobSq_columns (u v w : Vec) : frobSq (columns u v w) = sq u + sq v + sq w := by
  rw [frobSq_eq_columns, Fin.sum_univ_three]
  rfl

theorem frobSq_orth (U M : Mat) (hU : U.transpose * U = 1) : frobSq (U * M) = frobSq M := by
  rw [frobSq_eq_columns, frobSq_eq_columns]
  congr 1
  funext j
  have e : (fun i => (U * M) i j) = U.mulVec (fun i => M i j) := by
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e, sq_orthogonal hU]

theorem mul_columns (O : Mat) (u v w : Vec) :
    O * columns u v w = columns (O.mulVec u) (O.mulVec v) (O.mulVec w) := by
  ext i j
  fin_cases j <;> simp [Matrix.mul_apply, columns, Matrix.mulVec, dotProduct]

theorem columns_sub (u v w u' v' w' : Vec) :
    columns u v w - columns u' v' w' = columns (u - u') (v - v') (w - w') := by
  ext i j
  fin_cases j <;> simp [columns]

/-! ### The determinant estimate -/

private def nearDet (a b c d e f g h k : ℝ) : ℝ :=
  1/2 + (b+c+d+f+g+h)/2 +
  (-a*e/2 - a*f/2 - a*h/2 - a*k/2 + b*d/2 + b*f/2 + b*g/2 - b*k/2 + c*d/2 - c*e/2 + c*g/2 +
    c*h/2 + d*h/2 - d*k/2 - e*g/2 - e*k/2 + f*g/2 + f*h/2) +
  (a*e*k - a*f*h - b*d*k + b*f*g + c*d*h - c*e*g)

private theorem coord_small {x S : ℝ} (hxS : x^2 ≤ S) (hS : S < 1/25) : |x| < 1/5 := by
  have h : x^2 < (1/5)^2 := by
    have e : ((1:ℝ)/5)^2 = 1/25 := by norm_num
    rw [e]
    exact lt_of_le_of_lt hxS hS
  exact abs_lt_of_sq_lt_sq h (by norm_num)

private theorem triple_small {x y z : ℝ} (hx : |x| < 1/5) (hy : |y| < 1/5) (hz : |z| < 1/5) :
    -(1/125) < x*y*z ∧ x*y*z < 1/125 := by
  have h : |x*y*z| < 1/125 := by
    rw [abs_mul, abs_mul]
    have hx0 := abs_nonneg x
    have hy0 := abs_nonneg y
    have hz0 := abs_nonneg z
    have h1 : |x| * |y| < 1/25 := by nlinarith
    nlinarith [mul_nonneg hx0 hy0]
  exact ⟨by linarith [neg_abs_le (x*y*z)], by linarith [le_abs_self (x*y*z)]⟩

private theorem nearDet_bounds (a b c d e f g h k : ℝ)
    (hS : a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2+k^2 < 1/25) :
    0 < nearDet a b c d e f g h k ∧ nearDet a b c d e f g h k < 1 := by
  have pa := sq_nonneg a
  have pb := sq_nonneg b
  have pc := sq_nonneg c
  have pd := sq_nonneg d
  have pe := sq_nonneg e
  have pf := sq_nonneg f
  have pg := sq_nonneg g
  have ph := sq_nonneg h
  have pk := sq_nonneg k
  -- linear part
  have h6 : 0 ≤ (b-c)^2+(b-d)^2+(b-f)^2+(b-g)^2+(b-h)^2+(c-d)^2+(c-f)^2+(c-g)^2+(c-h)^2+
      (d-f)^2+(d-g)^2+(d-h)^2+(f-g)^2+(f-h)^2+(g-h)^2 := by positivity
  have e6 : ((b+c+d+f+g+h)/2)^2 = (6*(b^2+c^2+d^2+f^2+g^2+h^2) -
      ((b-c)^2+(b-d)^2+(b-f)^2+(b-g)^2+(b-h)^2+(c-d)^2+(c-f)^2+(c-g)^2+(c-h)^2+
      (d-f)^2+(d-g)^2+(d-h)^2+(f-g)^2+(f-h)^2+(g-h)^2))/4 := by ring
  have hL : ((b+c+d+f+g+h)/2)^2 < (49/200)^2 := by
    rw [e6]
    norm_num
    linarith
  have hLabs := abs_lt.mp (abs_lt_of_sq_lt_sq hL (by norm_num))
  -- quadratic part
  have hm : 0 ≤ (a + e)^2 + (a + f)^2 + (a + h)^2 + (a + k)^2 + (b - d)^2 + (b - f)^2 +
      (b - g)^2 + (b + k)^2 + (c - d)^2 + (c + e)^2 + (c - g)^2 + (c - h)^2 + (d - h)^2 +
      (d + k)^2 + (e + g)^2 + (e + k)^2 + (f - g)^2 + (f - h)^2 := by positivity
  have hp : 0 ≤ (a - e)^2 + (a - f)^2 + (a - h)^2 + (a - k)^2 + (b + d)^2 + (b + f)^2 +
      (b + g)^2 + (b - k)^2 + (c + d)^2 + (c - e)^2 + (c + g)^2 + (c + h)^2 + (d + h)^2 +
      (d - k)^2 + (e - g)^2 + (e - k)^2 + (f + g)^2 + (f + h)^2 := by positivity
  have eQm : (a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2+k^2) -
      (-a*e/2 - a*f/2 - a*h/2 - a*k/2 + b*d/2 + b*f/2 + b*g/2 - b*k/2 + c*d/2 - c*e/2 +
        c*g/2 + c*h/2 + d*h/2 - d*k/2 - e*g/2 - e*k/2 + f*g/2 + f*h/2) =
      ((a + e)^2 + (a + f)^2 + (a + h)^2 + (a + k)^2 + (b - d)^2 + (b - f)^2 +
      (b - g)^2 + (b + k)^2 + (c - d)^2 + (c + e)^2 + (c - g)^2 + (c - h)^2 + (d - h)^2 +
      (d + k)^2 + (e + g)^2 + (e + k)^2 + (f - g)^2 + (f - h)^2)/4 := by ring
  have eQp : (a^2+b^2+c^2+d^2+e^2+f^2+g^2+h^2+k^2) +
      (-a*e/2 - a*f/2 - a*h/2 - a*k/2 + b*d/2 + b*f/2 + b*g/2 - b*k/2 + c*d/2 - c*e/2 +
        c*g/2 + c*h/2 + d*h/2 - d*k/2 - e*g/2 - e*k/2 + f*g/2 + f*h/2) =
      ((a - e)^2 + (a - f)^2 + (a - h)^2 + (a - k)^2 + (b + d)^2 + (b + f)^2 +
      (b + g)^2 + (b - k)^2 + (c + d)^2 + (c - e)^2 + (c + g)^2 + (c + h)^2 + (d + h)^2 +
      (d - k)^2 + (e - g)^2 + (e - k)^2 + (f + g)^2 + (f + h)^2)/4 := by ring
  -- cubic part
  have sa : |a| < 1/5 := coord_small (by linarith) hS
  have sb : |b| < 1/5 := coord_small (by linarith) hS
  have sc : |c| < 1/5 := coord_small (by linarith) hS
  have sd : |d| < 1/5 := coord_small (by linarith) hS
  have se : |e| < 1/5 := coord_small (by linarith) hS
  have sf : |f| < 1/5 := coord_small (by linarith) hS
  have sg : |g| < 1/5 := coord_small (by linarith) hS
  have sh : |h| < 1/5 := coord_small (by linarith) hS
  have sk : |k| < 1/5 := coord_small (by linarith) hS
  have t1 := triple_small sa se sk
  have t2 := triple_small sa sf sh
  have t3 := triple_small sb sd sk
  have t4 := triple_small sb sf sg
  have t5 := triple_small sc sd sh
  have t6 := triple_small sc se sg
  unfold nearDet
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
    t6.1, t6.2]

theorem det_near_bcc (V : Mat) (hV : frobSq V < 1/25) :
    0 < (bccPrimitive + V).det ∧ (bccPrimitive + V).det < 1 := by
  have hS : (V 0 0)^2 + (V 0 1)^2 + (V 0 2)^2 + (V 1 0)^2 + (V 1 1)^2 + (V 1 2)^2 +
      (V 2 0)^2 + (V 2 1)^2 + (V 2 2)^2 < 1/25 := by
    have e : frobSq V = (V 0 0)^2 + (V 0 1)^2 + (V 0 2)^2 + (V 1 0)^2 + (V 1 1)^2 +
        (V 1 2)^2 + (V 2 0)^2 + (V 2 1)^2 + (V 2 2)^2 := by
      simp only [frobSq, Fin.sum_univ_three]
      ring
    linarith
  have hdet : (bccPrimitive + V).det =
      nearDet (V 0 0) (V 0 1) (V 0 2) (V 1 0) (V 1 1) (V 1 2) (V 2 0) (V 2 1) (V 2 2) := by
    rw [Matrix.det_fin_three]
    simp only [bccPrimitive, Constants.Reference.naturalBasis, Matrix.add_apply, nearDet,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    ring
  rw [hdet]
  exact nearDet_bounds _ _ _ _ _ _ _ _ _ hS

/-- Three vectors near the rotated primitive BCC basis have determinant
strictly between zero and one. -/
theorem det_columns_near (O : Mat) (hO : proper O) (u v w : Vec)
    (h : sq (u - O.mulVec (star 6)) + sq (v - O.mulVec (star 5)) +
      sq (w - O.mulVec (star 3)) < 1/25) :
    0 < (columns u v w).det ∧ (columns u v w).det < 1 := by
  have hOO : O * O.transpose = 1 := mul_eq_one_comm.mp hO.1
  set M := columns u v w with hMdef
  set V := O.transpose * M - bccPrimitive with hVdef
  have hM : M = O * (bccPrimitive + V) := by
    rw [hVdef, add_sub_cancel, ← mul_assoc, hOO, one_mul]
  have hdet : M.det = (bccPrimitive + V).det := by
    rw [hM, Matrix.det_mul, hO.2, one_mul]
  have hV : V = O.transpose * (M - O * bccPrimitive) := by
    rw [hVdef, Matrix.mul_sub, ← mul_assoc, hO.1, one_mul]
  have hOt : O.transpose.transpose * O.transpose = 1 := by
    rw [Matrix.transpose_transpose]
    exact hOO
  have hE : M - O * bccPrimitive = columns (u - O.mulVec (star 6)) (v - O.mulVec (star 5))
      (w - O.mulVec (star 3)) := by
    rw [bccPrimitive_columns, mul_columns, hMdef, columns_sub]
  rw [hdet]
  apply det_near_bcc
  rw [hV, frobSq_orth _ _ hOt, hE, frobSq_columns]
  exact h

/-! ### Integer bases -/

theorem det_toRealMatrix (Z : Matrix (Fin 3) (Fin 3) ℤ) : (toRealMatrix Z).det = (Z.det : ℝ) := by
  unfold toRealMatrix
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp

theorem exists_integer_of_columns (P : Mat) (u v w : Vec) (hu : u ∈ lattice P)
    (hv : v ∈ lattice P) (hw : w ∈ lattice P) :
    ∃ Z : Matrix (Fin 3) (Fin 3) ℤ, columns u v w = P * toRealMatrix Z := by
  have cols (j : Fin 3) : ∃ n : IntVec, P.mulVec (castVec n) = fun i => columns u v w i j := by
    fin_cases j
    · obtain ⟨n, hn⟩ := hu
      exact ⟨n, hn.trans (by funext i; rfl)⟩
    · obtain ⟨n, hn⟩ := hv
      exact ⟨n, hn.trans (by funext i; rfl)⟩
    · obtain ⟨n, hn⟩ := hw
      exact ⟨n, hn.trans (by funext i; rfl)⟩
  choose ns hns using cols
  refine ⟨fun i j => ns j i, ?_⟩
  ext i j
  rw [← congrFun (hns j) i]
  rfl

theorem columns_integral_false (R : Mat) (hR : R.det = 1) (u v w : Vec)
    (hu : u ∈ lattice R) (hv : v ∈ lattice R) (hw : w ∈ lattice R)
    (hpos : 0 < (columns u v w).det) (hlt : (columns u v w).det < 1) : False := by
  obtain ⟨Z, hZ⟩ := exists_integer_of_columns R u v w hu hv hw
  rw [hZ, Matrix.det_mul, hR, one_mul, det_toRealMatrix] at hpos hlt
  have h1 : (0 : ℤ) < Z.det := by exact_mod_cast hpos
  have h2 : Z.det < 1 := by exact_mod_cast hlt
  omega

theorem columns_half_basis (P : Mat) (hP : P.det = 1/2) (u v w : Vec)
    (hu : u ∈ lattice P) (hv : v ∈ lattice P) (hw : w ∈ lattice P)
    (hpos : 0 < (columns u v w).det) (hlt : (columns u v w).det < 1) :
    (columns u v w).det = 1/2 ∧ lattice (columns u v w) = lattice P := by
  obtain ⟨Z, hZ⟩ := exists_integer_of_columns P u v w hu hv hw
  have hd : (columns u v w).det = 1/2 * (Z.det : ℝ) := by
    rw [hZ, Matrix.det_mul, hP, det_toRealMatrix]
  have h1 : Z.det = 1 := by
    rw [hd] at hpos hlt
    have a : (0 : ℝ) < (Z.det : ℝ) := by linarith
    have b : (Z.det : ℝ) < 2 := by linarith
    have a' : (0 : ℤ) < Z.det := by exact_mod_cast a
    have b' : Z.det < 2 := by exact_mod_cast b
    omega
  refine ⟨by rw [hd, h1]; norm_num, ?_⟩
  have hadj : Z * Z.adjugate = 1 := by rw [Matrix.mul_adjugate, h1, one_smul]
  rw [hZ]
  exact rebase_sameLattice P Z Z.adjugate hadj

end BccSharp.Coulomb.GlobalInputs
