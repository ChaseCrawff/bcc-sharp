import BccSharp.Lattice.KzTransport

set_option autoImplicit false

/-! Reference values of the Series energy and of the actual capped defect on
the exact BCC and FCC point sets. Every valid two-site representation of a
rotated and translated reference point set has the reference energy and the
reference defect. This discharges the `bccValues`, `fccValues` and
`fccSaturated` fields of `GlobalAnalyticInputs`. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.GlobalInputs
open BccSharp.Coulomb.BravaisCover
open BccSharp.Coulomb.BravaisCover.KZ

/-! ### Integer change of basis between two bases of one lattice -/

private theorem castMatrix_injective' : Function.Injective toRealMatrix := by
  intro A B h
  ext i j
  have e := congrFun (congrFun h i) j
  change (A i j : ℝ)=(B i j : ℝ) at e
  exact_mod_cast e

private theorem castMatrix_one' : toRealMatrix (1 : Matrix (Fin 3) (Fin 3) ℤ)=1 := by
  ext i j
  by_cases h : i=j <;> simp [toRealMatrix,Matrix.one_apply,h]

private theorem castMatrix_mul' (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    toRealMatrix (A*B)=toRealMatrix A*toRealMatrix B := Matrix.map_mul

private theorem cancel_left' {B A C : Mat} (hB : B.det≠0) (h : B*A=B*C) : A=C := by
  have e := congrArg (fun R : Mat => B⁻¹*R) h
  simpa only [← mul_assoc,Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),one_mul] using e

/-- A basis whose lattice lies inside another lattice is an integer
combination of the other basis. -/
theorem exists_integer_rebase (P P' : Mat) (h : lattice P' ⊆ lattice P) :
    ∃ H : Matrix (Fin 3) (Fin 3) ℤ, P' = P*toRealMatrix H := by
  have cols (j : Fin 3) : ∃ n : IntVec, P.mulVec (castVec n) = fun i => P' i j :=
    h (column_lattice P' j)
  choose ns hns using cols
  refine ⟨fun i j => ns j i, ?_⟩
  ext i j
  rw [← congrFun (hns j) i]
  rfl

/-- Two nonsingular bases of the same lattice differ by a unimodular
integer matrix. -/
theorem sameLattice_unimodular (P P' : Mat) (hP : P.det≠0) (hP' : P'.det≠0)
    (h : lattice P = lattice P') :
    ∃ H G : Matrix (Fin 3) (Fin 3) ℤ, P' = P*toRealMatrix H ∧ H*G=1 ∧ G*H=1 := by
  obtain ⟨H,hH⟩ := exists_integer_rebase P P' h.symm.le
  obtain ⟨G,hG⟩ := exists_integer_rebase P' P h.le
  refine ⟨H,G,hH,?_,?_⟩
  · apply castMatrix_injective'
    rw [castMatrix_mul',castMatrix_one']
    apply cancel_left' hP
    rw [← mul_assoc,← hH,← hG,mul_one]
  · apply castMatrix_injective'
    rw [castMatrix_mul',castMatrix_one']
    apply cancel_left' hP'
    rw [← mul_assoc,← hG,← hH,mul_one]

/-- The one-site energy depends only on the lattice. -/
theorem oneSiteEnergy_sameLattice (P P' : Mat) (hP : P.det≠0) (hP' : P'.det≠0)
    (h : lattice P = lattice P') : oneSiteEnergy P' = oneSiteEnergy P := by
  obtain ⟨H,G,hH,hg,gh⟩ := sameLattice_unimodular P P' hP hP' h
  rw [hH]
  exact oneSiteEnergy_rebase P H G hg gh

/-! ### Point sets of half-period configurations -/

theorem zero_mem_points (q : TwoSite) : (0 : Vec)∈q.points :=
  Or.inl ⟨0,by show q.basis.mulVec (castVec 0)=0; rw [castVec_zero,Matrix.mulVec_zero]⟩

theorem offset_mem_points (q : TwoSite) : q.basis.mulVec q.offset∈q.points :=
  Or.inr ⟨0,(periodGroup q.basis).zero_mem,by rw [zero_add]⟩

/-- A two-site configuration whose offset is half an integer vector has a
point set that is an additive group. -/
def pointsGroup (q : TwoSite) (h : ∃ n : IntVec, (2 : ℝ) • q.offset=castVec n) :
    AddSubgroup Vec :=
  halfExtension (periodGroup q.basis) (q.basis.mulVec q.offset) (by
    obtain ⟨n,hn⟩ := h
    refine ⟨n,?_⟩
    show q.basis.mulVec (castVec n)=q.basis.mulVec q.offset+q.basis.mulVec q.offset
    rw [← hn,two_smul,Matrix.mulVec_add])

theorem pointsGroup_coe (q : TwoSite) (h : ∃ n : IntVec, (2 : ℝ) • q.offset=castVec n) :
    (pointsGroup q h : Set Vec)=q.points := rfl

/-- A translate of a linear image of a group that contains the origin is
the linear image itself. -/
theorem translate_image_group (H : AddSubgroup Vec) (U : Mat) (v : Vec)
    (h0 : (0 : Vec)∈translate v (U.mulVec '' (H : Set Vec))) :
    translate v (U.mulVec '' (H : Set Vec))=U.mulVec '' (H : Set Vec) := by
  obtain ⟨_,⟨x,hx,rfl⟩,hv⟩ := h0
  have hv' : v= -U.mulVec x := eq_neg_of_add_eq_zero_right hv.symm
  ext z
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨a-x,H.sub_mem ha hx,?_⟩
    rw [Matrix.mulVec_sub,hv']
    abel
  · rintro ⟨b,hb,rfl⟩
    refine ⟨U.mulVec (b+x),⟨b+x,H.add_mem hb hx,rfl⟩,?_⟩
    rw [Matrix.mulVec_add,hv']
    abel

theorem ideal_half (ref : Reference) :
    ∃ n : IntVec, (2 : ℝ) • (Constants.refTwo (referenceKind ref)).offset=castVec n := by
  cases ref
  · refine ⟨fun _ => 1,?_⟩
    funext i
    simp [Constants.refTwo,referenceKind,bcc,castVec]
  · refine ⟨fun i => if i=0 then 1 else 0,?_⟩
    funext i
    by_cases h : i=0 <;> simp [Constants.refTwo,referenceKind,fcc,castVec,h]

theorem idealPoints_eq (ref : Reference) :
    idealPoints ref=(Constants.refTwo (referenceKind ref)).points := by
  cases ref <;> rfl

/-- A rigid copy of a reference point set that contains the origin is a
rotated reference lattice in the Lattice strain chart. -/
theorem rigid_ideal_lattice (q : TwoSite) (ref : Reference) (h : rigidCopy q.points (idealPoints ref)) :
    ∃ U : Mat, proper U ∧ q.points=lattice (strainBasis ref U) := by
  obtain ⟨v,U,hU,hpts⟩ := h
  refine ⟨U,hU,?_⟩
  rw [strain_origin_points,hpts,idealPoints_eq]
  have hz := zero_mem_points q
  rw [hpts,idealPoints_eq,← pointsGroup_coe _ (ideal_half ref)] at hz
  rw [← pointsGroup_coe _ (ideal_half ref)]
  exact translate_image_group _ U v hz

/-- If the point set of a valid configuration is a lattice, the offset is
a nonzero half period. -/
theorem halfClass_of_lattice (q : TwoSite) (hq : q.Valid) (P : Mat) (h : q.points=lattice P) :
    HalfClass q.offset := by
  have hu : IsUnit q.basis := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hq.1]; exact isUnit_one)
  have inj := Matrix.mulVec_injective_of_isUnit hu
  let t := q.basis.mulVec q.offset
  have ht : t∈lattice P := h ▸ offset_mem_points q
  have htt : t+t∈q.points := h ▸ (periodGroup P).add_mem ht ht
  refine ⟨?_,hq.2⟩
  rcases htt with ⟨n,hn⟩ | ⟨y,⟨m,rfl⟩,hy⟩
  · refine ⟨n,inj ?_⟩
    change q.basis.mulVec ((2 : ℝ) • q.offset)=q.basis.mulVec (castVec n)
    rw [two_smul,Matrix.mulVec_add]
    exact hn.symm
  · exfalso
    apply hq.2 m
    apply inj
    change t=q.basis.mulVec (castVec m)
    have e : t+t=q.basis.mulVec (castVec m)+t := hy
    exact add_right_cancel e

theorem strainBasis_nonsingular (ref : Reference) (U : Mat) (hU : proper U) :
    (strainBasis ref U).det≠0 := by
  have ht : 0< Constants.fccLength := by unfold Constants.fccLength; positivity
  have hc : (cubicBasis ref).det≠0 := by
    intro e
    have h := cubicBasis_unitVolume ref
    simp [volumeOf,e] at h
  unfold strainBasis
  rw [Matrix.det_smul,Fintype.card_fin,Matrix.det_mul,hU.2,one_mul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht.ne')) hc

/-- Reference energy of every valid representation of a rigid reference copy. -/
theorem ideal_energy (q : TwoSite) (hq : q.Valid) (ref : Reference)
    (h : rigidCopy q.points (idealPoints ref)) : energy q=idealEnergy ref := by
  obtain ⟨U,hU,hpts⟩ := rigid_ideal_lattice q ref h
  obtain ⟨model⟩ := primitive_anchor_exists q hq (halfClass_of_lattice q hq _ hpts)
  have hm : model.basis.det≠0 := by rw [model.volume]; norm_num
  have same : lattice (strainBasis ref U)=lattice model.basis := by rw [model.points,hpts]
  rw [← model.sameEnergy,← strain_origin_energy ref U hU]
  exact oneSiteEnergy_sameLattice _ _ (strainBasis_nonsingular ref U hU) hm same

/-- The actual defect of every rigid reference copy is the Lattice origin value. -/
theorem ideal_defect (q : TwoSite) (ref : Reference)
    (h : rigidCopy q.points (idealPoints ref)) :
    ∃ U : Mat, proper U ∧ defect q=oneSiteDefect (strainBasis ref U) := by
  obtain ⟨U,hU,hpts⟩ := rigid_ideal_lattice q ref h
  refine ⟨U,hU,?_⟩
  show cappedDefect (liftedNeighbors q.points 0)=cappedDefect (liftedNeighbors (lattice (strainBasis ref U)) 0)
  rw [hpts]

theorem bccValues_proof (q : TwoSite) (hq : q.Valid) (h : IsBCC q) :
    energy q=energy bcc ∧ defect q=0 := by
  refine ⟨ideal_energy q hq .bcc h,?_⟩
  obtain ⟨U,hU,hD⟩ := ideal_defect q .bcc h
  rw [hD]
  exact bcc_origin_defect_zero U hU

theorem fccValues_proof (q : TwoSite) (hq : q.Valid) (h : IsFCC q) :
    energy q=energy fcc ∧ defect q=1 := by
  refine ⟨ideal_energy q hq .fcc h,?_⟩
  obtain ⟨U,hU,hD⟩ := ideal_defect q .fcc h
  rw [hD]
  exact fcc_origin_defect_one U hU

theorem proper_one : proper (1 : Mat) := ⟨by simp,by simp⟩

/-- `D(FCC)=1` for the two-site FCC reference. -/
theorem fccSaturated_proof : defect fcc=1 := by
  have h := fcc_origin_defect_one 1 proper_one
  unfold oneSiteDefect at h
  rw [strain_reference_points] at h
  exact h

end BccSharp.Coulomb.GlobalInputs
