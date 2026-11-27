import BccSharp.Lattice.KzChart
import BccSharp.Lattice.Routing
import BccSharp.TwoSite.Assembly

set_option autoImplicit false

/-! Physical transport from the arbitrary determinant-1/2 Bravais
model to the exact Lattice chart. Proper rotations transport the actual
matching and unmatched annular sum. -/

noncomputable section
open scoped BigOperators

namespace BccSharp.Coulomb.BravaisCover.KZ
open BccSharp.Coverage

private theorem proper_mul (U V : Mat) (hU : proper U) (hV : proper V) : proper (U*V) := by
  constructor
  · rw [Matrix.transpose_mul,mul_assoc,← mul_assoc U.transpose U V,hU.1,one_mul,hV.1]
  · rw [Matrix.det_mul,hU.2,hV.2,one_mul]

private theorem proper_transpose (U : Mat) (hU : proper U) : proper U.transpose := by
  constructor
  · rw [Matrix.transpose_transpose]
    have inv := Matrix.inv_eq_left_inv hU.1
    rw [← inv,Matrix.mul_nonsing_inv U (isUnit_iff_ne_zero.mpr (by rw [hU.2]; exact one_ne_zero))]
  · rw [Matrix.det_transpose,hU.2]

private theorem proper_injective (U : Mat) (hU : proper U) : Function.Injective U.mulVec :=
  Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hU.2]; exact isUnit_one))

private def neighborRotate (U : Mat) (hU : proper U) (S : Set Vec) :
    ↥(liftedNeighbors S 0) ≃ ↥(liftedNeighbors (U.mulVec '' S) 0) := by
  let toFun (v : ↥(liftedNeighbors S 0)) : ↥(liftedNeighbors (U.mulVec '' S) 0) :=
    ⟨U.mulVec v.val,by
      have h := v.property
      refine ⟨?_,?_,?_⟩
      · rw [zero_add]
        exact ⟨v.val,by simpa only [zero_add] using h.1,rfl⟩
      · intro e
        exact h.2.1 (proper_injective U hU (e.trans (Matrix.mulVec_zero U).symm))
      · rw [sq_orthogonal hU.1]
        exact h.2.2⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro x y e
    exact Subtype.ext (proper_injective U hU (congrArg Subtype.val e))
  · intro y
    have hy := y.property
    have mem : y.val∈U.mulVec '' S := by simpa only [zero_add] using hy.1
    obtain ⟨x,hx,e⟩ := mem
    have hnorm : sq x=sq y.val := by rw [← e,sq_orthogonal hU.1]
    have hn : x≠0 := by
      intro f
      apply hy.2.1
      simpa [f] using e.symm
    have h : x∈liftedNeighbors S 0 := ⟨by simpa only [zero_add] using hx,hn,hnorm.trans_lt hy.2.2⟩
    exact ⟨⟨x,h⟩,Subtype.ext e⟩

private theorem neighborRotate_val (U : Mat) (hU : proper U) (S : Set Vec)
    (v : ↥(liftedNeighbors S 0)) : (neighborRotate U hU S v).val=U.mulVec v.val := rfl

private theorem candidates_rotate (U : Mat) (hU : proper U) (S : Set Vec) :
    defectCandidates (liftedNeighbors S 0) ⊆ defectCandidates (liftedNeighbors (U.mulVec '' S) 0) := by
  classical
  intro c hc
  rcases Set.mem_insert_iff.mp hc with rfl | ⟨V,hV,σ,rfl⟩
  · exact Set.mem_insert _ _
  let e := neighborRotate U hU S
  let σ' := σ.trans e.toEmbedding
  apply Set.mem_insert_of_mem
  refine ⟨U*V,proper_mul U V hU hV,σ',?_⟩
  have matched (i : Fin 14) :
      sq ((σ' i : Vec)-(U*V).mulVec (star i))=sq ((σ i : Vec)-V.mulVec (star i)) := by
    change sq (U.mulVec ((σ i : Vec))-(U*V).mulVec (star i))=_
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_sub,sq_orthogonal hU.1]
  have range (v : ↥(liftedNeighbors S 0)) :
      e v∈Set.range σ' ↔ v∈Set.range σ := by
    constructor
    · rintro ⟨i,eq⟩
      exact ⟨i,e.injective eq⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,rfl⟩
  have weight (v : ↥(liftedNeighbors S 0)) : annularWeight (e v).val=annularWeight v.val := by
    unfold annularWeight
    rw [neighborRotate_val,sq_orthogonal hU.1]
  let removed (v : ↥(liftedNeighbors (U.mulVec '' S) 0)) : ℝ :=
    if v∈Set.range σ' then 0 else annularWeight v.val
  have tail : (∑' v : ↥(liftedNeighbors (U.mulVec '' S) 0), removed v) =
      ∑' v : ↥(liftedNeighbors S 0), if v∈Set.range σ then 0 else annularWeight v.val := by
    rw [← e.tsum_eq removed]
    apply tsum_congr
    intro v
    show (if e v ∈ Set.range σ' then 0 else annularWeight (e v).val) =
      if v ∈ Set.range σ then 0 else annularWeight v.val
    rw [weight v]
    by_cases hv : v ∈ Set.range σ
    · rw [if_pos hv, if_pos ((range v).mpr hv)]
    · rw [if_neg hv, if_neg (fun h => hv ((range v).mp h))]
  unfold defectTrial
  simp only [matched]
  change _ + _ = _ + (∑' v, removed v)
  rw [tail]

private theorem image_unrotate (U : Mat) (hU : proper U) (S : Set Vec) :
    U.transpose.mulVec '' (U.mulVec '' S)=S := by
  have same (x : Vec) : U.transpose.mulVec (U.mulVec x)=x := by
    rw [Matrix.mulVec_mulVec,hU.1,Matrix.one_mulVec]
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    rwa [same]
  · intro h
    exact ⟨U.mulVec x,⟨x,h,rfl⟩,same x⟩

theorem cappedDefect_proper (U : Mat) (hU : proper U) (S : Set Vec) :
    cappedDefect (liftedNeighbors (U.mulVec '' S) 0)=cappedDefect (liftedNeighbors S 0) := by
  unfold cappedDefect
  congr 1
  apply Set.Subset.antisymm
  · have e := candidates_rotate U.transpose (proper_transpose U hU) (U.mulVec '' S)
    rwa [image_unrotate U hU S] at e
  · exact candidates_rotate U hU S

theorem oneSiteEnergy_proper (U B : Mat) (hU : proper U) :
    oneSiteEnergy (U*B)=oneSiteEnergy B := by
  simp only [oneSite_energy_is_self]
  rw [← mul_smul_comm,proper_regularSelf _ U _ hU]

theorem oneSiteDefect_proper (U B : Mat) (hU : proper U) :
    oneSiteDefect (U*B)=oneSiteDefect B := by
  unfold oneSiteDefect
  rw [lattice_left_mul,cappedDefect_proper U hU]

structure PhysicalRepresentative (B : Mat) where
  point : Point
  reducedPoint : reduced point
  r1Positive : 0<point 0
  r2Positive : 0<point 1
  xBound : point 2∈Set.Icc (0 : ℝ) (1/2)
  yBound : point 3∈Set.Icc (0 : ℝ) (1/2)
  zBound : point 4∈Set.Icc (-1/2 : ℝ) (1/2)
  physicalPoints : rigidCopy (lattice B) (lattice (primitiveChart point))
  physicalEnergy : oneSiteEnergy (primitiveChart point)=oneSiteEnergy B
  physicalDefect : oneSiteDefect (primitiveChart point)=oneSiteDefect B

theorem physical_chart (B : Mat) (hB : B.det=1/2) : Nonempty (PhysicalRepresentative B) := by
  let t := Constants.fccLength
  have hp : 0<t := by unfold t Constants.fccLength; positivity
  have cube : t^3=2 := referenceLength_cube
  let L := t • B
  have hL : L.det=1 := by unfold L; rw [Matrix.det_smul,Fintype.card_fin,cube,hB]; norm_num
  obtain ⟨rep⟩ := oriented_chart L hL
  let p := rep.point
  let U := rep.rotation
  let H := rep.basisChange
  let G := rep.inverseChange
  have basis : B*toRealMatrix H=U*primitiveChart p := by
    calc
      _ = t⁻¹ • (L*toRealMatrix H) := by
        unfold L
        rw [← smul_mul_assoc,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]
      _ = t⁻¹ • (U*normalizedChart p) := congrArg (fun M : Mat => t⁻¹ • M) rep.basisEquation
      _ = _ := by unfold t primitiveChart; rw [mul_smul_comm]
  have lat : lattice (B*toRealMatrix H)=lattice B := rebase_sameLattice B H G rep.leftInverse
  have rebaseE := oneSiteEnergy_rebase B H G rep.leftInverse rep.rightInverse
  have P : rigidCopy (lattice B) (lattice (primitiveChart p)) := by
    refine ⟨0,U,rep.properRotation,?_⟩
    rw [← lat,basis,lattice_left_mul]
    ext x
    simp [translate]
  have E : oneSiteEnergy (primitiveChart p)=oneSiteEnergy B := by
    rw [← oneSiteEnergy_proper U _ rep.properRotation,← basis]
    exact rebaseE
  have D : oneSiteDefect (primitiveChart p)=oneSiteDefect B := by
    rw [← oneSiteDefect_proper U _ rep.properRotation,← basis]
    unfold oneSiteDefect
    rw [lat]
  exact ⟨⟨p,rep.reducedPoint,rep.r1Positive,rep.r2Positive,rep.xBound,rep.yBound,rep.zBound,P,E,D⟩⟩

theorem PhysicalRepresentative.transport {B : Mat} (r : PhysicalRepresentative B)
    (sharp : Sharp (primitiveChart r.point)) : Sharp B := by
  have e : oneSiteDeficit (primitiveChart r.point)=oneSiteDeficit B := by
    unfold oneSiteDeficit
    rw [r.physicalEnergy,r.physicalDefect]
  refine ⟨e ▸ sharp.1,fun h => ?_⟩
  exact (sharp.2 (e.trans h)).elim (fun b => Or.inl (rigidCopy_trans r.physicalPoints b))
    (fun f => Or.inr (rigidCopy_trans r.physicalPoints f))

theorem physical_escape_or_root (B : Mat) (hB : B.det=1/2) :
    Sharp B ∨ ∃ r : PhysicalRepresentative B, proofRoot r.point := by
  obtain ⟨r⟩ := physical_chart B hB
  exact (chart_escape_or_root r.point r.reducedPoint r.r1Positive r.r2Positive
    r.xBound r.yBound r.zBound).elim (fun s => Or.inl (r.transport s)) (fun h => Or.inr ⟨r,h⟩)

/-- The arbitrary input is already reduced by the preceding theorems.
The remaining inputs are the actual addressed cover checks and the
nonzero local-ball analytic certificate. -/
theorem latticeCase_from_checked_atlases (g : Grid 16) (gOK : g.check globalRoot=true)
    (forest : (Fin 2 → Fin 16) → (Fin 3 → Fin 16) → AddressedTree Payload)
    (checked : ∀ owner suffix, (forest owner suffix).check globalWithHandoffsCheck
      (gridAddress .global (Fin.append owner suffix)) (g.box (Fin.append owner suffix))=true)
    (atlas : Reference → AtlasRows) (atlasOK : ∀ ref, (atlas ref).check ref=true)
    (ballProof : ∀ ref, NonzeroLocalStrain ref) : LatticeCase := by
  intro B hB
  rcases physical_escape_or_root B hB with strict | ⟨r,root⟩
  · exact strict
  · apply r.transport
    exact addressed_grid_sound g (by decide) globalRoot gOK .global globalWithHandoffsCheck
      (globalWithHandoffsCheck_sound atlas atlasOK ballProof) forest checked r.point
      (globalRoot_contains r.point root) r.reducedPoint

end BccSharp.Coulomb.BravaisCover.KZ
