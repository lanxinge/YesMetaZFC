import YesMetaZFC.Model.Forcing.Proper.Elementary.FirstPreimage

/-! # 关系原像在内部初等模型中的闭包

关系原像由源载体内的分离构造。传递环境中的条目绝对性和目标成员界，保证
其精确方程可以反射到同一个 N；函数图不需要在元层解释成选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Rel_pull_d (M : SetTheory.Structure.{u}) (C F D E : M.Domain) : Prop := M.MemberSubset E C ∧
  ∀ p, M.mem p C → (M.mem p E ↔ ∃ q, Entry_d M p q F ∧ M.mem q D)

def rel_pull_m {n} (C F D E : Term n) : Formula 1 n := .conj (Formula.subset E C)
  (Formula.forallMem C (.iff (.mem .newest E.weaken) (.existsE
    (.conj (entry_m (.bound 1) .newest F.weaken.weaken) (.mem .newest D.weaken.weaken)))))
derive_free_closed rel_pull_m

theorem rel_pull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C F D E : Term n) :
    Formula.satisfies ρ (rel_pull_m C F D E) ↔ Rel_pull_d M (C.eval ρ) (F.eval ρ) (D.eval ρ) (E.eval ρ) := by
  simp only [rel_pull_m, Rel_pull_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

theorem rel_pull_exists_l (hZF : M.Models ZF) (C F D : M.Domain) : ∃ E, Rel_pull_d M C F D E := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push D
  let φ : UnarySchema 2 := {
    body := .existsE (.conj (entry_m (.bound 1) .newest (.bound 3)) (.mem .newest (.bound 2))) }
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF φ ρ C
  refine ⟨E, fun p hp => ((hE p).mp hp).1, fun p hp => ?_⟩
  rw [hE p, and_iff_right hp]
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, entry_sat_l M hZF.1, Formula.satisfies_mem_iff]
  rfl

theorem smem_rel_pull_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H T}
    (hM : Smdl_d I c H T) (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hH : M.TransitiveSet H) (C F D E : (smdl_structure_l I (R := T) hM.2.1).Domain) :
    Rel_pull_d (smdl_structure_l I (R := T) hM.2.1) C F D E ↔ Rel_pull_d M C.val F.val D.val E.val := by
  let L := smdl_structure_l I (R := T) hM.2.1
  have hp (p : L.Domain) : (∃ q, Entry_d L p q F ∧ L.mem q D) ↔
      ∃ q, Entry_d M p.val q F.val ∧ M.mem q D.val := by
    constructor
    · rintro ⟨q, hpq, hq⟩
      exact ⟨q.val, (smem_entry_l I hM hT hH p q F).mp hpq, (smem_member_l I hM hT q D).mp hq⟩
    · rintro ⟨q, hpq, hq⟩
      let q' : L.Domain := ⟨q, hH D.val D.property q hq⟩
      exact ⟨q', (smem_entry_l I hM hT hH p q' F).mpr hpq, (smem_member_l I hM hT q' D).mpr hq⟩
  constructor
  · rintro ⟨hE, he⟩
    refine ⟨(smem_subset_l I hM hT hH E C).mp hE, fun p hpc => ?_⟩
    let p' : L.Domain := ⟨p, hH C.val C.property p hpc⟩
    exact (smem_member_l I hM hT p' E).symm.trans
      ((he p' ((smem_member_l I hM hT p' C).mpr hpc)).trans (hp p'))
  · rintro ⟨hE, he⟩
    exact ⟨(smem_subset_l I hM hT hH E C).mpr hE, fun p hpc => (smem_member_l I hM hT p E).trans
      ((he p.val ((smem_member_l I hM hT p C).mp hpc)).trans (hp p).symm)⟩

theorem selem_rel_pull_l (hZF : M.Models ZF) {ω χ H c T d N S C F D}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H T N S)
    (he : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hC : M.mem C N) (hF : M.mem F N) (hD : M.mem D N) : ∃ E, M.mem E N ∧ Rel_pull_d M C F D E := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ₀ : Env L 1 := ⟨fun _ => ⟨C, hS.subset C hC⟩, fun _ => ⟨C, hS.subset C hC⟩⟩
  let ρ : Env L 3 := (ρ₀.push ⟨F, hS.subset F hF⟩).push ⟨D, hS.subset D hD⟩
  let η : Env Q 3 := ((⟨fun _ => ⟨C, hC⟩, fun _ => ⟨C, hC⟩⟩ : Env Q 1).push ⟨F, hF⟩).push ⟨D, hD⟩
  let φ : UnarySchema 3 := { body := rel_pull_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have htr := ZF.h_transitive_l I hZF hH
  have hφ (E : L.Domain) : φ.denote ρ E ↔ Rel_pull_d M C F D E.val :=
    (rel_pull_sat_l (smem_ext_l I hS.source hT htr hZF.1) _ _ _ _ _).trans (smem_rel_pull_l I hS.source hT htr _ _ _ E)
  obtain ⟨E, hE⟩ := rel_pull_exists_l hZF C F D
  have hEH := ZF.h_subsets_l I hZF hχ hH (hS.subset C hC) E hE.1
  obtain ⟨E', hE'⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
    ⟨⟨E, hEH⟩, (hφ _).mpr hE⟩
  exact ⟨E'.val, E'.property, (hφ _).mp hE'⟩

end YesMetaZFC.Model.Forcing.Internal
