import YesMetaZFC.Model.Forcing.Proper.Elementary.Inverse

/-! # 第一坐标原像的内部初等闭包

坐标原像是给定关系载体的子集；精确方程的所有坐标都由 Kuratowski 对和传递性
所界。因而只用 ZF，就能在 N 中取得同一个原像集合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Fst_pull_d (M : SetTheory.Structure.{u}) (C D F : M.Domain) : Prop := M.MemberSubset F C ∧
  ∀ x, M.mem x C → (M.mem x F ↔ ∃ p s, KPair_d M x p s ∧ M.mem p D)

def fst_pull_m {n} (C D F : Term n) : Formula 1 n := .conj (Formula.subset F C)
  (Formula.forallMem C (.iff (.mem .newest F.weaken) (.existsE (.existsE
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) D.weaken.weaken.weaken))))))
derive_free_closed fst_pull_m

theorem fst_pull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (C D F : Term n) :
    Formula.satisfies ρ (fst_pull_m C D F) ↔ Fst_pull_d M (C.eval ρ) (D.eval ρ) (F.eval ρ) := by
  simp only [fst_pull_m, Fst_pull_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem fst_pull_exists_l (hZF : M.Models ZF) (C D : M.Domain) : ∃ F, Fst_pull_d M C D F := by
  let ρ : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  let φ : UnarySchema 1 := { body := .existsE (.existsE
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) (.bound 3)))) }
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF φ ρ C
  refine ⟨F, fun x hx => ((hF x).mp hx).1, fun x hx => ?_⟩
  rw [hF x, and_iff_right hx]
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, kpair_sat_l M hZF.1, Formula.satisfies_mem_iff]
  rfl

theorem smem_fst_pull_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H T}
    (hM : Smdl_d I c H T) (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hH : M.TransitiveSet H) (C D F : (smdl_structure_l I (R := T) hM.2.1).Domain) :
    Fst_pull_d (smdl_structure_l I (R := T) hM.2.1) C D F ↔ Fst_pull_d M C.val D.val F.val := by
  let L := smdl_structure_l I (R := T) hM.2.1
  have hp (x : L.Domain) : (∃ p s, KPair_d L x p s ∧ L.mem p D) ↔
      ∃ p s, KPair_d M x.val p s ∧ M.mem p D.val := by
    constructor
    · rintro ⟨p, s, hps, hpD⟩
      exact ⟨p.val, s.val, (smem_kpair_l I hM hT hH x p s).mp hps, (smem_member_l I hM hT p D).mp hpD⟩
    · rintro ⟨p, s, hps, hpD⟩
      have hc := trans_kpair_l hH x.property hps
      exact ⟨⟨p, hc.1⟩, ⟨s, hc.2⟩, (smem_kpair_l I hM hT hH x _ _).mpr hps, (smem_member_l I hM hT _ D).mpr hpD⟩
  constructor
  · rintro ⟨hF, h⟩
    refine ⟨(smem_subset_l I hM hT hH F C).mp hF, fun x hx => ?_⟩
    let x' : L.Domain := ⟨x, hH C.val C.property x hx⟩
    exact (smem_member_l I hM hT x' F).symm.trans ((h x' ((smem_member_l I hM hT x' C).mpr hx)).trans (hp x'))
  · rintro ⟨hF, h⟩
    exact ⟨(smem_subset_l I hM hT hH F C).mpr hF, fun x hx => (smem_member_l I hM hT x F).trans
      ((h x.val ((smem_member_l I hM hT x C).mp hx)).trans (hp x).symm)⟩

theorem selem_fst_pull_l (hZF : M.Models ZF) {ω χ H c T d N S C D}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hT : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H T N S)
    (he : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hC : M.mem C N) (hD : M.mem D N) : ∃ F, M.mem F N ∧ Fst_pull_d M C D F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env L 2 := (⟨fun _ => ⟨C, hS.subset C hC⟩, fun _ => ⟨C, hS.subset C hC⟩⟩ : Env L 1).push ⟨D, hS.subset D hD⟩
  let η : Env Q 2 := (⟨fun _ => ⟨C, hC⟩, fun _ => ⟨C, hC⟩⟩ : Env Q 1).push ⟨D, hD⟩
  let φ : UnarySchema 2 := { body := fst_pull_m (.bound 2) (.bound 1) .newest }
  have htr := ZF.h_transitive_l I hZF hH
  have hφ (F : L.Domain) : φ.denote ρ F ↔ Fst_pull_d M C D F.val :=
    (fst_pull_sat_l (smem_ext_l I hS.source hT htr hZF.1) _ _ _ _).trans (smem_fst_pull_l I hS.source hT htr _ _ F)
  obtain ⟨F, hF⟩ := fst_pull_exists_l hZF C D
  have hFH := ZF.h_subsets_l I hZF hχ hH (hS.subset C hC) F hF.1
  obtain ⟨F', hF'⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (fun _ => rfl))
    ⟨⟨F, hFH⟩, (hφ _).mpr hF⟩
  exact ⟨F'.val, F'.property, (hφ _).mp hF'⟩

end YesMetaZFC.Model.Forcing.Internal
