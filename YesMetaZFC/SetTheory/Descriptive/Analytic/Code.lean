import YesMetaZFC.SetTheory.Descriptive.Projection

/-! # 内部解析码

解析码采用 Borel 关系码加一个 Baire 见证投影。码的合法性、集合解释和全部
见证都在模型内；可数并接收实际内部码族，不把逐项存在替换成选择函数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Aden_d (ω A B J c K : M.Domain) : Prop := ∃ R, Bden_d I ω A A B c R ∧ Pr_d I B J R K
def aden_m {d} (ω A B J c K : Term d) : Formula 1 d := .existsE (.conj
  (bden_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken B.weaken c.weaken .newest)
  (pr_m (𝒞 := 𝒞) B.weaken J.weaken .newest K.weaken))
derive_free_closed aden_m
@[prove_auto_norm semantic]
theorem aden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J c K : Term d) :
    Formula.satisfies ρ (aden_m (𝒞 := 𝒞) ω A B J c K) ↔
      Aden_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (c.eval ρ) (K.eval ρ) := by
  simp only [aden_m, Aden_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bden_sat_l I hE, pr_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem aden_mem_l {ω A B J c K} (h : Aden_d I ω A B J c K) (x : M.Domain) :
    M.mem x K ↔ M.mem x B ∧ ∃ y z,
      M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ Bsat_d I ω A A c z := by
  obtain ⟨R, hR, hK⟩ := h
  refine (hK x).trans (and_congr_right fun _ => exists_congr fun y => exists_congr fun z => ?_)
  exact and_congr_right fun _ => and_congr_right fun hz => and_congr_right fun _ =>
    (hR z).trans ⟨And.right, fun h => ⟨hz, h⟩⟩

theorem aden_exists_unique_l (hZF : M.Models ZF) (ω A B J c : M.Domain) :
    ∃ K, Aden_d I ω A B J c K ∧ ∀ L, Aden_d I ω A B J c L → L = K := by
  obtain ⟨R, hR, hu⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨K, hK⟩ := pr_exists_l I hZF B J R
  exact ⟨K, ⟨R, hR, hK⟩, fun L ⟨Q, hQ, hL⟩ => pr_unique_l I hZF.1 (hu Q hQ ▸ hL) hK⟩

def An_d (ω A B J K : M.Domain) : Prop := ∃ c, Bcode_d I ω A A c ∧ Aden_d I ω A B J c K
def an_m {d} (ω A B J K : Term d) : Formula 1 d := .existsE (.conj
  (bcode_m (𝒞 := 𝒞) ω.weaken A.weaken A.weaken .newest)
  (aden_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest K.weaken))
derive_free_closed an_m
@[prove_auto_norm semantic]
theorem an_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J K : Term d) :
    Formula.satisfies ρ (an_m (𝒞 := 𝒞) ω A B J K) ↔
      An_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) := by
  simp only [an_m, An_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bcode_sat_l I hE, aden_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem an_proj_l {ω A B J K : M.Domain} : An_d I ω A B J K ↔
    ∃ R, Borel_d I ω A A B R ∧ Pr_d I B J R K :=
  ⟨fun ⟨c, hc, R, hR, hK⟩ => ⟨R, ⟨c, hc, hR⟩, hK⟩,
    fun ⟨R, ⟨c, hc, hR⟩, hK⟩ => ⟨c, hc, R, hR, hK⟩⟩

def Coan_d (ω A B J K : M.Domain) : Prop := ∃ L, An_d I ω A B J L ∧ Cm_d B L K
def coan_m {d} (ω A B J K : Term d) : Formula 1 d := .existsE (.conj
  (an_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest) (cm_m B.weaken .newest K.weaken))
derive_free_closed coan_m
@[prove_auto_norm semantic]
theorem coan_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J K : Term d) :
    Formula.satisfies ρ (coan_m (𝒞 := 𝒞) ω A B J K) ↔
      Coan_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) := by
  simp only [coan_m, Coan_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    an_sat_l I hE, cm_sat_l, Definitional.Term.eval_weaken]; rfl

/-- 可数并直接合并 Borel 关系码，再交换指标与实数见证的存在量词。 -/
theorem an_union_l (hZF : M.Models ZF) {ω A B J H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A A H) : ∃ K, An_d I ω A B J K ∧
      ∀ x, M.mem x K ↔ ∃ i c L, M.PairMember I i c H ∧ Aden_d I ω A B J c L ∧ M.mem x L := by
  obtain ⟨c, hc, hv⟩ := bcode_union_l I hZF hω hA hH
  obtain ⟨K, hK, _⟩ := aden_exists_unique_l I hZF ω A B J c
  refine ⟨K, ⟨c, hc, hK⟩, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨hxB, y, z, hy, hz, hp, hvz⟩ := (aden_mem_l I hK x).mp hx
    obtain ⟨i, d, hid, hdz⟩ := (hv z).mp hvz
    obtain ⟨L, hL, _⟩ := aden_exists_unique_l I hZF ω A B J d
    exact ⟨i, d, L, hid, hL, (aden_mem_l I hL x).mpr ⟨hxB, y, z, hy, hz, hp, hdz⟩⟩
  · rintro ⟨i, d, L, hid, hL, hx⟩
    obtain ⟨hxB, y, z, hy, hz, hp, hdz⟩ := (aden_mem_l I hL x).mp hx
    exact (aden_mem_l I hK x).mpr ⟨hxB, y, z, hy, hz, hp, (hv z).mpr ⟨i, d, hid, hdz⟩⟩

/-- 内部闭树体的投影自动给出解析集的实际实例。 -/
theorem an_tree_l (hZF : M.Models ZF) {ω A B J} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (T : M.Domain) :
    ∃ R K, Body_d A B T R ∧ Pr_d I B J R K ∧ An_d I ω A B J K := by
  obtain ⟨R, hR⟩ := tree_body_exists_l (ZF.modelsKP hZF) A B T
  obtain ⟨K, hK⟩ := pr_exists_l I hZF B J R
  exact ⟨R, K, hR, hK, an_proj_l I |>.mpr ⟨R, tree_body_borel_l I hZF hω hA ha hR, hK⟩⟩

/-- 同一码族的余解析补集之交；由可数并的补得到，不选择实数见证。 -/
theorem coan_inter_l (hZF : M.Models ZF) {ω A B J H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A A H) : ∃ K, Coan_d I ω A B J K ∧
      ∀ x, M.mem x K ↔ M.mem x B ∧ ∀ i c L,
        M.PairMember I i c H → Aden_d I ω A B J c L → ¬ M.mem x L := by
  obtain ⟨U, hu, hv⟩ := an_union_l I hZF (B := B) (J := J) hω hA hH
  obtain ⟨K, hK⟩ := cm_exists_l (ZF.modelsKP hZF) B U
  refine ⟨K, ⟨U, hu, hK⟩, fun x => (hK x).trans (and_congr_right fun _ => ?_)⟩
  exact (not_congr (hv x)).trans ⟨fun h i c L hi hl hx => h ⟨i, c, L, hi, hl, hx⟩,
    fun h ⟨i, c, L, hi, hl, hx⟩ => h i c L hi hl hx⟩

end YesMetaZFC.SetTheory.Descriptive
