import YesMetaZFC.Model.SetTheory.Internal.RelativizationRule

/-! # 保留指令位置的程序追加

与语义构造器共享同一个原追加操作，额外返回实际新指令，供纯语法证书使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sr_rel_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i ω) (hj : M.mem j ω) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 0 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inl ⟨i, j, hc, hi, hj⟩)
  exact ⟨l, H, h, c, row, hc⟩

theorem sr_nor_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i m) (hj : M.mem j m) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 2 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 2 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inr (Or.inr (Or.inl ⟨i, j, hc, hi, hj⟩)))
  exact ⟨l, H, h, c, row, hc⟩

theorem sr_ex_add_l (hZF : M.Models ZF) {ω m G i j} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hi : M.mem i ω) (hj : M.mem j m) :
    ∃ l H, Sbuild_d I ω m G l H m ∧ Sr_at_d I 3 H m i j := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 3 i j
  obtain ⟨l, H, h, row⟩ := sfm_node_build_l I hZF hω hG (Or.inr (Or.inr (Or.inr ⟨i, j, hc, hi, hj⟩)))
  exact ⟨l, H, h, c, row, hc⟩

def Sr_and_d (G t u v : M.Domain) : Prop := ∃ a b,
  Sr_at_d I 2 G a u u ∧ Sr_at_d I 2 G b v v ∧ Sr_at_d I 2 G t a b

def sr_and_m {d} (G t u v : Term d) : Formula 1 d := set[d] ⟪∃ a b,
  ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, a, ⌜u⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, b, ⌜v⌝ₛ, ⌜v⌝ₛ) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜t⌝ₛ, a, b)⟫
derive_free_closed sr_and_m

theorem sr_and_sat_l {d} (ρ : Env M d) (G t u v : Term d) :
    Formula.satisfies ρ (sr_and_m (𝒞 := 𝒞) G t u v) ↔ Sr_and_d I (G.eval ρ) (t.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [sr_and_m, Sr_and_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem Sr_and_d.extend_l {ω m G l H z t u v : M.Domain} (h : Sr_and_d I G t u v)
    (e : Sbuild_d I ω m G l H z) : Sr_and_d I H t u v := by
  obtain ⟨a, b, ha, hb, ht⟩ := h
  exact ⟨a, b, ha.extend_l I e, hb.extend_l I e, ht.extend_l I e⟩

theorem sr_and_build_l (hZF : M.Models ZF) {ω m G u v} (hω : M.IsOmega ω)
    (hG : Sfm_d I ω m G) (hu : M.mem u m) (hv : M.mem v m) :
    ∃ l H t, Sbuild_d I ω m G l H t ∧ Sr_and_d I H t u v := by
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_nor_add_l I hZF hω hG hu hu
  obtain ⟨m₂, G₂, h₂, a₂⟩ := sr_nor_add_l I hZF hω h₁.program (h₁.span v hv) (h₁.span v hv)
  obtain ⟨l, H, h₃, a₃⟩ := sr_nor_add_l I hZF hω h₂.program (h₂.span m h₁.root) h₂.root
  exact ⟨l, H, m₂, (h₁.comp I h₂).comp I h₃, m, m₁, a₁.extend_l I (h₂.comp I h₃), a₂.extend_l I h₃, a₃⟩

theorem Sr_and_d.correct_l (hZF : M.Models ZF) {ω G m t u v X R E f : M.Domain}
    (hG : Sfm_d I ω m G) (h : Sr_and_d I G t u v) (hf : M.mem f E) :
    Ssat_d I X R E G m t f ↔ Ssat_d I X R E G m u f ∧ Ssat_d I X R E G m v f := by
  obtain ⟨a, b, ha, hb, ht⟩ := h
  obtain ⟨ca, hca, oa⟩ := ha
  obtain ⟨cb, hcb, ob⟩ := hb
  obtain ⟨ct, hct, ot⟩ := ht
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G hG.2.1.1
  rw [ssat_nor_l I hZF hG hH hct ot hf, ssat_nor_l I hZF hG hH hca oa hf,
    ssat_nor_l I hZF hG hH hcb ob hf]
  simp only [or_self, not_or, Classical.not_not]

end YesMetaZFC.SetTheory.Internal
