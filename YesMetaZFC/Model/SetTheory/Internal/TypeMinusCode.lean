import YesMetaZFC.Model.SetTheory.Internal.RelativizationCorrect
import YesMetaZFC.Model.SetTheory.Internal.LargestSet

/-! # 类型向前一秩层限制的纯语法代码

先编译所有量词的载体限制，再绑定该载体为当前结构的最大集合。
输出证书只包含原指令、自然数坐标和实际函数图，不包含真值假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_minus_d (ω F n r G m u : M.Domain) : Prop := ∃ b T v w t,
  M.mem b ω ∧ Sbound_d I F b ∧ Sr_state_d I ω b F n m G T ∧ M.PairMember I r v T ∧
    Sr_top_code_d I b G w ∧ Sr_and_d I G t w v ∧ Sr_at_d I 3 G u b t

def sr_minus_m {d} (ω F n r G m u : Term d) : Formula 1 d := set[d] ⟪∃ b T v w t,
  b ∈ ⌜ω⌝ₛ ∧ ⌜sbound_m (𝒞 := 𝒞)⌝ₚ(⌜F⌝ₛ, b) ∧
  ⌜sr_state_m (𝒞 := 𝒞)⌝ₚ(⌜ω⌝ₛ, b, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜m⌝ₛ, ⌜G⌝ₛ, T) ∧
  ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜r⌝ₛ, v, T) ∧ ⌜sr_top_code_m (𝒞 := 𝒞)⌝ₚ(b, ⌜G⌝ₛ, w) ∧
  ⌜sr_and_m (𝒞 := 𝒞)⌝ₚ(⌜G⌝ₛ, t, w, v) ∧ ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, ⌜u⌝ₛ, b, t)⟫
derive_free_closed sr_minus_m

theorem sr_minus_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F n r G m u : Term d) :
    Formula.satisfies ρ (sr_minus_m (𝒞 := 𝒞) ω F n r G m u) ↔
      Sr_minus_d I (ω.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (G.eval ρ) (m.eval ρ) (u.eval ρ) := by
  simp only [sr_minus_m, Sr_minus_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, sbound_sat_l I, sr_state_sat_l I hE, Formula.satisfies_orderedPairMem_iff I,
    sr_top_code_sat_l I, sr_and_sat_l I, sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem sr_minus_build_l (hZF : M.Models ZF) {ω F n r : M.Domain} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) : ∃ m G u, Sr_minus_d I ω F n r G m u := by
  obtain ⟨b, m, G, T, hb, bound, state⟩ := sr_compile_l I hZF hω hF
  obtain ⟨v, hv, hrv⟩ := state.map.2.2 r hr
  obtain ⟨m₁, G₁, w, h₁, top⟩ := sr_top_build_l I hZF hω hb state.program
  obtain ⟨m₂, G₂, t, h₂, conj⟩ := sr_and_build_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, H, h₃, ex⟩ := sr_ex_add_l I hZF hω h₂.program hb h₂.root
  exact ⟨l, H, m₂, b, T, v, w, t, hb, bound, state.extend_l I ((h₁.comp I h₂).comp I h₃),
    hrv, top.extend_l I (h₂.comp I h₃), conj.extend_l I h₃, ex⟩

theorem Sr_minus_d.program_l {ω F n r G m u : M.Domain} (h : Sr_minus_d I ω F n r G m u) :
    Sfm_d I ω m G ∧ M.mem u m := by
  obtain ⟨_, _, _, _, _, _, _, state, _, _, _, c, hc, _⟩ := h
  exact ⟨state.program, (state.program.2.1.2.2 u).mpr ⟨c, hc⟩⟩

end YesMetaZFC.SetTheory.Internal
