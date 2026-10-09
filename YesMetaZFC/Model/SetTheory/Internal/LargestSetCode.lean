import YesMetaZFC.Model.SetTheory.Internal.InstructionAppend
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 最大集合的实际内部指令

在 V(η+1) 中，Vη 是按包含关系最大的元素。用七条原指令表达
∀A∀x(x∈A→x∈v_b)，从而在限制公式中绑定前一秩层，无须把它加作类型常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sr_top_d (Y X : M.Domain) : Prop := M.mem X Y ∧ ∀ a, M.mem a Y → M.MemberSubset a X

theorem Sr_top_d.unique_l (hE : Extensional M) {Y X Z : M.Domain} (h : Sr_top_d Y X) (k : Sr_top_d Y Z) : X = Z :=
  hE.eq_of_same_members X Z (fun x => ⟨k.2 X h.1 x, h.2 Z k.1 x⟩)

theorem sr_top_power_l {X Y : M.Domain} (h : M.IsPowerSetOf Y X) : Sr_top_d Y X :=
  ⟨(h X).mpr (fun _ h => h), fun a ha => (h a).mp ha⟩

def Sr_top_code_d (b G w : M.Domain) : Prop := ∃ i j a d e t u v,
  M.SuccessorOf i b ∧ M.SuccessorOf j i ∧ Sr_at_d I 0 G a j i ∧ Sr_at_d I 0 G d j b ∧
    Sr_at_d I 2 G e a a ∧ Sr_at_d I 2 G t e d ∧ Sr_at_d I 3 G u j t ∧
      Sr_at_d I 3 G v i u ∧ Sr_at_d I 2 G w v v

def sr_top_code_m {d} (b G w : Term d) : Formula 1 d := set[d] ⟪
  ∃ i j a d e t u v, ⌜Formula.isSuccessor⌝ₚ(i, ⌜b⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(j, i) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, a, j, i) ∧ ⌜sr_at_m (𝒞 := 𝒞) 0⌝ₚ(⌜G⌝ₛ, d, j, ⌜b⌝ₛ) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, e, a, a) ∧ ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, t, e, d) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, u, j, t) ∧ ⌜sr_at_m (𝒞 := 𝒞) 3⌝ₚ(⌜G⌝ₛ, v, i, u) ∧
    ⌜sr_at_m (𝒞 := 𝒞) 2⌝ₚ(⌜G⌝ₛ, ⌜w⌝ₛ, v, v)⟫
derive_free_closed sr_top_code_m

theorem sr_top_code_sat_l {d} (ρ : Env M d) (b G w : Term d) :
    Formula.satisfies ρ (sr_top_code_m (𝒞 := 𝒞) b G w) ↔ Sr_top_code_d I (b.eval ρ) (G.eval ρ) (w.eval ρ) := by
  simp only [sr_top_code_m, Sr_top_code_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, sr_at_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem Sr_top_code_d.extend_l {ω m G l H z b w : M.Domain}
    (h : Sr_top_code_d I b G w) (e : Sbuild_d I ω m G l H z) : Sr_top_code_d I b H w := by
  obtain ⟨i, j, a, d, f, t, u, v, hi, hj, ha, hd, hf, ht, hu, hv, hw⟩ := h
  exact ⟨i, j, a, d, f, t, u, v, hi, hj, ha.extend_l I e, hd.extend_l I e, hf.extend_l I e,
    ht.extend_l I e, hu.extend_l I e, hv.extend_l I e, hw.extend_l I e⟩

theorem sr_top_build_l (hZF : M.Models ZF) {ω b m G : M.Domain} (hω : M.IsOmega ω)
    (hb : M.mem b ω) (hG : Sfm_d I ω m G) : ∃ l H w, Sbuild_d I ω m G l H w ∧ Sr_top_code_d I b H w := by
  obtain ⟨i, hi, hiω⟩ := hω.1.2 b hb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 i hiω
  obtain ⟨m₁, G₁, h₁, a₁⟩ := sr_rel_add_l I hZF hω hG hjω hiω
  obtain ⟨m₂, G₂, h₂, a₂⟩ := sr_rel_add_l I hZF hω h₁.program hjω hb
  obtain ⟨m₃, G₃, h₃, a₃⟩ := sr_nor_add_l I hZF hω h₂.program (h₂.span m h₁.root) (h₂.span m h₁.root)
  obtain ⟨m₄, G₄, h₄, a₄⟩ := sr_nor_add_l I hZF hω h₃.program h₃.root (h₃.span m₁ h₂.root)
  obtain ⟨m₅, G₅, h₅, a₅⟩ := sr_ex_add_l I hZF hω h₄.program hjω h₄.root
  obtain ⟨m₆, G₆, h₆, a₆⟩ := sr_ex_add_l I hZF hω h₅.program hiω h₅.root
  obtain ⟨l, H, h₇, a₇⟩ := sr_nor_add_l I hZF hω h₆.program h₆.root h₆.root
  have e₆ := h₆.comp I h₇
  have e₅ := h₅.comp I e₆
  have e₄ := h₄.comp I e₅
  have e₃ := h₃.comp I e₄
  have e₂ := h₂.comp I e₃
  exact ⟨l, H, m₆, h₁.comp I e₂, i, j, m, m₁, m₂, m₃, m₄, m₅, hi, hj,
    a₁.extend_l I e₂, a₂.extend_l I e₃, a₃.extend_l I e₄, a₄.extend_l I e₅,
    a₅.extend_l I e₆, a₆.extend_l I h₇, a₇⟩

end YesMetaZFC.SetTheory.Internal
