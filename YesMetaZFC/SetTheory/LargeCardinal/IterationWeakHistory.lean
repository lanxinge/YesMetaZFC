import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakState
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple

/-! # 弱迭代历史保留所有此前列图

第 i 行存长度 i+1 的真实状态；每条早期条目在所有后来状态中保持原值。
这使极限取并只须回到含有有限多个指定条目的同一旧行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_keep_d (Q G P Q' G' P' : M.Domain) : Prop :=
  (∀ i c, Rd_entry_d i c Q → Rd_entry_d i c Q') ∧
  (∀ i j f, It_map_d G i j f → It_map_d G' i j f) ∧
  ∀ i f, Rd_entry_d i f P → Rd_entry_d i f P'
def Wi_at_d (H i T Q G P : M.Domain) : Prop := ∃ s, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P

theorem Wi_keep_d.refl_l (Q G P : M.Domain) : Wi_keep_d Q G P Q G P := ⟨fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => h⟩
theorem Wi_keep_d.trans_l {Q G P Q' G' P' Q'' G'' P'' : M.Domain}
    (h : Wi_keep_d Q G P Q' G' P') (g : Wi_keep_d Q' G' P' Q'' G'' P'') : Wi_keep_d Q G P Q'' G'' P'' :=
  ⟨fun i c hc => g.1 i c (h.1 i c hc), fun i j f hf => g.2.1 i j f (h.2.1 i j f hf), fun i f hf => g.2.2 i f (h.2.2 i f hf)⟩

structure Wi_history_d (hZF : M.Models ZF) (ω a A S α D H : M.Domain) : Prop where
  function : Fn0_d α D H
  rows : ∀ i s, Rd_entry_d i s H → ∃ β T Q G P,
    M.SuccessorOf β i ∧ Rd_quad_d s T Q G P ∧ Wi_state_d hZF ω β T Q G a A S P
  past : ∀ i j T Q G P U Q' G' P', M.mem i j → Wi_at_d H i T Q G P → Wi_at_d H j U Q' G' P' → Wi_keep_d Q G P Q' G' P'

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_extension_d.keep_l {ω α T Q G a A S P β Q' G' P' : M.Domain}
    (state : Wi_state_d hZF ω α T Q G a A S P) (h : Wi_extension_d α Q G P β Q' G' P') : Wi_keep_d Q G P Q' G' P' :=
  ⟨h.2.1, fun i j f hf => (h.2.2.1 i j f (state.diagram.order.bound i j (state.diagram.map_bound_l hZF hf)).2).mpr hf, h.2.2.2⟩

theorem Wi_history_d.at_l {ω a A S α D H i T Q G P : M.Domain}
    (h : Wi_history_d hZF ω a A S α D H) (hi : Wi_at_d H i T Q G P) :
    ∃ β, M.SuccessorOf β i ∧ Wi_state_d hZF ω β T Q G a A S P := by
  obtain ⟨s, hs, pack⟩ := hi
  obtain ⟨β, T₀, Q₀, G₀, P₀, hβ, pack₀, state⟩ := h.rows i s hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := pack₀.unique_l pack
  exact ⟨β, hβ, state⟩

theorem Wi_history_d.restrict_l {ω a A S α D H β J : M.Domain}
    (h : Wi_history_d hZF ω a A S α D H) (sub : M.MemberSubset β α)
    (r : M.IsRestrictionOf I J H β) : Wi_history_d hZF ω a A S β D J := by
  refine ⟨fn0_of_function_l (ZF.modelsKP hZF) (r.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) h.function) sub),
    fun i s hs => h.rows i s ((r.2 i s).mp hs).2, ?_⟩
  intro i j T Q G P U Q' G' P' hij ⟨s, hs, ps⟩ ⟨t, ht, pt⟩
  exact h.past i j T Q G P U Q' G' P' hij ⟨s, ((r.2 i s).mp hs).2, ps⟩ ⟨t, ((r.2 j t).mp ht).2, pt⟩

end YesMetaZFC.SetTheory.LargeCardinal
