import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyCollapse

/-! # 双映射复制自动产生传递后继与支撑保持

只要求目标扩展器的可数共同纤维。先在原源构造未坍塌超幂，再沿实际
复制图回传良基性，最后共轭两侧坍塌；支撑上的限制精确等于所属图 σ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_successors_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (ex : Ex_pre_d hZF ω κ L F) (ex' : Ex_short_d hZF ω κ' L' F')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (theory : Sc_theory_d I ω N R₀) (hωN : M.mem ω N)
    (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ) (maps : Ea_maps_d ω κ X π σ) :
    ∃ P Rₚ P' Rₚ' o o' k, Ep_successor_d hZF ω κ L X R F P Rₚ ∧
      Ep_successor_d hZF ω κ' L' Y S F' P' Rₚ' ∧ Smem_d I o P Rₚ ∧ Smem_d I o' P' Rₚ' ∧
      Smap_d I ω o o' P P' k ∧ M.MemberSubset L P ∧ M.MemberSubset L' P' ∧
      (∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) ∧
      (∀ ξ, M.mem ξ P → M.MemberSubset ω ξ → ∃ K, Ep_source_d hZF ω ξ K P Rₚ) ∧
      (∀ ξ, M.mem ξ P' → M.MemberSubset ω ξ → ∃ K, Ep_source_d hZF ω ξ K P' Rₚ') := by
  have hκ := ex.critical.1.transitive
  have hL := ex.length.transitive
  have hωL : M.MemberSubset ω L := fun x hx => hL κ ex.above x (hκ ω ex.uncountable x hx)
  have family := ex.measures.source_l hZF X
  have family' := ex'.measures.source_l hZF Y
  have coherent := ex.coherent.source_l I X
  have coherent' := ex'.coherent.source_l I Y
  obtain ⟨J, O, Z, A, p, T, V, q, c₀, C, W, h, limit, model, _⟩ := ep_ultrapower_l hZFC source family coherent hωL
  obtain ⟨J', O', Z', A', p', T', V', q', c₁, C', W', h', limit', model', wf', _, collapse'⟩ := ex'.limit_l hZFC target
  obtain ⟨τ, _, _, hτ, _, _, copy, _, _, back⟩ := ep_copy_l hZFC source target hm hn hπ hκπ owner owner' h₀ h₁ hσ
    theory hωN hLσ hFσ family family' coherent coherent' maps h limit model h' limit' model'
  have collapse := ep_collapse_l hZFC source family coherent h limit model (back wf')
  obtain ⟨P, P', o, Rₚ, o', Rₚ', g, g', k, mdl, mdl', hP, hP', wc, bij, wc', bij', hg, hg', hk, cover, cover', _, fixed, next, next'⟩ :=
    ep_copy_collapse_l hZF source target hm hn hπ hκπ owner owner' h₀ h₁ hσ hωN hLσ hFσ hκ hL hωL
      family family' coherent coherent' ex.atoms ex'.atoms (ex.normal.source_l X) (ex'.normal.source_l Y)
      h limit h' limit' hτ copy collapse collapse'
  exact ⟨P, Rₚ, P', Rₚ', o, o', k,
    ⟨J, O, Z, A, p, T, V, q, c₀, C, W, o, g, h, limit, model, mdl, hP, wc, bij, hg⟩,
    ⟨J', O', Z', A', p', T', V', q', c₁, C', W', o', g', h', limit', model', mdl', hP', wc', bij', hg'⟩,
    mdl, mdl', hk, cover, cover', fixed, next, next'⟩

end YesMetaZFC.SetTheory.LargeCardinal
