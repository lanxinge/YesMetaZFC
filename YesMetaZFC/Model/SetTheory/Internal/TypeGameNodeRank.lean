import YesMetaZFC.Model.SetTheory.Internal.TypeGameNode
import YesMetaZFC.SetTheory.Cumulative

/-! # 原树的标签严格低于原树秩界

从实际三元节点逐层展开累积层级，证明标签对已在包含原树的同一 Vα 中。
α 不要求为极限序数；泛型 I 方向的回答高度因而无需额外闭包假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_node_d.labels_rank_l {α V k S s t g : M.Domain}
    (hV : V_d I α V) (hS : M.mem S V) (node : Tg_node_d I k S s t g) : M.MemberSubset g V := by
  have tr := ZF.v_transitive_l I hZF hV
  obtain ⟨q, hq, _, join⟩ := node.2.2.2
  intro p hp
  obtain ⟨i, z, cp⟩ := node.2.2.1.1.1 p hp
  obtain ⟨x, y, z', v, a, _, _, hz, cv, ca, j, cj, hj⟩ :=
    join i ((node.2.2.1.2 i).mpr ⟨z, p, cp, hp⟩)
  have eq := node.2.2.1.1.2 i z' z hz ⟨p, cp, hp⟩
  subst z'
  obtain ⟨β, W, hb, hW, sub⟩ := (ZF.v_unfold_l I hZF hV j).mp (tr q (tr S hS q hq) j hj)
  obtain ⟨s₀, t₀, hs₀, ht₀, hj⟩ := cj
  obtain ⟨s₁, t₁, hs₁, ht₁, hp⟩ := cp
  have ss := hZF.1.eq_of_same_members s₁ s₀ (fun b => (hs₁ b).trans (hs₀ b).symm)
  have hsW : M.mem s₁ W := ss.symm ▸ sub s₀ ((hj s₀).mpr (Or.inl rfl))
  obtain ⟨γ, Z, hg, hZ, tz⟩ := (ZF.v_unfold_l I hZF hW t₀).mp (sub t₀ ((hj t₀).mpr (Or.inr rfl)))
  have trZ := ZF.v_transitive_l I hZF hZ
  have hi := tz i ((ht₀ i).mpr (Or.inl rfl))
  have hz := (cv.mem_l M trZ (ca.mem_l M trZ (tz a ((ht₀ a).mpr (Or.inr rfl)))).2).2
  have htW : M.mem t₁ W := (ZF.v_unfold_l I hZF hW t₁).mpr ⟨γ, Z, hg, hZ, fun b hb =>
    ((ht₁ b).mp hb).elim (fun eq => eq.symm ▸ hi) (fun eq => eq.symm ▸ hz)⟩
  exact (ZF.v_unfold_l I hZF hV p).mpr ⟨β, W, hb, hW, fun b hb =>
    ((hp b).mp hb).elim (fun eq => eq.symm ▸ hsW) (fun eq => eq.symm ▸ htW)⟩

end YesMetaZFC.SetTheory.Internal
