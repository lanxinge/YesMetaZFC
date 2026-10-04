import YesMetaZFC.SetTheory.LargeCardinal.ExtenderComparison
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCoordinates
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed

/-! # 坍塌因子固定长度，超幂恢复原临界点

坐标代表保证所有长度以下序数都在因子像内。传递坍塌固定这些序数，交换
三角因此给出超幂嵌入的真实临界点 κ，并证明 L≤j_E(κ)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_length_d (hZF : M.Models ZF) (ω κ L X R j Y q C : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ b d N W i k κ', Smem_d I b X R ∧ Smem_d I d N W ∧ M.TransitiveSet N ∧ Smap_d I ω b d X N i ∧
    M.IsSetInjectionFromTo I k N Y ∧
    (∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v)) ∧
    (∀ y, (∃ z, Rd_entry_d z y k) ↔ ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u y) ∧
    (∀ x y z, Rd_entry_d x y i → (Rd_entry_d y z k ↔ Rd_entry_d x z j)) ∧
    M.MemberSubset L N ∧ (∀ α, M.mem α L → Rd_entry_d α α k) ∧ Wd_crit_d I X i κ κ' ∧ M.MemberSubset L κ'

theorem ep_length_l (hZF : M.Models ZF) {ω X R j Y q C κ k L : M.Domain}
    (comparison : Ep_comparison_d hZF ω X R j Y q C)
    (hX : M.TransitiveSet X)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.IsOrdinal L) (hκL : M.mem κ L) (hLk : M.MemberSubset L k)
    (cover : ∀ α, M.mem α L → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u α) :
    Ep_length_d hZF ω κ L X R j Y q C := by
  obtain ⟨b, d, N, W, i, e, hm, hn, ht, hi, he, rel, range, triangle⟩ := comparison
  obtain ⟨hLN, fixed⟩ := mem_embedding_fixed_l hZF ht he rel hL.transitive (fun α hα => (range α).mpr (cover α hα))
  obtain ⟨κ', _, hiκ⟩ := hi.1.1.2.2 κ hc.source
  have heκ := (triangle κ κ' k hiκ).mpr hc.image
  have hκ' := mem_embedding_ordinal_l (ZF.modelsKP hZF) ht he rel heκ hc.ordinal_image
  have crit : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X i κ κ' := by
    refine ⟨hc.ordinal, hc.source, hκ', hiκ, fun eq => ?_, fun α hα => ?_⟩
    · exact hc.moved (he.1.1.2 κ κ k (fixed κ hκL) (eq.symm ▸ heκ))
    · obtain ⟨β, _, hiα⟩ := hi.1.1.2.2 α (hX κ hc.source α hα)
      have hβα := (triangle α β α hiα).mpr (hc.fixed α hα)
      exact he.2 β α α hβα (fixed α (hL.transitive κ hκL α hα)) ▸ hiα
  exact ⟨b, d, N, W, i, e, κ', hm, hn, ht, hi, he, rel, range, triangle, hLN, fixed, crit,
    fun α hα => (rel α κ' α k (fixed α hα) heκ).mpr (hLk α hα)⟩

end YesMetaZFC.SetTheory.LargeCardinal
