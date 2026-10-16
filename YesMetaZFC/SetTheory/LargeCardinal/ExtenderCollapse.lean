import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstant
import YesMetaZFC.Model.SetTheory.Internal.RelationCollapse

/-! # 有限支撑极限的传递实现

外延性由常值初等嵌入实际传递，坍塌消费整个极限的内部良基性。
返回坍塌及其逆图的完整内部同构、源到传递目标的完整初等嵌入，
以及以 ω 为字母表的实际下一步源；新小字母表由该源重新装配。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 指定传递目标的原常值图及坍缩图；比较、长度与强度证书保持同一实现。 -/
def Ep_realizer_d (hZF : M.Models ZF) (ω X q b c C V d N i : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ t e, Smap_d I ω b c X C t ∧ Ep_constants_d X q t ∧ Wc_graph_d C V e ∧
    M.IsSetBijectionFromTo I e C N ∧ Smap_d I ω c d C N e ∧
    ∀ x y, Rd_entry_d x y i ↔ M.mem x X ∧ ∃ z, Rd_entry_d x z t ∧ Rd_entry_d z y e

def Ep_collapse_d (hZF : M.Models ZF) (ω X R q c C V : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  Wc_ext_d C V ∧ ∃ b i N e inv d W j, Smem_d I b X R ∧ Smap_d I ω b c X C i ∧ Ep_constants_d X q i ∧
    M.TransitiveSet N ∧ Wc_graph_d C V e ∧ M.IsSetBijectionFromTo I e C N ∧ Smem_d I d N W ∧
    Smap_d I ω c d C N e ∧ M.IsSetBijectionFromTo I inv N C ∧
    (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y e) ∧ Smap_d I ω d c N C inv ∧
    Smap_d I ω b d X N j ∧
    (∀ x y, Rd_entry_d x y j ↔ M.mem x X ∧ ∃ z, Rd_entry_d x z i ∧ Rd_entry_d z y e) ∧
    ∃ K, Ep_source_d hZF ω ω K N W

theorem ep_collapse_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hF : Em_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (wf : Wf_rel_d C V) : Ep_collapse_d hZF ω X R q c C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, i, hm, hi, constants, he⟩ := ep_constant_l hZF source hF h limit model elementary
  obtain ⟨N, e, inv, d, W, ht, hg, bij, hn, elem, bi, inverse, elemInv⟩ := wc_smaps_l hZF source.omega model wf he
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi elem
  have fix := hj.omega_l I hZF source.omega source.transitive ht hm hn source.omega_mem
  exact ⟨he, b, i, N, e, inv, d, W, j, hm, hi, constants, ht, hg, bij, hn, elem, bi, inverse, elemInv, hj, js,
    source.successor_l hZF hm hn ht hj (hj.1.1.output_mem_of_pairMember fix) (fun _ h => h)
      ((hj.small_l hZF source.omega source.transitive ht hm hn fix).mp (source.cardinal_small.mono_l source.below))⟩

end YesMetaZFC.SetTheory.LargeCardinal
