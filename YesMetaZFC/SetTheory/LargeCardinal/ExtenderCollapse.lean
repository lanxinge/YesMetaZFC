import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstant
import YesMetaZFC.Model.SetTheory.Internal.RelationCollapse

/-! # 有限支撑极限的传递实现

外延性由常值初等嵌入实际传递，坍塌消费整个极限的内部良基性。
返回坍塌及其逆图的完整内部同构、源到传递目标的完整初等嵌入，
以及该目标在任意新参数上的下一步源证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_collapse_d (hZF : M.Models ZF) (ω X R q c C V : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  Wc_ext_d C V ∧ ∃ b i N e inv d W j, Smem_d I b X R ∧ Smap_d I ω b c X C i ∧ Ep_constants_d X q i ∧
    M.TransitiveSet N ∧ Wc_graph_d C V e ∧ M.IsSetBijectionFromTo I e C N ∧ Smem_d I d N W ∧
    Smap_d I ω c d C N e ∧ M.IsSetBijectionFromTo I inv N C ∧
    (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y e) ∧ Smap_d I ω d c N C inv ∧
    Smap_d I ω b d X N j ∧
    (∀ x y, Rd_entry_d x y j ↔ M.mem x X ∧ ∃ z, Rd_entry_d x z i ∧ Rd_entry_d z y e) ∧
    ∀ κ, M.mem κ N → M.MemberSubset ω κ → ∃ K, Ep_source_d hZF ω κ K N W

theorem ep_collapse_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T S q c C V : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C V)
    (wf : Wf_rel_d C V) : Ep_collapse_d (ZFC.models_zf_l hZFC) ω X R q c C V := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := h.diagram.index.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, hz, _⟩ := h.models
  obtain ⟨d, _, had⟩ := hz.2.1 a ha
  obtain ⟨b, i, n, D, U, G, r, E, Q, hm, hi, hn, ha, hD, haU, hG, md, spec⟩ :=
    ep_constant_limit_l hZFC source hF coherent h limit model had
  have constants : Ep_constants_d X q i := by
    intro x H hxH
    obtain ⟨_, f, B, u, hf, hc, hfr, hu, huH⟩ := (spec x H).mp hxH
    have hDX := source.space_mem_l hZF hn hD
    exact ⟨u, a, B, f, D, hDX, source.function_l hZF hDX ((hG f).mp hf).1 ((hG f).mp hf).2,
      hc, md.map.representative_l I (hF.at_l hZF.1 haU ha hD).base hfr, hu, huH⟩
  have extX : Wc_ext_d X R := fun x hx y hy same => hZF.1.eq_of_same_members x y (fun z =>
    ⟨fun hz => ((hm.2 z y).mp ((same z (source.transitive x hx z hz)).mp
      ((hm.2 z x).mpr ⟨source.transitive x hx z hz, hx, hz⟩))).2.2,
     fun hz => ((hm.2 z x).mp ((same z (source.transitive y hy z hz)).mpr
      ((hm.2 z y).mpr ⟨source.transitive y hy z hz, hy, hz⟩))).2.2⟩)
  have he := hi.extensional_l hZF source.omega hm.1 model extX
  obtain ⟨N, e, inv, d, W, ht, hg, bij, hn, elem, bi, inverse, elemInv⟩ := wc_smaps_l hZF source.omega model wf he
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi elem
  exact ⟨he, b, i, N, e, inv, d, W, j, hm, hi, constants, ht, hg, bij, hn, elem, bi, inverse, elemInv, hj, js,
    fun _ hκ hωκ => source.successor_l hZF hm hn ht hj hκ hωκ⟩

end YesMetaZFC.SetTheory.LargeCardinal
