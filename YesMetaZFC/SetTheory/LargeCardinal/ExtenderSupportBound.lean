import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedCollapse
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOrdinal

/-! # 支撑端点由实际临界点像界住

把常值 κ 代表与任意坐标搬到共同支撑，直接在同一个超幂中比较两者。
于是 L⊆j(κ)；当 κ、L 为序数时，L 本身属于传递后继，而非仅其元素属于后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_value_support_l (hZF : M.Models ZF)
    {ω κ K L X R F J O Z A p T V q c C W d N S e n D a f ν : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (h : Ep_system_d hZF ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C W)
    (target : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (haJ : M.mem a J) (hn : M.mem n ω) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D X f) (fc : Rs_const_d D κ f) (fv : Ep_value_d q e a f ν) :
    M.MemberSubset L ν := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, code⟩ := source.code
  obtain ⟨H, fh, hHν⟩ := fv
  intro α hα
  obtain ⟨E, _, m, s, i, D₀, u, hs, hi, hD₀, hu, uh⟩ := ep_seed_exists_l hZF source family h limit hα
  obtain ⟨s₁, hs₁J, has, hss⟩ := h.order.directed a s haJ (uh.index_l hZF h limit)
  obtain ⟨l, D₁, i₁, u₁, hl, hs₁, hi₁, hD₁, _, hu₁, uh₁⟩ :=
    ep_seed_move_l hZF source family h limit hs hi hD₀ hu uh hss
  obtain ⟨_, _, r, n', l', _, _, hr, hs₁', hra⟩ := (h.order_spec a s₁).mp has
  have en := hra.1.domain_eq_l hZF.1 ha
  have el := hs₁'.domain_eq_l hZF.1 hs₁
  subst n' l'
  obtain ⟨g, _, hg, pull, gh⟩ := ep_repr_reindex_l hZF source family h limit hn hl hr hs₁J hs₁ hra hD hD₁ hfX hf fh
  have gc : Rs_const_d D₁ κ g := by
    intro v hv
    obtain ⟨t, ht⟩ := cp0_exists_l (ZF.modelsKP hZF) hr ((hD₁ v).mp hv)
    exact (pull.2.2 v t ((hD₁ v).mp hv) ht κ).mpr (fc t ((hD t).mpr ht.1))
  obtain ⟨U, hsU⟩ := family.total l s₁ hl hs₁
  have ultra := family.at_l hZF.1 hsU hs₁ hD₁
  have rel : Rd_entry_d E H W := (ep_repr_atoms_l hZF family h limit hsU uh₁ gh).2.mpr
    ⟨D₁, ultra.base.top, fun v hv => by
      obtain ⟨x, hx, hvx⟩ := hu₁.1.2.1 v hv
      have hxX := source.transitive κ source.cardinal_mem x hx
      exact ⟨x, hxX, κ, source.cardinal_mem, hvx, gc v hv,
        (code.2 x κ).mpr ⟨hxX, source.cardinal_mem, hx⟩⟩⟩
  exact ((target.2 α ν).mp ((he.relation_l I hZF source.omega model target.1
    (fixed α E ⟨l, s₁, i₁, D₁, u₁, hs₁, hi₁, hD₁, hu₁, uh₁⟩) hHν).mp rel)).2.2

/-- 从实际极限自动选取一个分量，证明支撑端点 L 本身属于传递后继。 -/
theorem ep_support_mem_l (hZFC : M.Models ZFC)
    {ω κ K L X R F J O Z A p T V q c C W d N S e : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L) : M.mem L N := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨H, hHC⟩ := model.2.1
  obtain ⟨n, a, D, _, hn, haJ, ha, hD, _⟩ := ep_repr_surjective_l hZF family h limit hHC
  obtain ⟨b, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent h limit model he haJ ha hD
  obtain ⟨ν, hνN, hκν⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨f, hfX, hf, fc, fv⟩ := constants κ ν hκν
  have bound := ep_value_support_l hZF source family h limit model target he fixed haJ hn ha hD hfX hf fc fv
  have hν := hj.ordinal_l hZF source.omega source.transitive hN code target hκν hκ
  rcases Structure.IsOrdinal.trichotomy hZF.1 hL hν (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) L ν) with eq | lt | gt
  · exact (hZF.1.eq_of_same_members L ν eq).symm ▸ hνN
  · exact hN ν hνN L lt
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) ν (bound ν gt)).elim

end YesMetaZFC.SetTheory.LargeCardinal
