import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeed

/-! # 正规性使坐标像对前驱封闭

先把任意前驱和坐标放进共同分量，再把前驱代表改为 κ 值函数。
正规性给出较小的末坐标；即使它重复旧坐标，也先覆盖到实际单射支撑，
再用源内协调律识别同一个极限元素。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_seed_down_l {ω κ K L X R F J O Z A p T S q C W α E H : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hκ : M.TransitiveSet κ) (hωL : M.MemberSubset ω L)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (normal : En_source_d ω κ L X F) (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) (seed : Ep_seed_d κ L q α E) (hHE : Rd_entry_d H E W) :
    ∃ β, M.mem β α ∧ Ep_seed_d κ L q β H := by
  obtain ⟨n₀, a, i₀, D₀, f₀, ha, hi₀, hD₀, hf₀, value₀⟩ := seed
  obtain ⟨v, hvH⟩ := (limit.range H).mp (limit.bounded H E hHE).1
  obtain ⟨b, B, hv, _⟩ := (h.nodes v).mp (limit.projection.bound_l hvH).1
  have hvb := (h.index v b B hv).mpr (limit.projection.bound_l hvH).1
  obtain ⟨c, hcJ, hac, hbc⟩ := h.order.directed a b (value₀.index_l hZF h limit) (h.projection.bound_l hvb).2
  obtain ⟨n, D, i, f, hn, hc, hi, hD, hfX, hf, value⟩ :=
    ep_seed_move_l hZF source family h limit ha hi₀ hD₀ hf₀ value₀ hac
  obtain ⟨w, hwc, hvw⟩ := h.diagram.total v b c hvb hbc
  obtain ⟨H₀, _, hwH₀⟩ := limit.projection.2.1 w (h.diagram.bound v w hvw).2
  have hwH : Rd_entry_d w H q := (limit.commute_l h.diagram hvw hvH hwH₀).symm ▸ hwH₀
  obtain ⟨B', hw, hat⟩ := h.toEp_graph_d.label_l hwc
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  obtain ⟨o, Q, V, hco, component, model, hBQ⟩ := ep_at_model_l hZF models hat
  obtain ⟨m, D', U, G, r, Q', V', _, hc', hD', hcU, hG, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have en := hc'.domain_eq_l hZF.1 hc
  subst m
  have eD := hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  obtain ⟨g, hgB⟩ := (md.map.range B').mp hBQ
  have hg := (hG g).mp (md.map.projection.input_mem_of_pairMember hgB)
  have ultra := family.at_l hZF.1 hcU hc hD
  have old : Ep_repr_d q c g H := ⟨w, B', hw, md.map.representative_l I ultra.base hgB, hwH⟩
  obtain ⟨z, _, hzω⟩ := source.omega.1.1
  obtain ⟨o₀, code⟩ := source.code
  have gBelow := (ep_repr_atoms_l hZF family h limit hcU old value).2.mp hHE
  obtain ⟨g', hg'X, hg', eqg⟩ := rs_bound_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD) source.cardinal_mem hg.1 hg.2 (source.below z hzω) ultra.base.bounds (by
      obtain ⟨B, hBU, bound⟩ := gBelow
      exact ⟨B, hBU, fun s hs => by
        obtain ⟨x, _, y, _, hsx, hsy, hxy⟩ := bound s hs
        exact ⟨x, hκ y (hf.1.bound_l hsy).2 x ((code.2 x y).mp hxy).2.2, hsx⟩⟩)
  obtain ⟨H', _, value'⟩ := ep_repr_exists_l hZF family h limit hcJ hc hD hg'X
    (hg'.mono_target_l (source.transitive κ source.cardinal_mem))
  have eH := (ep_repr_atoms_l hZF family h limit hcU old value').1.mpr eqg
  have repr : Ep_repr_d q c g' H := eH.symm ▸ value'
  -- 回归关系的精确真值集属于源，因而可以继续施加源内协调律。
  obtain ⟨B₀, hB₀X, bs₀⟩ := sc_member_trace_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn hD)
    (source.function_l hZF hg'X (hg'.mono_target_l (source.transitive κ source.cardinal_mem)))
    (source.function_l hZF hfX (hf.1.mono_target_l (source.transitive κ source.cardinal_mem)))
  have below := (ep_repr_atoms_l hZF family h limit hcU repr value).2.mp hHE
  have hB₀U : M.mem B₀ U := by
    obtain ⟨B, hBU, bound⟩ := below
    exact ultra.upward B B₀ hBU hB₀X (fun s hs => ((bs₀ s).mp hs).1)
      (fun s hs => (bs₀ s).mpr ⟨ultra.base.bounds B hBU s hs, bound s hs⟩)
  obtain ⟨m, b, V₀, β, B₁, hm, hmn, hb, hcb, hnβ, hβα, hbV, hB₁V, graph⟩ :=
    normal n c U D g' i α B₀ hn hc hcU hD hg'X hg' hi hB₀U (fun s hs x y hsx hiy => by
      obtain ⟨hsD, x', _, y', _, hsx', hsy', hxy⟩ := (bs₀ s).mp hs
      have ex := (fn0_function_l (ZF.modelsKP hZF) hg').1.2 s x' x hsx' hsx
      have ey := (fn0_function_l (ZF.modelsKP hZF) hf.1).1.2 s y' y hsy' ((hf.2 s y).mpr ⟨hsD, hiy⟩)
      exact ex ▸ ey ▸ ((code.2 x' y').mp hxy).2.2)
  obtain ⟨D₁, hD₁X, hD₁⟩ := source.space_l hZF hm
  let ρ : Env M 4 := ⟨Fin.cases g' (Fin.cases B₀ (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let φ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨B₂, hB₂X, bs₂⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (en_graph_delta_l ..) ρ (Fin.cases hg'X (Fin.cases hB₀X
      (Fin.cases source.cardinal_mem (fun _ => source.transitive ω source.omega_mem n hn)))) hD₁X
  have read s : M.mem s B₂ ↔ M.mem s D₁ ∧ En_graph_d n κ B₀ g' s :=
    (bs₂ s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 ..)
  have hB₂V := (family.at_l hZF.1 hbV hb hD₁).upward B₁ B₂ hB₁V hB₂X
    (fun s hs => ((read s).mp hs).1) (fun s hs => (read s).mpr
      ⟨(family.at_l hZF.1 hbV hb hD₁).base.bounds B₁ hB₁V s hs, graph s hs⟩)
  -- 新末坐标可能已经出现；统一覆盖到单射支撑后再作商计算。
  obtain ⟨l, d, r₁, _, hl, hd, hr₁, hrb, _⟩ := ec_join_l hZF source.omega hωL hm hm hb hb
  have hd' := fn0_of_function_l (ZF.modelsKP hZF) hd.1
  have hdJ := (h.indices d).mpr ⟨l, hl, hd', hd.2⟩
  have sub i x (hix : Rd_entry_d i x c) : Rd_entry_d i x b := hix.elim fun p hp => ⟨p, hp.1, hcb p hp.2⟩
  obtain ⟨r₀, hr₀, hrc⟩ := ec_factor_l hZF hc hd (fun i x hix => by
    obtain ⟨j, _, hij⟩ := hr₁.2.1 i (hb.bound_l (sub i x hix)).1
    exact ⟨j, (hrb.value_l hr₁ hd' hij).mp (sub i x hix)⟩)
  have same i j k (hij : Rd_entry_d i j r₀) (hik : Rd_entry_d i k r₁) : j = k := by
    obtain ⟨x, _, hix⟩ := hc.2.1 i (hr₀.bound_l hij).1
    exact hd.2 j k x ((hrc.value_l hr₀ hd' hij).mp hix) ((hrb.value_l hr₁ hd' hik).mp (sub i x hix))
  obtain ⟨D₂, _, hD₂⟩ := source.space_l hZF hl
  obtain ⟨g₂, _, _, pull, repr₂⟩ := ep_repr_reindex_l hZF source family h limit hn hl hr₀ hdJ hd' hrc hD hD₂
    hg'X (hg'.mono_target_l (source.transitive κ source.cardinal_mem)) repr
  obtain ⟨j, hj, hnj⟩ := hr₁.2.1 n hmn.predecessor_mem
  obtain ⟨f₂, hf₂X, hf₂⟩ := source.coordinate_l hZF hl hD₂ hj
  obtain ⟨E₂, _, value₂⟩ := ep_repr_exists_l hZF family h limit hdJ hd' hD₂ hf₂X
    (hf₂.1.mono_target_l (source.transitive κ source.cardinal_mem))
  obtain ⟨U₂, hdU⟩ := family.total l d hl hd'
  obtain ⟨B₃, bs₃, measure⟩ := coherent m l r₁ d b V₀ U₂ B₂ hm hl hB₂X hr₁ hd' hrb hdU hbV
    (fun s hs => (hD₁ s).mp ((read s).mp hs).1)
  have equal : Rp_eq_d X U₂ g₂ f₂ := by
    refine ⟨B₃, measure.mpr hB₂V, fun s hs => ?_⟩
    obtain ⟨hs, t, ht, hst⟩ := (bs₃ s).mp hs
    obtain ⟨_, v, hv, hvt, x, hx, hvx, hnx⟩ := (read t).mp ht
    have hvD := ((bs₀ v).mp hv).1
    have hvFn := (hD v).mp hvD
    have comp : Cp0_d n l κ r₀ s v := by
      refine ⟨hvFn, fun i hi => ?_⟩
      obtain ⟨k, hk, hik⟩ := hr₀.2.1 i hi
      obtain ⟨k', _, hik'⟩ := hr₁.2.1 i ((hmn i).mpr (Or.inl hi))
      have ek := same i k k' hik hik'
      obtain ⟨y, hy, hiy⟩ := hvFn.2.1 i hi
      exact ⟨k, hk, y, hy, hik, (hst.value_l hr₁ hs (ek.symm ▸ hik')).mp
        (hiy.elim fun p hp => ⟨p, hp.1, hvt p hp.2⟩), hiy⟩
    exact ⟨x, source.transitive κ source.cardinal_mem x hx, (pull.2.2 s v hs comp x).mpr hvx,
      (hf₂.2 s x).mpr ⟨(hD₂ s).mpr hs, (hst.value_l hr₁ hs hnj).mp hnx⟩⟩
  have eH₂ := (ep_repr_atoms_l hZF family h limit hdU repr₂ value₂).1.mpr equal
  exact ⟨β, hβα, l, d, j, D₂, f₂, hd', (hrb.value_l hr₁ hd' hnj).mp hnβ, hD₂, hf₂, eH₂.symm ▸ value₂⟩

end YesMetaZFC.SetTheory.LargeCardinal
