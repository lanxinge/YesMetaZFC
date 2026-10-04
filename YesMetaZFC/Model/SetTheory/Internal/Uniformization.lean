import YesMetaZFC.Model.SetTheory.Internal.UniformizationCode
import YesMetaZFC.Model.SetTheory.Internal.Collection
import YesMetaZFC.SetTheory.HereditaryAlgebra

/-! # 源模型中的实际统一见证函数

收集构造给出的函数图是 D×C 的子集，故它确实属于正则 H(χ)。统一化实例
再沿完整初等嵌入回拉，得到源中的函数图和源中的值域界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem h_uniform_l {ω χ H R E F n r i j f D} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hD : M.mem D H)
    (hh : Scollect_d I H R E F n r i j f D H) :
    ∃ B C, M.mem B H ∧ M.mem C H ∧ Suniform_d I H R E F n r i j f D C B := by
  obtain ⟨C, B, hC, hB, select⟩ := h_collect_function_l I hZFC hω hχ hωχ hH hD hh
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I D C
  have hb := fn0_of_function_l (ZF.modelsKP hZF) hB
  have hBH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (ZFC.h_product_l hZFC hω hχ hωχ hH hD hC hP) B
    (fun p hp => (hP p).mpr (hb.1 p hp))
  exact ⟨B, C, hBH, hC, hb, select⟩

theorem smap_uniform_l {ω χ c d X R H S q E F n r i j f D} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E) (hD : M.mem D X)
    (hh : Scollect_d I X R E F n r i j f D X) :
    ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨t, ht, htω⟩ := hω.1.2 s hs
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have st : M.MemberSubset s t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun e => ir i (e ▸ his)
  obtain ⟨n₁, F₁, r₁, h₁, total⟩ := sfm_total_l I hZF hω hF hr hi hj hs hsi
  obtain ⟨n₂, F₂, r₂, h₂, uniform⟩ := sfm_uniform_l I hZF hω hF hr hσω
    (uσ i (tu i (st i his))) (uσ j (tu j (st j hjs))) (uσ s (tu s ht.predecessor_mem))
    (uσ t hu.predecessor_mem) hσ.predecessor_mem hij hsi (fun e => ir i (e ▸ st i his))
    (fun e => ir j (e ▸ st j hjs)) (fun e => ir t (e ▸ ht.predecessor_mem))
    (fun e => ir s (e ▸ tu s ht.predecessor_mem)) (fun e => ir t (e ▸ hu.predecessor_mem)) hb (fun h => ir t (st t h))
  obtain ⟨f', hv, hfv⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs hD
  have hf' := (hE f').mpr hfv
  have hsD := (hv.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)
  have agree := hv.agree_l I (ir s)
  have source := (total X R E c f' D hX hm hE hf' hsD).mpr
    ((scollect_agree_l I hZF hF hb hr hi hj hE hf hf' agree (hX D hD) (fun _ h => h)).mp hh)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hq.1.1 hfv
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω H
  obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
  have hsD' := hfg s hs D D' hsD hDD
  have hHt := ZF.h_transitive_l I hZF hH
  have image := (hq.ssat_l I hZF.1 hm.1 hn.1 h₁.program h₁.root hE hK hf' ((hK g).mpr hg) hfg).mp source
  obtain ⟨B, C, hBH, hCH, hu⟩ := h_uniform_l hZFC hω hχ hωχ hH hDH
    ((total H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mp image)
  have image := (uniform H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mpr ⟨B, C, hBH, hCH, hu⟩
  have source := (hq.ssat_l I hZF.1 hm.1 hn.1 h₂.program h₂.root hE hK hf' ((hK g).mpr hg) hfg).mpr image
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := (uniform X R E c f' D hX hm hE hf' hsD).mp source
  exact ⟨B, C, hBX, hCX, hBC, fun x y hxy =>
    (sbin_agree_l I hZF hF hb hr hi hj hE hf hf' agree (hX D hD x (hBC.bound_l hxy).1)
      (hX C hCX y (hBC.bound_l hxy).2)).mpr (select x y hxy)⟩

end YesMetaZFC.SetTheory.Internal
