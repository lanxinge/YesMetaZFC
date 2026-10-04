import YesMetaZFC.Model.SetTheory.Internal.CollectionCode
import YesMetaZFC.Model.SetTheory.Internal.Separation
import YesMetaZFC.SetTheory.HereditaryClosure
import YesMetaZFC.SetTheory.DependentChoice

/-! # 正则遗传小结构中的内部收集及其回拉

背景选择给出真实逐点见证函数；值域由定义域的小基数界控制，正则 H(χ) 的
小集合封闭性使它属于目标。收集实例代码再把这一实际集合回拉到源结构。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem h_collect_function_l (hZFC : M.Models ZFC) {ω χ H R E F n r i j f D} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H) (hD : M.mem D H)
    (hh : Scollect_d I H R E F n r i j f D H) : ∃ C q, M.mem C H ∧ M.IsSetFunctionFromTo I q D C ∧
      ∀ x y, M.PairMember I x y q → Sbin_d I H R E F n r i j f x y := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases j (Fin.cases i (Fin.cases r (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => H)))))))), fun _ => H⟩
  let φ : BinarySchema 9 := {
    body := sbin_m (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x y : φ.denote ρ x y ↔ Sbin_d I H R E F n r i j f x y := sbin_sat_l I hZF.1 ..
  obtain ⟨q, hq, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := D) (Y := H)
    (fun x hx => (hh x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hq.1 hq.2.1
  have range : M.IsSetFunctionFromTo I q D C := ⟨hq.1, hq.2.1, fun x hx => by
    obtain ⟨y, _, hxy⟩ := hq.2.2 x hx
    exact ⟨y, (hC y).mpr ⟨x, hxy⟩, hxy⟩⟩
  obtain ⟨μ, hμ, hDμ⟩ := ZF.hmem_size_l I hZF ((hH D).mp hD)
  have hCμ := ZF.ordinal_image_bound_l I hZF (hχ.isCardinal.1.mem hμ) hDμ range
    (fun y hy => ((hC y).mp hy).imp fun x hx => ⟨hq.input_mem_of_pairMember hx, hx⟩)
  have hCH : M.MemberSubset C H := fun y hy => ((hC y).mp hy).elim fun _ hx => hq.output_mem_of_pairMember hx
  exact ⟨C, q, ZFC.h_small_closed_l I hZFC hω hχ hωχ hH hCH hμ hCμ, range,
    fun x y hxy => (sat x y).mp (select x y hxy)⟩

/-- 收集所得集合属于传递源，背景见证函数没有被当成源中的函数。 -/
theorem smap_collection_l (hZFC : M.Models ZFC) {ω χ c d X R H S q E F n r i j f D}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hf : M.mem f E) (hD : M.mem D X)
    (hh : Scollect_d I X R E F n r i j f D X) : ∃ C, M.mem C X ∧ Scollect_d I X R E F n r i j f D C := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, htj, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hj
  obtain ⟨n₁, F₁, r₁, h₁, total⟩ := sfm_total_l I hZF hω hF hr hi hj hs hsi
  obtain ⟨n₂, F₂, r₂, h₂, collect⟩ := sfm_collect_l I hZF hω hF hr hi hj hs ht hsi hti htj hst hb htb
  obtain ⟨f', hu, hfu⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs hD
  have hf' := (hE f').mpr hfu
  have hsD := (hu.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)
  have source := (total X R E c f' D hX hm hE hf' hsD).mpr
    ((scollect_agree_l I hZF hF hb hr hi hj hE hf hf' (hu.agree_l I hsb) (hX D hD) (fun _ h => h)).mp hh)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hq.1.1 hfu
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω H
  obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
  have hsD' := hfg s hs D D' hsD hDD
  have hHt := ZF.h_transitive_l I hZF hH
  have image := (hq.ssat_l I hZF.1 hm.1 hn.1 h₁.program h₁.root hE hK hf' ((hK g).mpr hg) hfg).mp source
  obtain ⟨B, p, hBH, hp, select⟩ := h_collect_function_l I hZFC hω hχ hωχ hH hDH
    ((total H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mp image)
  have hB : Scollect_d I H S K F n r i j g D' B := fun x hx =>
    (hp.2.2 x hx).imp fun y hy => ⟨hy.1, select x y hy.2⟩
  have image := (collect H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mpr ⟨B, hBH, hB⟩
  have source := (hq.ssat_l I hZF.1 hm.1 hn.1 h₂.program h₂.root hE hK hf' ((hK g).mpr hg) hfg).mpr image
  obtain ⟨C, hCX, hC⟩ := (collect X R E c f' D hX hm hE hf' hsD).mp source
  exact ⟨C, hCX, (scollect_agree_l I hZF hF hb hr hi hj hE hf hf' (hu.agree_l I hsb)
    (hX D hD) (hX C hCX)).mpr hC⟩

end YesMetaZFC.SetTheory.Internal
