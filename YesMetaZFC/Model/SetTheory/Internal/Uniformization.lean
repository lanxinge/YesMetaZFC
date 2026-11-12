import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.CollectionCode
import YesMetaZFC.Model.SetTheory.Internal.SeparationHull
import YesMetaZFC.SetTheory.HereditaryClosure
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.HereditaryAlgebra

/-! # 全内部公式的统一函数图代码

把有序对成员条件与原公式合取，再要求所选图是 D 上、某个源内集合中的函数。
函数图坐标在原支撑之外，函数值和原公式的两个变量使用不同坐标。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Suniform_d (X R E F n r i j f D C B : M.Domain) : Prop := Fn0_d D C B ∧
  ∀ x y, Rd_entry_d x y B → Sbin_d I X R E F n r i j f x y

theorem sfm_uniform_l (hZF : M.Models ZF) {ω n F r i j s t u σ b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hj : M.mem j σ) (hs : M.mem s σ) (ht : M.mem t σ) (hu : M.mem u σ)
    (hij : i ≠ j) (hsi : s ≠ i) (hti : t ≠ i) (htj : t ≠ j) (hst : s ≠ t) (hus : u ≠ s) (hut : u ≠ t)
    (hb : Sbound_d I F b) (htb : ¬ M.mem t b) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I s D f →
      (Ssat_d I X R E G m k f ↔ ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f D C B) := by
  obtain ⟨m, G, k, build, read⟩ := sfm_uniform_raw_l I hZF hω hF hr hσ hi hj hs ht hu hij hsi hti htj hst hus hut hb htb
  refine ⟨m, G, k, build, fun X R E c f D hX hm hE hf hD => ?_⟩
  let N := smdl_structure_l I (R := R) hm.1.2.1
  let D₀ : N.Domain := ⟨D, ((hE f).mp hf).output_mem_of_pairMember hD⟩
  have ext := smem_ext_l I hm.1 hm.2 hX hZF.1
  have fn (B C : N.Domain) : Fn0_d D₀ C B ↔ Fn0_d D C.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases D₀ (Fin.cases C (fun _ => B)), fun _ => B⟩
    exact (fn0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm hX (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 ..))
  have entry (x y B : N.Domain) : Rd_entry_d x y B ↔ Rd_entry_d x.val y.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
    exact (rd_entry0_sat_l ext ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm hX (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l hZF.1 ..))
  rw [read X R E c f hm.1 D₀ ext hE hf hD]
  constructor
  · rintro ⟨B, C, hBC, truth⟩
    have ff := (fn B C).mp hBC
    refine ⟨B.val, C.val, B.property, C.property, ff, fun x y hxy => ?_⟩
    exact truth ⟨x, hX D D₀.property x (ff.bound_l hxy).1⟩ ⟨y, hX C.val C.property y (ff.bound_l hxy).2⟩
      ((entry _ _ B).mpr hxy)
  · rintro ⟨B, C, hB, hC, ff, truth⟩
    exact ⟨⟨B, hB⟩, ⟨C, hC⟩, (fn ⟨B, hB⟩ ⟨C, hC⟩).mpr ff,
      fun x y hxy => truth x.val y.val ((entry x y ⟨B, hB⟩).mp hxy)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 正则遗传小结构中的内部收集及其回拉

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

/-! ## 源模型中的实际统一见证函数

收集构造给出的函数图是 D×C 的子集，故它确实属于正则 H(χ)。
一般源之间的统一化回拉在 SourceCollection 中直接消费小定义域闭包。
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


end YesMetaZFC.SetTheory.Internal
