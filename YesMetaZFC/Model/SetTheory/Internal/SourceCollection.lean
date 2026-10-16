import YesMetaZFC.Model.SetTheory.Internal.RelationCollection
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 小定义域上的全内部统一化

仅在源内单射可控制的定义域上收集见证。正则 Hχ 与正则极限 Vδ
分别由遗传大小闭包和共尾度秩界给出实例；不要求强极限。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

section Pull
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_uniform_l {ω c d X R H S q E F n r i j f D} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hHt : M.TransitiveSet H)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E) (hD : M.mem D X)
    (small : Sc_small_d X D) (target : Sc_collection_d I ω H S)
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
  have image := (hq.ssat_l I hZF.1 hm.1 hn.1 h₁.program h₁.root hE hK hf' ((hK g).mpr hg) hfg).mp source
  obtain ⟨B, C, hBH, hCH, hu⟩ := target D' hDH
    ((hq.small_l hZF hω hX hHt hm hn hDD).mp small) K F n r i j g D'
    hK hF hr hi hj hij ((hK g).mpr hg) hDH (fun _ h => h)
    ((total H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mp image)
  have image := (uniform H S K d g D' hHt hn hK ((hK g).mpr hg) hsD').mpr ⟨B, C, hBH, hCH, hu⟩
  have source := (hq.ssat_l I hZF.1 hm.1 hn.1 h₂.program h₂.root hE hK hf' ((hK g).mpr hg) hfg).mpr image
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := (uniform X R E c f' D hX hm hE hf' hsD).mp source
  exact ⟨B, C, hBX, hCX, hBC, fun x y hxy =>
    (sbin_agree_l I hZF hF hb hr hi hj hE hf hf' agree (hX D hD x (hBC.bound_l hxy).1)
      (hX C hCX y (hBC.bound_l hxy).2)).mpr (select x y hxy)⟩

/-- 小定义域的源内编号随图传输，目标统一函数的存在性再回拉。 -/
theorem Sc_collection_d.pull_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (h : Sc_collection_d I ω Y S) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_collection_d I ω X R := by
  intro D _ small E F n r i j f A hE hF hr hi hj hij hf hA hAD total
  exact smap_uniform_l hZF hω hX hY hm hn hq hE hF hr hi hj hij hf hA (small.mono_l hAD) h total
end Pull


theorem sc_h_collection_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) (R : M.Domain) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA _ => h_uniform_l hZFC hω hχ hωχ hH hA

theorem sc_v_collection_l (hZFC : M.Models ZFC) {δ V : M.Domain}
    (hδ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V) (ω R : M.Domain) :
    Sc_collection_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro D _ small E F n r i j f A _ _ _ _ _ _ _ hA hAD total
  obtain ⟨μ, e, hμ, _, index⟩ := small.mono_l hAD
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases j (Fin.cases i (Fin.cases r (Fin.cases n
    (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => V)))))))), fun _ => V⟩
  let φ : BinarySchema 9 := {
    body := sbin_m (𝒞 := kpair_convention_l) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat x y : φ.denote ρ x y ↔ Sbin_d I V R E F n r i j f x y := sbin_sat_l I hZF.1 ..
  obtain ⟨q, hq, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := A) (Y := V)
    (fun x hx => (total x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  obtain ⟨C, hC, hf, hqV⟩ := ZF.v_small_function_l hZF hδ
    (ZF.v_ordinal_height_l hZF hV index.ordinal hμ) (index.bound_l (ZF.modelsKP hZF)) hA hV hq
  exact ⟨q, C, hqV, hC, fn0_of_function_l (ZF.modelsKP hZF) hf, fun x y hxy => (sat x y).mp (select x y hxy)⟩

theorem sc_collection_forward_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (source : Sc_collection_d I ω X R) {K F n r i j g D : M.Domain}
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K) (hD : M.mem D Y)
    (small : Sc_small_d Y D) (total : Scollect_d I Y S K F n r i j g D Y) :
    ∃ B C, M.mem B Y ∧ M.mem C Y ∧ Suniform_d I Y S K F n r i j g D C B := by
  let N := smdl_structure_l I (R := S) hn.1.2.1
  let D₀ : N.Domain := ⟨D, hD⟩
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  let μ₀ : N.Domain := ⟨μ, hμ⟩
  let e₀ : N.Domain := ⟨e, he⟩
  let ρ : Env N 3 := ⟨Fin.cases μ₀ (Fin.cases D₀ (fun _ => e₀)), fun _ => D₀⟩
  have guard : Formula.satisfies ρ (sc_index_m .newest (.bound 1) (.bound 2)) :=
    (smem_delta_image_l I hn hY (sc_index_delta_l ..) ρ).mpr ((sc_index_sat_l (ZF.modelsKP hZF) ..).mpr idx)
  have ext := smem_ext_l I hn.1 hn.2 hY hZF.1
  obtain ⟨B, C, fn, truth⟩ := sc_collection_raw_l I hZF hω hX hm hn.1 ext hq source hK hF hr hi hj hij hg D₀ μ₀ e₀ guard
    (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := total x.val ((hn.2 x.val D).mp hx).2.2
      exact ⟨⟨y, hy⟩, hxy⟩)
  let η : Env N 3 := ⟨Fin.cases D₀ (Fin.cases C (fun _ => B)), fun _ => B⟩
  have ff : Fn0_d D C.val B.val := (fn0_sat_l hZF.1 ..).mp
    ((smem_delta_image_l I hn hY (fn0_delta_l ..) η).mp ((fn0_sat_l ext η .newest (.bound 1) (.bound 2)).mpr fn))
  refine ⟨B.val, C.val, B.property, C.property, ff, fun x y hxy => ?_⟩
  let x₀ : N.Domain := ⟨x, hY D hD x (ff.bound_l hxy).1⟩
  let y₀ : N.Domain := ⟨y, hY C.val C.property y (ff.bound_l hxy).2⟩
  let θ : Env N 3 := ⟨Fin.cases x₀ (Fin.cases y₀ (fun _ => B)), fun _ => B⟩
  exact truth x₀ y₀ ((rd_entry0_sat_l ext θ .newest (.bound 1) (.bound 2)).mp
    ((smem_delta_image_l I hn hY (rd_entry0_delta_l ..) θ).mpr ((rd_entry0_sat_l hZF.1 ..).mpr hxy)))

/-- 守卫本身是内部公式；传输覆盖新模型中的全部小集合及全部公式参数。 -/
theorem Sc_collection_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (source : Sc_collection_d I ω X R) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q) : Sc_collection_d I ω Y S := by
  intro D _ small E F n r i j f A hE hF hr hi hj hij hf hA hAD total
  exact sc_collection_forward_l I hZF hω hX hY hm hn hq source hE hF hr hi hj hij hf hA (small.mono_l hAD) total

end YesMetaZFC.SetTheory.Internal
