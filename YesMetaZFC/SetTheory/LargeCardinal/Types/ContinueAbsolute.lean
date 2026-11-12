import YesMetaZFC.SetTheory.LargeCardinal.Types.ImageSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CriticalPoint
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect

/-! # 相对类型像证书的实际读取

秩段、商、常值图和坍塌均读取原证书；源实例由工作模型的实际闭性构造。
只使用内层有限序列闭性与相对秩证书，毋须内层 ZF 或游戏特有的反射句子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω μ K₀ Z R₀ η C : M.Domain} (nc : Nonempty {x // M.mem x C}) {s}
  (ρ : Env (rt_model_l C nc) s)
  (o κ δ τ U D u X K R L F c d Y T j κ' U' D' u' : Term s)
local notation "v" => (fun (t : Term s) => Subtype.val (Definitional.Term.eval ρ t))

theorem ti_image_read_l (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K₀ Z R₀) (power : Sc_power_d Z)
    (hC : M.mem C Z) (rankC : Vr_d Z η C) (fs : Fs_read_d ω C)
    (hw : v o = ω) (hδ : M.IsLimitOrdinal (v δ)) (regular : Sc_regular_d Z (v δ))
    (valid : Formula.satisfies ρ (ti_image_m o κ δ τ U D u X K R L F c d Y T j κ' U' D' u')) :
    M.mem (v X) Z ∧ Vr_d Z (v δ) (v X) ∧ ∃ K₁, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (v κ) K₁ (v X) (v R) ∧
      M.mem (v L) (v δ) ∧ M.mem (v κ) (v L) ∧ M.mem (v τ) (v L) ∧
      It_local_d I ω (v X) (v R) (v κ) (v L) (v F) ∧ Sc_inaccessible_d ω (v X) (v L) ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω (v κ) (v L) (v X) (v F) ∧ Smem_d I (v c) (v X) (v R) ∧
      Smem_d I (v d) (v Y) (v T) ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω (v κ) (v L) (v F) (v c) (v d) (v j) ∧
      Wd_crit_d I (v X) (v j) (v κ) (v κ') ∧ M.MemberSubset (v L) (v κ') ∧ M.IsLimitOrdinal (v κ') ∧
      Rd_entry_d (v U) (v U') (v j) ∧ Rd_entry_d (v D) (v D') (v j) ∧ Rd_entry_d (v u) (v u') (v j) := by
  let N := rt_model_l C nc
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have Δ (φ : Formula 1 s) (hd : φ.IsDelta0) (h : Formula.satisfies ρ φ) :=
    (rt_model_delta_l fs.transitive nc hd ρ).mp h
  have smem (a A B : Term s) (h : Formula.satisfies ρ (smem_m (𝒞 := kpair_convention_l) a A B)) :
      Smem_d I (v a) (v A) (v B) :=
    (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair ..).mp ((smem_sat_l J ..).mp h)
  have entry (a b f : Term s) (h : Formula.satisfies ρ (rd_entry0_m a b f)) : Rd_entry_d (v a) (v b) (v f) := by
    simpa only [rd_entry0_sat_l hZF.1, @eval_image_env_l N M Subtype.val] using Δ _ (rd_entry0_delta_l ..) h
  simp only [ti_image_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨rank, _, hLδ, hκL, hτL, quality, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩ := valid
  have rank := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ δ X).mp rank
  have mx := smem c X R mx
  have my := smem d Y T my
  have hXZ := owner.transitive C hC (v X) (X.eval ρ).property
  have full := Vr_d.of_rank_l owner.transitive hC rankC (X.eval ρ).property rank
  have trans := full.transitive_l owner.transitive hXZ
  have quality := Δ _ (ex_quality_delta_l ..) quality
  simp only [ex_quality_m, Formula.satisfies_conj_iff] at quality
  obtain ⟨loc, card, strong⟩ := quality
  have loc := (ex_local_sat_l I (R := v R) _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)
    (by simpa only [@eval_image_env_l N M Subtype.val] using (show ∃ a, Smem_d I a (v X) (v R) from ⟨_, mx⟩))).mp loc
  have card := (ex_inaccessible_sat_l _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)).mp card
  simp only [@eval_image_env_l N M Subtype.val, hw] at loc card
  have ord := (loc.ordinals_l (ZF.modelsKP hZF) trans ⟨_, mx⟩).1
  have localCopy := loc
  obtain ⟨hωX, hκX, _, _, pre⟩ := (it_local_mem_l I ⟨_, mx⟩).mp localCopy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω (v κ) := ord.transitive ω pre.1.2.2.1
  obtain ⟨K₁, source⟩ := owner.rank_l hZF hXZ full hδ regular hωX mx hκX ord below
  have strong := (ex_strength_sat_l (ZF.modelsKP hZF) (K₀ := K₁) (R := v R) _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val, hw] using source)).mp strong
  simp only [@eval_image_env_l N M Subtype.val, hw] at strong
  obtain ⟨P, hP, subsets⟩ := power.rank_l owner.transitive hXZ full hδ K₁ source.finite.mem_l
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory (source.finite_l (ZF.modelsKP hZF)) hP subsets)
  have actual := it_ultra_read_l hZFC fs nc ρ o κ L F c d j hw source mx family (loc.coherent_l hZF (source.read_source_l hZF) source.code) ultra
  have critical := (wd_crit_sat_l J ext ρ X j κ κ').mp critical
  have image := (rt_entry_l fs.transitive nc hZF.1 ..).mp critical.image
  have crit := actual.critical_l hZF source family source (fun _ _ _ _ _ _ => Iff.rfl) loc hκL mx my image
  have bound : M.MemberSubset (v L) (v κ') := by
    have bound := (Formula.satisfies_subset_iff ..).mp (Δ _ (.atom ..) bound)
    simpa only [Structure.MemberSubset, @eval_image_env_l N M Subtype.val] using bound
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  exact ⟨hXZ, full, K₁, source, hLδ, hκL, hτL, loc, card, strong, mx, my, actual, crit, bound, limit,
    entry U U' j hU, entry D D' j hD, entry u u' j hu⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在给定所属模型内还原反射的单步证书

反射层是该模型自己的实际 Vη。较低的 Vδ 因秩覆盖而绝对，正则性提供
真实源实例；随后恢复原证书的同一商、常值图与超幂。这里不假定该模型
在外部传递或可数闭，定理可直接实例化到原关系结构。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际极限秩层中的武丁判断给出所属模型的正则性；两类游戏共用此读取。 -/
theorem ti_woodin_regular_l (hKP : M.Models KP) {w η C : M.Domain}
    (rank : V_d (kp_pair_l hKP) η C) (limit : M.IsLimitOrdinal η)
    (fs : Fs_read_d w C) (nc : Nonempty {x // M.mem x C}) {n}
    (ρ : Env (rt_model_l C nc) n) (δ : Term n)
    (valid : Formula.satisfies ρ (woodin_m (𝒞 := kpair_convention_l) δ)) :
    M.IsRegularCardinal (kp_pair_l hKP) (δ.eval ρ).val := by
  let J := rt_pair_l fs.transitive nc hKP.1 fs.pair
  have ext := rt_model_ext_l hKP.1 fs.transitive nc
  obtain ⟨a, _, _, below, regular, strong, _⟩ :=
    (woodin_sat_l J ext ρ δ).mp valid
  let θ : Env (rt_model_l C nc) 2 := ⟨Fin.cases (δ.eval ρ) (fun _ => a), fun _ => a⟩
  have card : Formula.satisfies θ (sc_inaccessible_m (.bound 1) .newest) := by
    simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_isRegularCardinal_iff J ext, Formula.satisfies_isStrongLimitCardinal_iff J ext]
    exact ⟨below, regular, strong⟩
  exact (sc_v_inaccessible_up_l hKP limit rank
    ((sc_inaccessible_sat_l hKP.1 fs.transitive fs.pair nc θ (.bound 1) .newest).mp card)).2.1

theorem ti_image_absolute_l {ω η C : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d I η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) {s} (ρ : Env (rt_model_l C nc) s)
    (o κ δ τ U D u X K R L F c d Y T j κ' U' D' u' : Term s)
    (hw : (o.eval ρ).val = ω) (regular : M.IsRegularCardinal I (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (ti_image_m o κ δ τ U D u X K R L F c d Y T j κ' U' D' u')) :
    V_d I (δ.eval ρ).val (X.eval ρ).val ∧
    ∃ K₁, Ep_source_d I ω (κ.eval ρ).val K₁ (X.eval ρ).val (R.eval ρ).val ∧
      M.mem (L.eval ρ).val (δ.eval ρ).val ∧ M.mem (κ.eval ρ).val (L.eval ρ).val ∧ M.mem (τ.eval ρ).val (L.eval ρ).val ∧
      It_local_d I ω (X.eval ρ).val (R.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val ∧
      Sc_inaccessible_d ω (X.eval ρ).val (L.eval ρ).val ∧
      Ex_strength_d I ω (κ.eval ρ).val (L.eval ρ).val (X.eval ρ).val (F.eval ρ).val ∧
      Smem_d I (c.eval ρ).val (X.eval ρ).val (R.eval ρ).val ∧ Smem_d I (d.eval ρ).val (Y.eval ρ).val (T.eval ρ).val ∧
      It_ultra_d I ω (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val (c.eval ρ).val (d.eval ρ).val (j.eval ρ).val ∧
      Wd_crit_d I (X.eval ρ).val (j.eval ρ).val (κ.eval ρ).val (κ'.eval ρ).val ∧
      M.MemberSubset (L.eval ρ).val (κ'.eval ρ).val ∧ M.IsLimitOrdinal (κ'.eval ρ).val ∧
      Rd_entry_d (U.eval ρ).val (U'.eval ρ).val (j.eval ρ).val ∧
      Rd_entry_d (D.eval ρ).val (D'.eval ρ).val (j.eval ρ).val ∧
      Rd_entry_d (u.eval ρ).val (u'.eval ρ).val (j.eval ρ).val := by
  let N := rt_model_l C nc
  let v (t : Term s) := (t.eval ρ).val
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have Δ (φ : Formula 1 s) (hd : φ.IsDelta0) (h : Formula.satisfies ρ φ) :=
    (rt_model_delta_l fs.transitive nc hd ρ).mp h
  have smem (a A B : Term s) (h : Formula.satisfies ρ (smem_m (𝒞 := kpair_convention_l) a A B)) :
      Smem_d I (v a) (v A) (v B) :=
    (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair ..).mp ((smem_sat_l J ..).mp h)
  have entry (a b f : Term s) (h : Formula.satisfies ρ (rd_entry0_m a b f)) : Rd_entry_d (v a) (v b) (v f) := by
    simpa only [rd_entry0_sat_l hZF.1, @eval_image_env_l N M Subtype.val] using Δ _ (rd_entry0_delta_l ..) h
  simp only [ti_image_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at valid
  obtain ⟨relative, _, hLδ, hκL, hτL, quality, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩ := valid
  have relative := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ δ X).mp relative
  have hδη := ZF.v_ordinal_height_l hZF rankC regular.isCardinal.1 (δ.eval ρ).property
  obtain ⟨A, rankA⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
  have hAC := ZF.v_mem_l I hZF rankA rankC hδη
  have eq := vr_agree_l hZF fs.transitive (X.eval ρ).property rankA (fs.transitive A hAC) relative
  have rank : V_d I (v δ) (v X) := by
    change V_d I (δ.eval ρ).val (X.eval ρ).val
    rw [eq]
    exact rankA
  have mx := smem c X R mx
  have my := smem d Y T my
  have trans := v_transitive_l I rank
  have quality := Δ _ (ex_quality_delta_l ..) quality
  simp only [ex_quality_m, Formula.satisfies_conj_iff] at quality
  obtain ⟨loc, card, strong⟩ := quality
  have loc := (ex_local_sat_l I (R := v R) _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)
    (by simpa only [@eval_image_env_l N M Subtype.val] using (show ∃ a, Smem_d I a (v X) (v R) from ⟨_, mx⟩))).mp loc
  have card := (ex_inaccessible_sat_l _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val] using trans)).mp card
  simp only [@eval_image_env_l N M Subtype.val, hw] at loc card
  have ord := (loc.ordinals_l (ZF.modelsKP hZF) trans ⟨_, mx⟩).1
  have localCopy := loc
  obtain ⟨hωX, _, _, _, pre⟩ := (it_local_mem_l I ⟨_, mx⟩).mp localCopy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω (v κ) := ord.transitive ω pre.1.2.2.1
  obtain ⟨K₁, seq⟩ := ZF.fseq_space_exists_l I hZF hω (v κ)
  obtain ⟨R₁, source⟩ := ep_regular_source_l hZFC hω
    (ZF.v_ordinal_height_l hZF rank (hω.isOrdinal (ZF.modelsKP hZF)) hωX) regular rank
    (regular.isLimitOrdinal.1.transitive (v L) hLδ (v κ) hκL) below seq
  obtain ⟨a₁, model⟩ := source.code
  have source : Ep_source_d I ω (v κ) K₁ (v X) (v R) := (smem_unique_l I hZF.1 model mx).2 ▸ source
  have strong := (ex_strength_sat_l (ZF.modelsKP hZF) (K₀ := K₁) (R := v R) _ _ _ _ _ _
    (by simpa only [@eval_image_env_l N M Subtype.val, hw] using source)).mp strong
  simp only [@eval_image_env_l N M Subtype.val, hw] at strong
  obtain ⟨P, power⟩ := ZF.exists_powerSet hZF K₁
  have hP := v_power_mem_l I rank regular.isLimitOrdinal source.finite.mem_l power
  have subsets : FilterZF.Source_d (v X) K₁ P := fun A => (power A).trans
    ⟨fun sub => ⟨v_subset_mem_l I rank source.finite.mem_l sub, sub⟩, And.right⟩
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory (source.finite_l (ZF.modelsKP hZF)) hP subsets)
  have actual := it_ultra_read_l hZFC fs nc ρ o κ L F c d j hw source mx family
    (loc.coherent_l hZF (source.read_source_l hZF) source.code) ultra
  have critical := (wd_crit_sat_l J ext ρ X j κ κ').mp critical
  have image := (rt_entry_l fs.transitive nc hZF.1 ..).mp critical.image
  have crit := actual.critical_l hZF source family source (fun _ _ _ _ _ _ => Iff.rfl) loc hκL mx my image
  have bound : M.MemberSubset (v L) (v κ') := by
    simpa only [Structure.MemberSubset, @eval_image_env_l N M Subtype.val] using
      (Formula.satisfies_subset_iff ..).mp (Δ _ (.atom ..) bound)
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  exact ⟨rank, K₁, source, hLδ, hκL, hτL, loc, card, strong, mx, my, actual, crit, bound, limit,
    entry U U' j hU, entry D D' j hD, entry u u' j hu⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次继续选择在所属模型中的完整证书

还原反射层选出的同一扩展器、超幂及三个类型像，并保留 χ∈L、
完整查询池和原 subtype 查询。只有源的有限列空间重新构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tc_image_absolute_l {ω η C : M.Domain}
    (hω : M.IsOmega ω) (rankC : V_d I η C) (fs : Fs_read_d ω C)
    (nc : Nonempty {x // M.mem x C}) {s} (ρ : Env (rt_model_l C nc) s)
    (o κ δ n U D u τ m w b z χ : Term s) (σ : Fin 7 → Term s)
    (hw : (o.eval ρ).val = ω) (regular : M.IsRegularCardinal I (δ.eval ρ).val)
    (valid : Formula.satisfies ρ (tc_image_m o κ δ n U D u τ m w b z χ σ)) :
    Formula.satisfies (image_env_l (M := rt_model_l C nc) (N := M) Subtype.val ρ)
      (tc_image_m o κ δ n U D u τ m w b z χ σ) := by
  simp only [tc_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at valid
  obtain ⟨X, K', R, L, F, c, d, Y, T, j, κ', U', D', u', core, high, pool, subtype⟩ := valid
  let ε := ρ.push X |>.push K' |>.push R |>.push L |>.push F |>.push c |>.push d |>.push Y
    |>.push T |>.push j |>.push κ' |>.push U' |>.push D' |>.push u'
  let a (t : Term s) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term (s + 14) := .bound ⟨i.val, by omega⟩
  obtain ⟨rank, K₀, source, hLδ, hκL, hτL, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu⟩ :=
    ti_image_absolute_l hZFC hω rankC fs nc ε (a o) (a κ) (a δ) (a τ) (a U) (a D) (a u)
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using regular) core
  simp only [ε, a, Definitional.Term.eval_weaken] at rank source hLδ hκL hτL loc card strong mx my ultra crit bound limit hU hD hu
  obtain ⟨A, E, _, _, names, seq, product⟩ :=
    (fs.pool_sat_l (ZF.modelsKP hZF) nc ε (a o) (a n) (t 2) (t 1)
      (by simpa only [ε, a, Definitional.Term.eval_weaken] using hw)).mp pool
  simp only [ε, a, Definitional.Term.eval_weaken] at names seq product
  have subtype := ts_subtype_source_l (ZF.modelsKP hZF) fs.transitive nc _ _ _ _ _ _ _ _ _ _ _ _ subtype
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hw] at subtype
  have eta (f : Fin 7 → Term (s + 14)) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [eta (fun i => a (σ i)), a, Definitional.Term.eval_weaken] at subtype
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at high
  apply (tc_image_sat_l (ZF.modelsKP hZF) _ o κ δ n U D u τ m w b z χ σ).mpr
  simp only [@eval_image_env_l (rt_model_l C nc) M Subtype.val, hw]
  exact ⟨X.val, K₀, R.val, L.val, F.val, c.val, d.val, Y.val, T.val, j.val, κ'.val, U'.val, D'.val, u'.val,
    ⟨rank, source, hLδ, hκL, hτL, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu⟩,
    high, ⟨A, E, names, seq, product⟩, subtype⟩

end YesMetaZFC.SetTheory.LargeCardinal
