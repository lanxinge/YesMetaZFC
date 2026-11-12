import YesMetaZFC.Model.SetTheory.Relations.Separation
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Embedding.ElementaryTrace
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 任意内部公式的分离实例代码

给原程序追加 x∈A ↔ (x∈D ∧ φ)，再量化 x 和 A。A 使用真实支撑外坐标，
有限支撑真值定理保证这一新参数不捕获原公式；最后的规格是实际集合的成员方程。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ssep_d (X R E F n r i f D A : M.Domain) : Prop := ∀ x, M.mem x A ↔ M.mem x D ∧
  ∃ g, Senv_update_d I f i x g ∧ Ssat_d I X R E F n r g

/-- 传递隶属结构中的分离集读取是原关系方程的特例。 -/
theorem ssep_relation_l {c X R E F n r i f D A : M.Domain} (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hD : M.mem D X) (hA : M.mem A X) :
    Sr_sep_d I X R E F n r i f D A ↔ Ssep_d I X R E F n r i f D A := by
  have mem x y (hx : M.mem x X) (hy : M.mem y X) : M.PairMember I x y R ↔ M.mem x y :=
    (hm.2 x y).trans ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩
  constructor
  · intro h x
    constructor
    · intro ha
      have hx := hX A hA x ha
      obtain ⟨hd, hs⟩ := (h x hx).mp ((mem x A hx hA).mpr ha)
      exact ⟨(mem x D hx hD).mp hd, hs⟩
    · rintro ⟨hd, hs⟩
      have hx := hX D hD x hd
      exact (mem x A hx hA).mp ((h x hx).mpr ⟨(mem x D hx hD).mpr hd, hs⟩)
  · exact fun h x hx => (mem x A hx hA).trans ((h x).trans (and_congr (mem x D hx hD).symm Iff.rfl))

theorem ssep_agree_l (hZF : M.Models ZF) {ω X R E F n r i f g b D A}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n) (hi : M.mem i ω)
    (hE : M.IsFunctionSpace I E ω X) (hf : M.mem f E) (hg : M.mem g E)
    (ha : Senv_agree_d I b f g) (hD : M.MemberSubset D X) :
    Ssep_d I X R E F n r i f D A ↔ Ssep_d I X R E F n r i g D A := by
  have transfer {f g} (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g)
      x (hx : M.mem x D) : (∃ v, Senv_update_d I f i x v ∧ Ssat_d I X R E F n r v) →
        ∃ w, Senv_update_d I g i x w ∧ Ssat_d I X R E F n r w := by
    rintro ⟨v, hv, ht⟩
    obtain ⟨w, hw, hwE⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi (hD x hx)
    exact ⟨w, hw, (ssat_agree_l I hZF hF hb hE hr
      ((hE v).mpr (hv.function_l I ((hE f).mp hf) hi (hD x hx))) ((hE w).mpr hwE)
      (ha.update_l I hv hw)).mp ht⟩
  exact forall_congr' fun x => iff_congr Iff.rfl (and_congr_right fun hx =>
    ⟨transfer hf hg ha x hx, transfer hg hf (ha.symm_l I) x hx⟩)

/-- 检查指定 A 的分离方程；A、D 是赋值中的参数。 -/
theorem sfm_sep_test_l (hZF : M.Models ZF) {ω n F r i s t} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) : ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D A,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → M.PairMember I t A f →
      (Ssat_d I X R E G m k f ↔ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨m, G, k, build, read⟩ := sfm_sep_test_raw_l I hZF hω hF hr hi hs ht hsi hti
  exact ⟨m, G, k, build, fun X R E c f D A hX hm hE hf hD hA =>
    (read X R E f D A hE hf hD hA).trans (ssep_relation_l I hX hm
      (((hE f).mp hf).output_mem_of_pairMember hD) (((hE f).mp hf).output_mem_of_pairMember hA))⟩

theorem sfm_sep_l (hZF : M.Models ZF) {ω n F r i s t b} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hs : M.mem s ω) (ht : M.mem t ω)
    (hsi : s ≠ i) (hti : t ≠ i) (hst : s ≠ t) (hb : Sbound_d I F b) (htb : ¬ M.mem t b) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ ∀ X R E c f D,
      M.TransitiveSet X → Smem_d I c X R → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I s D f → (Ssat_d I X R E G m k f ↔ ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A) := by
  obtain ⟨m, G, k, build, read⟩ := sfm_sep_raw_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  refine ⟨m, G, k, build, fun X R E c f D hX hm hE hf hD => ?_⟩
  exact (read X R E f D hE hf hD).trans (exists_congr fun A => and_congr_right fun hA =>
    ssep_relation_l I hX hm (((hE f).mp hf).output_mem_of_pairMember hD) hA)

end YesMetaZFC.SetTheory.Internal

/-! ## 完整初等嵌入回拉内部公式的实际分离集

目标容纳像集合的全部子集，故背景分离所得集合确实属于目标。
随后传输已经构造的分离实例代码，所得见证真正落在源中。公式与参数赋值均可内部非标准。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssep_exists_l (hZF : M.Models ZF) (X R E F n r i f D : M.Domain) :
    ∃ A, Ssep_d I X R E F n r i f D A := by
  let ρ : Env M 8 := ⟨Fin.cases f (Fin.cases i (Fin.cases r (Fin.cases n (Fin.cases F
    (Fin.cases E (Fin.cases R (fun _ => X))))))), fun _ => X⟩
  let φ : UnarySchema 8 := {
    body := .existsE (.conj (senv_update_m (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 1) .newest)
      (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest)) }
  obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ D
  refine ⟨A, fun x => (hA x).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    senv_update_sat_l I hZF.1, ssat_sat_l I hZF.1]
  rfl

/-- 一个内部自然数同时界住全部程序坐标和两个指定变量。 -/
theorem sbound_above_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j ω) :
    ∃ s, M.mem s ω ∧ Sbound_d I F s ∧ M.mem i s ∧ M.mem j s := by
  obtain ⟨b, hb, hB⟩ := sbound_exists_l I hZF hω hF
  have upper {b i} (hb : M.mem b ω) (hi : M.mem i ω) : ∃ s, M.mem s ω ∧ M.mem i s ∧ M.MemberSubset b s := by
    obtain ⟨v, hv, hvω⟩ := hω.1.2 i hi
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare b hb i hi with he | hbi | hib
    · exact ⟨v, hvω, hv.predecessor_mem, fun x hx => (hv x).mpr (Or.inl ((he x).mp hx))⟩
    · exact ⟨v, hvω, hv.predecessor_mem, fun x hx => (hv x).mpr
        (Or.inl ((hω.members_areOrdinals (ZF.modelsKP hZF) i hi).transitive b hbi x hx))⟩
    · exact ⟨b, hb, hib, fun _ h => h⟩
  obtain ⟨v, hv, hiv, hbv⟩ := upper hb hi
  obtain ⟨s, hs, hjs, hvs⟩ := upper hv hj
  have hbs : M.MemberSubset b s := fun x hx => hvs x (hbv x hx)
  exact ⟨s, hs, fun r i j h => ⟨hbs i (hB r i j h).1, hbs j (hB r i j h).2⟩, hvs i hiv, hjs⟩

/-- 上界本身和它的后继提供两个实际支撑外坐标。 -/
theorem sbound_fresh_l (hZF : M.Models ZF) {ω n F i j} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hi : M.mem i ω) (hj : M.mem j ω) : ∃ b s t, Sbound_d I F b ∧ M.mem s ω ∧ M.mem t ω ∧
      s ≠ i ∧ t ≠ i ∧ s ≠ j ∧ t ≠ j ∧ s ≠ t ∧ ¬ M.mem s b ∧ ¬ M.mem t b := by
  obtain ⟨s, hs, hB, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨t, ht, htω⟩ := hω.1.2 s hs
  have hst : M.MemberSubset s t := fun x hx => (ht x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  exact ⟨s, s, t, hB, hs, htω, (fun he => ir i (he ▸ his)),
    (fun he => ir i (he ▸ hst i his)), (fun he => ir j (he ▸ hjs)), (fun he => ir j (he ▸ hst j hjs)),
    (fun he => ir t (he ▸ ht.predecessor_mem)),
    ir s, fun h => ir t (hst t h)⟩

/-- 只需像集合的实际幂集包含于目标，不要求整个目标是 V 层或满足 ZF。 -/
theorem smap_separation_l (hZF : M.Models ZF) {ω c d X R Y S j E F n r i f D D' P}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hP : M.IsPowerSetOf P D') (hPY : M.MemberSubset P Y)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω)
    (hf : M.mem f E) (hD : M.PairMember I D D' j) : ∃ A, M.mem A X ∧ Ssep_d I X R E F n r i f D A := by
  have hDX := hj.1.1.input_mem_of_pairMember hD
  obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
  obtain ⟨m, G, k, hG, code⟩ := sfm_sep_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
  obtain ⟨f', hu, hfu⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs hDX
  have hf' := (hE f').mpr hfu
  have hsD := (hu.2 s D).mpr (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hj.1.1 hfu
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨B, hB⟩ := ssep_exists_l I hZF Y S K F n r i g D'
  have hBY := hPY B ((hP B).mpr fun x hx => ((hB x).mp hx).1)
  have truth := (code Y S K d g D' hY hn hK ((hK g).mpr hg) (hfg s hs D D' hsD hD)).mpr ⟨B, hBY, hB⟩
  have source := (hj.ssat_l I hZF.1 hm.1 hn.1 hG.program hG.root hE hK hf' ((hK g).mpr hg) hfg).mpr truth
  obtain ⟨A, hAX, hA⟩ := (code X R E c f' D hX hm hE hf' hsD).mp source
  exact ⟨A, hAX, (ssep_agree_l I hZF hF hb hr hi hE hf hf' (hu.agree_l I hsb) (hX D hDX)).mpr hA⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 可数传递模型中的全内部代码分离

从极限 V 层与可数种子自动构造传递坍塌，保留种子的原像，再沿实际初等嵌入
回拉全部内部公式的分离集。可数壳需要 ZFC；分离回拉本身保留 ZF 强度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem v_separation_hull_l (hZFC : M.Models ZFC) {ω δ Y A} (hω : M.IsOmega ω)
    (hδ : M.IsLimitOrdinal δ) (hY : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ Y)
    (hA : M.MemberSubset A Y)
    (hc : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) A ω) :
    let I := kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))
    ∃ B c R d S j, M.TransitiveSet B ∧ M.CardinalLessOrEqual I B ω ∧
      Smem_d I c Y R ∧ Smem_d I d B S ∧ Smap_d I ω d c B Y j ∧
      (∀ x, M.mem x A → ∃ b, M.mem b B ∧ M.PairMember I b x j) ∧
      ∀ E F n r i f D, M.IsFunctionSpace I E ω B → Sfm_d I ω n F → M.mem r n → M.mem i ω →
        M.mem f E → M.mem D B → ∃ C, M.mem C B ∧ Ssep_d I B S E F n r i f D C := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨a, ha⟩ := hδ.2.1
  obtain ⟨c, R, hm, hR⟩ := smdl_membership_l I hZF ⟨a, ZF.v_ordinal_mem_l I hZF hY ha⟩
  have hYt := v_transitive_l I hY
  obtain ⟨X, e, T, B, F, j, d, S, _, hAX, _, _, hB, hf, hb, hp, hs, hj⟩ :=
    selem_hull_collapse_l hZFC hω hYt ⟨hm, hR⟩ hA hc
  refine ⟨B, c, R, d, S, j, hB, hb, ⟨hm, hR⟩, hs, hj, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, hf⟩ := hf.function.2.1 x (hAX x hx)
    exact ⟨b, hb, (hp x b).mpr hf⟩
  · intro E F n r i f D hE hF hr hi hf hD
    obtain ⟨D', hDY, hDD⟩ := hj.1.1.2.2 D hD
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
    exact smap_separation_l I hZF hω hB hYt hs ⟨hm, hR⟩ hj hP
      (hYt P (v_power_mem_l I hY hδ hDY hP)) hE hF hr hi hf hDD

end YesMetaZFC.SetTheory.Internal
