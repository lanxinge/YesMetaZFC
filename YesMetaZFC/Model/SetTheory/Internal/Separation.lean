import YesMetaZFC.Model.SetTheory.Internal.SeparationCode
import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding

/-! # 完整初等嵌入回拉内部公式的实际分离集

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
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare b hb i hi with he | hbi | hib
    · exact ⟨v, hvω, hv.predecessor_mem, fun x hx => (hv x).mpr (Or.inl ((he x).mp hx))⟩
    · exact ⟨v, hvω, hv.predecessor_mem, fun x hx => (hv x).mpr
        (Or.inl ((hω.members_areOrdinals hZF i hi).transitive b hbi x hx))⟩
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
