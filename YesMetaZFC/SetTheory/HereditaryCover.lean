import YesMetaZFC.SetTheory.Hereditary
import YesMetaZFC.SetTheory.Card.Properties.SuccessorRegularity

/-! # 任意内部集合的正则 H(χ) 环境

将给定对象与 ω 一起放入传递闭包，用内部选择取得序数大小界，再取其基数代表
的 Hartogs 后继。正则性已由实际小并计数证明，故入口没有额外的大基数前提。
-/

namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 任意集合属于某个实际 H(χ)，其中 χ 是不可数正则基数。 -/
theorem h_cover_l (hZFC : M.Models ZFC) {ω} (hω : M.IsOmega ω) (x : M.Domain) :
    ∃ χ H, M.IsRegularCardinal I χ ∧ M.mem ω χ ∧ H_d I χ H ∧ M.mem x H := by
  have hZF := models_zf_l hZFC
  obtain ⟨a, ha⟩ := KP.exists_pair (ZF.modelsKP hZF) x ω
  obtain ⟨T, hT⟩ := ZF.tc_exists_l I hZF a
  have hxT := hT.1 a hT.2.1 x ((ha x).mpr (Or.inl rfl))
  have hωT := hT.1 a hT.2.1 ω ((ha ω).mpr (Or.inr rfl))
  obtain ⟨γ, F, hγ, hF, hf⟩ := ordinal_enum_l hZFC I T
  obtain ⟨G, hG⟩ := ZF.exists_identityBijection hZF I γ
  obtain ⟨J, hJ⟩ := ZF.ordinal_image_bound_l I hZF hγ ⟨G, hG.1⟩ hF hf
  obtain ⟨μ, hμ, _⟩ := ZF.ordinalCardinal_existsUnique hZF I hγ
  obtain ⟨K, hK⟩ := hμ.2.symm hZF I
  obtain ⟨L, hL⟩ := ZF.exists_compositionInjection hZF I hJ hK.1
  obtain ⟨W, hW⟩ := ZF.exists_inclusionInjection hZF I (hT.1 ω hωT)
  have hωμ := ZF.exists_compositionInjection hZF I hW hL
  obtain ⟨χ, hχ⟩ := ZF.exists_hartogsNumber hZF I μ
  have hχr := hartogs_regular_l I hZFC hω ⟨hμ.1, hωμ⟩ hχ
  obtain ⟨P, hP⟩ := ZF.exists_identityBijection hZF I μ
  have hμχ := (hχ.2 μ hμ.1.1).mpr ⟨P, hP.1⟩
  have hωχ : M.mem ω χ := by
    rcases (ZF.omega_cardinal_l I hZF hω).eq_or_mem_of_cardinalLessOrEqual hZF I hμ.1 hωμ with he | he
    · exact he.symm ▸ hμχ
    · exact hχ.1.transitive μ hμχ ω he
  obtain ⟨H, hH⟩ := ZF.h_exists_l I hZF hχr.isCardinal
  exact ⟨χ, H, hχr, hωχ, hH, (hH x).mpr (ZF.hmem_of_transitive_l I hZF hT.1 hxT hμχ ⟨L, hL⟩)⟩

end YesMetaZFC.SetTheory.ZFC
