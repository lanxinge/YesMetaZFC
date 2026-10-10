import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable

/-! # 正则 Hχ 中的全部内部有限序列空间 -/
namespace YesMetaZFC.SetTheory.ZFC
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem h_fseq_l (hZFC : M.Models ZFC) {ω χ H A : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) χ H) (hA : M.mem A H) :
    ∃ K, M.mem K H ∧ Fseq_space_d (kp_pair_l (ZF.modelsKP (models_zf_l hZFC))) ω A K := by
  let hZF := models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨μ, hμ, hAμ⟩ := ZF.hmem_size_l I hZF ((hH A).mp hA)
  obtain ⟨ν, hν, hn, hμν, _⟩ := ZF.common_cardinal_l I hZF hχ.isCardinal.1 hωχ hμ hμ
  obtain ⟨f, hf⟩ := hAμ
  obtain ⟨g, hg⟩ := hμν
  have hAν := ZF.exists_compositionInjection hZF I hf hg
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω A
  refine ⟨K, h_small_closed_l I hZFC hω hχ hωχ hH ?_ hν (ZF.fseq_bound_l I hZF hω hn hAν hK), hK⟩
  intro f hf
  obtain ⟨n, hn, hfn⟩ := (hK f).mp hf
  have ht := ZF.h_transitive_l I hZF hH
  exact h_function_l hZFC hω hχ hωχ hH
    (ht ω (ZF.h_ordinal_l I hZF hχ.isLimitOrdinal hH hωχ) n hn)
    ⟨hfn.1, hfn.2.1, fun i hi => (hfn.2.2 i hi).imp fun x hx => ⟨ht A hA x hx.1, hx.2⟩⟩

end YesMetaZFC.SetTheory.ZFC
