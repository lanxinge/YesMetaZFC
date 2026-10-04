import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTupleValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetCode

/-! # 同一代表的有界真值在两次施加之间一致

同一扩展器读同一个源内真值集。有限幂子集一致性搬运这个集合，
两侧源内 Łoś 随即给出实际坍塌值之间的有界公式一致性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_value_agree_l (hZFC : M.Models ZFC)
    {ω κ K K' L X R Y R' F J O Z A p T V q c C W d N S e
      J' O' Z' A' p' T' V' q' c' C' W' d' N' S' e' n D a U : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (source' : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (h' : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L Y R' F J' O' Z' A' p' T' V')
    (limit' : Di_limit_d A' p' T' V' q' C' W')
    (model' : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c' C' W')
    (hN' : M.TransitiveSet N') (target' : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d' N' S')
    (he' : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c' d' C' N' e')
    (haJ : M.mem a J) (haJ' : M.mem a J') (hn : M.mem n ω) (ha : Fn0_d n L a)
    (hD : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    {k} (φ : Formula 1 k) (hφ : φ.FreeClosed) (hd : φ.IsDelta0) (f : Fin k → M.Domain) (ρ η : Env M k)
    (values : ∀ i, Ep_value_d q e a (f i) (ρ.bound i))
    (values' : ∀ i, Ep_value_d q' e' a (f i) (η.bound i)) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  let hZF := ZFC.models_zf_l hZFC
  have left := ep_delta_value_l hZFC source family coherent h limit model hN target he haJ ha hD haU φ hφ hd f ρ values
  have right := ep_delta_value_l hZFC source' (family.transfer_l agree) (coherent.transfer_l hZF agree)
    h' limit' model' hN' target' he' haJ' ha hD haU φ hφ hd f η values'
  apply left.trans (Iff.trans ?_ right.symm)
  constructor <;> rintro ⟨B, hb, hu, sub, hs⟩
  · exact ⟨B, (agree n D B hn hD sub).mp hb, hu, sub, hs⟩
  · exact ⟨B, (agree n D B hn hD sub).mpr hb, hu, sub, hs⟩

end YesMetaZFC.SetTheory.LargeCardinal
