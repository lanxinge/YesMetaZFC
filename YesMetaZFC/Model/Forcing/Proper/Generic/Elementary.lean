import YesMetaZFC.Model.Forcing.Proper.Generic.OperationLift
import YesMetaZFC.Model.Forcing.Proper.Generic.Sequence
import YesMetaZFC.Model.Forcing.Internal.Ground.Syntax
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Internal.Elementary

/-! # N[G] 对全部内部公式码的初等提升

有限名称列和公式码都先回拉到地模型，再用实际判定／选择图给出内部司寇伦闭包。
最后应用完整内部 Tarski–Vaught 定理。结论的载体是整个 N[G] 与整个 X[G]，
没有把 N[G] 截成与另一个集合的交，也没有标准性或外部良基性假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

def ng_elementary_env_l (w μ u : M.Domain) : Env M 3 :=
  ((⟨fun _ => w, fun _ => u⟩ : Env M 1).push μ).push u

/-- 由已构造的有限元运算图推出全内部初等性；本提升步骤只使用 ZF。 -/
theorem ng_elementary_l {b ω X u w μ C T S D K L N q}
    (hb : U b) (hω : M.IsOmega ω) (hu : Name_d M B u) (huN : M.mem u N)
    (hw : Check_d M b ω w) (hμ : Ng_name_d M B X μ)
    (hC : Scode_d I ω C) (hT : M.IsCartesianProduct I T C ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hK : M.IsSetFunctionFromTo I K D X) (hL : M.IsSetFunctionFromTo I L D X)
    (hk : ∀ k A, Entry_d M k A K → Ng_dense_op_d (ssk_mem_s kpair_convention_l)
      (ng_elementary_env_l w μ u) B R z b X k A)
    (hl : ∀ k t, Entry_d M k t L → Ng_select_op_d I (ssk_mem_s kpair_convention_l)
      (ng_elementary_env_l w μ u) B R z b ω X u k t)
    (hNX : M.MemberSubset N X) (hKN : Fc_closed_d I ω T K N) (hLN : Fc_closed_d I ω T L N)
    (hm : Mstr_d M B R z N q) (hq : U q) :
    ∃ Y Z v c A d H : (E).Domain,
      (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U X x) ∧ (∀ x, x ∈ Z ↔ Ng_mem_d M B R z U N x) ∧
      (E).IsOmega v ∧ Smem_d J c Y A ∧ Ssub_d J c d Y A Z H ∧ Selem_d J v c d := by
  have hE := preserves_zf_l O hZF hU
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  have hωE : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hω (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  have hCE := image_scode_l hZF hE e hi he hω hωE hC
  obtain ⟨Y, hμY⟩ := name_value_l (R := R) (z := z) (U := U) hμ.1
  have hY := ng_value_l O hZF hU hμ hμY
  obtain ⟨Z, hZ⟩ := ng_set_l O hZF hU N
  obtain ⟨v, huv⟩ := name_value_l (R := R) (z := z) (U := U) hu
  have hvZ := (hZ v).mpr ⟨u, huN, huv⟩
  have hZY : (E).MemberSubset Z Y := fun x hx => by
    obtain ⟨t, ht, hx⟩ := (hZ x).mp hx
    exact (hY x).mpr ⟨t, hNX t ht, hx⟩
  obtain ⟨c, A, hModel, hRel⟩ := smdl_membership_l J hE ⟨v, hZY v hvZ⟩
  have hMem : Smem_d J c Y A := ⟨hModel, hRel⟩
  let ρ := ng_elementary_env_l w μ u
  let η := ng_elementary_env_l (M := E) (e ω) Y v
  have hEnv : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact huv
    | bound i => exact Fin.cases huv (Fin.cases hμY (fun _ => hv ω w hw)) i
  have hClosed : Ssk_closed_d J (e ω) c Y v (e C) Z := by
    intro a i n f ha hiω hn hf hex
    obtain ⟨a', ha', rfl⟩ := (he C a).mp ha
    obtain ⟨i', hi', rfl⟩ := (he ω i).mp hiω
    obtain ⟨m, s, t, hmω, _, hs, ht, htf⟩ := ng_fseq_name_l O hZF hU hb hω hZ e hi he hv hn hf
    obtain ⟨ca, hca, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 a'
    obtain ⟨ci, hci, _, _⟩ := zf_check_l M hZF (hU.proper b hb).1 i'
    obtain ⟨l, hlai⟩ := (I).total a' i'
    have hlT := (hT l).mpr ⟨a', ha', i', hi', hlai⟩
    let ξ := ((η.push (e a')).push (e i')).push f
    have hξ := env_val_push_l hZF (env_val_push_l hZF (env_val_push_l hZF hEnv (hv a' ca hca)) (hv i' ci hci)) htf
    have decode x : (ssk_mem_s kpair_convention_l).denote ξ x ↔
        x ∈ Y ∧ Ssk_wit_d J (e ω) c Y v (e a') (e i') f x :=
      (ssk_mem_sat_l J hE.1 (ξ.push x) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).trans
        (ssk_mem_decode_l J hE.1 hMem)
    have hex' : ∃ x, Ng_mem_d M B R z U X x ∧ (ssk_mem_s kpair_convention_l).denote ξ x := by
      obtain ⟨x, hx, hφ⟩ := hex
      exact ⟨x, (hY x).mp hx, (decode x).mpr ⟨hx, hφ⟩⟩
    obtain ⟨y, hy, hφ⟩ := ng_operation_lift_l O hZF hU (ssk_mem_s kpair_convention_l) ρ
      hω hS hD hK hL hk hl hNX hKN hLN hm hq hmω hs hlT hlai hca hci ht ξ hξ hex'
    exact ⟨y, (hZ y).mpr hy, ((decode y).mp hφ).2⟩
  obtain ⟨d, H, hSub, hElem⟩ := selem_of_skolem_l J hE hωE hModel hCE hZY hvZ hClosed
  exact ⟨Y, Z, e ω, c, A, d, H, hY, hZ, hωE, hMem, hSub, hElem⟩

end YesMetaZFC.Model.Forcing.Internal
