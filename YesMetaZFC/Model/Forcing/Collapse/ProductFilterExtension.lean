import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 相容滤子前缀中的实际条件延长

从新前缀任取一个已接受条件，只读取其末坐标；把该坐标接到任意旧已接受条件。
构造仍在原模型中进行，背景滤子列的原限制方程保证新条件被接受。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u v
variable {N : Structure.{u}} {M : Structure.{v}} (hN : N.Models ZF) (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hN)
local notation "J" => kp_pair_l (ZF.modelsKP hM)
variable (e : N.Domain → M.Domain) (inj : Function.Injective e)
  (full : ∀ a y, M.mem y (e a) ↔ ∃ x, N.mem x a ∧ e x = y)
include hN hM inj full

theorem fp_ground_extend_l {ω A n m q t : N.Domain} {F F' : M.Domain}
    (hw : N.IsOmega ω) (hn : N.mem n ω) (hm : N.mem m ω) (succ : N.SuccessorOf m n)
    (fq : Fp_at_d I ω A n q) (ft : Fp_at_d I ω A m t)
    (ff : M.IsSetFunction J F') (keep : M.IsRestrictionOf J F F' (e n))
    (old : Fp_ready_d J (e n) F (e q)) (new : Fp_ready_d J (e m) F' (e t)) :
    ∃ r, Fp_at_d I ω A m r ∧ Fp_ready_d J (e m) F' (e r) ∧ Fp_le_d I r q := by
  have entry := image_entry_iff_l e inj full (KP.exists_pair (ZF.modelsKP hN)) hM.1
  obtain ⟨s,ns⟩ := (ft.domain n).mp succ.predecessor_mem
  obtain ⟨κ,k,nκ,hk,fs⟩ := ft.coordinates n s ns
  obtain ⟨r,fr,ending⟩ := fq.snoc_l hN hw hn succ nκ ⟨k,hk,fs⟩
  obtain ⟨m₀,n₀,last⟩ := ending
  have en := last.prefix_sequence.2.2.2.eq hN.1 fq.domain
  have em := last.source.2.2.2.eq hN.1 fr.domain
  subst n₀ m₀
  have succ' := image_successor_l (hEN := hM.1) e inj full hN.1 succ
  obtain ⟨K,nK,sK⟩ := new (e n) (e s) succ'.predecessor_mem ((entry n s t).mp ns)
  have cut' := image_restriction_l hN hM e inj full fr.function.1 last.prefix_restriction
  have fn' := image_sequence_l hN hM e inj full ⟨hw.members_areOrdinals (ZF.modelsKP hN) m hm,fr.function,fr.domain⟩
  refine ⟨r,fr,(fp_ready_snoc_l J hM.1 succ' fn'.2.1 cut' ((entry n s r).mp last.last_value) ff keep nK).mpr ⟨old,sK⟩,?_⟩
  intro i a ia
  exact ⟨a,(last.prefix_restriction.2 i a).mp ia |>.2,fun _ hx => hx⟩

end YesMetaZFC.Model.Forcing.Internal
