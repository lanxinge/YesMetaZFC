import YesMetaZFC.Model.SetTheory.Images.BinaryImage
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.SetTheory.Ord.Code.Sequence

/-! # 规范序数配对沿成员满嵌入保持

先运输源中实际构造的整个有界方块证书，再恢复目标中的全局规范代码。
无需把规范配对公式误当作 Δ₀，也不要求整个嵌入初等。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem oc_pair_image_l (hM : M.Models ZF) (hN : N.Models ZF)
    (e : M.Domain → N.Domain) (ei : Function.Injective e)
    (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
    {a b c : M.Domain} (code : Oc_pair_d (kp_pair_l (ZF.modelsKP hM)) a b c) :
    Oc_pair_d (kp_pair_l (ZF.modelsKP hN)) (e a) (e b) (e c) := by
  obtain ⟨t,X,η,F,p,square,pair,hp,pc⟩ := oc_pair_square_l hM code
  have moved := (oc_square_image_l e ei ef (ZF.modelsKP hM) (ZF.modelsKP hN)).mp square
  exact ((moved.codes_l hN (e a) (e b) (e c)).mpr
    ⟨e p,(image_member_l e ei ef).mpr hp,image_kpair_l e ef pair,
      (image_entry_iff_l e ei ef (KP.exists_pair (ZF.modelsKP hM)) hN.1 p c F).mp pc⟩).1

end YesMetaZFC.SetTheory

/-! ## 内部有限序列的规范代码沿成员满嵌入保持

实际有限递归图逐步运输。后继读取在已知定义域上改写为有界公式；
无后继分支也由图成员的完整原像反射，故无需假设内部自然数外部标准。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}} (hM : M.Models ZF) (hN : N.Models ZF)
  (e : M.Domain → N.Domain) (ei : Function.Injective e)
  (ef : ∀ a y, N.mem y (e a) ↔ ∃ b, M.mem b a ∧ e b = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)

private def oc_read0_m : Formula 1 5 := Formula.existsMem (.bound 0)
  (.conj (KP.succ0_m (.bound 1) .newest)
    (.conj (rd_entry0_m .newest (.bound 4) (.bound 3))
      (.conj (rd_entry0_m .newest (.bound 5) (.bound 2))
        (.conj (KP.ord0_m (.bound 4)) (KP.ord0_m (.bound 5))))))

private theorem oc_read0_sat_l {L : Structure} (hL : L.Models KP) {n F H b a : L.Domain}
    (seq : L.IsSequenceOfLength (kp_pair_l hL) H n) :
    Formula.satisfies (⟨fun i => [n,F,H,b,a].get i,fun _ => n⟩ : Env L 5) oc_read0_m ↔
      Oc_read_d (kp_pair_l hL) F H b a := by
  simp only [oc_read0_m,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    KP.succ0_sat_l hL.1,rd_entry0_sat_l hL.1,KP.ord0_sat_l hL]
  change (∃ i, L.mem i n ∧ L.SuccessorOf n i ∧ Rd_entry_d i b H ∧ Rd_entry_d i a F ∧
    L.IsOrdinal b ∧ L.IsOrdinal a) ↔ _
  constructor
  · rintro ⟨i,hi,succ,ib,ia,ob,oa⟩
    exact ⟨n,i,seq.2.2,succ,seq.1.mem hi,ib,ia,ob,oa⟩
  · rintro ⟨m,i,dom,succ,_,ib,ia,ob,oa⟩
    have eq := dom.eq hL.1 seq.2.2
    subst m
    exact ⟨i,succ.predecessor_mem,succ,ib,ia,ob,oa⟩

include ei ef

theorem oc_fold_image_l {ω F n c : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (fn : M.IsSetFunction I F) (fold : Oc_fold_d I F n c) : Oc_fold_d J (e F) (e n) (e c) := by
  apply image_finite_recursion_l hM hN e ei ef hw hn ?_ fold
  intro H c i _ seq step
  have seq' := image_sequence_l hM hN e ei ef seq
  have read b a : Oc_read_d I F H b a ↔ Oc_read_d J (e F) (e H) (e b) (e a) := by
    let ρ : Env M 5 := ⟨fun k => [i,F,H,b,a].get k,fun _ => i⟩
    have tr := delta0_image_l e ei ef
      (show oc_read0_m.IsDelta0 from .existsMem _ (.conj (KP.succ0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (KP.ord0_delta_l _) (KP.ord0_delta_l _)))))) ρ
    have env : image_env_l e ρ = (⟨fun k => [e i,e F,e H,e b,e a].get k,fun _ => e i⟩ : Env N 5) := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k)))))),rfl⟩
    rw [env] at tr
    exact (oc_read0_sat_l (ZF.modelsKP hM) seq).symm.trans (tr.trans (oc_read0_sat_l (ZF.modelsKP hN) seq'))
  rcases step with ⟨b,a,valid,code⟩ | ⟨no,empty⟩
  · exact Or.inl ⟨e b,e a,(read b a).mp valid,oc_pair_image_l hM hN e ei ef code⟩
  · refine Or.inr ⟨?_,fun x hx => ((ef c x).mp hx).elim fun t ht => empty t ht.1⟩
    rintro ⟨b,a,valid⟩
    have old := valid
    obtain ⟨m,k,dom,succ,_,kb,ka,_⟩ := old
    have em := dom.eq hN.1 seq'.2.2
    subst m
    obtain ⟨k₀,_,ek⟩ := (ef i k).mp succ.predecessor_mem
    subst k
    obtain ⟨l,b₀,lb,el,eb⟩ := (image_entries_l e ef seq.2.1.1 (e k₀) b).mp kb
    have el' := ei el
    subst l b
    obtain ⟨l,a₀,la,el,ea⟩ := (image_entries_l e ef fn.1 (e k₀) a).mp ka
    have el' := ei el
    subst l a
    exact no ⟨b₀,a₀,(read b₀ a₀).mpr valid⟩

theorem oc_seq_image_l {ω F c : M.Domain} (hw : M.IsOmega ω) (code : Oc_seq_d I ω F c) :
    Oc_seq_d J (e ω) (e F) (e c) := by
  obtain ⟨n,b,hn,seq,fold,pair⟩ := code
  refine ⟨e n,e b,(image_member_l e ei ef).mpr hn,
    ⟨image_sequence_l hM hN e ei ef seq.1,?_⟩,
    oc_fold_image_l hM hN e ei ef hw hn seq.1.2.1 fold,oc_pair_image_l hM hN e ei ef pair⟩
  intro i hi a ia
  obtain ⟨k,v,kv,ek,ev⟩ := (image_entries_l e ef seq.1.2.1.1 i a).mp ia
  subst i a
  exact image_ord_l hM hN e ei ef (seq.2 k ((image_member_l e ei ef).mp hi) v kv)

end YesMetaZFC.SetTheory
