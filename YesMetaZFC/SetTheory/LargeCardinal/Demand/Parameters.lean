import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple

/-! # demanding 类型游戏的实际走法与双图元数

固定参数直接复用 Tg_params_d。辅助走法只编码轮指针、节点长度、类型域
和类型本身；双图元数以内部加倍和三个后继计算，不保留旧辅助 t 图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_move_d (v ℓ k κ u : M.Domain) : Prop := Rd_quad_d v ℓ k κ u

def td_move_m {d} (v ℓ k κ u : Term d) : Formula 1 d := rd_quad_m v ℓ k κ u
derive_free_closed td_move_m

theorem td_move_sat_l (hE : Extensional M) {d} (ρ : Env M d) (v ℓ k κ u : Term d) :
    Formula.satisfies ρ (td_move_m v ℓ k κ u) ↔
      Td_move_d (v.eval ρ) (ℓ.eval ρ) (k.eval ρ) (κ.eval ρ) (u.eval ρ) :=
  rd_quad_sat_l hE ρ v ℓ k κ u

theorem td_move_exists_l (hKP : M.Models KP) (ℓ k κ u : M.Domain) :
    ∃ v, Td_move_d v ℓ k κ u := rd_quad_exists_l hKP ℓ k κ u

theorem Td_move_d.unique_l {v ℓ k κ u ℓ' k' κ' u' : M.Domain}
    (h : Td_move_d v ℓ k κ u) (g : Td_move_d v ℓ' k' κ' u') :
    ℓ = ℓ' ∧ k = k' ∧ κ = κ' ∧ u = u' := Rd_quad_d.unique_l h g

/-- d 是两图标签数，q 加上树坐标，n 再加高度，m 是回答增加 pending 后的元数。 -/
def Td_arity_d (I : kpair_convention_l.Interpretation M) (k d q n m : M.Domain) : Prop :=
  M.IsOrdinalAddition I d k k ∧ M.SuccessorOf q d ∧ M.SuccessorOf n q ∧ M.SuccessorOf m n

def td_arity_m {d} (k v q n m : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(⌜v⌝ₛ,⌜k⌝ₛ,⌜k⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜q⌝ₛ,⌜v⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ,⌜q⌝ₛ) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜m⌝ₛ,⌜n⌝ₛ)⟫
derive_free_closed td_arity_m

theorem td_arity_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (k v q n m : Term d) :
    Formula.satisfies ρ (td_arity_m k v q n m) ↔
      Td_arity_d I (k.eval ρ) (v.eval ρ) (q.eval ρ) (n.eval ρ) (m.eval ρ) := by
  simp only [td_arity_m,Td_arity_d,Formula.satisfies_conj_iff,
    Formula.satisfies_isOrdinalAddition_iff I hE,Formula.satisfies_isSuccessor_iff]

/-- 每个内部有限 k 都实际产生全套有限元数。 -/
theorem td_arity_exists_l (hZF : M.Models ZF) {ω k : M.Domain}
    (hw : M.IsOmega ω) (hk : M.mem k ω) :
    ∃ d q n m, Td_arity_d (kp_pair_l (ZF.modelsKP hZF)) k d q n m ∧
      M.mem d ω ∧ M.mem q ω ∧ M.mem n ω ∧ M.mem m ω := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨d,add,_⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
  have hd := ZF.ordinalAddition_mem_omega hZF I hw hk hk add
  obtain ⟨q,sq,hq⟩ := hw.1.2 d hd
  obtain ⟨n,sn,hn⟩ := hw.1.2 q hq
  obtain ⟨m,sm,hm⟩ := hw.1.2 n hn
  exact ⟨d,q,n,m,⟨add,sq,sn,sm⟩,hd,hq,hn,hm⟩

/-- 同一节点长度的两份实际元数证书逐项一致。 -/
theorem Td_arity_d.unique_l (hZF : M.Models ZF)
    {k d q n m d' q' n' m' : M.Domain}
    (a : Td_arity_d (kp_pair_l (ZF.modelsKP hZF)) k d q n m)
    (b : Td_arity_d (kp_pair_l (ZF.modelsKP hZF)) k d' q' n' m') :
    d = d' ∧ q = q' ∧ n = n' ∧ m = m' := by
  have ok : M.IsOrdinal k := a.1.elim (fun _ h => h.1.1.1)
  obtain ⟨_,_,unique⟩ := ZF.ordinalAddition_existsUnique hZF (kp_pair_l (ZF.modelsKP hZF)) k ok
  have ed := (unique d a.1).trans (unique d' b.1).symm
  subst d'
  have eq := a.2.1.eq hZF.1 b.2.1
  subst q'
  have en := a.2.2.1.eq hZF.1 b.2.2.1
  subst n'
  exact ⟨rfl,rfl,rfl,a.2.2.2.eq hZF.1 b.2.2.2⟩

/-- 节点长度增一时，旧回答元数恰等于当前去掉高度后的元数。 -/
theorem Td_arity_d.next_l (hZF : M.Models ZF) {ω j k d q n m d' q' n' m' : M.Domain}
    (hw : M.IsOmega ω) (hk : M.mem k ω) (step : M.SuccessorOf k j)
    (old : Td_arity_d (kp_pair_l (ZF.modelsKP hZF)) j d q n m)
    (next : Td_arity_d (kp_pair_l (ZF.modelsKP hZF)) k d' q' n' m') : m = q' := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj := hw.transitive (ZF.modelsKP hZF) k hk j step.predecessor_mem
  obtain ⟨v,add,sv⟩ := (ZF.ordinalAddition_successor_iff hZF I
    (hw.members_areOrdinals (ZF.modelsKP hZF) j hj) step).mp next.1
  have ev := (Structure.natural_add_left_successor hZF I hw hj step hj old.1 add).eq hZF.1 old.2.1
  have ed := (ev ▸ sv).eq hZF.1 old.2.2.1
  exact old.2.2.2.eq hZF.1 (ed ▸ next.2.1)

end YesMetaZFC.SetTheory.LargeCardinal
