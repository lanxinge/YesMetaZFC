import YesMetaZFC.SetTheory.InnerModel.Order.Relation
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.Model.SetTheory.DirectedSystem.Basic
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalBookkeeping

/-! # 对象模型内的迭代树序及后继添枝

树序存储自反闭包。前驱集线性，树边沿序数递增；序数后继有树前驱，
非零极限的严格前驱共尾。添枝允许挂在任意旧结点，完整保留旧前驱集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def It_pred_d (T k j : M.Domain) : Prop := M.mem k j ∧
  ∀ i, Rd_entry_d i j T ↔ i = j ∨ Rd_entry_d i k T

structure It_order_d (α T : M.Domain) : Prop where
  ordinal : M.IsOrdinal α
  relation : ∀ p, M.mem p T → ∃ i j, KPair_d M p i j
  bound : ∀ i j, Rd_entry_d i j T → M.mem i α ∧ M.mem j α
  refl : ∀ i, M.mem i α → Rd_entry_d i i T
  trans : ∀ i j k, Rd_entry_d i j T → Rd_entry_d j k T → Rd_entry_d i k T
  forward : ∀ i j, Rd_entry_d i j T → i = j ∨ M.mem i j
  chain : ∀ i j k, Rd_entry_d i k T → Rd_entry_d j k T → Rd_entry_d i j T ∨ Rd_entry_d j i T
  predecessor : ∀ i j, M.mem j α → M.SuccessorOf j i → ∃ k, It_pred_d T k j
  cofinal : ∀ δ, M.mem δ α → M.IsLimitOrdinal δ → ∀ i, M.mem i δ →
    ∃ j, M.mem j δ ∧ Rd_entry_d j δ T ∧ (i = j ∨ M.mem i j)

/-- 每个实际结点都在空序数根之上；证明也覆盖非标准长度和极限结点。 -/
theorem It_order_d.root_l (hZF : M.Models ZF) {α T z : M.Domain} (h : It_order_d α T)
    (hz : ∀ x, ¬ M.mem x z) : ∀ i, M.mem i α → Rd_entry_d z i T := by
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases z (fun _ => T)), fun _ => T⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (rd_entry0_m (.bound 2) .newest (.bound 3)) }
  have sat i : φ.denote ρ i ↔ M.mem i α → Rd_entry_d z i T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1]; rfl
  intro i hi
  apply (sat i).mp (ZF.mem_ind_l M hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ ?_ i) hi
  intro i ih
  apply (sat i).mpr
  intro hi
  have prev j (hj : M.mem j i) := (sat j).mp (ih j hj) (h.ordinal.transitive i hi j hj)
  rcases (h.ordinal.mem hi).classify hZF.1 with empty | ⟨j, _, succ⟩ | limit
  · have eq := hZF.1.eq_of_same_members i z (fun x => iff_of_false (empty x) (hz x))
    exact eq ▸ h.refl i hi
  · obtain ⟨k, hk, pred⟩ := h.predecessor j i hi succ
    exact (pred z).mpr (Or.inr (prev k hk))
  · obtain ⟨j, hj⟩ := limit.2.1
    obtain ⟨k, hk, edge, _⟩ := h.cofinal i hi limit j hj
    exact h.trans z k i (prev k hk) edge

theorem it_successor_not_limit_l (hE : Extensional M) {α ξ : M.Domain} (ho : M.IsOrdinal ξ) (hs : M.SuccessorOf α ξ) : ¬ M.IsLimitOrdinal α := by
  intro hl
  obtain ⟨j, hj, hξj⟩ := hl.2.2 ξ hs.predecessor_mem
  rcases (hs j).mp hj with hjξ | eq
  · have self := ho.transitive j hjξ ξ hξj
    exact ho.wellOrder.linear.irrefl ξ self self
  · have eq := hE.eq_of_same_members j ξ eq
    exact ho.wellOrder.linear.irrefl ξ (eq ▸ hξj) (eq ▸ hξj)

variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem it_order_extend_l {α ξ T k : M.Domain} (h : It_order_d α T)
    (hα : M.SuccessorOf α ξ) (hk : M.mem k α) : ∃ β U, M.SuccessorOf β α ∧ It_order_d β U ∧
      ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) := by
  obtain ⟨β, hβ⟩ := KP.exists_successor hKP α
  have no : ¬ M.mem α α := fun ha => h.ordinal.wellOrder.linear.irrefl α ha ha
  have sc i : M.mem i β ↔ M.mem i α ∨ i = α := (hβ i).trans
    (or_congr Iff.rfl ⟨hKP.1.eq_of_same_members i α, fun e => e ▸ fun _ => Iff.rfl⟩)
  let ρ : Env M 3 := ⟨Fin.cases α (Fin.cases k (fun _ => T)), fun _ => α⟩
  let φ : Delta0BinarySchema 3 := {
    body := .disj (rd_entry0_m (.bound 1) .newest (.bound 4))
      (.conj (Formula.extensionalEq .newest (.bound 2))
        (.disj (Formula.extensionalEq (.bound 1) (.bound 2)) (rd_entry0_m (.bound 1) (.bound 3) (.bound 4))))
    delta0 := .disj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (.disj (.atom _ _ _) (rd_entry0_delta_l ..))) }
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  obtain ⟨U, ur⟩ := rw_rel_exists_l hKP φ ρ β
  have us i j := ur.entry_l hKP (x := i) (y := j)
  have rel : M.IsSetRelationOn I U β := ⟨fun p hp => by
    obtain ⟨i, _, j, _, hp, _⟩ := (ur p).mp hp
    exact ⟨i, j, hp⟩,
    fun i j hij => ⟨((us i j).mp hij).1, ((us i j).mp hij).2.1⟩⟩
  have bounds i j (hr : Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T)) : M.mem i β ∧ M.mem j β := by
    rcases hr with hr | ⟨rfl, rfl | hr⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i j hr).1), (sc j).mpr (Or.inl (h.bound i j hr).2)⟩
    · exact ⟨hβ.predecessor_mem, hβ.predecessor_mem⟩
    · exact ⟨(sc i).mpr (Or.inl (h.bound i k hr).1), hβ.predecessor_mem⟩
  have read i j : Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ Rd_entry_d i k T) :=
    (us i j).trans ⟨fun hh => (sat i j).mp hh.2.2, fun hh => ⟨(bounds i j hh).1, (bounds i j hh).2, (sat i j).mpr hh⟩⟩
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T :=
    (read i j).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have tip i : Rd_entry_d i α U ↔ i = α ∨ Rd_entry_d i k T :=
    (read i α).trans ⟨fun hh => hh.elim (fun hh => (no (h.bound i α hh).2).elim) And.right,
      fun hh => Or.inr ⟨rfl, hh⟩⟩
  have limit_old δ (hδ : M.mem δ β) (limit : M.IsLimitOrdinal δ) : M.mem δ α := by
    rcases (sc δ).mp hδ with hl | rfl
    · exact hl
    · exact (it_successor_not_limit_l hKP.1 (h.ordinal.mem hα.predecessor_mem) hα limit).elim
  refine ⟨β, U, hβ, ⟨KP.successor_isOrdinal hKP h.ordinal hβ, rel.1, rel.2, ?_, ?_, ?_, ?_, ?_, ?_⟩, read⟩
  · intro i hi
    rcases (sc i).mp hi with hi | rfl
    · exact (read i i).mpr (Or.inl (h.refl i hi))
    · exact (tip _).mpr (Or.inl rfl)
  · intro i j l hij hjl
    rcases (sc l).mp (rel.2 j l hjl).2 with hl | rfl
    · have hjl := (old j l hl).mp hjl
      exact (old i l hl).mpr (h.trans i j l ((old i j (h.bound j l hjl).1).mp hij) hjl)
    · rcases (tip j).mp hjl with rfl | hjk
      · exact hij
      · exact (tip i).mpr (Or.inr (h.trans i j k ((old i j (h.bound j k hjk).1).mp hij) hjk))
  · intro i j hij
    rcases (read i j).mp hij with hij | ⟨rfl, rfl | hik⟩
    · exact h.forward i j hij
    · exact Or.inl rfl
    · exact Or.inr (h.bound i k hik).1
  · intro i j l hil hjl
    rcases (sc l).mp (rel.2 i l hil).2 with hl | rfl
    · exact (h.chain i j l ((old i l hl).mp hil) ((old j l hl).mp hjl)).imp
        (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
    · rcases (tip i).mp hil with rfl | hik
      · exact Or.inr hjl
      · rcases (tip j).mp hjl with rfl | hjk
        · exact Or.inl hil
        · exact (h.chain i j k hik hjk).imp (fun hh => (read i j).mpr (Or.inl hh)) (fun hh => (read j i).mpr (Or.inl hh))
  · intro i j hj hs
    rcases (sc j).mp hj with hj | rfl
    · obtain ⟨p, hp, ps⟩ := h.predecessor i j hj hs
      exact ⟨p, hp, fun l => (old l j hj).trans ((ps l).trans (or_congr Iff.rfl (old l p (h.ordinal.transitive j hj p hp)).symm))⟩
    · exact ⟨k, hk, fun l => (tip l).trans (or_congr Iff.rfl (old l k hk).symm)⟩
  · intro δ hδ hl i hi
    have hδα := limit_old δ hδ hl
    obtain ⟨j, hj, hjδ, above⟩ := h.cofinal δ hδα hl i hi
    exact ⟨j, hj, (old j δ hδα).mpr hjδ, above⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 序数上的实际自反线性迭代序

同一个规范序同时服务于 padding 树和弱迭代的极限取并。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem it_linear_order_l (hKP : M.Models KP) {α : M.Domain} (ho : M.IsOrdinal α) : ∃ T, It_order_d α T ∧
    (∀ i j, Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j)) ∧
    ∀ i j, M.mem j α → M.SuccessorOf j i → It_pred_d T i j := by
  let φ : Delta0BinarySchema 0 := {
    body := .disj (Formula.extensionalEq (.bound 1) .newest) (.mem (.bound 1) .newest)
    delta0 := .disj (.atom _ _ _) (.mem _ _) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => α⟩
  obtain ⟨T, ts⟩ := rw_rel_exists_l hKP φ ρ α
  have sat i j : φ.toBinarySchema.denote ρ i j ↔ i = j ∨ M.mem i j := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff]; rfl
  have read i j : Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j) :=
    (ts.entry_l hKP).trans (and_congr_right fun _ => and_congr_right fun _ => sat i j)
  have ht : M.IsSetRelationOn (kp_pair_l hKP) T α := ⟨fun p hp => by
    obtain ⟨i, _, j, _, hp, _⟩ := (ts p).mp hp
    exact ⟨i, j, hp⟩, fun i j hij => ⟨((read i j).mp hij).1, ((read i j).mp hij).2.1⟩⟩
  have refl i hi := (read i i).mpr ⟨hi, hi, Or.inl rfl⟩
  have pred i j (hj : M.mem j α) (hs : M.SuccessorOf j i) : It_pred_d T i j := by
    have hi := ho.transitive j hj i hs.predecessor_mem
    refine ⟨hs.predecessor_mem, fun k => ⟨?_, ?_⟩⟩
    · intro hk
      obtain ⟨hkα, _, eq | hkj⟩ := (read k j).mp hk
      · exact Or.inl eq
      · rcases (hs k).mp hkj with hki | eq
        · exact Or.inr ((read k i).mpr ⟨hkα, hi, Or.inr hki⟩)
        · exact Or.inr ((read k i).mpr ⟨hkα, hi, Or.inl (hKP.1.eq_of_same_members k i eq)⟩)
    · rintro (rfl | hk)
      · exact refl _ hj
      · obtain ⟨hkα, _, rfl | hki⟩ := (read k i).mp hk
        · exact (read _ j).mpr ⟨hkα, hj, Or.inr hs.predecessor_mem⟩
        · exact (read k j).mpr ⟨hkα, hj, Or.inr ((hs k).mpr (Or.inl hki))⟩
  refine ⟨T, ⟨ho, ht.1, ht.2, refl, ?_, fun i j hij => ((read i j).mp hij).2.2, ?_,
    fun i j hj hs => ⟨i, pred i j hj hs⟩, ?_⟩, read, pred⟩
  · intro i j k hij hjk
    obtain ⟨hi, _, rfl | hij⟩ := (read i j).mp hij
    · exact hjk
    · obtain ⟨_, hk, rfl | hjk⟩ := (read j k).mp hjk
      · exact (read i _).mpr ⟨hi, hk, Or.inr hij⟩
      · exact (read i k).mpr ⟨hi, hk, Or.inr ((ho.mem hk).transitive j hjk i hij)⟩
  · intro i j k hik hjk
    have hi := (ht.2 i k hik).1
    have hj := (ht.2 j k hjk).1
    rcases ho.wellOrder.linear.compare i hi j hj with eq | hij | hji
    · exact Or.inl ((read i j).mpr ⟨hi, hj, Or.inl (hKP.1.eq_of_same_members i j eq)⟩)
    · exact Or.inl ((read i j).mpr ⟨hi, hj, Or.inr hij⟩)
    · exact Or.inr ((read j i).mpr ⟨hj, hi, Or.inr hji⟩)
  · intro δ hδ _ i hi
    exact ⟨i, hi, (read i δ).mpr ⟨ho.transitive δ hδ i hi, hδ, Or.inr hi⟩, Or.inl rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾树枝及其实际指标序

树枝是旧树序中向下封闭的链；共尾性针对时间长度。指标序由原树序限制
得到，其定向性只使用链条件，不假定极限模型已经存在。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_branch_d (α T B : M.Domain) : Prop where
  subset : M.MemberSubset B α
  chain : ∀ i j, M.mem i B → M.mem j B → Rd_entry_d i j T ∨ Rd_entry_d j i T
  down : ∀ i j, Rd_entry_d i j T → M.mem j B → M.mem i B
  cofinal : ∀ i, M.mem i α → ∃ j, M.mem j B ∧ (i = j ∨ M.mem i j)

/-! `cofinal` 的无选择前端接口。

`It_front_d` 只记录一个原树节点在分支中的前端见证；外部枚举再以
`slot` 的重复性把这个见证推到任意晚的编号。 -/
def It_front_d (α B : M.Domain) (i j : M.Domain) : Prop :=
  M.mem i α ∧ M.mem j B ∧ (i = j ∨ M.mem i j)

theorem It_branch_d.front_exists_l {α T B : M.Domain}
    (branch : It_branch_d α T B) {i : M.Domain} (hi : M.mem i α) :
    ∃ j, It_front_d α B i j := by
  obtain ⟨j, hj, hij⟩ := branch.cofinal i hi
  exact ⟨j, hi, hj, hij⟩

/-! 分支前端关系具有有限定向性：两个阶段可同时提升到一个分支节点。
这一步只使用 α 的良序和 branch 的 cofinality，为后续构造单调 stage
sequence 提供实际的有限延拓律。 -/
theorem It_branch_d.front_directed_l {α T B : M.Domain}
    (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B) :
    ∀ i j, M.mem i α → M.mem j α →
      ∃ b, It_front_d α B i b ∧ It_front_d α B j b := by
  intro i j hi hj
  have lift {x t b : M.Domain} (hx : M.mem x α) (ht : M.mem t α)
      (hxt : x = t ∨ M.mem x t) (hb : M.mem b B)
      (htb : t = b ∨ M.mem t b) : It_front_d α B x b := by
    refine ⟨hx, hb, ?_⟩
    rcases htb with rfl | htb
    · exact hxt
    · rcases hxt with rfl | hxt
      · exact Or.inr htb
      · exact Or.inr ((order.ordinal.mem (branch.subset b hb)).transitive t htb x hxt)
  rcases order.ordinal.wellOrder.linear.compare i hi j hj with hij | hij | hji
  · have eq := hZF0.1.eq_of_same_members i j hij
    subst j
    obtain ⟨b, hb, hbt⟩ := branch.cofinal i hi
    exact ⟨b, lift hi hi (Or.inl rfl) hb hbt, lift hi hi (Or.inl rfl) hb hbt⟩
  · obtain ⟨b, hb, hbt⟩ := branch.cofinal j hj
    exact ⟨b, lift hi hj (Or.inr hij) hb hbt, lift hj hj (Or.inl rfl) hb hbt⟩
  · obtain ⟨b, hb, hbt⟩ := branch.cofinal i hi
    exact ⟨b, lift hi hi (Or.inl rfl) hb hbt, lift hj hi (Or.inr hji) hb hbt⟩

/-! 给定外部重复枚举，分支的共尾性自动产生 branch-hitting fronts。

`enum_sub` 是唯一的外部模型接口；`slot` 不作选择，只要求每个代码在
任意下界后仍有一个更晚的编号。 -/
theorem It_branch_d.external_front_l {α T B : M.Domain}
    (branch : It_branch_d α T B) (enum : Nat → M.Domain)
    (enum_sub : ∀ n, M.mem (enum n) α)
    (slot : ∀ j, M.mem j B → Nat → Nat)
    (replete : ∀ j hj k, k < slot j hj k ∧ enum (slot j hj k) = j) :
    ∀ n k, ∃ m, k < m ∧ It_front_d α B (enum n) (enum m) := by
  intro n k
  obtain ⟨j, hj⟩ := branch.front_exists_l (enum_sub n)
  let m := slot j hj.2.1 k
  have hm : k < m := (replete j hj.2.1 k).1
  have hcode : enum m = j := (replete j hj.2.1 k).2
  refine ⟨m, hm, ?_⟩
  have hBm : M.mem (enum m) B := by simpa only [hcode] using hj.2.1
  rcases hj.2.2 with h | h
  · exact ⟨hj.1, hBm, Or.inl (h.trans hcode.symm)⟩
  · exact ⟨hj.1, hBm, Or.inr (by simpa only [hcode.symm] using h)⟩

/-! 以原阶段代码为参数的 front 版本；它正好对应 bookkeeping 的 hit 条件。 -/
theorem It_branch_d.external_front_code_l {α T B : M.Domain}
    (branch : It_branch_d α T B) (enum : Nat → M.Domain)
    (slot : ∀ j, M.mem j B → Nat → Nat)
    (replete : ∀ j hj k, k < slot j hj k ∧ enum (slot j hj k) = j) :
    ∀ c, M.mem c α → ∀ k, ∃ m, k < m ∧ It_front_d α B c (enum m) := by
  intro c hc k
  obtain ⟨j, hj⟩ := branch.front_exists_l hc
  let m := slot j hj.2.1 k
  have hm : k < m := (replete j hj.2.1 k).1
  have hcode : enum m = j := (replete j hj.2.1 k).2
  have hBm : M.mem (enum m) B := by simpa only [hcode] using hj.2.1
  refine ⟨m, hm, ⟨hc, hBm, ?_⟩⟩
  rcases hj.2.2 with h | h
  · exact Or.inl (h.trans hcode.symm)
  · exact Or.inr (by simpa only [hcode.symm] using h)

/-! 当阶段代码本身有显式外部可数枚举时，前端接口可直接消费
`Bk_countable` 的无重复 section；分支节点仍只需提供自己的 slot。 -/
theorem It_branch_d.external_front_code_countable_l {α T B : M.Domain}
    (branch : It_branch_d α T B)
    (count : Bk_countable {c : M.Domain // M.mem c α})
    (slot : ∀ j, M.mem j B → Nat → Nat)
    (replete : ∀ j hj k, k < slot j hj k ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (slot j hj k)).1 = ⟨j, branch.subset j hj⟩) :
    ∀ c : {c : M.Domain // M.mem c α}, ∀ k,
      ∃ m, k < m ∧ It_front_d α B c.1
        ((count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) := by
  intro c k
  apply branch.external_front_code_l
    (fun n => (count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1).1)
    slot
    (fun j hj l => by
      have ha := replete j hj l
      exact ⟨ha.1, congrArg Subtype.val ha.2⟩)
    c.1 c.2 k

/-! 显式阶段枚举已经足够时，分支节点的重复 slot 由同一个 pairing
自动产生，不再把 slot/replete 作为调用端参数。 -/
theorem It_branch_d.external_front_code_auto_l {α T B : M.Domain}
    (branch : It_branch_d α T B)
    (count : Bk_countable {c : M.Domain // M.mem c α}) :
    ∀ c : {c : M.Domain // M.mem c α}, ∀ k,
      ∃ m, k < m ∧ It_front_d α B c.1
        ((count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) := by
  let slot : ∀ j, M.mem j B → Nat → Nat := fun j hj k =>
    YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l
      (count.pick ⟨j, branch.subset j hj⟩) (k + 1)
  have replete : ∀ j hj k, k < slot j hj k ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (slot j hj k)).1 = ⟨j, branch.subset j hj⟩ := by
    intro j hj k
    simpa only [slot] using
      (count.replete_l (c := ⟨j, branch.subset j hj⟩) k)
  exact branch.external_front_code_countable_l count slot replete

theorem It_branch_d.order_l (hKP : M.Models KP) {α T B : M.Domain}
    (h : It_order_d α T) (b : It_branch_d α T B) : ∃ L, Di_order_d B L ∧
      ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T := by
  let φ : Delta0BinarySchema 1 := {
    body := rd_entry0_m (.bound 1) .newest (.bound 2), delta0 := rd_entry0_delta_l .. }
  let ρ : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  obtain ⟨L, ls⟩ := rw_rel_exists_l hKP φ ρ B
  have read i j : Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T :=
    (ls.entry_l hKP).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry0_sat_l hKP.1 ..)
  refine ⟨L, ⟨fun i hi => (read i i).mpr ⟨hi, hi, h.refl i (b.subset i hi)⟩,
    fun i j k hij hjk => (read i k).mpr ⟨((read i j).mp hij).1, ((read j k).mp hjk).2.1,
      h.trans i j k ((read i j).mp hij).2.2 ((read j k).mp hjk).2.2⟩,
    fun i j hij => ⟨((read i j).mp hij).1, ((read i j).mp hij).2.1⟩, ?_⟩, read⟩
  intro i j hi hj
  rcases b.chain i j hi hj with hij | hji
  · exact ⟨j, hj, (read i j).mpr ⟨hi, hj, hij⟩, (read j j).mpr ⟨hj, hj, h.refl j (b.subset j hj)⟩⟩
  · exact ⟨i, hi, (read i i).mpr ⟨hi, hi, h.refl i (b.subset i hi)⟩, (read j i).mpr ⟨hj, hi, hji⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
