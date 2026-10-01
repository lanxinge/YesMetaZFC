import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Bound

/-! # 分级规范码名 (序数界,内部高度,构造树)

第一坐标 α 要求构造树属于 rud(α)，第二坐标给出语法高度界。
同一树可以有多个名字；以下固定所有名字的次序，不预先选择最小名字。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pn_name_d (v a h c : M.Domain) : Prop := Rd_triple_d v a h c ∧ M.IsOrdinal a ∧ KP.N0_d h ∧
  Ps_height_d h c ∧ ∃ C, Rd_closure_d a C ∧ M.mem c C
def Pn_valid_d (v : M.Domain) : Prop := ∃ a h c, Pn_name_d v a h c

def Pn_key_d (a h c b m d : M.Domain) : Prop :=
  M.mem a b ∨ (a = b ∧ (M.mem h m ∨ (h = m ∧ Po_lt_d c d)))
def Pn_lt_d (v w : M.Domain) : Prop := ∃ a h c b m d,
  Rd_triple_d v a h c ∧ Rd_triple_d w b m d ∧ Pn_key_d a h c b m d

theorem pn_lt_iff_l {v w a h c b m d : M.Domain} (hv : Rd_triple_d v a h c) (hw : Rd_triple_d w b m d) :
    Pn_lt_d v w ↔ Pn_key_d a h c b m d := by
  constructor
  · rintro ⟨a', h', c', b', m', d', hv', hw', he⟩
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hw' hw
    exact he
  · exact fun he => ⟨a, h, c, b, m, d, hv, hw, he⟩

theorem pn_name_exists_l (hM : M.Models KPi) {c : M.Domain} (hc : Ps_valid_d c) : ∃ v a h, Pn_name_d v a h c := by
  obtain ⟨a, C, ha, hC, hcC⟩ := po_code_bound_l hM hc
  obtain ⟨n, T, F, hf, hcn⟩ := hc
  obtain ⟨v, hv⟩ := pc_triple_exists_l (KPi.models_iff_l.mp hM).1 a n c
  exact ⟨v, a, n, hv, ha, (hf.at_l hcn).2.2.1, ⟨n, Or.inr rfl, T, F, hf, hcn⟩, C, hC, hcC⟩

def Pn_eval_d (v x : M.Domain) : Prop := ∃ a h c, Pn_name_d v a h c ∧ Pc_eval_d c x

theorem pn_eval_total_l (hM : M.Models KPi) {v : M.Domain} (hv : Pn_valid_d v) : ∃ x, Pn_eval_d v x := by
  obtain ⟨a, h, c, hv⟩ := hv
  obtain ⟨x, hx⟩ := ps_eval_total_l hM hv.2.2.2.1.valid_l
  exact ⟨x, a, h, c, hv, hx⟩

theorem pn_eval_unique_l (hM : M.Models KPi) {v x y : M.Domain} (hx : Pn_eval_d v x) (hy : Pn_eval_d v y) : x = y := by
  obtain ⟨a, h, c, hv, hx⟩ := hx
  obtain ⟨b, m, d, hw, hy⟩ := hy
  obtain ⟨_, _, rfl⟩ := pc_triple_inj_l hv.1 hw.1
  exact pc_eval_unique_l hM hx hy

theorem pn_cover_l (hM : M.Models KPi) (x : M.Domain) : L_d x ↔ ∃ v, Pn_eval_d v x := by
  constructor
  · intro hx
    obtain ⟨c, hc, hx⟩ := (pc_valid_cover_l hM x).mp hx
    obtain ⟨v, a, h, hv⟩ := pn_name_exists_l hM hc
    exact ⟨v, a, h, c, hv, hx⟩
  · rintro ⟨v, a, h, c, _, hx⟩; exact pc_eval_in_l_l hM hx

end YesMetaZFC.SetTheory.InnerModel
