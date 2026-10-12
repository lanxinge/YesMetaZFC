import YesMetaZFC.Model.SetTheory.Internal.LocalType

/-! # 同一完整类型的指定点与有限参数真值

第一个公式变量解释为指定序数，其余变量解释为共同参数域中的原对象。
查询在两个实现之前固定，因此同一类型的成员关系直接给出真值对应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 原公式的纸面赋值 (δ,a₀,…,aₖ₋₁)，不选择任何载体基点。 -/
def Tt_realized_d.point_env_l {ω c X R n s δ U D t : M.Domain}
    (h : Tt_realized_d I ω c X R n s δ U D t) {k : Nat} (a : Fin k → M.Domain)
    (ha : ∀ i, M.mem (a i) U) : Env (smdl_structure_l I (R := R) h.model.2.1) (k+1) :=
  ⟨Fin.cases ⟨δ, h.point⟩ (fun i => ⟨a i, h.constants (a i) (ha i)⟩), fun _ => ⟨δ, h.point⟩⟩

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 包括重复参数和任意参数顺序；两边可位于不同秩层、具有不同指定点。 -/
theorem Tt_realized_d.point_congr_l {ω n U D t c X R s δ d Y S r ε : M.Domain}
    (hω : M.IsOmega ω) (h : Tt_realized_d Q ω c X R n s δ U D t)
    (g : Tt_realized_d Q ω d Y S n r ε U D t) {k : Nat}
    (φ : Formula 1 (k+1)) (hφ : φ.FreeClosed) (a : Fin k → M.Domain) (ha : ∀ i, M.mem (a i) U) :
    Formula.satisfies (h.point_env_l Q a ha) φ ↔ Formula.satisfies (g.point_env_l Q a ha) φ := by
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice (fun i => (Q).total (a i) (a i))
  let v : Fin (k+1) → M.Domain := Fin.cases n b
  have names : ∀ i, Tn_name_d n U (v i) :=
    Fin.cases (Or.inr (Or.inl rfl)) (fun i => Or.inr (Or.inr ⟨a i, ha i, hb i⟩))
  have values {c X R s δ} (h : Tt_realized_d Q ω c X R n s δ U D t) :
      ∀ i, Tn_value_d n s δ (v i) ((h.point_env_l Q a ha).bound i).val :=
    Fin.cases (Or.inr (Or.inl ⟨rfl, rfl⟩)) (fun i => Or.inr (Or.inr (hb i)))
  obtain ⟨p, _, read⟩ := tt_fixed_query_l hZF hω h.pool φ hφ v names
  exact (read c X R s δ t h (h.point_env_l _ a ha) (values h)).symm.trans
    (read d Y S r ε t g (g.point_env_l _ a ha) (values g))

end YesMetaZFC.SetTheory.Internal
