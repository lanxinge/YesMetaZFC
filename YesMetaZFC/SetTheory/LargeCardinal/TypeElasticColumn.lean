import YesMetaZFC.Model.SetTheory.Internal.TypeDomain
import YesMetaZFC.Model.SetTheory.Internal.TypeColumn

/-! # 弹性查询的合法名字列

原 n 个变量后依次放置 ω、n、指定常量 δ、κ。非零极限 κ 已包含全部
内部自然数；ω<κ 时 ω∈Vκ，ω=κ 时使用已有的 κ 常量。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ee_stretch_code_d (ω n κ v d e z p : M.Domain) : Prop := ∃ C kw kn kk,
  KPair_d M p z C ∧ KPair_d M kw ω ω ∧ KPair_d M kn n n ∧ KPair_d M kk κ κ ∧
    (∀ i, M.mem i n → Rd_entry_d i i C) ∧ Rd_entry_d n kw C ∧ Rd_entry_d v kn C ∧
      Rd_entry_d d n C ∧ Rd_entry_d e kk C

theorem ee_column_l {ω n v d e κ U N : M.Domain} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hv : M.SuccessorOf v n) (hd : M.SuccessorOf d v) (he : M.SuccessorOf e d)
    (hωU : M.mem ω U) (hnU : M.mem n U) (hκU : M.mem κ U) (names : Tn_names_d n U N) :
    ∃ b C kw kn kk, M.SuccessorOf b e ∧ M.mem b ω ∧ M.IsSetFunctionFromTo I C b N ∧
      (I).Codes kw ω ω ∧ (I).Codes kn n n ∧ (I).Codes kk κ κ ∧
      (∀ i, M.mem i n → Rd_entry_d i i C) ∧
      Rd_entry_d n kw C ∧ Rd_entry_d v kn C ∧ Rd_entry_d d n C ∧ Rd_entry_d e kk C := by
  have ho := hω.members_areOrdinals hZF n hn
  have vo := KP.successor_isOrdinal (ZF.modelsKP hZF) ho hv
  have dord := KP.successor_isOrdinal (ZF.modelsKP hZF) vo hd
  have eo := KP.successor_isOrdinal (ZF.modelsKP hZF) dord he
  have vω : M.mem v ω := by obtain ⟨v', h, hω⟩ := hω.1.2 n hn; exact Structure.SuccessorOf.eq hZF.1 h hv ▸ hω
  have dω : M.mem d ω := by obtain ⟨d', h, hω⟩ := hω.1.2 v vω; exact Structure.SuccessorOf.eq hZF.1 h hd ▸ hω
  have eω : M.mem e ω := by obtain ⟨e', h, hω⟩ := hω.1.2 d dω; exact Structure.SuccessorOf.eq hZF.1 h he ▸ hω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 e eω
  obtain ⟨kw, hw⟩ := (I).total ω ω
  obtain ⟨kn, hnn⟩ := (I).total n n
  obtain ⟨kk, hk⟩ := (I).total κ κ
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => n⟩
  have sat i x : φ.denote ρ i x ↔ x = i := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨f, base, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := N)
    (fun i _ => ⟨i, (sat i i).mpr rfl⟩)
    (fun i _ x y hx hy => ((sat i x).mp hx).trans ((sat i y).mp hy).symm)
    (fun i x hi hx => ((sat i x).mp hx).symm ▸ (names i).mpr (Or.inl hi))
  obtain ⟨f₁, h₁, old₁, end₁⟩ := tt_column_append_l hZF ho hv base ((names kw).mpr (Or.inr (Or.inr ⟨ω, hωU, hw⟩)))
  obtain ⟨f₂, h₂, old₂, end₂⟩ := tt_column_append_l hZF vo hd h₁ ((names kn).mpr (Or.inr (Or.inr ⟨n, hnU, hnn⟩)))
  obtain ⟨f₃, h₃, old₃, end₃⟩ := tt_column_append_l hZF dord he h₂ ((names n).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨C, hC, old₄, end₄⟩ := tt_column_append_l hZF eo hb h₃ ((names kk).mpr (Or.inr (Or.inr ⟨κ, hκU, hk⟩)))
  have ne := (he n).mpr (Or.inl ((hd n).mpr (Or.inl hv.predecessor_mem)))
  have ve := (he v).mpr (Or.inl hd.predecessor_mem)
  refine ⟨b, C, kw, kn, kk, hb, hbω, hC, hw, hnn, hk, ?_, ?_, ?_, ?_, end₄⟩
  · intro i hi
    exact (old₄ i i (eo.transitive n ne i hi)).mpr ((old₃ i i ((hd i).mpr (Or.inl ((hv i).mpr (Or.inl hi))))).mpr
      ((old₂ i i ((hv i).mpr (Or.inl hi))).mpr ((old₁ i i hi).mpr ((graph i i).mpr ⟨hi, (sat i i).mpr rfl⟩))))
  · exact (old₄ n kw ne).mpr ((old₃ n kw ((hd n).mpr (Or.inl hv.predecessor_mem))).mpr ((old₂ n kw hv.predecessor_mem).mpr end₁))
  · exact (old₄ v kn ve).mpr ((old₃ v kn hd.predecessor_mem).mpr end₂)
  · exact (old₄ d n he.predecessor_mem).mpr end₃

end YesMetaZFC.SetTheory.LargeCardinal
