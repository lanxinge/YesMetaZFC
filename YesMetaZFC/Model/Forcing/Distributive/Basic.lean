import YesMetaZFC.Model.Forcing.Truth.Definability

/-! # 内部可数分配性

可数稠密族由实际集合关系 H 的各行给出。ZF 把任意带有限参数的公式族
收集为这样的关系码，因此消费者无需选择函数或可数闭性。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Distributive_d (B R z ω : M.Domain) : Prop := ∀ H {p},
  (∀ i, M.mem i ω → Dense_d M B R z (fun q => Entry_d M i q H) p) →
  (∀ i, M.mem i ω → Lower_d M B R z (fun q => Entry_d M i q H)) →
  M.mem p B → p ≠ z → ∃ q, Below_d M B R z q p ∧ ∀ i, M.mem i ω → Entry_d M i q H

/-- 可定义族先成为模型中的关系集合，再使用可数分配性。 -/
theorem distributive_intersection_l (hZF : M.Models ZF) {B R z ω} (hD : Distributive_d (M := M) B R z ω)
    {n} (φ : BinarySchema n) (ρ : Env M n) {p}
    (hd : ∀ i, M.mem i ω → Dense_d M B R z (φ.denote ρ i) p)
    (hl : ∀ i, M.mem i ω → Lower_d M B R z (φ.denote ρ i)) (hp : M.mem p B) (hn : p ≠ z) :
    ∃ q, Below_d M B R z q p ∧ ∀ i, M.mem i ω → φ.denote ρ i q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) ω B
  obtain ⟨W, hW⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have hw i (hi : M.mem i ω) : M.mem i W := (hW i).mpr ⟨ω, (hP ω).mpr (Or.inl rfl), hi⟩
  have hb q (hq : M.mem q B) : M.mem q W := (hW q).mpr ⟨B, (hP B).mpr (Or.inr rfl), hq⟩
  obtain ⟨H, _, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  obtain ⟨q, hq, hi⟩ := hD H (fun i hi p hp => by
    obtain ⟨q, hq, hφ⟩ := hd i hi p hp
    exact ⟨q, hq, (he i q).mpr ⟨hw i hi, hb q hq.1, hφ⟩⟩)
    (fun i hi p q hp hq h => (he i q).mpr
      ⟨hw i hi, hb q hq.1, hl i hi p q hp hq ((he i p).mp h).2.2⟩) hp hn
  exact ⟨q, hq, fun i h => ((he i q).mp (hi i h)).2.2⟩

end YesMetaZFC.Model.Forcing.Internal
