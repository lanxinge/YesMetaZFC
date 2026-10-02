import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 可定义非空序数类的最小元

先用一个给定见证的后继截取集合，再应用分离和正则。全过程在模型内部进行，
不使用序数的外部良基性。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ordinal_min_l (hZF : M.Models ZF) {n} (φ : UnarySchema n) (ρ : Env M n)
    {a} (ha : M.IsOrdinal a) (h : φ.denote ρ a) :
    ∃ b, M.IsOrdinal b ∧ φ.denote ρ b ∧ ∀ c, M.mem c b → ¬ φ.denote ρ c := by
  obtain ⟨s, hs, has⟩ := KP.ordinal_successor_l (modelsKP hZF) ha
  obtain ⟨D, hd⟩ := separation_exists_d hZF φ ρ s
  obtain ⟨b, hb, hm⟩ := KP.mem_minimal_exists_d (modelsKP hZF) ⟨a, (hd a).mpr ⟨has.predecessor_mem, h⟩⟩
  obtain ⟨hbS, hbφ⟩ := (hd b).mp hb
  exact ⟨b, hs.mem hbS, hbφ, fun c hc hp => hm c ((hd c).mpr ⟨hs.transitive b hbS c hc, hp⟩) hc⟩

end YesMetaZFC.SetTheory.ZF
