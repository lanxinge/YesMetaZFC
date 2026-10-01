import YesMetaZFC.SetTheory.CumulativeSelection

/-! # 原模型内部的集合秩

秩是包含全部成员的最早累积层的指标。存在性从已构造的最早非空层取得，
而非使用宿主良基递归；成员层级与秩比较的等价式适用于外部非良基地模型。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rk_d (x α : M.Domain) : Prop := ∃ V, V_d I α V ∧ M.MemberSubset x V ∧
  ∀ β W, V_d I β W → M.MemberSubset x W → M.MemberSubset α β

def rk_m {n} (x α : Term n) : Formula 1 n :=
  .existsE (.conj (v_m 𝒞 α.weaken .newest) (.conj (Formula.subset x.weaken .newest)
    (.forallE (.forallE (.imp (v_m 𝒞 (.bound 1) .newest)
      (.imp (Formula.subset x.weaken.weaken.weaken .newest)
        (Formula.subset α.weaken.weaken.weaken (.bound 1))))))))
derive_free_closed rk_m

theorem rk_sat_l (hE : Extensional M) {n} (ρ : Env M n) (x α : Term n) :
    Formula.satisfies ρ (rk_m (𝒞 := 𝒞) x α) ↔ Rk_d I (x.eval ρ) (α.eval ρ) := by
  simp only [rk_m, Rk_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_sat_l I hE, Formula.satisfies_subset_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem Rk_d.ordinal {x α} (h : Rk_d I x α) : M.IsOrdinal α :=
  h.elim fun _ h => v_ordinal_l I h.1

theorem rk_unique_l (hE : Extensional M) {x α β} (h : Rk_d I x α) (k : Rk_d I x β) : α = β := by
  obtain ⟨V, hV, hxV, h⟩ := h
  obtain ⟨W, hW, hxW, k⟩ := k
  exact hE.eq_of_same_members α β (fun y => ⟨h β W hW hxW y, k α V hV hxV y⟩)

namespace ZF

/-- 内部集合秩实际存在，不要求模型成员关系在外部良基。 -/
theorem rk_exists_l (hZF : M.Models ZF) (x : M.Domain) : ∃ α, Rk_d I x α := by
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  let φ : UnarySchema 1 := { body := Formula.extensionalEq .newest (.bound 1) }
  have hφ y : φ.denote ρ y ↔ y = x := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨γ, S, V, hV, ⟨y, hy⟩, hS, hMin⟩ := v_min_exists_l I hZF φ ρ ⟨x, (hφ x).mpr rfl⟩
  have hyx := (hφ y).mp ((hS y).mp hy).2
  subst y
  obtain ⟨α, W, hαγ, hW, hxW⟩ := (v_unfold_l I hZF hV x).mp ((hS x).mp hy).1
  refine ⟨α, W, hW, hxW, fun β U hU hxU => ?_⟩
  obtain ⟨δ, hδ⟩ := KP.exists_successor (modelsKP hZF) β
  obtain ⟨Z, hZ⟩ := v_exists_l I hZF (KP.successor_isOrdinal (modelsKP hZF) (v_ordinal_l I hU) hδ)
  have hγδ := hMin δ ⟨Z, hZ, x, (v_unfold_l I hZF hZ x).mpr ⟨β, U, hδ.predecessor_mem, hU, hxU⟩, (hφ x).mpr rfl⟩
  rcases (hδ α).mp (hγδ α hαγ) with hαβ | hαβ
  · exact (v_ordinal_l I hU).transitive.memberSubset hαβ
  · exact fun a ha => (hαβ a).mp ha

/-- 层级成员资格恰好是秩严格小于层级指标。 -/
theorem rk_mem_l (hZF : M.Models ZF) {x α β V} (hx : Rk_d I x α) (hV : V_d I β V) :
    M.mem x V ↔ M.mem α β := by
  obtain ⟨W, hW, hxW, hMin⟩ := hx
  constructor
  · intro hx
    obtain ⟨γ, U, hγβ, hU, hxU⟩ := (v_unfold_l I hZF hV x).mp hx
    have hαγ := hMin γ U hU hxU
    by_cases he : M.SameMembers α γ
    · exact (hZF.1.eq_of_same_members α γ he).symm ▸ hγβ
    · have hαγ' := Structure.IsOrdinal.mem_of_properSubset hZF.1 (v_ordinal_l I hW)
        (v_ordinal_l I hU) ⟨hαγ, he⟩ (KP.difference_exists_d (modelsKP hZF) α γ)
      exact (v_ordinal_l I hV).transitive γ hγβ α hαγ'
  · exact fun hαβ => (v_unfold_l I hZF hV x).mpr ⟨α, W, hαβ, hW, hxW⟩

theorem rk_member_l (hZF : M.Models ZF) {x y α β} (hx : Rk_d I x α) (hy : Rk_d I y β)
    (hxy : M.mem x y) : M.mem α β := by
  obtain ⟨V, hV, hyV, _⟩ := hy
  exact (rk_mem_l I hZF hx hV).mp (hyV x hxy)

end ZF
end YesMetaZFC.SetTheory
