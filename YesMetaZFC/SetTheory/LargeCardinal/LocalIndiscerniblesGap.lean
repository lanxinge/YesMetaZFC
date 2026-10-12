import YesMetaZFC.SetTheory.LargeCardinal.LocalIndiscerniblesLeast
import YesMetaZFC.Model.SetTheory.Internal.FiniteTailSource
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 原局部不可分辨点之间的实际高度间隔

两点的有限后继尾长由共同参数域中的内部自然数命名。
类型相同使尾长相同，故低点的任意有限后继仍严格低于高点。
不修改原最小对的定义，也不向游戏参数另加间隔条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Li_pair_d.finite_gap_l {ω e γ U D ν μ k β : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hU : V_d I γ U) (hwU : M.mem ω U) (pool : Tt_pool_d I ω e U D)
    (pair : Li_pair_d I ω e U D ν μ) (hk : M.mem k ω) (sum : M.IsOrdinalAddition I β ν k) : M.mem β μ := by
  obtain ⟨ξ, ζ, X, Y, c, R, d, S, t, sx, sy, hx, hy, mx, my, low, high, _⟩ := pair.read_l hZF hω he heω pool
  have lx := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I pair.1).limit_value (hω.isLimitOrdinal hZF) sx
  have ly := (ZF.ordinalAddition_isNormalOrdinalFunction hZF I pair.2.1).limit_value (hω.isLimitOrdinal hZF) sy
  obtain ⟨n, tail⟩ := ZF.ot_tail_exists_l I hZF hω pair.1
  let a : Fin 2 → M.Domain := Fin.cases ω (fun _ => n)
  have ha : ∀ i, M.mem (a i) U := Fin.cases hwU (fun _ => ZF.v_transitive_l I hZF hU ω hwU n tail.1)
  let φ : Formula 1 3 := ot_tail_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 2) (.bound 0)
  have read {η Z b H v} (hη : M.IsLimitOrdinal η) (hZ : V_d I η Z)
      (model : Smem_d I b Z H) (type : Tt_realized_d I ω b Z H e e v U D t) :
      Formula.satisfies (type.point_env_l I a ha) φ ↔ Ot_tail_d I ω n v := by
    let nz : Nonempty {x // M.mem x Z} := ⟨⟨v, type.point⟩⟩
    let ρ : Env (rt_model_l Z nz) 3 := ⟨Fin.cases ⟨v, type.point⟩
      (fun i => ⟨a i, type.constants _ (ha i)⟩), fun _ => ⟨v, type.point⟩⟩
    exact (smem_formula_l I model nz φ ρ).symm.trans
      (ot_tail_source_l hZF hη hZ nz ρ (.bound 1) (.bound 2) (.bound 0))
  have same := low.point_congr_l hZF hω high φ (by simp -implicitDefEqProofs [φ]) a ha
  have tail' := (read ly hy my high).mp (same.mp ((read lx hx mx low).mpr tail))
  exact ZF.ot_tail_gap_l I hZF hω tail tail' pair.2.2.1 hk sum

end YesMetaZFC.SetTheory.LargeCardinal
