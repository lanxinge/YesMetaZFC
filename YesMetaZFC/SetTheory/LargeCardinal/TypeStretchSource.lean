import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchFormula

/-! # 原伸展公式在传递外层中的精确读取

有界矩阵的全部见证留在所属源中，因此外层只需传递并拥有公式参数。
原超幂、相对支撑层及源内小关系坍塌提供实际实例；外层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {T : M.Domain}
  (hT : M.TransitiveSet T) (nt : Nonempty {x // M.mem x T})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "N₀" => rt_model_l T nt

include hT in
theorem et_stretch_source_l {d K R V c c' Z S j} (ρ : Env N₀ d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ).val (κ.eval ρ).val K (X.eval ρ).val R)
    (power : Sc_power_d (X.eval ρ).val)
    (family : Em_source_d (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (X.eval ρ).val (F.eval ρ).val)
    (hm : Smem_d I c (X.eval ρ).val R) (hn : Smem_d I c' Z S)
    (ultra : It_ultra_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val c c' j)
    (hL : M.mem (L.eval ρ).val (X.eval ρ).val) (hF : M.mem (F.eval ρ).val (X.eval ρ).val)
    (hl : M.IsLimitOrdinal (L.eval ρ).val) (level : Er_level_d (X.eval ρ).val (L.eval ρ).val V)
    (hκ : M.mem (κ.eval ρ).val V) (ht : M.mem (t.eval ρ).val V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val
        (X.eval ρ).val R (t.eval ρ).val (D.eval ρ).val (v.eval ρ).val := by
  have read := et_stretch_sat_l hZF (K₀ := K) (R := R) (V := V) (c := c) (c' := c') (N := Z) (S := S) (j := j)
    (image_env_l (M := N₀) (N := M) Subtype.val ρ) ω κ L X F t D v
  simp only [eval_image_env_l (M := N₀) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hT nt (et_stretch_delta_l ..) ρ).trans
    (read source power family hm hn ultra hL hF hl level hκ ht)

end YesMetaZFC.SetTheory.LargeCardinal
