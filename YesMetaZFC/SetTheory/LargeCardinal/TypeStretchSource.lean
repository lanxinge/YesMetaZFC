import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchFormula
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderClosedLimit

/-! # 原伸展公式在传递外层中的精确读取

有界矩阵的全部见证留在所属源中，因此外层只需传递并拥有公式参数。
有界可数闭源从原短扩展器判断自动构造良基超幂；外层无需满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同源的有界可数闭性直接给出实际超幂，不向调用者索取超幂或测度族见证。 -/
theorem et_stretch_closed_l {d K R V} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R)
    (closed : Sc_bounded_omega_closed_d (ω.eval ρ) (X.eval ρ)) (power : Sc_power_d (X.eval ρ))
    (loc : It_local_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ))
    (hl : M.IsLimitOrdinal (L.eval ρ)) (level : Er_level_d (X.eval ρ) (L.eval ρ) V)
    (hκ : M.mem (κ.eval ρ) V) (ht : M.mem (t.eval ρ) V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  obtain ⟨P, hP, subsets⟩ := power K source.finite_mem
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨c', j, ultra, N, S, _, hn, _⟩ := it_ultra_exists_l hZF hm
    (loc.closed_limit_l hZFC source source closed (fun _ _ _ _ _ _ => Iff.rfl) hP subsets)
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory source.finite hP subsets)
  obtain ⟨_, _, hL, hF, _⟩ := loc
  exact et_stretch_sat_l hZF ρ ω κ L X F t D v source power family hm hn ultra hL hF hl level hκ ht

variable {T : M.Domain} (hT : M.TransitiveSet T) (nt : Nonempty {x // M.mem x T})
local notation "N₀" => rt_model_l T nt

include hT in
theorem et_stretch_source_l {d K R V} (ρ : Env N₀ d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ).val (κ.eval ρ).val K (X.eval ρ).val R)
    (closed : Sc_bounded_omega_closed_d (ω.eval ρ).val (X.eval ρ).val)
    (power : Sc_power_d (X.eval ρ).val)
    (loc : It_local_d (ω.eval ρ).val (X.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val)
    (hl : M.IsLimitOrdinal (L.eval ρ).val) (level : Er_level_d (X.eval ρ).val (L.eval ρ).val V)
    (hκ : M.mem (κ.eval ρ).val V) (ht : M.mem (t.eval ρ).val V) :
    Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
      Et_stretch_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val
        (X.eval ρ).val R (t.eval ρ).val (D.eval ρ).val (v.eval ρ).val := by
  have read := et_stretch_closed_l hZFC (K := K) (R := R) (V := V)
    (image_env_l (M := N₀) (N := M) Subtype.val ρ) ω κ L X F t D v
  simp only [eval_image_env_l (M := N₀) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hT nt (et_stretch_delta_l ..) ρ).trans
    (read source closed power loc hl level hκ ht)

end YesMetaZFC.SetTheory.LargeCardinal
