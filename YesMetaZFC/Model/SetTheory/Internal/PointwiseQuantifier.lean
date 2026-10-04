import YesMetaZFC.Model.SetTheory.Internal.PointwiseSteps
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 存在量词的逐点翻译

把对象见证改为定义域上的源内函数见证，并加入实际函数域代码。正向使用
源内常值函数，反向读取给定点处的值；两边均构造真实单坐标赋值更新。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pe_ex_step_l {ω χ c d X R H S q D E F n V b t m G r z i j v u σ}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hV : Seval_d I X R E F n V) (hG : Sfm_d I ω m G)
    (hc : M.PairMember I r z F) (hs : Sop_d I 3 z i j) (hv : M.mem v m)
    (hj : Pe_row_d I b t D X R E F n m G j v) (hσ : M.mem σ ω)
    (hi : M.mem i σ) (hb : M.mem b σ) (hu : M.mem u σ)
    (hub : u ≠ b) (hui : u ≠ i) (hbi : b ≠ i) (hti : t ≠ i) :
    ∃ l J k, Sbuild_d I ω m G l J k ∧ Pe_row_d I b t D X R E F n l J r k := by
  have hiω := hω.transitive hZF σ hσ i hi
  obtain ⟨n₁, F₁, r₁, h₁, a₁⟩ := sfm_function_l I hZF hω hG hσ hi hb hu hub hui
  obtain ⟨n₂, F₂, r₂, h₂, a₂⟩ := sfm_and_l I hZF hω h₁.program h₁.root (h₁.span v hv)
  obtain ⟨l, J, k, h₃, a₃⟩ := sfm_ex_l I hZF hω h₂.program hiω h₂.root
  refine ⟨l, J, k, (h₁.comp I h₂).comp I h₃, fun p a f hp ha hf hDa ht he => ?_⟩
  have body B a' (hB : M.mem B X) (ha' : Senv_update_d I a i B a') :
      Ssat_d I X R E F₂ n₂ r₂ a' ↔ Sfun_d X D B ∧ Ssat_d I X R E G m v a' := by
    have hA := (hE a').mpr (ha'.function_l I ((hE a).mp ha) hiω hB)
    rw [a₂ X R E a' hA, a₁ X R E c a' B D hX hm hE hA
      ((ha'.2 i B).mpr (Or.inl ⟨rfl, rfl⟩)) ((ha'.2 b D).mpr (Or.inr ⟨hbi, hDa⟩)),
      ← h₁.sat_l I hZF hG hv X R E a']
  have row B x a' f' (hB : Sfun_d X D B) (hx : Rd_entry_d p x B)
      (ha' : Senv_update_d I a i B a') (hf' : Senv_update_d I f i x f') :
      Ssat_d I X R E F n j f' ↔ Ssat_d I X R E G m v a' :=
    hj p a' f' hp ((hE a').mpr (ha'.function_l I ((hE a).mp ha) hiω hB.1))
      ((hE f').mpr (hf'.function_l I ((hE f).mp hf) hiω ((hB.function_l hX).bound_l hx).2))
      ((ha'.2 b D).mpr (Or.inr ⟨hbi, hDa⟩)) ((ha'.2 t p).mpr (Or.inr ⟨hti, ht⟩))
      (he.update_l I hB hx ha' hf')
  rw [ssat_exists_l I hZF hF hV hc hs hf, a₃ X R E a ha]
  constructor
  · rintro ⟨x, f', hx, hf', ht⟩
    obtain ⟨B, C, hBX, hCX, hBC, hB⟩ := smap_constant_l hZFC hω hχ hωχ hH hX hm hn hq hD hx
    obtain ⟨a', ha', _⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hiω hBX
    have hfun : Sfun_d X D B := ⟨hBX, C, hCX, hBC⟩
    exact ⟨B, a', hBX, ha', (body B a' hBX ha').mpr
      ⟨hfun, (row B x a' f' hfun ((hB p x).mpr ⟨hp, rfl⟩) ha' hf').mp ht⟩⟩
  · rintro ⟨B, a', hBX, ha', ht⟩
    obtain ⟨hB, hs⟩ := (body B a' hBX ha').mp ht
    obtain ⟨x, hx, hpx⟩ := (hB.function_l hX).2.1 p hp
    obtain ⟨f', hf', _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hiω hx
    exact ⟨x, f', hx, hf', (row B x a' f' hB hpx ha' hf').mpr hs⟩

end YesMetaZFC.SetTheory.Internal
