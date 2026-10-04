import YesMetaZFC.Model.SetTheory.Internal.Pointwise
import YesMetaZFC.Model.SetTheory.Internal.PointwiseValue

/-! # 源模型内的逐点真值集合

给定真实代表函数赋值，编译任意内部公式，再在源中分离其真值逆像。
逐点赋值由唯一值收集实际构造；参数赋值不必自身属于源模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smap_pe_trace_l {ω χ c d X R H S q D E F n r b a}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ)
    (hH : H_d I χ H) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (hn : Smem_d I d H S)
    (hq : Smap_d I ω c d X H q) (hD : M.mem D X) (hE : M.IsFunctionSpace I E ω X)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (hB : Sbound_d I F b)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X a) :
    ∃ A, M.mem A X ∧ ∀ p, M.mem p A ↔ M.mem p D ∧ Pe_sat_d I b D X R E F n r a p := by
  obtain ⟨t, ht, htω⟩ := hω.1.2 b hb
  obtain ⟨m, G, T, h⟩ := pe_compile_bound_l hZFC hω hχ hωχ hH hX hm hn hq hD hE hF hb hB ht
  obtain ⟨k, hk, hrk⟩ := h.2.1.2.2 r hr
  have bt : M.MemberSubset b t := fun i hi => (ht i).mpr (Or.inl hi)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hbt : b ≠ t := fun e => ir t (e ▸ ht.predecessor_mem)
  have htb : ¬ M.mem t b := fun hi => ir t (bt t hi)
  obtain ⟨aD, hDa, haD⟩ := senv_update_exists_l I hZF ((hE a).mp ha) hb hD
  obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
  obtain ⟨A, hAX, hA⟩ := smap_separation_l I hZF hω hX (ZF.h_transitive_l I hZF hH) hm hn hq hP
    (fun C hC => ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hDH C ((hP C).mp hC)) hE h.1 hk htω
    ((hE aD).mpr haD) hDD
  have read p a' f (hp : M.mem p D) (hu : Senv_update_d I aD t p a')
      (hf : M.mem f E) (he : Pe_assign_d I b D X a f p) :
      Ssat_d I X R E F n r f ↔ Ssat_d I X R E G m k a' := by
    have agree : Senv_agree_d I b a a' := fun i x hi =>
      (hDa.agree_l I (ir b) i x hi).trans (hu.agree_l I htb i x hi)
    exact h.2.2 r k hrk p a' f hp ((hE a').mpr (hu.function_l I haD htω (hX D hD p hp))) hf
      ((hu.2 b D).mpr (Or.inr ⟨hbt, (hDa.2 b D).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      ((hu.2 t p).mpr (Or.inl ⟨rfl, rfl⟩)) (he.congr_left_l I agree)
  refine ⟨A, hAX, fun p => (hA p).trans ?_⟩
  apply and_congr_right
  intro hp
  constructor
  · rintro ⟨a', hu, hs⟩
    obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF hX hE ha (hω.transitive hZF b hb) hp hm.1.2.1 hh
    exact ⟨f, hf, he, (read p a' f hp hu hf he).mpr hs⟩
  · rintro ⟨f, hf, he, hs⟩
    obtain ⟨a', hu, _⟩ := senv_update_exists_l I hZF haD htω (hX D hD p hp)
    exact ⟨a', hu, (read p a' f hp hu hf he).mp hs⟩

end YesMetaZFC.SetTheory.Internal
