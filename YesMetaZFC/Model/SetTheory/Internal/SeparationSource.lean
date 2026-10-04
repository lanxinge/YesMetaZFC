import YesMetaZFC.Model.SetTheory.Internal.DeltaCode
import YesMetaZFC.Model.SetTheory.Internal.Separation
import YesMetaZFC.SetTheory.Hereditary

/-! # 源中有界关系的实际分离

固定有界原公式先编译为内部程序，再沿已有初等嵌入回拉分离集。
目标只用 H(χ) 对子集的封闭，χ 为极限序数即可，背景保持 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smap_separate_source_l (hZF : M.Models ZF) {ω χ c d X R H S q D}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (hn : Smem_d I d H S) (hq : Smap_d I ω c d X H q)
    {p} (φ : UnarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p)
    (hρ : ∀ i, M.mem (ρ.bound i) X) (hD : M.mem D X) :
    ∃ A, M.mem A X ∧ ∀ x, M.mem x A ↔ M.mem x D ∧ φ.denote ρ x := by
  obtain ⟨z, hz⟩ := hm.1.2.1
  obtain ⟨a, n, F, r, v, hF, hv, hc⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have hinj : Function.Injective v := fun i j he => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (he.symm ▸ hv j))
  have hωv i := num_mem_l hZF.1 hω (hv i)
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hm.1.2.1 v (ρ.push z).bound hinj hωv (Fin.cases hz hρ)
  have read x g (hx : M.mem x X) (hu : Senv_update_d I f (v 0) x g) :
      Ssat_d I X R E F n r g ↔ φ.denote ρ x := by
    have params : ∀ i, M.PairMember I (v i) ((ρ.push x).bound i) g := Fin.cases
      ((hu.2 (v 0) x).mpr (Or.inl ⟨rfl, rfl⟩)) (fun i =>
        (hu.2 (v i.succ) (ρ.bound i)).mpr (Or.inr ⟨fun h => Fin.succ_ne_zero i (hinj h), hp i.succ⟩))
    exact hc.delta_l I φ.freeClosed hd (ρ.push x) hX hm hE
      ((hE g).mpr (hu.function_l I ((hE f).mp hf) (hωv 0) hx)) params
  obtain ⟨D', hDH, hDD⟩ := hq.1.1.2.2 D hD
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D'
  obtain ⟨A, hAX, hA⟩ := smap_separation_l I hZF hω hX (ZF.h_transitive_l I hZF hH) hm hn hq hP
    (fun C hC => ZF.h_subsets_l I hZF hχ hH hDH C ((hP C).mp hC)) hE hF.2.1 hF.2.2 (hωv 0) hf hDD
  refine ⟨A, hAX, fun x => (hA x).trans (and_congr_right fun hx => ?_)⟩
  refine ⟨fun ⟨g, hu, ht⟩ => (read x g (hX D hD x hx) hu).mp ht, fun ht => ?_⟩
  obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hωv 0) (hX D hD x hx)
  exact ⟨g, hu, (read x g (hX D hD x hx) hu).mpr ht⟩

end YesMetaZFC.SetTheory.Internal
